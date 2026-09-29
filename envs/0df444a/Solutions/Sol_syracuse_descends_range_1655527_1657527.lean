-- Prove2me | solution 1 for syracuse_descends_range_1655527_1657527
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:18:26.942812+00:00
-- url     : https://prove2.me/submissions/74ce1291-23ab-4bb4-a5c6-276758d9e5fc

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


theorem B2097181 : Blo 1655527 2097181 := bbase (se 3 (by rfl) ⟨393221, by rfl⟩ : syracuseStep 2097181 = 786443) (by norm_num)
theorem B2154533 : Blo 1655527 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B3727421 : Blo 1655527 3727421 := bbase (se 3 (by rfl) ⟨698891, by rfl⟩ : syracuseStep 3727421 = 1397783) (by norm_num)
theorem B9437269 : Blo 1655527 9437269 := bbase (se 8 (by rfl) ⟨55296, by rfl⟩ : syracuseStep 9437269 = 110593) (by norm_num)
theorem B8503381 : Blo 1655527 8503381 := bbase (se 8 (by rfl) ⟨49824, by rfl⟩ : syracuseStep 8503381 = 99649) (by norm_num)
theorem B5308517 : Blo 1655527 5308517 := bbase (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) (by norm_num)
theorem B3539045 : Blo 1655527 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B4194413 : Blo 1655527 4194413 := bbase (se 3 (by rfl) ⟨786452, by rfl⟩ : syracuseStep 4194413 = 1572905) (by norm_num)
theorem B8953973 : Blo 1655527 8953973 := bbase (se 5 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 8953973 = 839435) (by norm_num)
theorem B3727493 : Blo 1655527 3727493 := bbase (se 4 (by rfl) ⟨349452, by rfl⟩ : syracuseStep 3727493 = 698905) (by norm_num)
theorem B4538549 : Blo 1655527 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B2359477 : Blo 1655527 2359477 := bbase (se 5 (by rfl) ⟨110600, by rfl⟩ : syracuseStep 2359477 = 221201) (by norm_num)
theorem B2097353 : Blo 1655527 2097353 := bbase (se 2 (by rfl) ⟨786507, by rfl⟩ : syracuseStep 2097353 = 1573015) (by norm_num)
theorem B3727565 : Blo 1655527 3727565 := bbase (se 3 (by rfl) ⟨698918, by rfl⟩ : syracuseStep 3727565 = 1397837) (by norm_num)
theorem B1769693 : Blo 1655527 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B2097409 : Blo 1655527 2097409 := bbase (se 2 (by rfl) ⟨786528, by rfl⟩ : syracuseStep 2097409 = 1573057) (by norm_num)
theorem B2154757 : Blo 1655527 2154757 := bbase (se 4 (by rfl) ⟨202008, by rfl⟩ : syracuseStep 2154757 = 404017) (by norm_num)
theorem B3727637 : Blo 1655527 3727637 := bbase (se 6 (by rfl) ⟨87366, by rfl⟩ : syracuseStep 3727637 = 174733) (by norm_num)
theorem B2793757 : Blo 1655527 2793757 := bbase (se 3 (by rfl) ⟨523829, by rfl⟩ : syracuseStep 2793757 = 1047659) (by norm_num)
theorem B4194605 : Blo 1655527 4194605 := bbase (se 3 (by rfl) ⟨786488, by rfl⟩ : syracuseStep 4194605 = 1572977) (by norm_num)
theorem B3146053 : Blo 1655527 3146053 := bbase (se 4 (by rfl) ⟨294942, by rfl⟩ : syracuseStep 3146053 = 589885) (by norm_num)
theorem B3727709 : Blo 1655527 3727709 := bbase (se 3 (by rfl) ⟨698945, by rfl⟩ : syracuseStep 3727709 = 1397891) (by norm_num)
theorem B2097505 : Blo 1655527 2097505 := bbase (se 2 (by rfl) ⟨786564, by rfl⟩ : syracuseStep 2097505 = 1573129) (by norm_num)
theorem B2793845 : Blo 1655527 2793845 := bbase (se 5 (by rfl) ⟨130961, by rfl⟩ : syracuseStep 2793845 = 261923) (by norm_num)
theorem B8069509 : Blo 1655527 8069509 := bbase (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) (by norm_num)
theorem B3727781 : Blo 1655527 3727781 := bbase (se 4 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 3727781 = 698959) (by norm_num)
theorem B6291877 : Blo 1655527 6291877 := bbase (se 4 (by rfl) ⟨589863, by rfl⟩ : syracuseStep 6291877 = 1179727) (by norm_num)
theorem B2654669 : Blo 1655527 2654669 := bbase (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) (by norm_num)
theorem B3146197 : Blo 1655527 3146197 := bbase (se 7 (by rfl) ⟨36869, by rfl⟩ : syracuseStep 3146197 = 73739) (by norm_num)
theorem B1769941 : Blo 1655527 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B3727853 : Blo 1655527 3727853 := bbase (se 3 (by rfl) ⟨698972, by rfl⟩ : syracuseStep 3727853 = 1397945) (by norm_num)
theorem B2793973 : Blo 1655527 2793973 := bbase (se 5 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 2793973 = 261935) (by norm_num)
theorem B2097677 : Blo 1655527 2097677 := bbase (se 3 (by rfl) ⟨393314, by rfl⟩ : syracuseStep 2097677 = 786629) (by norm_num)
theorem B3727925 : Blo 1655527 3727925 := bbase (se 5 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 3727925 = 349493) (by norm_num)
theorem B2097733 : Blo 1655527 2097733 := bbase (se 4 (by rfl) ⟨196662, by rfl⟩ : syracuseStep 2097733 = 393325) (by norm_num)
theorem B2794061 : Blo 1655527 2794061 := bbase (se 3 (by rfl) ⟨523886, by rfl⟩ : syracuseStep 2794061 = 1047773) (by norm_num)
theorem B5587541 : Blo 1655527 5587541 := bbase (se 8 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 5587541 = 65479) (by norm_num)
theorem B1991261 : Blo 1655527 1991261 := bbase (se 3 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 1991261 = 746723) (by norm_num)
theorem B3146357 : Blo 1655527 3146357 := bbase (se 5 (by rfl) ⟨147485, by rfl⟩ : syracuseStep 3146357 = 294971) (by norm_num)
theorem B3727997 : Blo 1655527 3727997 := bbase (se 3 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 3727997 = 1397999) (by norm_num)
theorem B4194949 : Blo 1655527 4194949 := bbase (se 4 (by rfl) ⟨393276, by rfl⟩ : syracuseStep 4194949 = 786553) (by norm_num)
theorem B5972629 : Blo 1655527 5972629 := bbase (se 6 (by rfl) ⟨139983, by rfl⟩ : syracuseStep 5972629 = 279967) (by norm_num)
theorem B2654893 : Blo 1655527 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B3728069 : Blo 1655527 3728069 := bbase (se 4 (by rfl) ⟨349506, by rfl⟩ : syracuseStep 3728069 = 699013) (by norm_num)
theorem B2794189 : Blo 1655527 2794189 := bbase (se 3 (by rfl) ⟨523910, by rfl⟩ : syracuseStep 2794189 = 1047821) (by norm_num)
theorem B30646997 : Blo 1655527 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B6292181 : Blo 1655527 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B3982061 : Blo 1655527 3982061 := bbase (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) (by norm_num)
theorem B4195061 : Blo 1655527 4195061 := bbase (se 5 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 4195061 = 393287) (by norm_num)
theorem B3146501 : Blo 1655527 3146501 := bbase (se 4 (by rfl) ⟨294984, by rfl⟩ : syracuseStep 3146501 = 589969) (by norm_num)
theorem B3728141 : Blo 1655527 3728141 := bbase (se 3 (by rfl) ⟨699026, by rfl⟩ : syracuseStep 3728141 = 1398053) (by norm_num)
theorem B15319829 : Blo 1655527 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B30237461 : Blo 1655527 30237461 := bbase (se 6 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 30237461 = 1417381) (by norm_num)
theorem B2794277 : Blo 1655527 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B3728213 : Blo 1655527 3728213 := bbase (se 9 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 3728213 = 21845) (by norm_num)
theorem B8389493 : Blo 1655527 8389493 := bbase (se 5 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 8389493 = 786515) (by norm_num)
theorem B14156693 : Blo 1655527 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B10617749 : Blo 1655527 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B3728285 : Blo 1655527 3728285 := bbase (se 3 (by rfl) ⟨699053, by rfl⟩ : syracuseStep 3728285 = 1398107) (by norm_num)
theorem B2794405 : Blo 1655527 2794405 := bbase (se 4 (by rfl) ⟨261975, by rfl⟩ : syracuseStep 2794405 = 523951) (by norm_num)
theorem B4195253 : Blo 1655527 4195253 := bbase (se 5 (by rfl) ⟨196652, by rfl⟩ : syracuseStep 4195253 = 393305) (by norm_num)
theorem B22668245 : Blo 1655527 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B3728357 : Blo 1655527 3728357 := bbase (se 4 (by rfl) ⟨349533, by rfl⟩ : syracuseStep 3728357 = 699067) (by norm_num)
theorem B2794493 : Blo 1655527 2794493 := bbase (se 3 (by rfl) ⟨523967, by rfl⟩ : syracuseStep 2794493 = 1047935) (by norm_num)
theorem B5587973 : Blo 1655527 5587973 := bbase (se 4 (by rfl) ⟨523872, by rfl⟩ : syracuseStep 5587973 = 1047745) (by norm_num)
theorem B4719637 : Blo 1655527 4719637 := bbase (se 6 (by rfl) ⟨110616, by rfl⟩ : syracuseStep 4719637 = 221233) (by norm_num)
theorem B3728429 : Blo 1655527 3728429 := bbase (se 3 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 3728429 = 1398161) (by norm_num)
theorem B7955509 : Blo 1655527 7955509 := bbase (se 5 (by rfl) ⟨372914, by rfl⟩ : syracuseStep 7955509 = 745829) (by norm_num)
theorem B2483309 : Blo 1655527 2483309 := bbase (se 3 (by rfl) ⟨465620, by rfl⟩ : syracuseStep 2483309 = 931241) (by norm_num)
theorem B16999541 : Blo 1655527 16999541 := bbase (se 5 (by rfl) ⟨796853, by rfl⟩ : syracuseStep 16999541 = 1593707) (by norm_num)
theorem B3728501 : Blo 1655527 3728501 := bbase (se 5 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 3728501 = 349547) (by norm_num)
theorem B2794621 : Blo 1655527 2794621 := bbase (se 3 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 2794621 = 1047983) (by norm_num)
theorem B2483333 : Blo 1655527 2483333 := bbase (se 4 (by rfl) ⟨232812, by rfl⟩ : syracuseStep 2483333 = 465625) (by norm_num)
theorem B30631061 : Blo 1655527 30631061 := bbase (se 6 (by rfl) ⟨717915, by rfl⟩ : syracuseStep 30631061 = 1435831) (by norm_num)
theorem B2483357 : Blo 1655527 2483357 := bbase (se 3 (by rfl) ⟨465629, by rfl⟩ : syracuseStep 2483357 = 931259) (by norm_num)
theorem B3982493 : Blo 1655527 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B2483381 : Blo 1655527 2483381 := bbase (se 5 (by rfl) ⟨116408, by rfl⟩ : syracuseStep 2483381 = 232817) (by norm_num)
theorem B3728573 : Blo 1655527 3728573 := bbase (se 3 (by rfl) ⟨699107, by rfl⟩ : syracuseStep 3728573 = 1398215) (by norm_num)
theorem B2483405 : Blo 1655527 2483405 := bbase (se 3 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 2483405 = 931277) (by norm_num)
theorem B2237645 : Blo 1655527 2237645 := bbase (se 3 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 2237645 = 839117) (by norm_num)
theorem B2794709 : Blo 1655527 2794709 := bbase (se 7 (by rfl) ⟨32750, by rfl⟩ : syracuseStep 2794709 = 65501) (by norm_num)
theorem B2483429 : Blo 1655527 2483429 := bbase (se 4 (by rfl) ⟨232821, by rfl⟩ : syracuseStep 2483429 = 465643) (by norm_num)
theorem B2483453 : Blo 1655527 2483453 := bbase (se 3 (by rfl) ⟨465647, by rfl⟩ : syracuseStep 2483453 = 931295) (by norm_num)
theorem B3728645 : Blo 1655527 3728645 := bbase (se 4 (by rfl) ⟨349560, by rfl⟩ : syracuseStep 3728645 = 699121) (by norm_num)
theorem B4195597 : Blo 1655527 4195597 := bbase (se 3 (by rfl) ⟨786674, by rfl⟩ : syracuseStep 4195597 = 1573349) (by norm_num)
theorem B8381717 : Blo 1655527 8381717 := bbase (se 6 (by rfl) ⟨196446, by rfl⟩ : syracuseStep 8381717 = 392893) (by norm_num)
theorem B2483477 : Blo 1655527 2483477 := bbase (se 6 (by rfl) ⟨58206, by rfl⟩ : syracuseStep 2483477 = 116413) (by norm_num)
theorem B2483501 : Blo 1655527 2483501 := bbase (se 3 (by rfl) ⟨465656, by rfl⟩ : syracuseStep 2483501 = 931313) (by norm_num)
theorem B2483525 : Blo 1655527 2483525 := bbase (se 4 (by rfl) ⟨232830, by rfl⟩ : syracuseStep 2483525 = 465661) (by norm_num)
theorem B3728717 : Blo 1655527 3728717 := bbase (se 3 (by rfl) ⟨699134, by rfl⟩ : syracuseStep 3728717 = 1398269) (by norm_num)
theorem B2794837 : Blo 1655527 2794837 := bbase (se 12 (by rfl) ⟨1023, by rfl⟩ : syracuseStep 2794837 = 2047) (by norm_num)
theorem B2483549 : Blo 1655527 2483549 := bbase (se 3 (by rfl) ⟨465665, by rfl⟩ : syracuseStep 2483549 = 931331) (by norm_num)
theorem B2483573 : Blo 1655527 2483573 := bbase (se 5 (by rfl) ⟨116417, by rfl⟩ : syracuseStep 2483573 = 232835) (by norm_num)
theorem B3024253 : Blo 1655527 3024253 := bbase (se 3 (by rfl) ⟨567047, by rfl⟩ : syracuseStep 3024253 = 1134095) (by norm_num)
theorem B2483597 : Blo 1655527 2483597 := bbase (se 3 (by rfl) ⟨465674, by rfl⟩ : syracuseStep 2483597 = 931349) (by norm_num)
theorem B3728789 : Blo 1655527 3728789 := bbase (se 6 (by rfl) ⟨87393, by rfl⟩ : syracuseStep 3728789 = 174787) (by norm_num)
theorem B2483621 : Blo 1655527 2483621 := bbase (se 4 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 2483621 = 465679) (by norm_num)
theorem B2794925 : Blo 1655527 2794925 := bbase (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) (by norm_num)
theorem B5588405 : Blo 1655527 5588405 := bbase (se 5 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 5588405 = 523913) (by norm_num)
theorem B2483645 : Blo 1655527 2483645 := bbase (se 3 (by rfl) ⟨465683, by rfl⟩ : syracuseStep 2483645 = 931367) (by norm_num)
theorem B2483669 : Blo 1655527 2483669 := bbase (se 7 (by rfl) ⟨29105, by rfl⟩ : syracuseStep 2483669 = 58211) (by norm_num)
theorem B3728861 : Blo 1655527 3728861 := bbase (se 3 (by rfl) ⟨699161, by rfl⟩ : syracuseStep 3728861 = 1398323) (by norm_num)
theorem B2483693 : Blo 1655527 2483693 := bbase (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) (by norm_num)
theorem B13436405 : Blo 1655527 13436405 := bbase (se 5 (by rfl) ⟨629831, by rfl⟩ : syracuseStep 13436405 = 1259663) (by norm_num)
theorem B2483717 : Blo 1655527 2483717 := bbase (se 4 (by rfl) ⟨232848, by rfl⟩ : syracuseStep 2483717 = 465697) (by norm_num)
theorem B2483741 : Blo 1655527 2483741 := bbase (se 3 (by rfl) ⟨465701, by rfl⟩ : syracuseStep 2483741 = 931403) (by norm_num)
theorem B3728933 : Blo 1655527 3728933 := bbase (se 4 (by rfl) ⟨349587, by rfl⟩ : syracuseStep 3728933 = 699175) (by norm_num)
theorem B2795053 : Blo 1655527 2795053 := bbase (se 3 (by rfl) ⟨524072, by rfl⟩ : syracuseStep 2795053 = 1048145) (by norm_num)
theorem B2483765 : Blo 1655527 2483765 := bbase (se 5 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 2483765 = 232853) (by norm_num)
theorem B2483789 : Blo 1655527 2483789 := bbase (se 3 (by rfl) ⟨465710, by rfl⟩ : syracuseStep 2483789 = 931421) (by norm_num)
theorem B2483813 : Blo 1655527 2483813 := bbase (se 4 (by rfl) ⟨232857, by rfl⟩ : syracuseStep 2483813 = 465715) (by norm_num)
theorem B7079525 : Blo 1655527 7079525 := bbase (se 4 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 7079525 = 1327411) (by norm_num)
theorem B3729005 : Blo 1655527 3729005 := bbase (se 3 (by rfl) ⟨699188, by rfl⟩ : syracuseStep 3729005 = 1398377) (by norm_num)
theorem B2483837 : Blo 1655527 2483837 := bbase (se 3 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 2483837 = 931439) (by norm_num)
theorem B2238077 : Blo 1655527 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B2795141 : Blo 1655527 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B5973637 : Blo 1655527 5973637 := bbase (se 4 (by rfl) ⟨560028, by rfl⟩ : syracuseStep 5973637 = 1120057) (by norm_num)
theorem B2483861 : Blo 1655527 2483861 := bbase (se 6 (by rfl) ⟨58215, by rfl⟩ : syracuseStep 2483861 = 116431) (by norm_num)
theorem B2483885 : Blo 1655527 2483885 := bbase (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) (by norm_num)
theorem B17000117 : Blo 1655527 17000117 := bbase (se 5 (by rfl) ⟨796880, by rfl⟩ : syracuseStep 17000117 = 1593761) (by norm_num)
theorem B3729077 : Blo 1655527 3729077 := bbase (se 5 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 3729077 = 349601) (by norm_num)
theorem B2483909 : Blo 1655527 2483909 := bbase (se 4 (by rfl) ⟨232866, by rfl⟩ : syracuseStep 2483909 = 465733) (by norm_num)
theorem B2483933 : Blo 1655527 2483933 := bbase (se 3 (by rfl) ⟨465737, by rfl⟩ : syracuseStep 2483933 = 931475) (by norm_num)
theorem B2483957 : Blo 1655527 2483957 := bbase (se 5 (by rfl) ⟨116435, by rfl⟩ : syracuseStep 2483957 = 232871) (by norm_num)
theorem B3729149 : Blo 1655527 3729149 := bbase (se 3 (by rfl) ⟨699215, by rfl⟩ : syracuseStep 3729149 = 1398431) (by norm_num)
theorem B2795269 : Blo 1655527 2795269 := bbase (se 4 (by rfl) ⟨262056, by rfl⟩ : syracuseStep 2795269 = 524113) (by norm_num)
theorem B2483981 : Blo 1655527 2483981 := bbase (se 3 (by rfl) ⟨465746, by rfl⟩ : syracuseStep 2483981 = 931493) (by norm_num)
theorem B2484005 : Blo 1655527 2484005 := bbase (se 4 (by rfl) ⟨232875, by rfl⟩ : syracuseStep 2484005 = 465751) (by norm_num)
theorem B2484029 : Blo 1655527 2484029 := bbase (se 3 (by rfl) ⟨465755, by rfl⟩ : syracuseStep 2484029 = 931511) (by norm_num)
theorem B3729221 : Blo 1655527 3729221 := bbase (se 4 (by rfl) ⟨349614, by rfl⟩ : syracuseStep 3729221 = 699229) (by norm_num)
theorem B2484053 : Blo 1655527 2484053 := bbase (se 9 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 2484053 = 14555) (by norm_num)
theorem B2795357 : Blo 1655527 2795357 := bbase (se 3 (by rfl) ⟨524129, by rfl⟩ : syracuseStep 2795357 = 1048259) (by norm_num)
theorem B5588837 : Blo 1655527 5588837 := bbase (se 4 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 5588837 = 1047907) (by norm_num)
theorem B2484077 : Blo 1655527 2484077 := bbase (se 3 (by rfl) ⟨465764, by rfl⟩ : syracuseStep 2484077 = 931529) (by norm_num)
theorem B2484101 : Blo 1655527 2484101 := bbase (se 4 (by rfl) ⟨232884, by rfl⟩ : syracuseStep 2484101 = 465769) (by norm_num)
theorem B3729293 : Blo 1655527 3729293 := bbase (se 3 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 3729293 = 1398485) (by norm_num)
theorem B2484125 : Blo 1655527 2484125 := bbase (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) (by norm_num)
theorem B2484149 : Blo 1655527 2484149 := bbase (se 5 (by rfl) ⟨116444, by rfl⟩ : syracuseStep 2484149 = 232889) (by norm_num)
theorem B2484173 : Blo 1655527 2484173 := bbase (se 3 (by rfl) ⟨465782, by rfl⟩ : syracuseStep 2484173 = 931565) (by norm_num)
theorem B3729365 : Blo 1655527 3729365 := bbase (se 7 (by rfl) ⟨43703, by rfl⟩ : syracuseStep 3729365 = 87407) (by norm_num)
theorem B2795485 : Blo 1655527 2795485 := bbase (se 3 (by rfl) ⟨524153, by rfl⟩ : syracuseStep 2795485 = 1048307) (by norm_num)
theorem B2484197 : Blo 1655527 2484197 := bbase (se 4 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 2484197 = 465787) (by norm_num)
theorem B2484221 : Blo 1655527 2484221 := bbase (se 3 (by rfl) ⟨465791, by rfl⟩ : syracuseStep 2484221 = 931583) (by norm_num)
theorem B2484245 : Blo 1655527 2484245 := bbase (se 6 (by rfl) ⟨58224, by rfl⟩ : syracuseStep 2484245 = 116449) (by norm_num)
theorem B9439253 : Blo 1655527 9439253 := bbase (se 6 (by rfl) ⟨221232, by rfl⟩ : syracuseStep 9439253 = 442465) (by norm_num)
theorem B3729437 : Blo 1655527 3729437 := bbase (se 3 (by rfl) ⟨699269, by rfl⟩ : syracuseStep 3729437 = 1398539) (by norm_num)
theorem B2484269 : Blo 1655527 2484269 := bbase (se 3 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 2484269 = 931601) (by norm_num)
theorem B2795573 : Blo 1655527 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B2484293 : Blo 1655527 2484293 := bbase (se 4 (by rfl) ⟨232902, by rfl⟩ : syracuseStep 2484293 = 465805) (by norm_num)
theorem B2484317 : Blo 1655527 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B2238557 : Blo 1655527 2238557 := bbase (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) (by norm_num)
theorem B2484341 : Blo 1655527 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B8390789 : Blo 1655527 8390789 := bbase (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) (by norm_num)
theorem B2484365 : Blo 1655527 2484365 := bbase (se 3 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 2484365 = 931637) (by norm_num)
theorem B2484389 : Blo 1655527 2484389 := bbase (se 4 (by rfl) ⟨232911, by rfl⟩ : syracuseStep 2484389 = 465823) (by norm_num)
theorem B2017445 : Blo 1655527 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B15911093 : Blo 1655527 15911093 := bbase (se 5 (by rfl) ⟨745832, by rfl⟩ : syracuseStep 15911093 = 1491665) (by norm_num)
theorem B2795701 : Blo 1655527 2795701 := bbase (se 5 (by rfl) ⟨131048, by rfl⟩ : syracuseStep 2795701 = 262097) (by norm_num)
theorem B2484413 : Blo 1655527 2484413 := bbase (se 3 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 2484413 = 931655) (by norm_num)
theorem B2484437 : Blo 1655527 2484437 := bbase (se 7 (by rfl) ⟨29114, by rfl⟩ : syracuseStep 2484437 = 58229) (by norm_num)
theorem B2484461 : Blo 1655527 2484461 := bbase (se 3 (by rfl) ⟨465836, by rfl⟩ : syracuseStep 2484461 = 931673) (by norm_num)
theorem B2484485 : Blo 1655527 2484485 := bbase (se 4 (by rfl) ⟨232920, by rfl⟩ : syracuseStep 2484485 = 465841) (by norm_num)
theorem B2795789 : Blo 1655527 2795789 := bbase (se 3 (by rfl) ⟨524210, by rfl⟩ : syracuseStep 2795789 = 1048421) (by norm_num)
theorem B5589269 : Blo 1655527 5589269 := bbase (se 6 (by rfl) ⟨130998, by rfl⟩ : syracuseStep 5589269 = 261997) (by norm_num)
theorem B2484509 : Blo 1655527 2484509 := bbase (se 3 (by rfl) ⟨465845, by rfl⟩ : syracuseStep 2484509 = 931691) (by norm_num)
theorem B2484533 : Blo 1655527 2484533 := bbase (se 5 (by rfl) ⟨116462, by rfl⟩ : syracuseStep 2484533 = 232925) (by norm_num)
theorem B2484557 : Blo 1655527 2484557 := bbase (se 3 (by rfl) ⟨465854, by rfl⟩ : syracuseStep 2484557 = 931709) (by norm_num)
theorem B2484581 : Blo 1655527 2484581 := bbase (se 4 (by rfl) ⟨232929, by rfl⟩ : syracuseStep 2484581 = 465859) (by norm_num)
theorem B2484605 : Blo 1655527 2484605 := bbase (se 3 (by rfl) ⟨465863, by rfl⟩ : syracuseStep 2484605 = 931727) (by norm_num)
theorem B2795917 : Blo 1655527 2795917 := bbase (se 3 (by rfl) ⟨524234, by rfl⟩ : syracuseStep 2795917 = 1048469) (by norm_num)
theorem B2484629 : Blo 1655527 2484629 := bbase (se 6 (by rfl) ⟨58233, by rfl⟩ : syracuseStep 2484629 = 116467) (by norm_num)
theorem B2484653 : Blo 1655527 2484653 := bbase (se 3 (by rfl) ⟨465872, by rfl⟩ : syracuseStep 2484653 = 931745) (by norm_num)
theorem B2484677 : Blo 1655527 2484677 := bbase (se 4 (by rfl) ⟨232938, by rfl⟩ : syracuseStep 2484677 = 465877) (by norm_num)
theorem B2484701 : Blo 1655527 2484701 := bbase (se 3 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 2484701 = 931763) (by norm_num)
theorem B6048229 : Blo 1655527 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B2796005 : Blo 1655527 2796005 := bbase (se 4 (by rfl) ⟨262125, by rfl⟩ : syracuseStep 2796005 = 524251) (by norm_num)
theorem B2484725 : Blo 1655527 2484725 := bbase (se 5 (by rfl) ⟨116471, by rfl⟩ : syracuseStep 2484725 = 232943) (by norm_num)
theorem B2484749 : Blo 1655527 2484749 := bbase (se 3 (by rfl) ⟨465890, by rfl⟩ : syracuseStep 2484749 = 931781) (by norm_num)
theorem B8383013 : Blo 1655527 8383013 := bbase (se 4 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 8383013 = 1571815) (by norm_num)
theorem B2484773 : Blo 1655527 2484773 := bbase (se 4 (by rfl) ⟨232947, by rfl⟩ : syracuseStep 2484773 = 465895) (by norm_num)
theorem B2484797 : Blo 1655527 2484797 := bbase (se 3 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 2484797 = 931799) (by norm_num)
theorem B2484821 : Blo 1655527 2484821 := bbase (se 8 (by rfl) ⟨14559, by rfl⟩ : syracuseStep 2484821 = 29119) (by norm_num)
theorem B2796133 : Blo 1655527 2796133 := bbase (se 4 (by rfl) ⟨262137, by rfl⟩ : syracuseStep 2796133 = 524275) (by norm_num)
theorem B2484845 : Blo 1655527 2484845 := bbase (se 3 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 2484845 = 931817) (by norm_num)
theorem B2484869 : Blo 1655527 2484869 := bbase (se 4 (by rfl) ⟨232956, by rfl⟩ : syracuseStep 2484869 = 465913) (by norm_num)
theorem B2484893 : Blo 1655527 2484893 := bbase (se 3 (by rfl) ⟨465917, by rfl⟩ : syracuseStep 2484893 = 931835) (by norm_num)
theorem B4475557 : Blo 1655527 4475557 := bbase (se 4 (by rfl) ⟨419583, by rfl⟩ : syracuseStep 4475557 = 839167) (by norm_num)
theorem B2484917 : Blo 1655527 2484917 := bbase (se 5 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 2484917 = 232961) (by norm_num)
theorem B2796221 : Blo 1655527 2796221 := bbase (se 3 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 2796221 = 1048583) (by norm_num)
theorem B5589701 : Blo 1655527 5589701 := bbase (se 4 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 5589701 = 1048069) (by norm_num)
theorem B2484941 : Blo 1655527 2484941 := bbase (se 3 (by rfl) ⟨465926, by rfl⟩ : syracuseStep 2484941 = 931853) (by norm_num)
theorem B2484965 : Blo 1655527 2484965 := bbase (se 4 (by rfl) ⟨232965, by rfl⟩ : syracuseStep 2484965 = 465931) (by norm_num)
theorem B10611445 : Blo 1655527 10611445 := bbase (se 5 (by rfl) ⟨497411, by rfl⟩ : syracuseStep 10611445 = 994823) (by norm_num)
theorem B2984701 : Blo 1655527 2984701 := bbase (se 3 (by rfl) ⟨559631, by rfl⟩ : syracuseStep 2984701 = 1119263) (by norm_num)
theorem B2484989 : Blo 1655527 2484989 := bbase (se 3 (by rfl) ⟨465935, by rfl⟩ : syracuseStep 2484989 = 931871) (by norm_num)
theorem B2485013 : Blo 1655527 2485013 := bbase (se 6 (by rfl) ⟨58242, by rfl⟩ : syracuseStep 2485013 = 116485) (by norm_num)
theorem B2485037 : Blo 1655527 2485037 := bbase (se 3 (by rfl) ⟨465944, by rfl⟩ : syracuseStep 2485037 = 931889) (by norm_num)
theorem B2796349 : Blo 1655527 2796349 := bbase (se 3 (by rfl) ⟨524315, by rfl⟩ : syracuseStep 2796349 = 1048631) (by norm_num)
theorem B2485061 : Blo 1655527 2485061 := bbase (se 4 (by rfl) ⟨232974, by rfl⟩ : syracuseStep 2485061 = 465949) (by norm_num)
theorem B1862473 : Blo 1655527 1862473 := bbase (se 2 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 1862473 = 1396855) (by norm_num)
theorem B24218453 : Blo 1655527 24218453 := bbase (se 9 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 24218453 = 141905) (by norm_num)
theorem B2485085 : Blo 1655527 2485085 := bbase (se 3 (by rfl) ⟨465953, by rfl⟩ : syracuseStep 2485085 = 931907) (by norm_num)
theorem B1862509 : Blo 1655527 1862509 := bbase (se 3 (by rfl) ⟨349220, by rfl⟩ : syracuseStep 1862509 = 698441) (by norm_num)
theorem B2485109 : Blo 1655527 2485109 := bbase (se 5 (by rfl) ⟨116489, by rfl⟩ : syracuseStep 2485109 = 232979) (by norm_num)
theorem B2485133 : Blo 1655527 2485133 := bbase (se 3 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 2485133 = 931925) (by norm_num)
theorem B1862545 : Blo 1655527 1862545 := bbase (se 2 (by rfl) ⟨698454, by rfl⟩ : syracuseStep 1862545 = 1396909) (by norm_num)
theorem B2796437 : Blo 1655527 2796437 := bbase (se 6 (by rfl) ⟨65541, by rfl⟩ : syracuseStep 2796437 = 131083) (by norm_num)
theorem B2485157 : Blo 1655527 2485157 := bbase (se 4 (by rfl) ⟨232983, by rfl⟩ : syracuseStep 2485157 = 465967) (by norm_num)
theorem B1862581 : Blo 1655527 1862581 := bbase (se 5 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 1862581 = 174617) (by norm_num)
theorem B2485181 : Blo 1655527 2485181 := bbase (se 3 (by rfl) ⟨465971, by rfl⟩ : syracuseStep 2485181 = 931943) (by norm_num)
theorem B2485205 : Blo 1655527 2485205 := bbase (se 7 (by rfl) ⟨29123, by rfl⟩ : syracuseStep 2485205 = 58247) (by norm_num)
theorem B12585941 : Blo 1655527 12585941 := bbase (se 7 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 12585941 = 294983) (by norm_num)
theorem B1862617 : Blo 1655527 1862617 := bbase (se 2 (by rfl) ⟨698481, by rfl⟩ : syracuseStep 1862617 = 1396963) (by norm_num)
theorem B2485229 : Blo 1655527 2485229 := bbase (se 3 (by rfl) ⟨465980, by rfl⟩ : syracuseStep 2485229 = 931961) (by norm_num)
theorem B1862653 : Blo 1655527 1862653 := bbase (se 3 (by rfl) ⟨349247, by rfl⟩ : syracuseStep 1862653 = 698495) (by norm_num)
theorem B2485253 : Blo 1655527 2485253 := bbase (se 4 (by rfl) ⟨232992, by rfl⟩ : syracuseStep 2485253 = 465985) (by norm_num)
theorem B2796565 : Blo 1655527 2796565 := bbase (se 6 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 2796565 = 131089) (by norm_num)
theorem B2485277 : Blo 1655527 2485277 := bbase (se 3 (by rfl) ⟨465989, by rfl⟩ : syracuseStep 2485277 = 931979) (by norm_num)
theorem B1862689 : Blo 1655527 1862689 := bbase (se 2 (by rfl) ⟨698508, by rfl⟩ : syracuseStep 1862689 = 1397017) (by norm_num)
theorem B2485301 : Blo 1655527 2485301 := bbase (se 5 (by rfl) ⟨116498, by rfl⟩ : syracuseStep 2485301 = 232997) (by norm_num)
theorem B1862725 : Blo 1655527 1862725 := bbase (se 4 (by rfl) ⟨174630, by rfl⟩ : syracuseStep 1862725 = 349261) (by norm_num)
theorem B2485325 : Blo 1655527 2485325 := bbase (se 3 (by rfl) ⟨465998, by rfl⟩ : syracuseStep 2485325 = 931997) (by norm_num)
theorem B2485349 : Blo 1655527 2485349 := bbase (se 4 (by rfl) ⟨233001, by rfl⟩ : syracuseStep 2485349 = 466003) (by norm_num)
theorem B1862761 : Blo 1655527 1862761 := bbase (se 2 (by rfl) ⟨698535, by rfl⟩ : syracuseStep 1862761 = 1397071) (by norm_num)
theorem B2796653 : Blo 1655527 2796653 := bbase (se 3 (by rfl) ⟨524372, by rfl⟩ : syracuseStep 2796653 = 1048745) (by norm_num)
theorem B5590133 : Blo 1655527 5590133 := bbase (se 5 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 5590133 = 524075) (by norm_num)
theorem B2485373 : Blo 1655527 2485373 := bbase (se 3 (by rfl) ⟨466007, by rfl⟩ : syracuseStep 2485373 = 932015) (by norm_num)
theorem B1862797 : Blo 1655527 1862797 := bbase (se 3 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 1862797 = 698549) (by norm_num)
theorem B2485397 : Blo 1655527 2485397 := bbase (se 6 (by rfl) ⟨58251, by rfl⟩ : syracuseStep 2485397 = 116503) (by norm_num)
theorem B2485421 : Blo 1655527 2485421 := bbase (se 3 (by rfl) ⟨466016, by rfl⟩ : syracuseStep 2485421 = 932033) (by norm_num)
theorem B1862833 : Blo 1655527 1862833 := bbase (se 2 (by rfl) ⟨698562, by rfl⟩ : syracuseStep 1862833 = 1397125) (by norm_num)
theorem B6286517 : Blo 1655527 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B8498357 : Blo 1655527 8498357 := bbase (se 5 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 8498357 = 796721) (by norm_num)
theorem B2485445 : Blo 1655527 2485445 := bbase (se 4 (by rfl) ⟨233010, by rfl⟩ : syracuseStep 2485445 = 466021) (by norm_num)
theorem B2239693 : Blo 1655527 2239693 := bbase (se 3 (by rfl) ⟨419942, by rfl⟩ : syracuseStep 2239693 = 839885) (by norm_num)
theorem B1862869 : Blo 1655527 1862869 := bbase (se 7 (by rfl) ⟨21830, by rfl⟩ : syracuseStep 1862869 = 43661) (by norm_num)
theorem B2485469 : Blo 1655527 2485469 := bbase (se 3 (by rfl) ⟨466025, by rfl⟩ : syracuseStep 2485469 = 932051) (by norm_num)
theorem B2796781 : Blo 1655527 2796781 := bbase (se 3 (by rfl) ⟨524396, by rfl⟩ : syracuseStep 2796781 = 1048793) (by norm_num)
theorem B2485493 : Blo 1655527 2485493 := bbase (se 5 (by rfl) ⟨116507, by rfl⟩ : syracuseStep 2485493 = 233015) (by norm_num)
theorem B1862905 : Blo 1655527 1862905 := bbase (se 2 (by rfl) ⟨698589, by rfl⟩ : syracuseStep 1862905 = 1397179) (by norm_num)
theorem B2485517 : Blo 1655527 2485517 := bbase (se 3 (by rfl) ⟨466034, by rfl⟩ : syracuseStep 2485517 = 932069) (by norm_num)
theorem B1862941 : Blo 1655527 1862941 := bbase (se 3 (by rfl) ⟨349301, by rfl⟩ : syracuseStep 1862941 = 698603) (by norm_num)
theorem B2485541 : Blo 1655527 2485541 := bbase (se 4 (by rfl) ⟨233019, by rfl⟩ : syracuseStep 2485541 = 466039) (by norm_num)
theorem B2485565 : Blo 1655527 2485565 := bbase (se 3 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 2485565 = 932087) (by norm_num)
theorem B1862977 : Blo 1655527 1862977 := bbase (se 2 (by rfl) ⟨698616, by rfl⟩ : syracuseStep 1862977 = 1397233) (by norm_num)
theorem B2796869 : Blo 1655527 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B2485589 : Blo 1655527 2485589 := bbase (se 11 (by rfl) ⟨1820, by rfl⟩ : syracuseStep 2485589 = 3641) (by norm_num)
theorem B1863013 : Blo 1655527 1863013 := bbase (se 4 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 1863013 = 349315) (by norm_num)
theorem B2485613 : Blo 1655527 2485613 := bbase (se 3 (by rfl) ⟨466052, by rfl⟩ : syracuseStep 2485613 = 932105) (by norm_num)
theorem B12578165 : Blo 1655527 12578165 := bbase (se 5 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 12578165 = 1179203) (by norm_num)
theorem B2485637 : Blo 1655527 2485637 := bbase (se 4 (by rfl) ⟨233028, by rfl⟩ : syracuseStep 2485637 = 466057) (by norm_num)
theorem B1863049 : Blo 1655527 1863049 := bbase (se 2 (by rfl) ⟨698643, by rfl⟩ : syracuseStep 1863049 = 1397287) (by norm_num)
theorem B2485661 : Blo 1655527 2485661 := bbase (se 3 (by rfl) ⟨466061, by rfl⟩ : syracuseStep 2485661 = 932123) (by norm_num)
theorem B1863085 : Blo 1655527 1863085 := bbase (se 3 (by rfl) ⟨349328, by rfl⟩ : syracuseStep 1863085 = 698657) (by norm_num)
theorem B2485685 : Blo 1655527 2485685 := bbase (se 5 (by rfl) ⟨116516, by rfl⟩ : syracuseStep 2485685 = 233033) (by norm_num)
theorem B2796997 : Blo 1655527 2796997 := bbase (se 4 (by rfl) ⟨262218, by rfl⟩ : syracuseStep 2796997 = 524437) (by norm_num)
theorem B2485709 : Blo 1655527 2485709 := bbase (se 3 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 2485709 = 932141) (by norm_num)
theorem B1863121 : Blo 1655527 1863121 := bbase (se 2 (by rfl) ⟨698670, by rfl⟩ : syracuseStep 1863121 = 1397341) (by norm_num)
theorem B6286805 : Blo 1655527 6286805 := bbase (se 7 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 6286805 = 147347) (by norm_num)
theorem B7073237 : Blo 1655527 7073237 := bbase (se 7 (by rfl) ⟨82889, by rfl⟩ : syracuseStep 7073237 = 165779) (by norm_num)
theorem B2485733 : Blo 1655527 2485733 := bbase (se 4 (by rfl) ⟨233037, by rfl⟩ : syracuseStep 2485733 = 466075) (by norm_num)
theorem B1863157 : Blo 1655527 1863157 := bbase (se 5 (by rfl) ⟨87335, by rfl⟩ : syracuseStep 1863157 = 174671) (by norm_num)
theorem B2485757 : Blo 1655527 2485757 := bbase (se 3 (by rfl) ⟨466079, by rfl⟩ : syracuseStep 2485757 = 932159) (by norm_num)
theorem B2985493 : Blo 1655527 2985493 := bbase (se 6 (by rfl) ⟨69972, by rfl⟩ : syracuseStep 2985493 = 139945) (by norm_num)
theorem B2485781 : Blo 1655527 2485781 := bbase (se 6 (by rfl) ⟨58260, by rfl⟩ : syracuseStep 2485781 = 116521) (by norm_num)
theorem B1863193 : Blo 1655527 1863193 := bbase (se 2 (by rfl) ⟨698697, by rfl⟩ : syracuseStep 1863193 = 1397395) (by norm_num)
theorem B5590565 : Blo 1655527 5590565 := bbase (se 4 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 5590565 = 1048231) (by norm_num)
theorem B2485805 : Blo 1655527 2485805 := bbase (se 3 (by rfl) ⟨466088, by rfl⟩ : syracuseStep 2485805 = 932177) (by norm_num)
theorem B1863229 : Blo 1655527 1863229 := bbase (se 3 (by rfl) ⟨349355, by rfl⟩ : syracuseStep 1863229 = 698711) (by norm_num)
theorem B2485829 : Blo 1655527 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B2485853 : Blo 1655527 2485853 := bbase (se 3 (by rfl) ⟨466097, by rfl⟩ : syracuseStep 2485853 = 932195) (by norm_num)
theorem B2240093 : Blo 1655527 2240093 := bbase (se 3 (by rfl) ⟨420017, by rfl⟩ : syracuseStep 2240093 = 840035) (by norm_num)
theorem B1863265 : Blo 1655527 1863265 := bbase (se 2 (by rfl) ⟨698724, by rfl⟩ : syracuseStep 1863265 = 1397449) (by norm_num)
theorem B2485877 : Blo 1655527 2485877 := bbase (se 5 (by rfl) ⟨116525, by rfl⟩ : syracuseStep 2485877 = 233051) (by norm_num)
theorem B1863301 : Blo 1655527 1863301 := bbase (se 4 (by rfl) ⟨174684, by rfl⟩ : syracuseStep 1863301 = 349369) (by norm_num)
theorem B2485901 : Blo 1655527 2485901 := bbase (se 3 (by rfl) ⟨466106, by rfl⟩ : syracuseStep 2485901 = 932213) (by norm_num)
theorem B2485925 : Blo 1655527 2485925 := bbase (se 4 (by rfl) ⟨233055, by rfl⟩ : syracuseStep 2485925 = 466111) (by norm_num)
theorem B1863337 : Blo 1655527 1863337 := bbase (se 2 (by rfl) ⟨698751, by rfl⟩ : syracuseStep 1863337 = 1397503) (by norm_num)
theorem B2485949 : Blo 1655527 2485949 := bbase (se 3 (by rfl) ⟨466115, by rfl⟩ : syracuseStep 2485949 = 932231) (by norm_num)
theorem B7073477 : Blo 1655527 7073477 := bbase (se 4 (by rfl) ⟨663138, by rfl⟩ : syracuseStep 7073477 = 1326277) (by norm_num)
theorem B1863373 : Blo 1655527 1863373 := bbase (se 3 (by rfl) ⟨349382, by rfl⟩ : syracuseStep 1863373 = 698765) (by norm_num)
theorem B2485973 : Blo 1655527 2485973 := bbase (se 7 (by rfl) ⟨29132, by rfl⟩ : syracuseStep 2485973 = 58265) (by norm_num)
theorem B2125537 : Blo 1655527 2125537 := bbase (se 2 (by rfl) ⟨797076, by rfl⟩ : syracuseStep 2125537 = 1594153) (by norm_num)
theorem B2485997 : Blo 1655527 2485997 := bbase (se 3 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 2485997 = 932249) (by norm_num)
theorem B1863409 : Blo 1655527 1863409 := bbase (se 2 (by rfl) ⟨698778, by rfl⟩ : syracuseStep 1863409 = 1397557) (by norm_num)
theorem B6713077 : Blo 1655527 6713077 := bbase (se 5 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 6713077 = 629351) (by norm_num)
theorem B2486021 : Blo 1655527 2486021 := bbase (se 4 (by rfl) ⟨233064, by rfl⟩ : syracuseStep 2486021 = 466129) (by norm_num)
theorem B1863445 : Blo 1655527 1863445 := bbase (se 6 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 1863445 = 87349) (by norm_num)
theorem B2486045 : Blo 1655527 2486045 := bbase (se 3 (by rfl) ⟨466133, by rfl⟩ : syracuseStep 2486045 = 932267) (by norm_num)
theorem B8384309 : Blo 1655527 8384309 := bbase (se 5 (by rfl) ⟨393014, by rfl⟩ : syracuseStep 8384309 = 786029) (by norm_num)
theorem B2486069 : Blo 1655527 2486069 := bbase (se 5 (by rfl) ⟨116534, by rfl⟩ : syracuseStep 2486069 = 233069) (by norm_num)
theorem B1863481 : Blo 1655527 1863481 := bbase (se 2 (by rfl) ⟨698805, by rfl⟩ : syracuseStep 1863481 = 1397611) (by norm_num)
theorem B2985797 : Blo 1655527 2985797 := bbase (se 4 (by rfl) ⟨279918, by rfl⟩ : syracuseStep 2985797 = 559837) (by norm_num)
theorem B2486093 : Blo 1655527 2486093 := bbase (se 3 (by rfl) ⟨466142, by rfl⟩ : syracuseStep 2486093 = 932285) (by norm_num)
theorem B15109973 : Blo 1655527 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B1863517 : Blo 1655527 1863517 := bbase (se 3 (by rfl) ⟨349409, by rfl⟩ : syracuseStep 1863517 = 698819) (by norm_num)
theorem B2486117 : Blo 1655527 2486117 := bbase (se 4 (by rfl) ⟨233073, by rfl⟩ : syracuseStep 2486117 = 466147) (by norm_num)
theorem B2486141 : Blo 1655527 2486141 := bbase (se 3 (by rfl) ⟨466151, by rfl⟩ : syracuseStep 2486141 = 932303) (by norm_num)
theorem B1863553 : Blo 1655527 1863553 := bbase (se 2 (by rfl) ⟨698832, by rfl⟩ : syracuseStep 1863553 = 1397665) (by norm_num)
theorem B2486165 : Blo 1655527 2486165 := bbase (se 6 (by rfl) ⟨58269, by rfl⟩ : syracuseStep 2486165 = 116539) (by norm_num)
theorem B1863589 : Blo 1655527 1863589 := bbase (se 4 (by rfl) ⟨174711, by rfl⟩ : syracuseStep 1863589 = 349423) (by norm_num)
theorem B2486189 : Blo 1655527 2486189 := bbase (se 3 (by rfl) ⟨466160, by rfl⟩ : syracuseStep 2486189 = 932321) (by norm_num)
theorem B2486213 : Blo 1655527 2486213 := bbase (se 4 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 2486213 = 466165) (by norm_num)
theorem B1863625 : Blo 1655527 1863625 := bbase (se 2 (by rfl) ⟨698859, by rfl⟩ : syracuseStep 1863625 = 1397719) (by norm_num)
theorem B5590997 : Blo 1655527 5590997 := bbase (se 7 (by rfl) ⟨65519, by rfl⟩ : syracuseStep 5590997 = 131039) (by norm_num)
theorem B2486237 : Blo 1655527 2486237 := bbase (se 3 (by rfl) ⟨466169, by rfl⟩ : syracuseStep 2486237 = 932339) (by norm_num)
theorem B1863661 : Blo 1655527 1863661 := bbase (se 3 (by rfl) ⟨349436, by rfl⟩ : syracuseStep 1863661 = 698873) (by norm_num)
theorem B2486261 : Blo 1655527 2486261 := bbase (se 5 (by rfl) ⟨116543, by rfl⟩ : syracuseStep 2486261 = 233087) (by norm_num)
theorem B2486285 : Blo 1655527 2486285 := bbase (se 3 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 2486285 = 932357) (by norm_num)
theorem B1863697 : Blo 1655527 1863697 := bbase (se 2 (by rfl) ⟨698886, by rfl⟩ : syracuseStep 1863697 = 1397773) (by norm_num)
theorem B1863733 : Blo 1655527 1863733 := bbase (se 5 (by rfl) ⟨87362, by rfl⟩ : syracuseStep 1863733 = 174725) (by norm_num)
theorem B21508181 : Blo 1655527 21508181 := bbase (se 8 (by rfl) ⟨126024, by rfl⟩ : syracuseStep 21508181 = 252049) (by norm_num)
theorem B1863769 : Blo 1655527 1863769 := bbase (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) (by norm_num)
theorem B2986085 : Blo 1655527 2986085 := bbase (se 4 (by rfl) ⟨279945, by rfl⟩ : syracuseStep 2986085 = 559891) (by norm_num)
theorem B1863805 : Blo 1655527 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B1863841 : Blo 1655527 1863841 := bbase (se 2 (by rfl) ⟨698940, by rfl⟩ : syracuseStep 1863841 = 1397881) (by norm_num)
theorem B1863877 : Blo 1655527 1863877 := bbase (se 4 (by rfl) ⟨174738, by rfl⟩ : syracuseStep 1863877 = 349477) (by norm_num)
theorem B1863913 : Blo 1655527 1863913 := bbase (se 2 (by rfl) ⟨698967, by rfl⟩ : syracuseStep 1863913 = 1397935) (by norm_num)
theorem B1863949 : Blo 1655527 1863949 := bbase (se 3 (by rfl) ⟨349490, by rfl⟩ : syracuseStep 1863949 = 698981) (by norm_num)
theorem B23892245 : Blo 1655527 23892245 := bbase (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) (by norm_num)
theorem B1863985 : Blo 1655527 1863985 := bbase (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) (by norm_num)
theorem B1864021 : Blo 1655527 1864021 := bbase (se 10 (by rfl) ⟨2730, by rfl⟩ : syracuseStep 1864021 = 5461) (by norm_num)
theorem B1864057 : Blo 1655527 1864057 := bbase (se 2 (by rfl) ⟨699021, by rfl⟩ : syracuseStep 1864057 = 1398043) (by norm_num)
theorem B1888637 : Blo 1655527 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B5591429 : Blo 1655527 5591429 := bbase (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) (by norm_num)
theorem B12751253 : Blo 1655527 12751253 := bbase (se 6 (by rfl) ⟨298857, by rfl⟩ : syracuseStep 12751253 = 597715) (by norm_num)
theorem B1864093 : Blo 1655527 1864093 := bbase (se 3 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 1864093 = 699035) (by norm_num)
theorem B1864129 : Blo 1655527 1864129 := bbase (se 2 (by rfl) ⟨699048, by rfl⟩ : syracuseStep 1864129 = 1398097) (by norm_num)
theorem B1864165 : Blo 1655527 1864165 := bbase (se 4 (by rfl) ⟨174765, by rfl⟩ : syracuseStep 1864165 = 349531) (by norm_num)
theorem B4190717 : Blo 1655527 4190717 := bbase (se 3 (by rfl) ⟨785759, by rfl⟩ : syracuseStep 4190717 = 1571519) (by norm_num)
theorem B1864201 : Blo 1655527 1864201 := bbase (se 2 (by rfl) ⟨699075, by rfl⟩ : syracuseStep 1864201 = 1398151) (by norm_num)
theorem B1864237 : Blo 1655527 1864237 := bbase (se 3 (by rfl) ⟨349544, by rfl⟩ : syracuseStep 1864237 = 699089) (by norm_num)
theorem B1864273 : Blo 1655527 1864273 := bbase (se 2 (by rfl) ⟨699102, by rfl⟩ : syracuseStep 1864273 = 1398205) (by norm_num)
theorem B6287989 : Blo 1655527 6287989 := bbase (se 5 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 6287989 = 589499) (by norm_num)
theorem B1864309 : Blo 1655527 1864309 := bbase (se 5 (by rfl) ⟨87389, by rfl⟩ : syracuseStep 1864309 = 174779) (by norm_num)
theorem B1864345 : Blo 1655527 1864345 := bbase (se 2 (by rfl) ⟨699129, by rfl⟩ : syracuseStep 1864345 = 1398259) (by norm_num)
theorem B1864381 : Blo 1655527 1864381 := bbase (se 3 (by rfl) ⟨349571, by rfl⟩ : syracuseStep 1864381 = 699143) (by norm_num)
theorem B1864417 : Blo 1655527 1864417 := bbase (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) (by norm_num)
theorem B1864453 : Blo 1655527 1864453 := bbase (se 4 (by rfl) ⟨174792, by rfl⟩ : syracuseStep 1864453 = 349585) (by norm_num)
theorem B2519837 : Blo 1655527 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1864489 : Blo 1655527 1864489 := bbase (se 2 (by rfl) ⟨699183, by rfl⟩ : syracuseStep 1864489 = 1398367) (by norm_num)
theorem B5591861 : Blo 1655527 5591861 := bbase (se 5 (by rfl) ⟨262118, by rfl⟩ : syracuseStep 5591861 = 524237) (by norm_num)
theorem B1864525 : Blo 1655527 1864525 := bbase (se 3 (by rfl) ⟨349598, by rfl⟩ : syracuseStep 1864525 = 699197) (by norm_num)
theorem B4191061 : Blo 1655527 4191061 := bbase (se 9 (by rfl) ⟨12278, by rfl⟩ : syracuseStep 4191061 = 24557) (by norm_num)
theorem B3232613 : Blo 1655527 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B1864561 : Blo 1655527 1864561 := bbase (se 2 (by rfl) ⟨699210, by rfl⟩ : syracuseStep 1864561 = 1398421) (by norm_num)
theorem B2986877 : Blo 1655527 2986877 := bbase (se 3 (by rfl) ⟨560039, by rfl⟩ : syracuseStep 2986877 = 1120079) (by norm_num)
theorem B6714245 : Blo 1655527 6714245 := bbase (se 4 (by rfl) ⟨629460, by rfl⟩ : syracuseStep 6714245 = 1258921) (by norm_num)
theorem B5108629 : Blo 1655527 5108629 := bbase (se 6 (by rfl) ⟨119733, by rfl⟩ : syracuseStep 5108629 = 239467) (by norm_num)
theorem B1864597 : Blo 1655527 1864597 := bbase (se 6 (by rfl) ⟨43701, by rfl⟩ : syracuseStep 1864597 = 87403) (by norm_num)
theorem B6288293 : Blo 1655527 6288293 := bbase (se 4 (by rfl) ⟨589527, by rfl⟩ : syracuseStep 6288293 = 1179055) (by norm_num)
theorem B1864633 : Blo 1655527 1864633 := bbase (se 2 (by rfl) ⟨699237, by rfl⟩ : syracuseStep 1864633 = 1398475) (by norm_num)
theorem B4191173 : Blo 1655527 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B3978197 : Blo 1655527 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B1864669 : Blo 1655527 1864669 := bbase (se 3 (by rfl) ⟨349625, by rfl⟩ : syracuseStep 1864669 = 699251) (by norm_num)
theorem B1864705 : Blo 1655527 1864705 := bbase (se 2 (by rfl) ⟨699264, by rfl⟩ : syracuseStep 1864705 = 1398529) (by norm_num)
theorem B3535901 : Blo 1655527 3535901 := bbase (se 3 (by rfl) ⟨662981, by rfl⟩ : syracuseStep 3535901 = 1325963) (by norm_num)
theorem B8385605 : Blo 1655527 8385605 := bbase (se 4 (by rfl) ⟨786150, by rfl⟩ : syracuseStep 8385605 = 1572301) (by norm_num)
theorem B4191365 : Blo 1655527 4191365 := bbase (se 4 (by rfl) ⟨392940, by rfl⟩ : syracuseStep 4191365 = 785881) (by norm_num)
theorem B3978389 : Blo 1655527 3978389 := bbase (se 6 (by rfl) ⟨93243, by rfl⟩ : syracuseStep 3978389 = 186487) (by norm_num)
theorem B5592293 : Blo 1655527 5592293 := bbase (se 4 (by rfl) ⟨524277, by rfl⟩ : syracuseStep 5592293 = 1048555) (by norm_num)
theorem B4715765 : Blo 1655527 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B5305621 : Blo 1655527 5305621 := bbase (se 6 (by rfl) ⟨124350, by rfl⟩ : syracuseStep 5305621 = 248701) (by norm_num)
theorem B3143053 : Blo 1655527 3143053 := bbase (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) (by norm_num)
theorem B3978677 : Blo 1655527 3978677 := bbase (se 5 (by rfl) ⟨186500, by rfl⟩ : syracuseStep 3978677 = 373001) (by norm_num)
theorem B4249045 : Blo 1655527 4249045 := bbase (se 7 (by rfl) ⟨49793, by rfl⟩ : syracuseStep 4249045 = 99587) (by norm_num)
theorem B4191709 : Blo 1655527 4191709 := bbase (se 3 (by rfl) ⟨785945, by rfl⟩ : syracuseStep 4191709 = 1571891) (by norm_num)
theorem B2831861 : Blo 1655527 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B5969429 : Blo 1655527 5969429 := bbase (se 6 (by rfl) ⟨139908, by rfl⟩ : syracuseStep 5969429 = 279817) (by norm_num)
theorem B4191821 : Blo 1655527 4191821 := bbase (se 3 (by rfl) ⟨785966, by rfl⟩ : syracuseStep 4191821 = 1571933) (by norm_num)
theorem B10753685 : Blo 1655527 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B5592725 : Blo 1655527 5592725 := bbase (se 6 (by rfl) ⟨131079, by rfl⟩ : syracuseStep 5592725 = 262159) (by norm_num)
theorem B1701545 : Blo 1655527 1701545 := bbase (se 2 (by rfl) ⟨638079, by rfl⟩ : syracuseStep 1701545 = 1276159) (by norm_num)
theorem B3724973 : Blo 1655527 3724973 := bbase (se 3 (by rfl) ⟨698432, by rfl⟩ : syracuseStep 3724973 = 1396865) (by norm_num)
theorem B3143357 : Blo 1655527 3143357 := bbase (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) (by norm_num)
theorem B2651869 : Blo 1655527 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3725045 : Blo 1655527 3725045 := bbase (se 5 (by rfl) ⟨174611, by rfl⟩ : syracuseStep 3725045 = 349223) (by norm_num)
theorem B4192013 : Blo 1655527 4192013 := bbase (se 3 (by rfl) ⟨786002, by rfl⟩ : syracuseStep 4192013 = 1572005) (by norm_num)
theorem B3725117 : Blo 1655527 3725117 := bbase (se 3 (by rfl) ⟨698459, by rfl⟩ : syracuseStep 3725117 = 1396919) (by norm_num)
theorem B3725189 : Blo 1655527 3725189 := bbase (se 4 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 3725189 = 698473) (by norm_num)
theorem B3536789 : Blo 1655527 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B7075765 : Blo 1655527 7075765 := bbase (se 5 (by rfl) ⟨331676, by rfl⟩ : syracuseStep 7075765 = 663353) (by norm_num)
theorem B3725261 : Blo 1655527 3725261 := bbase (se 3 (by rfl) ⟨698486, by rfl⟩ : syracuseStep 3725261 = 1396973) (by norm_num)
theorem B14153717 : Blo 1655527 14153717 := bbase (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) (by norm_num)
theorem B4249597 : Blo 1655527 4249597 := bbase (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) (by norm_num)
theorem B1914881 : Blo 1655527 1914881 := bbase (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) (by norm_num)
theorem B3725333 : Blo 1655527 3725333 := bbase (se 6 (by rfl) ⟨87312, by rfl⟩ : syracuseStep 3725333 = 174625) (by norm_num)
theorem B5593157 : Blo 1655527 5593157 := bbase (se 4 (by rfl) ⟨524358, by rfl⟩ : syracuseStep 5593157 = 1048717) (by norm_num)
theorem B3725405 : Blo 1655527 3725405 := bbase (se 3 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 3725405 = 1397027) (by norm_num)
theorem B4192357 : Blo 1655527 4192357 := bbase (se 4 (by rfl) ⟨393033, by rfl⟩ : syracuseStep 4192357 = 786067) (by norm_num)
theorem B2357381 : Blo 1655527 2357381 := bbase (se 4 (by rfl) ⟨221004, by rfl⟩ : syracuseStep 2357381 = 442009) (by norm_num)
theorem B3537029 : Blo 1655527 3537029 := bbase (se 4 (by rfl) ⟨331596, by rfl⟩ : syracuseStep 3537029 = 663193) (by norm_num)
theorem B3725477 : Blo 1655527 3725477 := bbase (se 4 (by rfl) ⟨349263, by rfl⟩ : syracuseStep 3725477 = 698527) (by norm_num)
theorem B2357461 : Blo 1655527 2357461 := bbase (se 7 (by rfl) ⟨27626, by rfl⟩ : syracuseStep 2357461 = 55253) (by norm_num)
theorem B4192469 : Blo 1655527 4192469 := bbase (se 7 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 4192469 = 98261) (by norm_num)
theorem B3725549 : Blo 1655527 3725549 := bbase (se 3 (by rfl) ⟨698540, by rfl⟩ : syracuseStep 3725549 = 1397081) (by norm_num)
theorem B2095409 : Blo 1655527 2095409 := bbase (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) (by norm_num)
theorem B3725621 : Blo 1655527 3725621 := bbase (se 5 (by rfl) ⟨174638, by rfl⟩ : syracuseStep 3725621 = 349277) (by norm_num)
theorem B2357581 : Blo 1655527 2357581 := bbase (se 3 (by rfl) ⟨442046, by rfl⟩ : syracuseStep 2357581 = 884093) (by norm_num)
theorem B8386901 : Blo 1655527 8386901 := bbase (se 10 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 8386901 = 24571) (by norm_num)
theorem B2095465 : Blo 1655527 2095465 := bbase (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) (by norm_num)
theorem B3725693 : Blo 1655527 3725693 := bbase (se 3 (by rfl) ⟨698567, by rfl⟩ : syracuseStep 3725693 = 1397135) (by norm_num)
theorem B1988993 : Blo 1655527 1988993 := bbase (se 2 (by rfl) ⟨745872, by rfl⟩ : syracuseStep 1988993 = 1491745) (by norm_num)
theorem B4192661 : Blo 1655527 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B4716949 : Blo 1655527 4716949 := bbase (se 6 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 4716949 = 221107) (by norm_num)
theorem B2357677 : Blo 1655527 2357677 := bbase (se 3 (by rfl) ⟨442064, by rfl⟩ : syracuseStep 2357677 = 884129) (by norm_num)
theorem B3144109 : Blo 1655527 3144109 := bbase (se 3 (by rfl) ⟨589520, by rfl⟩ : syracuseStep 3144109 = 1179041) (by norm_num)
theorem B3586493 : Blo 1655527 3586493 := bbase (se 3 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 3586493 = 1344935) (by norm_num)
theorem B3725765 : Blo 1655527 3725765 := bbase (se 4 (by rfl) ⟨349290, by rfl⟩ : syracuseStep 3725765 = 698581) (by norm_num)
theorem B2095561 : Blo 1655527 2095561 := bbase (se 2 (by rfl) ⟨785835, by rfl⟩ : syracuseStep 2095561 = 1571671) (by norm_num)
theorem B5593589 : Blo 1655527 5593589 := bbase (se 5 (by rfl) ⟨262199, by rfl⟩ : syracuseStep 5593589 = 524399) (by norm_num)
theorem B3725837 : Blo 1655527 3725837 := bbase (se 3 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 3725837 = 1397189) (by norm_num)
theorem B4717109 : Blo 1655527 4717109 := bbase (se 5 (by rfl) ⟨221114, by rfl⟩ : syracuseStep 4717109 = 442229) (by norm_num)
theorem B3144253 : Blo 1655527 3144253 := bbase (se 3 (by rfl) ⟨589547, by rfl⟩ : syracuseStep 3144253 = 1179095) (by norm_num)
theorem B4250173 : Blo 1655527 4250173 := bbase (se 3 (by rfl) ⟨796907, by rfl⟩ : syracuseStep 4250173 = 1593815) (by norm_num)
theorem B3725909 : Blo 1655527 3725909 := bbase (se 8 (by rfl) ⟨21831, by rfl⟩ : syracuseStep 3725909 = 43663) (by norm_num)
theorem B2095733 : Blo 1655527 2095733 := bbase (se 5 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 2095733 = 196475) (by norm_num)
theorem B2652797 : Blo 1655527 2652797 := bbase (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) (by norm_num)
theorem B3537533 : Blo 1655527 3537533 := bbase (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) (by norm_num)
theorem B3357317 : Blo 1655527 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B3537541 : Blo 1655527 3537541 := bbase (se 4 (by rfl) ⟨331644, by rfl⟩ : syracuseStep 3537541 = 663289) (by norm_num)
theorem B30227093 : Blo 1655527 30227093 := bbase (se 6 (by rfl) ⟨708447, by rfl⟩ : syracuseStep 30227093 = 1416895) (by norm_num)
theorem B3725981 : Blo 1655527 3725981 := bbase (se 3 (by rfl) ⟨698621, by rfl⟩ : syracuseStep 3725981 = 1397243) (by norm_num)
theorem B2095789 : Blo 1655527 2095789 := bbase (se 3 (by rfl) ⟨392960, by rfl⟩ : syracuseStep 2095789 = 785921) (by norm_num)
theorem B1989301 : Blo 1655527 1989301 := bbase (se 5 (by rfl) ⟨93248, by rfl⟩ : syracuseStep 1989301 = 186497) (by norm_num)
theorem B3144413 : Blo 1655527 3144413 := bbase (se 3 (by rfl) ⟨589577, by rfl⟩ : syracuseStep 3144413 = 1179155) (by norm_num)
theorem B3726053 : Blo 1655527 3726053 := bbase (se 4 (by rfl) ⟨349317, by rfl⟩ : syracuseStep 3726053 = 698635) (by norm_num)
theorem B4193005 : Blo 1655527 4193005 := bbase (se 3 (by rfl) ⟨786188, by rfl⟩ : syracuseStep 4193005 = 1572377) (by norm_num)
theorem B2095885 : Blo 1655527 2095885 := bbase (se 3 (by rfl) ⟨392978, by rfl⟩ : syracuseStep 2095885 = 785957) (by norm_num)
theorem B4717349 : Blo 1655527 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B3726125 : Blo 1655527 3726125 := bbase (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) (by norm_num)
theorem B1768241 : Blo 1655527 1768241 := bbase (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) (by norm_num)
theorem B4193117 : Blo 1655527 4193117 := bbase (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) (by norm_num)
theorem B3144557 : Blo 1655527 3144557 := bbase (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) (by norm_num)
theorem B3726197 : Blo 1655527 3726197 := bbase (se 5 (by rfl) ⟨174665, by rfl⟩ : syracuseStep 3726197 = 349331) (by norm_num)
theorem B1678205 : Blo 1655527 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B1989517 : Blo 1655527 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B2358173 : Blo 1655527 2358173 := bbase (se 3 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 2358173 = 884315) (by norm_num)
theorem B5594021 : Blo 1655527 5594021 := bbase (se 4 (by rfl) ⟨524439, by rfl⟩ : syracuseStep 5594021 = 1048879) (by norm_num)
theorem B9436085 : Blo 1655527 9436085 := bbase (se 5 (by rfl) ⟨442316, by rfl⟩ : syracuseStep 9436085 = 884633) (by norm_num)
theorem B2096057 : Blo 1655527 2096057 := bbase (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) (by norm_num)
theorem B3726269 : Blo 1655527 3726269 := bbase (se 3 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 3726269 = 1397351) (by norm_num)
theorem B4717541 : Blo 1655527 4717541 := bbase (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) (by norm_num)
theorem B6290405 : Blo 1655527 6290405 := bbase (se 4 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 6290405 = 1179451) (by norm_num)
theorem B1768429 : Blo 1655527 1768429 := bbase (se 3 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 1768429 = 663161) (by norm_num)
theorem B2096113 : Blo 1655527 2096113 := bbase (se 2 (by rfl) ⟨786042, by rfl⟩ : syracuseStep 2096113 = 1572085) (by norm_num)
theorem B3726341 : Blo 1655527 3726341 := bbase (se 4 (by rfl) ⟨349344, by rfl⟩ : syracuseStep 3726341 = 698689) (by norm_num)
theorem B4193309 : Blo 1655527 4193309 := bbase (se 3 (by rfl) ⟨786245, by rfl⟩ : syracuseStep 4193309 = 1572491) (by norm_num)
theorem B2653253 : Blo 1655527 2653253 := bbase (se 4 (by rfl) ⟨248742, by rfl⟩ : syracuseStep 2653253 = 497485) (by norm_num)
theorem B3726413 : Blo 1655527 3726413 := bbase (se 3 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 3726413 = 1397405) (by norm_num)
theorem B2096209 : Blo 1655527 2096209 := bbase (se 2 (by rfl) ⟨786078, by rfl⟩ : syracuseStep 2096209 = 1572157) (by norm_num)
theorem B3144845 : Blo 1655527 3144845 := bbase (se 3 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 3144845 = 1179317) (by norm_num)
theorem B3726485 : Blo 1655527 3726485 := bbase (se 6 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 3726485 = 174679) (by norm_num)
theorem B1678493 : Blo 1655527 1678493 := bbase (se 3 (by rfl) ⟨314717, by rfl⟩ : syracuseStep 1678493 = 629435) (by norm_num)
theorem B1678529 : Blo 1655527 1678529 := bbase (se 2 (by rfl) ⟨629448, by rfl⟩ : syracuseStep 1678529 = 1258897) (by norm_num)
theorem B11943125 : Blo 1655527 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B15924437 : Blo 1655527 15924437 := bbase (se 7 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 15924437 = 373229) (by norm_num)
theorem B3726557 : Blo 1655527 3726557 := bbase (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) (by norm_num)
theorem B2268397 : Blo 1655527 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B2096381 : Blo 1655527 2096381 := bbase (se 3 (by rfl) ⟨393071, by rfl⟩ : syracuseStep 2096381 = 786143) (by norm_num)
theorem B6290693 : Blo 1655527 6290693 := bbase (se 4 (by rfl) ⟨589752, by rfl⟩ : syracuseStep 6290693 = 1179505) (by norm_num)
theorem B3726629 : Blo 1655527 3726629 := bbase (se 4 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 3726629 = 698743) (by norm_num)
theorem B3144997 : Blo 1655527 3144997 := bbase (se 4 (by rfl) ⟨294843, by rfl⟩ : syracuseStep 3144997 = 589687) (by norm_num)
theorem B2096437 : Blo 1655527 2096437 := bbase (se 5 (by rfl) ⟨98270, by rfl⟩ : syracuseStep 2096437 = 196541) (by norm_num)
theorem B3726701 : Blo 1655527 3726701 := bbase (se 3 (by rfl) ⟨698756, by rfl⟩ : syracuseStep 3726701 = 1397513) (by norm_num)
theorem B4193653 : Blo 1655527 4193653 := bbase (se 5 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 4193653 = 393155) (by norm_num)
theorem B3980677 : Blo 1655527 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B7077253 : Blo 1655527 7077253 := bbase (se 4 (by rfl) ⟨663492, by rfl⟩ : syracuseStep 7077253 = 1326985) (by norm_num)
theorem B2096533 : Blo 1655527 2096533 := bbase (se 6 (by rfl) ⟨49137, by rfl⟩ : syracuseStep 2096533 = 98275) (by norm_num)
theorem B5037461 : Blo 1655527 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B7077269 : Blo 1655527 7077269 := bbase (se 6 (by rfl) ⟨165873, by rfl⟩ : syracuseStep 7077269 = 331747) (by norm_num)
theorem B3726773 : Blo 1655527 3726773 := bbase (se 5 (by rfl) ⟨174692, by rfl⟩ : syracuseStep 3726773 = 349385) (by norm_num)
theorem B2358725 : Blo 1655527 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B1990117 : Blo 1655527 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B4193765 : Blo 1655527 4193765 := bbase (se 4 (by rfl) ⟨393165, by rfl⟩ : syracuseStep 4193765 = 786331) (by norm_num)
theorem B11943413 : Blo 1655527 11943413 := bbase (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) (by norm_num)
theorem B3726845 : Blo 1655527 3726845 := bbase (se 3 (by rfl) ⟨698783, by rfl⟩ : syracuseStep 3726845 = 1397567) (by norm_num)
theorem B2096705 : Blo 1655527 2096705 := bbase (se 2 (by rfl) ⟨786264, by rfl⟩ : syracuseStep 2096705 = 1572529) (by norm_num)
theorem B3726917 : Blo 1655527 3726917 := bbase (se 4 (by rfl) ⟨349398, by rfl⟩ : syracuseStep 3726917 = 698797) (by norm_num)
theorem B3145301 : Blo 1655527 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B8388197 : Blo 1655527 8388197 := bbase (se 4 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 8388197 = 1572787) (by norm_num)
theorem B2096761 : Blo 1655527 2096761 := bbase (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) (by norm_num)
theorem B3726989 : Blo 1655527 3726989 := bbase (se 3 (by rfl) ⟨698810, by rfl⟩ : syracuseStep 3726989 = 1397621) (by norm_num)
theorem B4193957 : Blo 1655527 4193957 := bbase (se 4 (by rfl) ⟨393183, by rfl⟩ : syracuseStep 4193957 = 786367) (by norm_num)
theorem B1793701 : Blo 1655527 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B22658773 : Blo 1655527 22658773 := bbase (se 7 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 22658773 = 531065) (by norm_num)
theorem B3727061 : Blo 1655527 3727061 := bbase (se 7 (by rfl) ⟨43676, by rfl⟩ : syracuseStep 3727061 = 87353) (by norm_num)
theorem B2096857 : Blo 1655527 2096857 := bbase (se 2 (by rfl) ⟨786321, by rfl⟩ : syracuseStep 2096857 = 1572643) (by norm_num)
theorem B1679077 : Blo 1655527 1679077 := bbase (se 4 (by rfl) ⟨157413, by rfl⟩ : syracuseStep 1679077 = 314827) (by norm_num)
theorem B3538669 : Blo 1655527 3538669 := bbase (se 3 (by rfl) ⟨663500, by rfl⟩ : syracuseStep 3538669 = 1327001) (by norm_num)
theorem B7962389 : Blo 1655527 7962389 := bbase (se 6 (by rfl) ⟨186618, by rfl⟩ : syracuseStep 7962389 = 373237) (by norm_num)
theorem B3727133 : Blo 1655527 3727133 := bbase (se 3 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 3727133 = 1397675) (by norm_num)
theorem B1769249 : Blo 1655527 1769249 := bbase (se 2 (by rfl) ⟨663468, by rfl⟩ : syracuseStep 1769249 = 1326937) (by norm_num)
theorem B4251485 : Blo 1655527 4251485 := bbase (se 3 (by rfl) ⟨797153, by rfl⟩ : syracuseStep 4251485 = 1594307) (by norm_num)
theorem B3727205 : Blo 1655527 3727205 := bbase (se 4 (by rfl) ⟨349425, by rfl⟩ : syracuseStep 3727205 = 698851) (by norm_num)
theorem B2097029 : Blo 1655527 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B3727277 : Blo 1655527 3727277 := bbase (se 3 (by rfl) ⟨698864, by rfl⟩ : syracuseStep 3727277 = 1397729) (by norm_num)
theorem B2097085 : Blo 1655527 2097085 := bbase (se 3 (by rfl) ⟨393203, by rfl⟩ : syracuseStep 2097085 = 786407) (by norm_num)
theorem B4718533 : Blo 1655527 4718533 := bbase (se 4 (by rfl) ⟨442362, by rfl⟩ : syracuseStep 4718533 = 884725) (by norm_num)
theorem B3727349 : Blo 1655527 3727349 := bbase (se 5 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 3727349 = 349439) (by norm_num)
theorem B4194301 : Blo 1655527 4194301 := bbase (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) (by norm_num)
theorem B3539011 : Blo 1655527 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B2359363 : Blo 1655527 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B1990723 : Blo 1655527 1990723 := bstep (se 1 (by rfl) ⟨1493042, by rfl⟩ : syracuseStep 1990723 = 2986085) B2986085
theorem B12583025 : Blo 1655527 12583025 := bstep (se 2 (by rfl) ⟨4718634, by rfl⟩ : syracuseStep 12583025 = 9437269) B9437269
theorem B11337841 : Blo 1655527 11337841 := bstep (se 2 (by rfl) ⟨4251690, by rfl⟩ : syracuseStep 11337841 = 8503381) B8503381
theorem B3727601 : Blo 1655527 3727601 := bstep (se 2 (by rfl) ⟨1397850, by rfl⟩ : syracuseStep 3727601 = 2795701) B2795701
theorem B3145969 : Blo 1655527 3145969 := bstep (se 2 (by rfl) ⟨1179738, by rfl⟩ : syracuseStep 3145969 = 2359477) B2359477
theorem B3727619 : Blo 1655527 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B1769779 : Blo 1655527 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B2793811 : Blo 1655527 2793811 := bstep (se 1 (by rfl) ⟨2095358, by rfl⟩ : syracuseStep 2793811 = 4190717) B4190717
theorem B2097571 : Blo 1655527 2097571 := bstep (se 1 (by rfl) ⟨1573178, by rfl⟩ : syracuseStep 2097571 = 3146357) B3146357
theorem B4194737 : Blo 1655527 4194737 := bstep (se 2 (by rfl) ⟨1573026, by rfl⟩ : syracuseStep 4194737 = 3146053) B3146053
theorem B2793953 : Blo 1655527 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B20431331 : Blo 1655527 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B4194787 : Blo 1655527 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B2654707 : Blo 1655527 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B2097667 : Blo 1655527 2097667 := bstep (se 1 (by rfl) ⟨1573250, by rfl⟩ : syracuseStep 2097667 = 3146501) B3146501
theorem B3727889 : Blo 1655527 3727889 := bstep (se 2 (by rfl) ⟨1397958, by rfl⟩ : syracuseStep 3727889 = 2795917) B2795917
theorem B1679891 : Blo 1655527 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B3727907 : Blo 1655527 3727907 := bstep (se 1 (by rfl) ⟨2795930, by rfl⟩ : syracuseStep 3727907 = 5591861) B5591861
theorem B8389169 : Blo 1655527 8389169 := bstep (se 2 (by rfl) ⟨3145938, by rfl⟩ : syracuseStep 8389169 = 6291877) B6291877
theorem B2155075 : Blo 1655527 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B1991251 : Blo 1655527 1991251 := bstep (se 1 (by rfl) ⟨1493438, by rfl⟩ : syracuseStep 1991251 = 2986877) B2986877
theorem B2794081 : Blo 1655527 2794081 := bstep (se 2 (by rfl) ⟨1047780, by rfl⟩ : syracuseStep 2794081 = 2095561) B2095561
theorem B9437795 : Blo 1655527 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B7078499 : Blo 1655527 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B4194929 : Blo 1655527 4194929 := bstep (se 2 (by rfl) ⟨1573098, by rfl⟩ : syracuseStep 4194929 = 3146197) B3146197
theorem B2794115 : Blo 1655527 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B1655539 : Blo 1655527 1655539 := bstep (se 1 (by rfl) ⟨1241654, by rfl⟩ : syracuseStep 1655539 = 2483309) B2483309
theorem B1655555 : Blo 1655527 1655555 := bstep (se 1 (by rfl) ⟨1241666, by rfl⟩ : syracuseStep 1655555 = 2483333) B2483333
theorem B2794243 : Blo 1655527 2794243 := bstep (se 1 (by rfl) ⟨2095682, by rfl⟩ : syracuseStep 2794243 = 4191365) B4191365
theorem B1655571 : Blo 1655527 1655571 := bstep (se 1 (by rfl) ⟨1241678, by rfl⟩ : syracuseStep 1655571 = 2483357) B2483357
theorem B1655587 : Blo 1655527 1655587 := bstep (se 1 (by rfl) ⟨1241690, by rfl⟩ : syracuseStep 1655587 = 2483381) B2483381
theorem B5587757 : Blo 1655527 5587757 := bstep (se 3 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 5587757 = 2095409) B2095409
theorem B3728177 : Blo 1655527 3728177 := bstep (se 2 (by rfl) ⟨1398066, by rfl⟩ : syracuseStep 3728177 = 2796133) B2796133
theorem B1655603 : Blo 1655527 1655603 := bstep (se 1 (by rfl) ⟨1241702, by rfl⟩ : syracuseStep 1655603 = 2483405) B2483405
theorem B1655619 : Blo 1655527 1655619 := bstep (se 1 (by rfl) ⟨1241714, by rfl⟩ : syracuseStep 1655619 = 2483429) B2483429
theorem B3728195 : Blo 1655527 3728195 := bstep (se 1 (by rfl) ⟨2796146, by rfl⟩ : syracuseStep 3728195 = 5592293) B5592293
theorem B1655635 : Blo 1655527 1655635 := bstep (se 1 (by rfl) ⟨1241726, by rfl⟩ : syracuseStep 1655635 = 2483453) B2483453
theorem B5587811 : Blo 1655527 5587811 := bstep (se 1 (by rfl) ⟨4190858, by rfl⟩ : syracuseStep 5587811 = 8381717) B8381717
theorem B1655651 : Blo 1655527 1655651 := bstep (se 1 (by rfl) ⟨1241738, by rfl⟩ : syracuseStep 1655651 = 2483477) B2483477
theorem B7963505 : Blo 1655527 7963505 := bstep (se 2 (by rfl) ⟨2986314, by rfl⟩ : syracuseStep 7963505 = 5972629) B5972629
theorem B1655667 : Blo 1655527 1655667 := bstep (se 1 (by rfl) ⟨1241750, by rfl⟩ : syracuseStep 1655667 = 2483501) B2483501
theorem B1655683 : Blo 1655527 1655683 := bstep (se 1 (by rfl) ⟨1241762, by rfl⟩ : syracuseStep 1655683 = 2483525) B2483525
theorem B2794385 : Blo 1655527 2794385 := bstep (se 2 (by rfl) ⟨1047894, by rfl⟩ : syracuseStep 2794385 = 2095789) B2095789
theorem B1655699 : Blo 1655527 1655699 := bstep (se 1 (by rfl) ⟨1241774, by rfl⟩ : syracuseStep 1655699 = 2483549) B2483549
theorem B3539857 : Blo 1655527 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B1655715 : Blo 1655527 1655715 := bstep (se 1 (by rfl) ⟨1241786, by rfl⟩ : syracuseStep 1655715 = 2483573) B2483573
theorem B1655731 : Blo 1655527 1655731 := bstep (se 1 (by rfl) ⟨1241798, by rfl⟩ : syracuseStep 1655731 = 2483597) B2483597
theorem B1655747 : Blo 1655527 1655747 := bstep (se 1 (by rfl) ⟨1241810, by rfl⟩ : syracuseStep 1655747 = 2483621) B2483621
theorem B1655763 : Blo 1655527 1655763 := bstep (se 1 (by rfl) ⟨1241822, by rfl⟩ : syracuseStep 1655763 = 2483645) B2483645
theorem B1655779 : Blo 1655527 1655779 := bstep (se 1 (by rfl) ⟨1241834, by rfl⟩ : syracuseStep 1655779 = 2483669) B2483669
theorem B14148593 : Blo 1655527 14148593 := bstep (se 2 (by rfl) ⟨5305722, by rfl⟩ : syracuseStep 14148593 = 10611445) B10611445
theorem B1655795 : Blo 1655527 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1655811 : Blo 1655527 1655811 := bstep (se 1 (by rfl) ⟨1241858, by rfl⟩ : syracuseStep 1655811 = 2483717) B2483717
theorem B2794513 : Blo 1655527 2794513 := bstep (se 2 (by rfl) ⟨1047942, by rfl⟩ : syracuseStep 2794513 = 2095885) B2095885
theorem B1655827 : Blo 1655527 1655827 := bstep (se 1 (by rfl) ⟨1241870, by rfl⟩ : syracuseStep 1655827 = 2483741) B2483741
theorem B1655843 : Blo 1655527 1655843 := bstep (se 1 (by rfl) ⟨1241882, by rfl⟩ : syracuseStep 1655843 = 2483765) B2483765
theorem B1655859 : Blo 1655527 1655859 := bstep (se 1 (by rfl) ⟨1241894, by rfl⟩ : syracuseStep 1655859 = 2483789) B2483789
theorem B2794547 : Blo 1655527 2794547 := bstep (se 1 (by rfl) ⟨2095910, by rfl⟩ : syracuseStep 2794547 = 4191821) B4191821
theorem B1655875 : Blo 1655527 1655875 := bstep (se 1 (by rfl) ⟨1241906, by rfl⟩ : syracuseStep 1655875 = 2483813) B2483813
theorem B4719683 : Blo 1655527 4719683 := bstep (se 1 (by rfl) ⟨3539762, by rfl⟩ : syracuseStep 4719683 = 7079525) B7079525
theorem B11945029 : Blo 1655527 11945029 := bstep (se 4 (by rfl) ⟨1119846, by rfl⟩ : syracuseStep 11945029 = 2239693) B2239693
theorem B3728465 : Blo 1655527 3728465 := bstep (se 2 (by rfl) ⟨1398174, by rfl⟩ : syracuseStep 3728465 = 2796349) B2796349
theorem B1655891 : Blo 1655527 1655891 := bstep (se 1 (by rfl) ⟨1241918, by rfl⟩ : syracuseStep 1655891 = 2483837) B2483837
theorem B2483297 : Blo 1655527 2483297 := bstep (se 2 (by rfl) ⟨931236, by rfl⟩ : syracuseStep 2483297 = 1862473) B1862473
theorem B7169123 : Blo 1655527 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B1655907 : Blo 1655527 1655907 := bstep (se 1 (by rfl) ⟨1241930, by rfl⟩ : syracuseStep 1655907 = 2483861) B2483861
theorem B3728483 : Blo 1655527 3728483 := bstep (se 1 (by rfl) ⟨2796362, by rfl⟩ : syracuseStep 3728483 = 5592725) B5592725
theorem B5588081 : Blo 1655527 5588081 := bstep (se 2 (by rfl) ⟨2095530, by rfl⟩ : syracuseStep 5588081 = 4191061) B4191061
theorem B2483315 : Blo 1655527 2483315 := bstep (se 1 (by rfl) ⟨1862486, by rfl⟩ : syracuseStep 2483315 = 3724973) B3724973
theorem B1655923 : Blo 1655527 1655923 := bstep (se 1 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 1655923 = 2483885) B2483885
theorem B1655939 : Blo 1655527 1655939 := bstep (se 1 (by rfl) ⟨1241954, by rfl⟩ : syracuseStep 1655939 = 2483909) B2483909
theorem B10609805 : Blo 1655527 10609805 := bstep (se 3 (by rfl) ⟨1989338, by rfl⟩ : syracuseStep 10609805 = 3978677) B3978677
theorem B2483345 : Blo 1655527 2483345 := bstep (se 2 (by rfl) ⟨931254, by rfl⟩ : syracuseStep 2483345 = 1862509) B1862509
theorem B1655955 : Blo 1655527 1655955 := bstep (se 1 (by rfl) ⟨1241966, by rfl⟩ : syracuseStep 1655955 = 2483933) B2483933
theorem B2483363 : Blo 1655527 2483363 := bstep (se 1 (by rfl) ⟨1862522, by rfl⟩ : syracuseStep 2483363 = 3725045) B3725045
theorem B1655971 : Blo 1655527 1655971 := bstep (se 1 (by rfl) ⟨1241978, by rfl⟩ : syracuseStep 1655971 = 2483957) B2483957
theorem B1655987 : Blo 1655527 1655987 := bstep (se 1 (by rfl) ⟨1241990, by rfl⟩ : syracuseStep 1655987 = 2483981) B2483981
theorem B2794675 : Blo 1655527 2794675 := bstep (se 1 (by rfl) ⟨2096006, by rfl⟩ : syracuseStep 2794675 = 4192013) B4192013
theorem B2483393 : Blo 1655527 2483393 := bstep (se 2 (by rfl) ⟨931272, by rfl⟩ : syracuseStep 2483393 = 1862545) B1862545
theorem B1656003 : Blo 1655527 1656003 := bstep (se 1 (by rfl) ⟨1242002, by rfl⟩ : syracuseStep 1656003 = 2484005) B2484005
theorem B2483411 : Blo 1655527 2483411 := bstep (se 1 (by rfl) ⟨1862558, by rfl⟩ : syracuseStep 2483411 = 3725117) B3725117
theorem B1656019 : Blo 1655527 1656019 := bstep (se 1 (by rfl) ⟨1242014, by rfl⟩ : syracuseStep 1656019 = 2484029) B2484029
theorem B1656035 : Blo 1655527 1656035 := bstep (se 1 (by rfl) ⟨1242026, by rfl⟩ : syracuseStep 1656035 = 2484053) B2484053
theorem B2483441 : Blo 1655527 2483441 := bstep (se 2 (by rfl) ⟨931290, by rfl⟩ : syracuseStep 2483441 = 1862581) B1862581
theorem B1656051 : Blo 1655527 1656051 := bstep (se 1 (by rfl) ⟨1242038, by rfl⟩ : syracuseStep 1656051 = 2484077) B2484077
theorem B2483459 : Blo 1655527 2483459 := bstep (se 1 (by rfl) ⟨1862594, by rfl⟩ : syracuseStep 2483459 = 3725189) B3725189
theorem B1656067 : Blo 1655527 1656067 := bstep (se 1 (by rfl) ⟨1242050, by rfl⟩ : syracuseStep 1656067 = 2484101) B2484101
theorem B1656083 : Blo 1655527 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B2483489 : Blo 1655527 2483489 := bstep (se 2 (by rfl) ⟨931308, by rfl⟩ : syracuseStep 2483489 = 1862617) B1862617
theorem B1656099 : Blo 1655527 1656099 := bstep (se 1 (by rfl) ⟨1242074, by rfl⟩ : syracuseStep 1656099 = 2484149) B2484149
theorem B2483507 : Blo 1655527 2483507 := bstep (se 1 (by rfl) ⟨1862630, by rfl⟩ : syracuseStep 2483507 = 3725261) B3725261
theorem B1656115 : Blo 1655527 1656115 := bstep (se 1 (by rfl) ⟨1242086, by rfl⟩ : syracuseStep 1656115 = 2484173) B2484173
theorem B2794817 : Blo 1655527 2794817 := bstep (se 2 (by rfl) ⟨1048056, by rfl⟩ : syracuseStep 2794817 = 2096113) B2096113
theorem B1656131 : Blo 1655527 1656131 := bstep (se 1 (by rfl) ⟨1242098, by rfl⟩ : syracuseStep 1656131 = 2484197) B2484197
theorem B2483537 : Blo 1655527 2483537 := bstep (se 2 (by rfl) ⟨931326, by rfl⟩ : syracuseStep 2483537 = 1862653) B1862653
theorem B1656147 : Blo 1655527 1656147 := bstep (se 1 (by rfl) ⟨1242110, by rfl⟩ : syracuseStep 1656147 = 2484221) B2484221
theorem B2483555 : Blo 1655527 2483555 := bstep (se 1 (by rfl) ⟨1862666, by rfl⟩ : syracuseStep 2483555 = 3725333) B3725333
theorem B1656163 : Blo 1655527 1656163 := bstep (se 1 (by rfl) ⟨1242122, by rfl⟩ : syracuseStep 1656163 = 2484245) B2484245
theorem B6292835 : Blo 1655527 6292835 := bstep (se 1 (by rfl) ⟨4719626, by rfl⟩ : syracuseStep 6292835 = 9439253) B9439253
theorem B3728753 : Blo 1655527 3728753 := bstep (se 2 (by rfl) ⟨1398282, by rfl⟩ : syracuseStep 3728753 = 2796565) B2796565
theorem B6292849 : Blo 1655527 6292849 := bstep (se 2 (by rfl) ⟨2359818, by rfl⟩ : syracuseStep 6292849 = 4719637) B4719637
theorem B1656179 : Blo 1655527 1656179 := bstep (se 1 (by rfl) ⟨1242134, by rfl⟩ : syracuseStep 1656179 = 2484269) B2484269
theorem B2483585 : Blo 1655527 2483585 := bstep (se 2 (by rfl) ⟨931344, by rfl⟩ : syracuseStep 2483585 = 1862689) B1862689
theorem B1656195 : Blo 1655527 1656195 := bstep (se 1 (by rfl) ⟨1242146, by rfl⟩ : syracuseStep 1656195 = 2484293) B2484293
theorem B3728771 : Blo 1655527 3728771 := bstep (se 1 (by rfl) ⟨2796578, by rfl⟩ : syracuseStep 3728771 = 5593157) B5593157
theorem B2483603 : Blo 1655527 2483603 := bstep (se 1 (by rfl) ⟨1862702, by rfl⟩ : syracuseStep 2483603 = 3725405) B3725405
theorem B1656211 : Blo 1655527 1656211 := bstep (se 1 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 1656211 = 2484317) B2484317
theorem B1656227 : Blo 1655527 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B2483633 : Blo 1655527 2483633 := bstep (se 2 (by rfl) ⟨931362, by rfl⟩ : syracuseStep 2483633 = 1862725) B1862725
theorem B1656243 : Blo 1655527 1656243 := bstep (se 1 (by rfl) ⟨1242182, by rfl⟩ : syracuseStep 1656243 = 2484365) B2484365
theorem B2794945 : Blo 1655527 2794945 := bstep (se 2 (by rfl) ⟨1048104, by rfl⟩ : syracuseStep 2794945 = 2096209) B2096209
theorem B2483651 : Blo 1655527 2483651 := bstep (se 1 (by rfl) ⟨1862738, by rfl⟩ : syracuseStep 2483651 = 3725477) B3725477
theorem B1656259 : Blo 1655527 1656259 := bstep (se 1 (by rfl) ⟨1242194, by rfl⟩ : syracuseStep 1656259 = 2484389) B2484389
theorem B1656275 : Blo 1655527 1656275 := bstep (se 1 (by rfl) ⟨1242206, by rfl⟩ : syracuseStep 1656275 = 2484413) B2484413
theorem B2483681 : Blo 1655527 2483681 := bstep (se 2 (by rfl) ⟨931380, by rfl⟩ : syracuseStep 2483681 = 1862761) B1862761
theorem B2794979 : Blo 1655527 2794979 := bstep (se 1 (by rfl) ⟨2096234, by rfl⟩ : syracuseStep 2794979 = 4192469) B4192469
theorem B1656291 : Blo 1655527 1656291 := bstep (se 1 (by rfl) ⟨1242218, by rfl⟩ : syracuseStep 1656291 = 2484437) B2484437
theorem B2483699 : Blo 1655527 2483699 := bstep (se 1 (by rfl) ⟨1862774, by rfl⟩ : syracuseStep 2483699 = 3725549) B3725549
theorem B1656307 : Blo 1655527 1656307 := bstep (se 1 (by rfl) ⟨1242230, by rfl⟩ : syracuseStep 1656307 = 2484461) B2484461
theorem B1656323 : Blo 1655527 1656323 := bstep (se 1 (by rfl) ⟨1242242, by rfl⟩ : syracuseStep 1656323 = 2484485) B2484485
theorem B2483729 : Blo 1655527 2483729 := bstep (se 2 (by rfl) ⟨931398, by rfl⟩ : syracuseStep 2483729 = 1862797) B1862797
theorem B1656339 : Blo 1655527 1656339 := bstep (se 1 (by rfl) ⟨1242254, by rfl⟩ : syracuseStep 1656339 = 2484509) B2484509
theorem B2483747 : Blo 1655527 2483747 := bstep (se 1 (by rfl) ⟨1862810, by rfl⟩ : syracuseStep 2483747 = 3725621) B3725621
theorem B1656355 : Blo 1655527 1656355 := bstep (se 1 (by rfl) ⟨1242266, by rfl⟩ : syracuseStep 1656355 = 2484533) B2484533
theorem B1656371 : Blo 1655527 1656371 := bstep (se 1 (by rfl) ⟨1242278, by rfl⟩ : syracuseStep 1656371 = 2484557) B2484557
theorem B2483777 : Blo 1655527 2483777 := bstep (se 2 (by rfl) ⟨931416, by rfl⟩ : syracuseStep 2483777 = 1862833) B1862833
theorem B1656387 : Blo 1655527 1656387 := bstep (se 1 (by rfl) ⟨1242290, by rfl⟩ : syracuseStep 1656387 = 2484581) B2484581
theorem B5973581 : Blo 1655527 5973581 := bstep (se 3 (by rfl) ⟨1120046, by rfl⟩ : syracuseStep 5973581 = 2240093) B2240093
theorem B5310029 : Blo 1655527 5310029 := bstep (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) B1991261
theorem B2483795 : Blo 1655527 2483795 := bstep (se 1 (by rfl) ⟨1862846, by rfl⟩ : syracuseStep 2483795 = 3725693) B3725693
theorem B1656403 : Blo 1655527 1656403 := bstep (se 1 (by rfl) ⟨1242302, by rfl⟩ : syracuseStep 1656403 = 2484605) B2484605
theorem B2795107 : Blo 1655527 2795107 := bstep (se 1 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 2795107 = 4192661) B4192661
theorem B1656419 : Blo 1655527 1656419 := bstep (se 1 (by rfl) ⟨1242314, by rfl⟩ : syracuseStep 1656419 = 2484629) B2484629
theorem B2483825 : Blo 1655527 2483825 := bstep (se 2 (by rfl) ⟨931434, by rfl⟩ : syracuseStep 2483825 = 1862869) B1862869
theorem B1656435 : Blo 1655527 1656435 := bstep (se 1 (by rfl) ⟨1242326, by rfl⟩ : syracuseStep 1656435 = 2484653) B2484653
theorem B2483843 : Blo 1655527 2483843 := bstep (se 1 (by rfl) ⟨1862882, by rfl⟩ : syracuseStep 2483843 = 3725765) B3725765
theorem B1656451 : Blo 1655527 1656451 := bstep (se 1 (by rfl) ⟨1242338, by rfl⟩ : syracuseStep 1656451 = 2484677) B2484677
theorem B5588621 : Blo 1655527 5588621 := bstep (se 3 (by rfl) ⟨1047866, by rfl⟩ : syracuseStep 5588621 = 2095733) B2095733
theorem B3729041 : Blo 1655527 3729041 := bstep (se 2 (by rfl) ⟨1398390, by rfl⟩ : syracuseStep 3729041 = 2796781) B2796781
theorem B1656467 : Blo 1655527 1656467 := bstep (se 1 (by rfl) ⟨1242350, by rfl⟩ : syracuseStep 1656467 = 2484701) B2484701
theorem B2483873 : Blo 1655527 2483873 := bstep (se 2 (by rfl) ⟨931452, by rfl⟩ : syracuseStep 2483873 = 1862905) B1862905
theorem B1656483 : Blo 1655527 1656483 := bstep (se 1 (by rfl) ⟨1242362, by rfl⟩ : syracuseStep 1656483 = 2484725) B2484725
theorem B3729059 : Blo 1655527 3729059 := bstep (se 1 (by rfl) ⟨2796794, by rfl⟩ : syracuseStep 3729059 = 5593589) B5593589
theorem B2483891 : Blo 1655527 2483891 := bstep (se 1 (by rfl) ⟨1862918, by rfl⟩ : syracuseStep 2483891 = 3725837) B3725837
theorem B1656499 : Blo 1655527 1656499 := bstep (se 1 (by rfl) ⟨1242374, by rfl⟩ : syracuseStep 1656499 = 2484749) B2484749
theorem B5588675 : Blo 1655527 5588675 := bstep (se 1 (by rfl) ⟨4191506, by rfl⟩ : syracuseStep 5588675 = 8383013) B8383013
theorem B1656515 : Blo 1655527 1656515 := bstep (se 1 (by rfl) ⟨1242386, by rfl⟩ : syracuseStep 1656515 = 2484773) B2484773
theorem B2483921 : Blo 1655527 2483921 := bstep (se 2 (by rfl) ⟨931470, by rfl⟩ : syracuseStep 2483921 = 1862941) B1862941
theorem B1656531 : Blo 1655527 1656531 := bstep (se 1 (by rfl) ⟨1242398, by rfl⟩ : syracuseStep 1656531 = 2484797) B2484797
theorem B2483939 : Blo 1655527 2483939 := bstep (se 1 (by rfl) ⟨1862954, by rfl⟩ : syracuseStep 2483939 = 3725909) B3725909
theorem B1656547 : Blo 1655527 1656547 := bstep (se 1 (by rfl) ⟨1242410, by rfl⟩ : syracuseStep 1656547 = 2484821) B2484821
theorem B2795249 : Blo 1655527 2795249 := bstep (se 2 (by rfl) ⟨1048218, by rfl⟩ : syracuseStep 2795249 = 2096437) B2096437
theorem B1656563 : Blo 1655527 1656563 := bstep (se 1 (by rfl) ⟨1242422, by rfl⟩ : syracuseStep 1656563 = 2484845) B2484845
theorem B2483969 : Blo 1655527 2483969 := bstep (se 2 (by rfl) ⟨931488, by rfl⟩ : syracuseStep 2483969 = 1862977) B1862977
theorem B2238211 : Blo 1655527 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B1656579 : Blo 1655527 1656579 := bstep (se 1 (by rfl) ⟨1242434, by rfl⟩ : syracuseStep 1656579 = 2484869) B2484869
theorem B2483987 : Blo 1655527 2483987 := bstep (se 1 (by rfl) ⟨1862990, by rfl⟩ : syracuseStep 2483987 = 3725981) B3725981
theorem B1656595 : Blo 1655527 1656595 := bstep (se 1 (by rfl) ⟨1242446, by rfl⟩ : syracuseStep 1656595 = 2484893) B2484893
theorem B1656611 : Blo 1655527 1656611 := bstep (se 1 (by rfl) ⟨1242458, by rfl⟩ : syracuseStep 1656611 = 2484917) B2484917
theorem B2484017 : Blo 1655527 2484017 := bstep (se 2 (by rfl) ⟨931506, by rfl⟩ : syracuseStep 2484017 = 1863013) B1863013
theorem B1656627 : Blo 1655527 1656627 := bstep (se 1 (by rfl) ⟨1242470, by rfl⟩ : syracuseStep 1656627 = 2484941) B2484941
theorem B2484035 : Blo 1655527 2484035 := bstep (se 1 (by rfl) ⟨1863026, by rfl⟩ : syracuseStep 2484035 = 3726053) B3726053
theorem B1656643 : Blo 1655527 1656643 := bstep (se 1 (by rfl) ⟨1242482, by rfl⟩ : syracuseStep 1656643 = 2484965) B2484965
theorem B4032337 : Blo 1655527 4032337 := bstep (se 2 (by rfl) ⟨1512126, by rfl⟩ : syracuseStep 4032337 = 3024253) B3024253
theorem B1656659 : Blo 1655527 1656659 := bstep (se 1 (by rfl) ⟨1242494, by rfl⟩ : syracuseStep 1656659 = 2484989) B2484989
theorem B2484065 : Blo 1655527 2484065 := bstep (se 2 (by rfl) ⟨931524, by rfl⟩ : syracuseStep 2484065 = 1863049) B1863049
theorem B1656675 : Blo 1655527 1656675 := bstep (se 1 (by rfl) ⟨1242506, by rfl⟩ : syracuseStep 1656675 = 2485013) B2485013
theorem B2795377 : Blo 1655527 2795377 := bstep (se 2 (by rfl) ⟨1048266, by rfl⟩ : syracuseStep 2795377 = 2096533) B2096533
theorem B2484083 : Blo 1655527 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B1656691 : Blo 1655527 1656691 := bstep (se 1 (by rfl) ⟨1242518, by rfl⟩ : syracuseStep 1656691 = 2485037) B2485037
theorem B1656707 : Blo 1655527 1656707 := bstep (se 1 (by rfl) ⟨1242530, by rfl⟩ : syracuseStep 1656707 = 2485061) B2485061
theorem B2484113 : Blo 1655527 2484113 := bstep (se 2 (by rfl) ⟨931542, by rfl⟩ : syracuseStep 2484113 = 1863085) B1863085
theorem B2795411 : Blo 1655527 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B1656723 : Blo 1655527 1656723 := bstep (se 1 (by rfl) ⟨1242542, by rfl⟩ : syracuseStep 1656723 = 2485085) B2485085
theorem B2484131 : Blo 1655527 2484131 := bstep (se 1 (by rfl) ⟨1863098, by rfl⟩ : syracuseStep 2484131 = 3726197) B3726197
theorem B1656739 : Blo 1655527 1656739 := bstep (se 1 (by rfl) ⟨1242554, by rfl⟩ : syracuseStep 1656739 = 2485109) B2485109
theorem B3729329 : Blo 1655527 3729329 := bstep (se 2 (by rfl) ⟨1398498, by rfl⟩ : syracuseStep 3729329 = 2796997) B2796997
theorem B1656755 : Blo 1655527 1656755 := bstep (se 1 (by rfl) ⟨1242566, by rfl⟩ : syracuseStep 1656755 = 2485133) B2485133
theorem B2484161 : Blo 1655527 2484161 := bstep (se 2 (by rfl) ⟨931560, by rfl⟩ : syracuseStep 2484161 = 1863121) B1863121
theorem B1656771 : Blo 1655527 1656771 := bstep (se 1 (by rfl) ⟨1242578, by rfl⟩ : syracuseStep 1656771 = 2485157) B2485157
theorem B3729347 : Blo 1655527 3729347 := bstep (se 1 (by rfl) ⟨2797010, by rfl⟩ : syracuseStep 3729347 = 5594021) B5594021
theorem B5588945 : Blo 1655527 5588945 := bstep (se 2 (by rfl) ⟨2095854, by rfl⟩ : syracuseStep 5588945 = 4191709) B4191709
theorem B2484179 : Blo 1655527 2484179 := bstep (se 1 (by rfl) ⟨1863134, by rfl⟩ : syracuseStep 2484179 = 3726269) B3726269
theorem B1656787 : Blo 1655527 1656787 := bstep (se 1 (by rfl) ⟨1242590, by rfl⟩ : syracuseStep 1656787 = 2485181) B2485181
theorem B1656803 : Blo 1655527 1656803 := bstep (se 1 (by rfl) ⟨1242602, by rfl⟩ : syracuseStep 1656803 = 2485205) B2485205
theorem B8390627 : Blo 1655527 8390627 := bstep (se 1 (by rfl) ⟨6292970, by rfl⟩ : syracuseStep 8390627 = 12585941) B12585941
theorem B2484209 : Blo 1655527 2484209 := bstep (se 2 (by rfl) ⟨931578, by rfl⟩ : syracuseStep 2484209 = 1863157) B1863157
theorem B1656819 : Blo 1655527 1656819 := bstep (se 1 (by rfl) ⟨1242614, by rfl⟩ : syracuseStep 1656819 = 2485229) B2485229
theorem B2484227 : Blo 1655527 2484227 := bstep (se 1 (by rfl) ⟨1863170, by rfl⟩ : syracuseStep 2484227 = 3726341) B3726341
theorem B1656835 : Blo 1655527 1656835 := bstep (se 1 (by rfl) ⟨1242626, by rfl⟩ : syracuseStep 1656835 = 2485253) B2485253
theorem B2795539 : Blo 1655527 2795539 := bstep (se 1 (by rfl) ⟨2096654, by rfl⟩ : syracuseStep 2795539 = 4193309) B4193309
theorem B1656851 : Blo 1655527 1656851 := bstep (se 1 (by rfl) ⟨1242638, by rfl⟩ : syracuseStep 1656851 = 2485277) B2485277
theorem B45344789 : Blo 1655527 45344789 := bstep (se 6 (by rfl) ⟨1062768, by rfl⟩ : syracuseStep 45344789 = 2125537) B2125537
theorem B2484257 : Blo 1655527 2484257 := bstep (se 2 (by rfl) ⟨931596, by rfl⟩ : syracuseStep 2484257 = 1863193) B1863193
theorem B1656867 : Blo 1655527 1656867 := bstep (se 1 (by rfl) ⟨1242650, by rfl⟩ : syracuseStep 1656867 = 2485301) B2485301
theorem B2484275 : Blo 1655527 2484275 := bstep (se 1 (by rfl) ⟨1863206, by rfl⟩ : syracuseStep 2484275 = 3726413) B3726413
theorem B1656883 : Blo 1655527 1656883 := bstep (se 1 (by rfl) ⟨1242662, by rfl⟩ : syracuseStep 1656883 = 2485325) B2485325
theorem B1656899 : Blo 1655527 1656899 := bstep (se 1 (by rfl) ⟨1242674, by rfl⟩ : syracuseStep 1656899 = 2485349) B2485349
theorem B2484305 : Blo 1655527 2484305 := bstep (se 2 (by rfl) ⟨931614, by rfl⟩ : syracuseStep 2484305 = 1863229) B1863229
theorem B1656915 : Blo 1655527 1656915 := bstep (se 1 (by rfl) ⟨1242686, by rfl⟩ : syracuseStep 1656915 = 2485373) B2485373
theorem B2484323 : Blo 1655527 2484323 := bstep (se 1 (by rfl) ⟨1863242, by rfl⟩ : syracuseStep 2484323 = 3726485) B3726485
theorem B1656931 : Blo 1655527 1656931 := bstep (se 1 (by rfl) ⟨1242698, by rfl⟩ : syracuseStep 1656931 = 2485397) B2485397
theorem B1656947 : Blo 1655527 1656947 := bstep (se 1 (by rfl) ⟨1242710, by rfl⟩ : syracuseStep 1656947 = 2485421) B2485421
theorem B2484353 : Blo 1655527 2484353 := bstep (se 2 (by rfl) ⟨931632, by rfl⟩ : syracuseStep 2484353 = 1863265) B1863265
theorem B1656963 : Blo 1655527 1656963 := bstep (se 1 (by rfl) ⟨1242722, by rfl⟩ : syracuseStep 1656963 = 2485445) B2485445
theorem B2484371 : Blo 1655527 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B1656979 : Blo 1655527 1656979 := bstep (se 1 (by rfl) ⟨1242734, by rfl⟩ : syracuseStep 1656979 = 2485469) B2485469
theorem B2795681 : Blo 1655527 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B1656995 : Blo 1655527 1656995 := bstep (se 1 (by rfl) ⟨1242746, by rfl⟩ : syracuseStep 1656995 = 2485493) B2485493
theorem B2484401 : Blo 1655527 2484401 := bstep (se 2 (by rfl) ⟨931650, by rfl⟩ : syracuseStep 2484401 = 1863301) B1863301
theorem B7964849 : Blo 1655527 7964849 := bstep (se 2 (by rfl) ⟨2986818, by rfl⟩ : syracuseStep 7964849 = 5973637) B5973637
theorem B1657011 : Blo 1655527 1657011 := bstep (se 1 (by rfl) ⟨1242758, by rfl⟩ : syracuseStep 1657011 = 2485517) B2485517
theorem B2484419 : Blo 1655527 2484419 := bstep (se 1 (by rfl) ⟨1863314, by rfl⟩ : syracuseStep 2484419 = 3726629) B3726629
theorem B1657027 : Blo 1655527 1657027 := bstep (se 1 (by rfl) ⟨1242770, by rfl⟩ : syracuseStep 1657027 = 2485541) B2485541
theorem B1657043 : Blo 1655527 1657043 := bstep (se 1 (by rfl) ⟨1242782, by rfl⟩ : syracuseStep 1657043 = 2485565) B2485565
theorem B2484449 : Blo 1655527 2484449 := bstep (se 2 (by rfl) ⟨931668, by rfl⟩ : syracuseStep 2484449 = 1863337) B1863337
theorem B1657059 : Blo 1655527 1657059 := bstep (se 1 (by rfl) ⟨1242794, by rfl⟩ : syracuseStep 1657059 = 2485589) B2485589
theorem B2484467 : Blo 1655527 2484467 := bstep (se 1 (by rfl) ⟨1863350, by rfl⟩ : syracuseStep 2484467 = 3726701) B3726701
theorem B1657075 : Blo 1655527 1657075 := bstep (se 1 (by rfl) ⟨1242806, by rfl⟩ : syracuseStep 1657075 = 2485613) B2485613
theorem B1657091 : Blo 1655527 1657091 := bstep (se 1 (by rfl) ⟨1242818, by rfl⟩ : syracuseStep 1657091 = 2485637) B2485637
theorem B2484497 : Blo 1655527 2484497 := bstep (se 2 (by rfl) ⟨931686, by rfl⟩ : syracuseStep 2484497 = 1863373) B1863373
theorem B1657107 : Blo 1655527 1657107 := bstep (se 1 (by rfl) ⟨1242830, by rfl⟩ : syracuseStep 1657107 = 2485661) B2485661
theorem B2795809 : Blo 1655527 2795809 := bstep (se 2 (by rfl) ⟨1048428, by rfl⟩ : syracuseStep 2795809 = 2096857) B2096857
theorem B2484515 : Blo 1655527 2484515 := bstep (se 1 (by rfl) ⟨1863386, by rfl⟩ : syracuseStep 2484515 = 3726773) B3726773
theorem B1657123 : Blo 1655527 1657123 := bstep (se 1 (by rfl) ⟨1242842, by rfl⟩ : syracuseStep 1657123 = 2485685) B2485685
theorem B2238769 : Blo 1655527 2238769 := bstep (se 2 (by rfl) ⟨839538, by rfl⟩ : syracuseStep 2238769 = 1679077) B1679077
theorem B1657139 : Blo 1655527 1657139 := bstep (se 1 (by rfl) ⟨1242854, by rfl⟩ : syracuseStep 1657139 = 2485709) B2485709
theorem B18876725 : Blo 1655527 18876725 := bstep (se 5 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 18876725 = 1769693) B1769693
theorem B2484545 : Blo 1655527 2484545 := bstep (se 2 (by rfl) ⟨931704, by rfl⟩ : syracuseStep 2484545 = 1863409) B1863409
theorem B2795843 : Blo 1655527 2795843 := bstep (se 1 (by rfl) ⟨2096882, by rfl⟩ : syracuseStep 2795843 = 4193765) B4193765
theorem B1657155 : Blo 1655527 1657155 := bstep (se 1 (by rfl) ⟨1242866, by rfl⟩ : syracuseStep 1657155 = 2485733) B2485733
theorem B4475213 : Blo 1655527 4475213 := bstep (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) B1678205
theorem B2484563 : Blo 1655527 2484563 := bstep (se 1 (by rfl) ⟨1863422, by rfl⟩ : syracuseStep 2484563 = 3726845) B3726845
theorem B1657171 : Blo 1655527 1657171 := bstep (se 1 (by rfl) ⟨1242878, by rfl⟩ : syracuseStep 1657171 = 2485757) B2485757
theorem B1657187 : Blo 1655527 1657187 := bstep (se 1 (by rfl) ⟨1242890, by rfl⟩ : syracuseStep 1657187 = 2485781) B2485781
theorem B2484593 : Blo 1655527 2484593 := bstep (se 2 (by rfl) ⟨931722, by rfl⟩ : syracuseStep 2484593 = 1863445) B1863445
theorem B1657203 : Blo 1655527 1657203 := bstep (se 1 (by rfl) ⟨1242902, by rfl⟩ : syracuseStep 1657203 = 2485805) B2485805
theorem B2484611 : Blo 1655527 2484611 := bstep (se 1 (by rfl) ⟨1863458, by rfl⟩ : syracuseStep 2484611 = 3726917) B3726917
theorem B1657219 : Blo 1655527 1657219 := bstep (se 1 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 1657219 = 2485829) B2485829
theorem B9431437 : Blo 1655527 9431437 := bstep (se 3 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 9431437 = 3536789) B3536789
theorem B1657235 : Blo 1655527 1657235 := bstep (se 1 (by rfl) ⟨1242926, by rfl⟩ : syracuseStep 1657235 = 2485853) B2485853
theorem B2484641 : Blo 1655527 2484641 := bstep (se 2 (by rfl) ⟨931740, by rfl⟩ : syracuseStep 2484641 = 1863481) B1863481
theorem B1657251 : Blo 1655527 1657251 := bstep (se 1 (by rfl) ⟨1242938, by rfl⟩ : syracuseStep 1657251 = 2485877) B2485877
theorem B2484659 : Blo 1655527 2484659 := bstep (se 1 (by rfl) ⟨1863494, by rfl⟩ : syracuseStep 2484659 = 3726989) B3726989
theorem B1657267 : Blo 1655527 1657267 := bstep (se 1 (by rfl) ⟨1242950, by rfl⟩ : syracuseStep 1657267 = 2485901) B2485901
theorem B2795971 : Blo 1655527 2795971 := bstep (se 1 (by rfl) ⟨2096978, by rfl⟩ : syracuseStep 2795971 = 4193957) B4193957
theorem B1657283 : Blo 1655527 1657283 := bstep (se 1 (by rfl) ⟨1242962, by rfl⟩ : syracuseStep 1657283 = 2485925) B2485925
theorem B9439685 : Blo 1655527 9439685 := bstep (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) B1769941
theorem B2484689 : Blo 1655527 2484689 := bstep (se 2 (by rfl) ⟨931758, by rfl⟩ : syracuseStep 2484689 = 1863517) B1863517
theorem B1657299 : Blo 1655527 1657299 := bstep (se 1 (by rfl) ⟨1242974, by rfl⟩ : syracuseStep 1657299 = 2485949) B2485949
theorem B2484707 : Blo 1655527 2484707 := bstep (se 1 (by rfl) ⟨1863530, by rfl⟩ : syracuseStep 2484707 = 3727061) B3727061
theorem B1657315 : Blo 1655527 1657315 := bstep (se 1 (by rfl) ⟨1242986, by rfl⟩ : syracuseStep 1657315 = 2485973) B2485973
theorem B5589485 : Blo 1655527 5589485 := bstep (se 3 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 5589485 = 2096057) B2096057
theorem B1657331 : Blo 1655527 1657331 := bstep (se 1 (by rfl) ⟨1242998, by rfl⟩ : syracuseStep 1657331 = 2485997) B2485997
theorem B2484737 : Blo 1655527 2484737 := bstep (se 2 (by rfl) ⟨931776, by rfl⟩ : syracuseStep 2484737 = 1863553) B1863553
theorem B1657347 : Blo 1655527 1657347 := bstep (se 1 (by rfl) ⟨1243010, by rfl⟩ : syracuseStep 1657347 = 2486021) B2486021
theorem B2484755 : Blo 1655527 2484755 := bstep (se 1 (by rfl) ⟨1863566, by rfl⟩ : syracuseStep 2484755 = 3727133) B3727133
theorem B1657363 : Blo 1655527 1657363 := bstep (se 1 (by rfl) ⟨1243022, by rfl⟩ : syracuseStep 1657363 = 2486045) B2486045
theorem B5589539 : Blo 1655527 5589539 := bstep (se 1 (by rfl) ⟨4192154, by rfl⟩ : syracuseStep 5589539 = 8384309) B8384309
theorem B1657379 : Blo 1655527 1657379 := bstep (se 1 (by rfl) ⟨1243034, by rfl⟩ : syracuseStep 1657379 = 2486069) B2486069
theorem B2484785 : Blo 1655527 2484785 := bstep (se 2 (by rfl) ⟨931794, by rfl⟩ : syracuseStep 2484785 = 1863589) B1863589
theorem B1657395 : Blo 1655527 1657395 := bstep (se 1 (by rfl) ⟨1243046, by rfl⟩ : syracuseStep 1657395 = 2486093) B2486093
theorem B2484803 : Blo 1655527 2484803 := bstep (se 1 (by rfl) ⟨1863602, by rfl⟩ : syracuseStep 2484803 = 3727205) B3727205
theorem B1657411 : Blo 1655527 1657411 := bstep (se 1 (by rfl) ⟨1243058, by rfl⟩ : syracuseStep 1657411 = 2486117) B2486117
theorem B2796113 : Blo 1655527 2796113 := bstep (se 2 (by rfl) ⟨1048542, by rfl⟩ : syracuseStep 2796113 = 2097085) B2097085
theorem B1657427 : Blo 1655527 1657427 := bstep (se 1 (by rfl) ⟨1243070, by rfl⟩ : syracuseStep 1657427 = 2486141) B2486141
theorem B2484833 : Blo 1655527 2484833 := bstep (se 2 (by rfl) ⟨931812, by rfl⟩ : syracuseStep 2484833 = 1863625) B1863625
theorem B1657443 : Blo 1655527 1657443 := bstep (se 1 (by rfl) ⟨1243082, by rfl⟩ : syracuseStep 1657443 = 2486165) B2486165
theorem B2484851 : Blo 1655527 2484851 := bstep (se 1 (by rfl) ⟨1863638, by rfl⟩ : syracuseStep 2484851 = 3727277) B3727277
theorem B1657459 : Blo 1655527 1657459 := bstep (se 1 (by rfl) ⟨1243094, by rfl⟩ : syracuseStep 1657459 = 2486189) B2486189
theorem B1657475 : Blo 1655527 1657475 := bstep (se 1 (by rfl) ⟨1243106, by rfl⟩ : syracuseStep 1657475 = 2486213) B2486213
theorem B2484881 : Blo 1655527 2484881 := bstep (se 2 (by rfl) ⟨931830, by rfl⟩ : syracuseStep 2484881 = 1863661) B1863661
theorem B1657491 : Blo 1655527 1657491 := bstep (se 1 (by rfl) ⟨1243118, by rfl⟩ : syracuseStep 1657491 = 2486237) B2486237
theorem B2484899 : Blo 1655527 2484899 := bstep (se 1 (by rfl) ⟨1863674, by rfl⟩ : syracuseStep 2484899 = 3727349) B3727349
theorem B1657507 : Blo 1655527 1657507 := bstep (se 1 (by rfl) ⟨1243130, by rfl⟩ : syracuseStep 1657507 = 2486261) B2486261
theorem B5106349 : Blo 1655527 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1657523 : Blo 1655527 1657523 := bstep (se 1 (by rfl) ⟨1243142, by rfl⟩ : syracuseStep 1657523 = 2486285) B2486285
theorem B2484929 : Blo 1655527 2484929 := bstep (se 2 (by rfl) ⟨931848, by rfl⟩ : syracuseStep 2484929 = 1863697) B1863697
theorem B2796241 : Blo 1655527 2796241 := bstep (se 2 (by rfl) ⟨1048590, by rfl⟩ : syracuseStep 2796241 = 2097181) B2097181
theorem B2484947 : Blo 1655527 2484947 := bstep (se 1 (by rfl) ⟨1863710, by rfl⟩ : syracuseStep 2484947 = 3727421) B3727421
theorem B14338787 : Blo 1655527 14338787 := bstep (se 1 (by rfl) ⟨10754090, by rfl⟩ : syracuseStep 14338787 = 21508181) B21508181
theorem B2484977 : Blo 1655527 2484977 := bstep (se 2 (by rfl) ⟨931866, by rfl⟩ : syracuseStep 2484977 = 1863733) B1863733
theorem B2796275 : Blo 1655527 2796275 := bstep (se 1 (by rfl) ⟨2097206, by rfl⟩ : syracuseStep 2796275 = 4194413) B4194413
theorem B2484995 : Blo 1655527 2484995 := bstep (se 1 (by rfl) ⟨1863746, by rfl⟩ : syracuseStep 2484995 = 3727493) B3727493
theorem B5745421 : Blo 1655527 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B2485025 : Blo 1655527 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B5589809 : Blo 1655527 5589809 := bstep (se 2 (by rfl) ⟨2096178, by rfl⟩ : syracuseStep 5589809 = 4192357) B4192357
theorem B2485043 : Blo 1655527 2485043 := bstep (se 1 (by rfl) ⟨1863782, by rfl⟩ : syracuseStep 2485043 = 3727565) B3727565
theorem B2485073 : Blo 1655527 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B2485091 : Blo 1655527 2485091 := bstep (se 1 (by rfl) ⟨1863818, by rfl⟩ : syracuseStep 2485091 = 3727637) B3727637
theorem B15928163 : Blo 1655527 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B2796403 : Blo 1655527 2796403 := bstep (se 1 (by rfl) ⟨2097302, by rfl⟩ : syracuseStep 2796403 = 4194605) B4194605
theorem B2485121 : Blo 1655527 2485121 := bstep (se 2 (by rfl) ⟨931920, by rfl⟩ : syracuseStep 2485121 = 1863841) B1863841
theorem B2485139 : Blo 1655527 2485139 := bstep (se 1 (by rfl) ⟨1863854, by rfl⟩ : syracuseStep 2485139 = 3727709) B3727709
theorem B1862563 : Blo 1655527 1862563 := bstep (se 1 (by rfl) ⟨1396922, by rfl⟩ : syracuseStep 1862563 = 2793845) B2793845
theorem B2485169 : Blo 1655527 2485169 := bstep (se 2 (by rfl) ⟨931938, by rfl⟩ : syracuseStep 2485169 = 1863877) B1863877
theorem B2485187 : Blo 1655527 2485187 := bstep (se 1 (by rfl) ⟨1863890, by rfl⟩ : syracuseStep 2485187 = 3727781) B3727781
theorem B2485217 : Blo 1655527 2485217 := bstep (se 2 (by rfl) ⟨931956, by rfl⟩ : syracuseStep 2485217 = 1863913) B1863913
theorem B2485235 : Blo 1655527 2485235 := bstep (se 1 (by rfl) ⟨1863926, by rfl⟩ : syracuseStep 2485235 = 3727853) B3727853
theorem B2796545 : Blo 1655527 2796545 := bstep (se 2 (by rfl) ⟨1048704, by rfl⟩ : syracuseStep 2796545 = 2097409) B2097409
theorem B6286349 : Blo 1655527 6286349 := bstep (se 3 (by rfl) ⟨1178690, by rfl⟩ : syracuseStep 6286349 = 2357381) B2357381
theorem B2485265 : Blo 1655527 2485265 := bstep (se 2 (by rfl) ⟨931974, by rfl⟩ : syracuseStep 2485265 = 1863949) B1863949
theorem B2485283 : Blo 1655527 2485283 := bstep (se 1 (by rfl) ⟨1863962, by rfl⟩ : syracuseStep 2485283 = 3727925) B3727925
theorem B1862707 : Blo 1655527 1862707 := bstep (se 1 (by rfl) ⟨1397030, by rfl⟩ : syracuseStep 1862707 = 2794061) B2794061
theorem B2485313 : Blo 1655527 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B4475981 : Blo 1655527 4475981 := bstep (se 3 (by rfl) ⟨839246, by rfl⟩ : syracuseStep 4475981 = 1678493) B1678493
theorem B10619981 : Blo 1655527 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B2485331 : Blo 1655527 2485331 := bstep (se 1 (by rfl) ⟨1863998, by rfl⟩ : syracuseStep 2485331 = 3727997) B3727997
theorem B2485361 : Blo 1655527 2485361 := bstep (se 2 (by rfl) ⟨932010, by rfl⟩ : syracuseStep 2485361 = 1864021) B1864021
theorem B2796673 : Blo 1655527 2796673 := bstep (se 2 (by rfl) ⟨1048752, by rfl⟩ : syracuseStep 2796673 = 2097505) B2097505
theorem B2485379 : Blo 1655527 2485379 := bstep (se 1 (by rfl) ⟨1864034, by rfl⟩ : syracuseStep 2485379 = 3728069) B3728069
theorem B12102797 : Blo 1655527 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B2485409 : Blo 1655527 2485409 := bstep (se 2 (by rfl) ⟨932028, by rfl⟩ : syracuseStep 2485409 = 1864057) B1864057
theorem B2796707 : Blo 1655527 2796707 := bstep (se 1 (by rfl) ⟨2097530, by rfl⟩ : syracuseStep 2796707 = 4195061) B4195061
theorem B4476077 : Blo 1655527 4476077 := bstep (se 3 (by rfl) ⟨839264, by rfl⟩ : syracuseStep 4476077 = 1678529) B1678529
theorem B2485427 : Blo 1655527 2485427 := bstep (se 1 (by rfl) ⟨1864070, by rfl⟩ : syracuseStep 2485427 = 3728141) B3728141
theorem B1862851 : Blo 1655527 1862851 := bstep (se 1 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 1862851 = 2794277) B2794277
theorem B5967053 : Blo 1655527 5967053 := bstep (se 3 (by rfl) ⟨1118822, by rfl⟩ : syracuseStep 5967053 = 2237645) B2237645
theorem B2485457 : Blo 1655527 2485457 := bstep (se 2 (by rfl) ⟨932046, by rfl⟩ : syracuseStep 2485457 = 1864093) B1864093
theorem B2485475 : Blo 1655527 2485475 := bstep (se 1 (by rfl) ⟨1864106, by rfl⟩ : syracuseStep 2485475 = 3728213) B3728213
theorem B2485505 : Blo 1655527 2485505 := bstep (se 2 (by rfl) ⟨932064, by rfl⟩ : syracuseStep 2485505 = 1864129) B1864129
theorem B4476163 : Blo 1655527 4476163 := bstep (se 1 (by rfl) ⟨3357122, by rfl⟩ : syracuseStep 4476163 = 6714245) B6714245
theorem B2485523 : Blo 1655527 2485523 := bstep (se 1 (by rfl) ⟨1864142, by rfl⟩ : syracuseStep 2485523 = 3728285) B3728285
theorem B2796835 : Blo 1655527 2796835 := bstep (se 1 (by rfl) ⟨2097626, by rfl⟩ : syracuseStep 2796835 = 4195253) B4195253
theorem B8064305 : Blo 1655527 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B2485553 : Blo 1655527 2485553 := bstep (se 2 (by rfl) ⟨932082, by rfl⟩ : syracuseStep 2485553 = 1864165) B1864165
theorem B2485571 : Blo 1655527 2485571 := bstep (se 1 (by rfl) ⟨1864178, by rfl⟩ : syracuseStep 2485571 = 3728357) B3728357
theorem B5590349 : Blo 1655527 5590349 := bstep (se 3 (by rfl) ⟨1048190, by rfl⟩ : syracuseStep 5590349 = 2096381) B2096381
theorem B1862995 : Blo 1655527 1862995 := bstep (se 1 (by rfl) ⟨1397246, by rfl⟩ : syracuseStep 1862995 = 2794493) B2794493
theorem B2485601 : Blo 1655527 2485601 := bstep (se 2 (by rfl) ⟨932100, by rfl⟩ : syracuseStep 2485601 = 1864201) B1864201
theorem B2485619 : Blo 1655527 2485619 := bstep (se 1 (by rfl) ⟨1864214, by rfl⟩ : syracuseStep 2485619 = 3728429) B3728429
theorem B5590403 : Blo 1655527 5590403 := bstep (se 1 (by rfl) ⟨4192802, by rfl⟩ : syracuseStep 5590403 = 8385605) B8385605
theorem B2485649 : Blo 1655527 2485649 := bstep (se 2 (by rfl) ⟨932118, by rfl⟩ : syracuseStep 2485649 = 1864237) B1864237
theorem B11333027 : Blo 1655527 11333027 := bstep (se 1 (by rfl) ⟨8499770, by rfl⟩ : syracuseStep 11333027 = 16999541) B16999541
theorem B2485667 : Blo 1655527 2485667 := bstep (se 1 (by rfl) ⟨1864250, by rfl⟩ : syracuseStep 2485667 = 3728501) B3728501
theorem B2796977 : Blo 1655527 2796977 := bstep (se 2 (by rfl) ⟨1048866, by rfl⟩ : syracuseStep 2796977 = 2097733) B2097733
theorem B2485697 : Blo 1655527 2485697 := bstep (se 2 (by rfl) ⟨932136, by rfl⟩ : syracuseStep 2485697 = 1864273) B1864273
theorem B2485715 : Blo 1655527 2485715 := bstep (se 1 (by rfl) ⟨1864286, by rfl⟩ : syracuseStep 2485715 = 3728573) B3728573
theorem B1863139 : Blo 1655527 1863139 := bstep (se 1 (by rfl) ⟨1397354, by rfl⟩ : syracuseStep 1863139 = 2794709) B2794709
theorem B8383985 : Blo 1655527 8383985 := bstep (se 2 (by rfl) ⟨3143994, by rfl⟩ : syracuseStep 8383985 = 6287989) B6287989
theorem B2485745 : Blo 1655527 2485745 := bstep (se 2 (by rfl) ⟨932154, by rfl⟩ : syracuseStep 2485745 = 1864309) B1864309
theorem B2485763 : Blo 1655527 2485763 := bstep (se 1 (by rfl) ⟨1864322, by rfl⟩ : syracuseStep 2485763 = 3728645) B3728645
theorem B2485793 : Blo 1655527 2485793 := bstep (se 2 (by rfl) ⟨932172, by rfl⟩ : syracuseStep 2485793 = 1864345) B1864345
theorem B2485811 : Blo 1655527 2485811 := bstep (se 1 (by rfl) ⟨1864358, by rfl⟩ : syracuseStep 2485811 = 3728717) B3728717
theorem B2485841 : Blo 1655527 2485841 := bstep (se 2 (by rfl) ⟨932190, by rfl⟩ : syracuseStep 2485841 = 1864381) B1864381
theorem B2485859 : Blo 1655527 2485859 := bstep (se 1 (by rfl) ⟨1864394, by rfl⟩ : syracuseStep 2485859 = 3728789) B3728789
theorem B1863283 : Blo 1655527 1863283 := bstep (se 1 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 1863283 = 2794925) B2794925
theorem B2485889 : Blo 1655527 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B5590673 : Blo 1655527 5590673 := bstep (se 2 (by rfl) ⟨2096502, by rfl⟩ : syracuseStep 5590673 = 4193005) B4193005
theorem B2485907 : Blo 1655527 2485907 := bstep (se 1 (by rfl) ⟨1864430, by rfl⟩ : syracuseStep 2485907 = 3728861) B3728861
theorem B8957603 : Blo 1655527 8957603 := bstep (se 1 (by rfl) ⟨6718202, by rfl⟩ : syracuseStep 8957603 = 13436405) B13436405
theorem B5303981 : Blo 1655527 5303981 := bstep (se 3 (by rfl) ⟨994496, by rfl⟩ : syracuseStep 5303981 = 1988993) B1988993
theorem B2485937 : Blo 1655527 2485937 := bstep (se 2 (by rfl) ⟨932226, by rfl⟩ : syracuseStep 2485937 = 1864453) B1864453
theorem B2485955 : Blo 1655527 2485955 := bstep (se 1 (by rfl) ⟨1864466, by rfl⟩ : syracuseStep 2485955 = 3728933) B3728933
theorem B2485985 : Blo 1655527 2485985 := bstep (se 2 (by rfl) ⟨932244, by rfl⟩ : syracuseStep 2485985 = 1864489) B1864489
theorem B2486003 : Blo 1655527 2486003 := bstep (se 1 (by rfl) ⟨1864502, by rfl⟩ : syracuseStep 2486003 = 3729005) B3729005
theorem B1863427 : Blo 1655527 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B2486033 : Blo 1655527 2486033 := bstep (se 2 (by rfl) ⟨932262, by rfl⟩ : syracuseStep 2486033 = 1864525) B1864525
theorem B11333411 : Blo 1655527 11333411 := bstep (se 1 (by rfl) ⟨8500058, by rfl⟩ : syracuseStep 11333411 = 17000117) B17000117
theorem B2486051 : Blo 1655527 2486051 := bstep (se 1 (by rfl) ⟨1864538, by rfl⟩ : syracuseStep 2486051 = 3729077) B3729077
theorem B2486081 : Blo 1655527 2486081 := bstep (se 2 (by rfl) ⟨932280, by rfl⟩ : syracuseStep 2486081 = 1864561) B1864561
theorem B2486099 : Blo 1655527 2486099 := bstep (se 1 (by rfl) ⟨1864574, by rfl⟩ : syracuseStep 2486099 = 3729149) B3729149
theorem B6811505 : Blo 1655527 6811505 := bstep (se 2 (by rfl) ⟨2554314, by rfl⟩ : syracuseStep 6811505 = 5108629) B5108629
theorem B2486129 : Blo 1655527 2486129 := bstep (se 2 (by rfl) ⟨932298, by rfl⟩ : syracuseStep 2486129 = 1864597) B1864597
theorem B2486147 : Blo 1655527 2486147 := bstep (se 1 (by rfl) ⟨1864610, by rfl⟩ : syracuseStep 2486147 = 3729221) B3729221
theorem B1863571 : Blo 1655527 1863571 := bstep (se 1 (by rfl) ⟨1397678, by rfl⟩ : syracuseStep 1863571 = 2795357) B2795357
theorem B2486177 : Blo 1655527 2486177 := bstep (se 2 (by rfl) ⟨932316, by rfl⟩ : syracuseStep 2486177 = 1864633) B1864633
theorem B2486195 : Blo 1655527 2486195 := bstep (se 1 (by rfl) ⟨1864646, by rfl⟩ : syracuseStep 2486195 = 3729293) B3729293
theorem B2486225 : Blo 1655527 2486225 := bstep (se 2 (by rfl) ⟨932334, by rfl⟩ : syracuseStep 2486225 = 1864669) B1864669
theorem B2486243 : Blo 1655527 2486243 := bstep (se 1 (by rfl) ⟨1864682, by rfl⟩ : syracuseStep 2486243 = 3729365) B3729365
theorem B2486273 : Blo 1655527 2486273 := bstep (se 2 (by rfl) ⟨932352, by rfl⟩ : syracuseStep 2486273 = 1864705) B1864705
theorem B2486291 : Blo 1655527 2486291 := bstep (se 1 (by rfl) ⟨1864718, by rfl⟩ : syracuseStep 2486291 = 3729437) B3729437
theorem B1863715 : Blo 1655527 1863715 := bstep (se 1 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 1863715 = 2795573) B2795573
theorem B5591213 : Blo 1655527 5591213 := bstep (se 3 (by rfl) ⟨1048352, by rfl⟩ : syracuseStep 5591213 = 2096705) B2096705
theorem B1863859 : Blo 1655527 1863859 := bstep (se 1 (by rfl) ⟨1397894, by rfl⟩ : syracuseStep 1863859 = 2795789) B2795789
theorem B5591267 : Blo 1655527 5591267 := bstep (se 1 (by rfl) ⟨4193450, by rfl⟩ : syracuseStep 5591267 = 8386901) B8386901
theorem B1864003 : Blo 1655527 1864003 := bstep (se 1 (by rfl) ⟨1398002, by rfl⟩ : syracuseStep 1864003 = 2796005) B2796005
theorem B5968205 : Blo 1655527 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B7074125 : Blo 1655527 7074125 := bstep (se 3 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 7074125 = 2652797) B2652797
theorem B9433421 : Blo 1655527 9433421 := bstep (se 3 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 9433421 = 3537533) B3537533
theorem B7074161 : Blo 1655527 7074161 := bstep (se 2 (by rfl) ⟨2652810, by rfl⟩ : syracuseStep 7074161 = 5305621) B5305621
theorem B1864147 : Blo 1655527 1864147 := bstep (se 1 (by rfl) ⟨1398110, by rfl⟩ : syracuseStep 1864147 = 2796221) B2796221
theorem B5591537 : Blo 1655527 5591537 := bstep (se 2 (by rfl) ⟨2096826, by rfl⟩ : syracuseStep 5591537 = 4193653) B4193653
theorem B4190737 : Blo 1655527 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B1864291 : Blo 1655527 1864291 := bstep (se 1 (by rfl) ⟨1398218, by rfl⟩ : syracuseStep 1864291 = 2796437) B2796437
theorem B5665393 : Blo 1655527 5665393 := bstep (se 2 (by rfl) ⟨2124522, by rfl⟩ : syracuseStep 5665393 = 4249045) B4249045
theorem B43037381 : Blo 1655527 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B1864435 : Blo 1655527 1864435 := bstep (se 1 (by rfl) ⟨1398326, by rfl⟩ : syracuseStep 1864435 = 2796653) B2796653
theorem B4191011 : Blo 1655527 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B5665571 : Blo 1655527 5665571 := bstep (se 1 (by rfl) ⟨4249178, by rfl⟩ : syracuseStep 5665571 = 8498357) B8498357
theorem B4715309 : Blo 1655527 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1864579 : Blo 1655527 1864579 := bstep (se 1 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 1864579 = 2796869) B2796869
theorem B8385443 : Blo 1655527 8385443 := bstep (se 1 (by rfl) ⟨6289082, by rfl⟩ : syracuseStep 8385443 = 12578165) B12578165
theorem B3535825 : Blo 1655527 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B4191203 : Blo 1655527 4191203 := bstep (se 1 (by rfl) ⟨3143402, by rfl⟩ : syracuseStep 4191203 = 6286805) B6286805
theorem B4715491 : Blo 1655527 4715491 := bstep (se 1 (by rfl) ⟨3536618, by rfl⟩ : syracuseStep 4715491 = 7073237) B7073237
theorem B8950769 : Blo 1655527 8950769 := bstep (se 2 (by rfl) ⟨3356538, by rfl⟩ : syracuseStep 8950769 = 6713077) B6713077
theorem B5592077 : Blo 1655527 5592077 := bstep (se 3 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 5592077 = 2097029) B2097029
theorem B5592131 : Blo 1655527 5592131 := bstep (se 1 (by rfl) ⟨4194098, by rfl⟩ : syracuseStep 5592131 = 8388197) B8388197
theorem B6288461 : Blo 1655527 6288461 := bstep (se 3 (by rfl) ⟨1179086, by rfl⟩ : syracuseStep 6288461 = 2358173) B2358173
theorem B4715651 : Blo 1655527 4715651 := bstep (se 1 (by rfl) ⟨3536738, by rfl⟩ : syracuseStep 4715651 = 7073477) B7073477
theorem B10073315 : Blo 1655527 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B9434353 : Blo 1655527 9434353 := bstep (se 2 (by rfl) ⟨3537882, by rfl⟩ : syracuseStep 9434353 = 7075765) B7075765
theorem B12580109 : Blo 1655527 12580109 := bstep (se 3 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 12580109 = 4717541) B4717541
theorem B5666129 : Blo 1655527 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B5592401 : Blo 1655527 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B5969315 : Blo 1655527 5969315 := bstep (se 1 (by rfl) ⟨4476986, by rfl⟩ : syracuseStep 5969315 = 8953973) B8953973
theorem B5969485 : Blo 1655527 5969485 := bstep (se 3 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 5969485 = 2238557) B2238557
theorem B8500835 : Blo 1655527 8500835 := bstep (se 1 (by rfl) ⟨6375626, by rfl⟩ : syracuseStep 8500835 = 12751253) B12751253
theorem B3143281 : Blo 1655527 3143281 := bstep (se 2 (by rfl) ⟨1178730, by rfl⟩ : syracuseStep 3143281 = 2357461) B2357461
theorem B2873009 : Blo 1655527 2873009 := bstep (se 2 (by rfl) ⟨1077378, by rfl⟩ : syracuseStep 2873009 = 2154757) B2154757
theorem B8386253 : Blo 1655527 8386253 := bstep (se 3 (by rfl) ⟨1572422, by rfl⟩ : syracuseStep 8386253 = 3144845) B3144845
theorem B3725009 : Blo 1655527 3725009 := bstep (se 2 (by rfl) ⟨1396878, by rfl⟩ : syracuseStep 3725009 = 2793757) B2793757
theorem B3725027 : Blo 1655527 3725027 := bstep (se 1 (by rfl) ⟨2793770, by rfl⟩ : syracuseStep 3725027 = 5587541) B5587541
theorem B5379853 : Blo 1655527 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B3143441 : Blo 1655527 3143441 := bstep (se 2 (by rfl) ⟨1178790, by rfl⟩ : syracuseStep 3143441 = 2357581) B2357581
theorem B10213219 : Blo 1655527 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B20158307 : Blo 1655527 20158307 := bstep (se 1 (by rfl) ⟨15118730, by rfl⟩ : syracuseStep 20158307 = 30237461) B30237461
theorem B5592941 : Blo 1655527 5592941 := bstep (se 3 (by rfl) ⟨1048676, by rfl⟩ : syracuseStep 5592941 = 2097353) B2097353
theorem B6289265 : Blo 1655527 6289265 := bstep (se 2 (by rfl) ⟨2358474, by rfl⟩ : syracuseStep 6289265 = 4716949) B4716949
theorem B4192145 : Blo 1655527 4192145 := bstep (se 2 (by rfl) ⟨1572054, by rfl⟩ : syracuseStep 4192145 = 3144109) B3144109
theorem B5592995 : Blo 1655527 5592995 := bstep (se 1 (by rfl) ⟨4194746, by rfl⟩ : syracuseStep 5592995 = 8389493) B8389493
theorem B4192195 : Blo 1655527 4192195 := bstep (se 1 (by rfl) ⟨3144146, by rfl⟩ : syracuseStep 4192195 = 6288293) B6288293
theorem B2652131 : Blo 1655527 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B15112163 : Blo 1655527 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B3725297 : Blo 1655527 3725297 := bstep (se 2 (by rfl) ⟨1396986, by rfl⟩ : syracuseStep 3725297 = 2793973) B2793973
theorem B3725315 : Blo 1655527 3725315 := bstep (se 1 (by rfl) ⟨2793986, by rfl⟩ : syracuseStep 3725315 = 5587973) B5587973
theorem B2357267 : Blo 1655527 2357267 := bstep (se 1 (by rfl) ⟨1767950, by rfl⟩ : syracuseStep 2357267 = 3535901) B3535901
theorem B4192337 : Blo 1655527 4192337 := bstep (se 2 (by rfl) ⟨1572126, by rfl⟩ : syracuseStep 4192337 = 3144253) B3144253
theorem B5666897 : Blo 1655527 5666897 := bstep (se 2 (by rfl) ⟨2125086, by rfl⟩ : syracuseStep 5666897 = 4250173) B4250173
theorem B2652259 : Blo 1655527 2652259 := bstep (se 1 (by rfl) ⟨1989194, by rfl⟩ : syracuseStep 2652259 = 3978389) B3978389
theorem B20420707 : Blo 1655527 20420707 := bstep (se 1 (by rfl) ⟨15315530, by rfl⟩ : syracuseStep 20420707 = 30631061) B30631061
theorem B3143843 : Blo 1655527 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B4716721 : Blo 1655527 4716721 := bstep (se 2 (by rfl) ⟨1768770, by rfl⟩ : syracuseStep 4716721 = 3537541) B3537541
theorem B5593265 : Blo 1655527 5593265 := bstep (se 2 (by rfl) ⟨2097474, by rfl⟩ : syracuseStep 5593265 = 4194949) B4194949
theorem B23869637 : Blo 1655527 23869637 := bstep (se 4 (by rfl) ⟨2237778, by rfl⟩ : syracuseStep 23869637 = 4475557) B4475557
theorem B2652401 : Blo 1655527 2652401 := bstep (se 2 (by rfl) ⟨994650, by rfl⟩ : syracuseStep 2652401 = 1989301) B1989301
theorem B3725585 : Blo 1655527 3725585 := bstep (se 2 (by rfl) ⟨1397094, by rfl⟩ : syracuseStep 3725585 = 2794189) B2794189
theorem B3725603 : Blo 1655527 3725603 := bstep (se 1 (by rfl) ⟨2794202, by rfl⟩ : syracuseStep 3725603 = 5588405) B5588405
theorem B5036365 : Blo 1655527 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B3979601 : Blo 1655527 3979601 := bstep (se 2 (by rfl) ⟨1492350, by rfl⟩ : syracuseStep 3979601 = 2984701) B2984701
theorem B3979619 : Blo 1655527 3979619 := bstep (se 1 (by rfl) ⟨2984714, by rfl⟩ : syracuseStep 3979619 = 5969429) B5969429
theorem B2095571 : Blo 1655527 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B6289933 : Blo 1655527 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B2652689 : Blo 1655527 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B3725873 : Blo 1655527 3725873 := bstep (se 2 (by rfl) ⟨1397202, by rfl⟩ : syracuseStep 3725873 = 2794405) B2794405
theorem B3725891 : Blo 1655527 3725891 := bstep (se 1 (by rfl) ⟨2794418, by rfl⟩ : syracuseStep 3725891 = 5588837) B5588837
theorem B12098117 : Blo 1655527 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B7551629 : Blo 1655527 7551629 := bstep (se 3 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 7551629 = 2831861) B2831861
theorem B2357905 : Blo 1655527 2357905 := bstep (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) B1768429
theorem B9435811 : Blo 1655527 9435811 := bstep (se 1 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 9435811 = 14153717) B14153717
theorem B5593805 : Blo 1655527 5593805 := bstep (se 3 (by rfl) ⟨1048838, by rfl⟩ : syracuseStep 5593805 = 2097677) B2097677
theorem B10607345 : Blo 1655527 10607345 := bstep (se 2 (by rfl) ⟨3977754, by rfl⟩ : syracuseStep 10607345 = 7955509) B7955509
theorem B2358019 : Blo 1655527 2358019 := bstep (se 1 (by rfl) ⟨1768514, by rfl⟩ : syracuseStep 2358019 = 3537029) B3537029
theorem B5593859 : Blo 1655527 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B10607395 : Blo 1655527 10607395 := bstep (se 1 (by rfl) ⟨7955546, by rfl⟩ : syracuseStep 10607395 = 15911093) B15911093
theorem B3726161 : Blo 1655527 3726161 := bstep (se 2 (by rfl) ⟨1397310, by rfl⟩ : syracuseStep 3726161 = 2794621) B2794621
theorem B3726179 : Blo 1655527 3726179 := bstep (se 1 (by rfl) ⟨2794634, by rfl⟩ : syracuseStep 3726179 = 5589269) B5589269
theorem B2390995 : Blo 1655527 2390995 := bstep (se 1 (by rfl) ⟨1793246, by rfl⟩ : syracuseStep 2390995 = 3586493) B3586493
theorem B5594129 : Blo 1655527 5594129 := bstep (se 2 (by rfl) ⟨2097798, by rfl⟩ : syracuseStep 5594129 = 4195597) B4195597
theorem B3144739 : Blo 1655527 3144739 := bstep (se 1 (by rfl) ⟨2358554, by rfl⟩ : syracuseStep 3144739 = 4717109) B4717109
theorem B4193329 : Blo 1655527 4193329 := bstep (se 2 (by rfl) ⟨1572498, by rfl⟩ : syracuseStep 4193329 = 3144997) B3144997
theorem B20151395 : Blo 1655527 20151395 := bstep (se 1 (by rfl) ⟨15113546, by rfl⟩ : syracuseStep 20151395 = 30227093) B30227093
theorem B4537453 : Blo 1655527 4537453 := bstep (se 3 (by rfl) ⟨850772, by rfl⟩ : syracuseStep 4537453 = 1701545) B1701545
theorem B3726449 : Blo 1655527 3726449 := bstep (se 2 (by rfl) ⟨1397418, by rfl⟩ : syracuseStep 3726449 = 2794837) B2794837
theorem B3726467 : Blo 1655527 3726467 := bstep (se 1 (by rfl) ⟨2794850, by rfl⟩ : syracuseStep 3726467 = 5589701) B5589701
theorem B2096275 : Blo 1655527 2096275 := bstep (se 1 (by rfl) ⟨1572206, by rfl⟩ : syracuseStep 2096275 = 3144413) B3144413
theorem B5307569 : Blo 1655527 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B9436337 : Blo 1655527 9436337 := bstep (se 2 (by rfl) ⟨3538626, by rfl⟩ : syracuseStep 9436337 = 7077253) B7077253
theorem B3144899 : Blo 1655527 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B16145635 : Blo 1655527 16145635 := bstep (se 1 (by rfl) ⟨12109226, by rfl⟩ : syracuseStep 16145635 = 24218453) B24218453
theorem B2096371 : Blo 1655527 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B6290723 : Blo 1655527 6290723 := bstep (se 1 (by rfl) ⟨4718042, by rfl⟩ : syracuseStep 6290723 = 9436085) B9436085
theorem B2653489 : Blo 1655527 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B4193603 : Blo 1655527 4193603 := bstep (se 1 (by rfl) ⟨3145202, by rfl⟩ : syracuseStep 4193603 = 6290405) B6290405
theorem B3980657 : Blo 1655527 3980657 := bstep (se 2 (by rfl) ⟨1492746, by rfl⟩ : syracuseStep 3980657 = 2985493) B2985493
theorem B1768835 : Blo 1655527 1768835 := bstep (se 1 (by rfl) ⟨1326626, by rfl⟩ : syracuseStep 1768835 = 2653253) B2653253
theorem B3726737 : Blo 1655527 3726737 := bstep (se 2 (by rfl) ⟨1397526, by rfl⟩ : syracuseStep 3726737 = 2795053) B2795053
theorem B3726755 : Blo 1655527 3726755 := bstep (se 1 (by rfl) ⟨2795066, by rfl⟩ : syracuseStep 3726755 = 5590133) B5590133
theorem B4717997 : Blo 1655527 4717997 := bstep (se 3 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 4717997 = 1769249) B1769249
theorem B7962083 : Blo 1655527 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B10616291 : Blo 1655527 10616291 := bstep (se 1 (by rfl) ⟨7962218, by rfl⟩ : syracuseStep 10616291 = 15924437) B15924437
theorem B4193795 : Blo 1655527 4193795 := bstep (se 1 (by rfl) ⟨3145346, by rfl⟩ : syracuseStep 4193795 = 6290693) B6290693
theorem B2391601 : Blo 1655527 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B12574277 : Blo 1655527 12574277 := bstep (se 4 (by rfl) ⟨1178838, by rfl⟩ : syracuseStep 12574277 = 2357677) B2357677
theorem B11337293 : Blo 1655527 11337293 := bstep (se 3 (by rfl) ⟨2125742, by rfl⟩ : syracuseStep 11337293 = 4251485) B4251485
theorem B3358307 : Blo 1655527 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B4718179 : Blo 1655527 4718179 := bstep (se 1 (by rfl) ⟨3538634, by rfl⟩ : syracuseStep 4718179 = 7077269) B7077269
theorem B30211697 : Blo 1655527 30211697 := bstep (se 2 (by rfl) ⟨11329386, by rfl⟩ : syracuseStep 30211697 = 22658773) B22658773
theorem B4718225 : Blo 1655527 4718225 := bstep (se 2 (by rfl) ⟨1769334, by rfl⟩ : syracuseStep 4718225 = 3538669) B3538669
theorem B7962275 : Blo 1655527 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B3727025 : Blo 1655527 3727025 := bstep (se 2 (by rfl) ⟨1397634, by rfl⟩ : syracuseStep 3727025 = 2795269) B2795269
theorem B3727043 : Blo 1655527 3727043 := bstep (se 1 (by rfl) ⟨2795282, by rfl⟩ : syracuseStep 3727043 = 5590565) B5590565
theorem B2096867 : Blo 1655527 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B5308259 : Blo 1655527 5308259 := bstep (se 1 (by rfl) ⟨3981194, by rfl⟩ : syracuseStep 5308259 = 7962389) B7962389
theorem B1990531 : Blo 1655527 1990531 := bstep (se 1 (by rfl) ⟨1492898, by rfl⟩ : syracuseStep 1990531 = 2985797) B2985797
theorem B6291377 : Blo 1655527 6291377 := bstep (se 2 (by rfl) ⟨2359266, by rfl⟩ : syracuseStep 6291377 = 4718533) B4718533
theorem B3727313 : Blo 1655527 3727313 := bstep (se 2 (by rfl) ⟨1397742, by rfl⟩ : syracuseStep 3727313 = 2795485) B2795485
theorem B3727331 : Blo 1655527 3727331 := bstep (se 1 (by rfl) ⟨2795498, by rfl⟩ : syracuseStep 3727331 = 5590997) B5590997
theorem B3727385 : Blo 1655527 3727385 := bstep (se 2 (by rfl) ⟨1397769, by rfl⟩ : syracuseStep 3727385 = 2795539) B2795539
theorem B8388683 : Blo 1655527 8388683 := bstep (se 1 (by rfl) ⟨6291512, by rfl⟩ : syracuseStep 8388683 = 12583025) B12583025
theorem B4718681 : Blo 1655527 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B3145817 : Blo 1655527 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B2654297 : Blo 1655527 2654297 := bstep (se 2 (by rfl) ⟨995361, by rfl⟩ : syracuseStep 2654297 = 1990723) B1990723
theorem B3727475 : Blo 1655527 3727475 := bstep (se 1 (by rfl) ⟨2795606, by rfl⟩ : syracuseStep 3727475 = 5591213) B5591213
theorem B3727511 : Blo 1655527 3727511 := bstep (se 1 (by rfl) ⟨2795633, by rfl⟩ : syracuseStep 3727511 = 5591267) B5591267
theorem B4194625 : Blo 1655527 4194625 := bstep (se 2 (by rfl) ⟨1572984, by rfl⟩ : syracuseStep 4194625 = 3145969) B3145969
theorem B3727691 : Blo 1655527 3727691 := bstep (se 1 (by rfl) ⟨2795768, by rfl⟩ : syracuseStep 3727691 = 5591537) B5591537
theorem B11493733 : Blo 1655527 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B3727745 : Blo 1655527 3727745 := bstep (se 2 (by rfl) ⟨1397904, by rfl⟩ : syracuseStep 3727745 = 2795809) B2795809
theorem B6291863 : Blo 1655527 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4718999 : Blo 1655527 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B2359705 : Blo 1655527 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B12575249 : Blo 1655527 12575249 := bstep (se 2 (by rfl) ⟨4715718, by rfl⟩ : syracuseStep 12575249 = 9431437) B9431437
theorem B2794007 : Blo 1655527 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B3777047 : Blo 1655527 3777047 := bstep (se 1 (by rfl) ⟨2832785, by rfl⟩ : syracuseStep 3777047 = 5665571) B5665571
theorem B5309003 : Blo 1655527 5309003 := bstep (se 1 (by rfl) ⟨3981752, by rfl⟩ : syracuseStep 5309003 = 7963505) B7963505
theorem B3727961 : Blo 1655527 3727961 := bstep (se 2 (by rfl) ⟨1397985, by rfl⟩ : syracuseStep 3727961 = 2795971) B2795971
theorem B2794135 : Blo 1655527 2794135 := bstep (se 1 (by rfl) ⟨2095601, by rfl⟩ : syracuseStep 2794135 = 4191203) B4191203
theorem B3539609 : Blo 1655527 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B3728051 : Blo 1655527 3728051 := bstep (se 1 (by rfl) ⟨2796038, by rfl⟩ : syracuseStep 3728051 = 5592077) B5592077
theorem B5587649 : Blo 1655527 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B3728087 : Blo 1655527 3728087 := bstep (se 1 (by rfl) ⟨2796065, by rfl⟩ : syracuseStep 3728087 = 5592131) B5592131
theorem B3146455 : Blo 1655527 3146455 := bstep (se 1 (by rfl) ⟨2359841, by rfl⟩ : syracuseStep 3146455 = 4719683) B4719683
theorem B1655531 : Blo 1655527 1655531 := bstep (se 1 (by rfl) ⟨1241648, by rfl⟩ : syracuseStep 1655531 = 2483297) B2483297
theorem B1655543 : Blo 1655527 1655543 := bstep (se 1 (by rfl) ⟨1241657, by rfl⟩ : syracuseStep 1655543 = 2483315) B2483315
theorem B1655563 : Blo 1655527 1655563 := bstep (se 1 (by rfl) ⟨1241672, by rfl⟩ : syracuseStep 1655563 = 2483345) B2483345
theorem B1655575 : Blo 1655527 1655575 := bstep (se 1 (by rfl) ⟨1241681, by rfl⟩ : syracuseStep 1655575 = 2483363) B2483363
theorem B2655001 : Blo 1655527 2655001 := bstep (se 2 (by rfl) ⟨995625, by rfl⟩ : syracuseStep 2655001 = 1991251) B1991251
theorem B1655595 : Blo 1655527 1655595 := bstep (se 1 (by rfl) ⟨1241696, by rfl⟩ : syracuseStep 1655595 = 2483393) B2483393
theorem B1655607 : Blo 1655527 1655607 := bstep (se 1 (by rfl) ⟨1241705, by rfl⟩ : syracuseStep 1655607 = 2483411) B2483411
theorem B7553857 : Blo 1655527 7553857 := bstep (se 2 (by rfl) ⟨2832696, by rfl⟩ : syracuseStep 7553857 = 5665393) B5665393
theorem B1655627 : Blo 1655527 1655627 := bstep (se 1 (by rfl) ⟨1241720, by rfl⟩ : syracuseStep 1655627 = 2483441) B2483441
theorem B1655639 : Blo 1655527 1655639 := bstep (se 1 (by rfl) ⟨1241729, by rfl⟩ : syracuseStep 1655639 = 2483459) B2483459
theorem B1655659 : Blo 1655527 1655659 := bstep (se 1 (by rfl) ⟨1241744, by rfl⟩ : syracuseStep 1655659 = 2483489) B2483489
theorem B1655671 : Blo 1655527 1655671 := bstep (se 1 (by rfl) ⟨1241753, by rfl⟩ : syracuseStep 1655671 = 2483507) B2483507
theorem B1655691 : Blo 1655527 1655691 := bstep (se 1 (by rfl) ⟨1241768, by rfl⟩ : syracuseStep 1655691 = 2483537) B2483537
theorem B3777419 : Blo 1655527 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B3728267 : Blo 1655527 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B6808465 : Blo 1655527 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B1655703 : Blo 1655527 1655703 := bstep (se 1 (by rfl) ⟨1241777, by rfl⟩ : syracuseStep 1655703 = 2483555) B2483555
theorem B4195223 : Blo 1655527 4195223 := bstep (se 1 (by rfl) ⟨3146417, by rfl⟩ : syracuseStep 4195223 = 6292835) B6292835
theorem B1655723 : Blo 1655527 1655723 := bstep (se 1 (by rfl) ⟨1241792, by rfl⟩ : syracuseStep 1655723 = 2483585) B2483585
theorem B1655735 : Blo 1655527 1655735 := bstep (se 1 (by rfl) ⟨1241801, by rfl⟩ : syracuseStep 1655735 = 2483603) B2483603
theorem B3728321 : Blo 1655527 3728321 := bstep (se 2 (by rfl) ⟨1398120, by rfl⟩ : syracuseStep 3728321 = 2796241) B2796241
theorem B1655755 : Blo 1655527 1655755 := bstep (se 1 (by rfl) ⟨1241816, by rfl⟩ : syracuseStep 1655755 = 2483633) B2483633
theorem B1655767 : Blo 1655527 1655767 := bstep (se 1 (by rfl) ⟨1241825, by rfl⟩ : syracuseStep 1655767 = 2483651) B2483651
theorem B1655787 : Blo 1655527 1655787 := bstep (se 1 (by rfl) ⟨1241840, by rfl⟩ : syracuseStep 1655787 = 2483681) B2483681
theorem B1655799 : Blo 1655527 1655799 := bstep (se 1 (by rfl) ⟨1241849, by rfl⟩ : syracuseStep 1655799 = 2483699) B2483699
theorem B1655819 : Blo 1655527 1655819 := bstep (se 1 (by rfl) ⟨1241864, by rfl⟩ : syracuseStep 1655819 = 2483729) B2483729
theorem B1655831 : Blo 1655527 1655831 := bstep (se 1 (by rfl) ⟨1241873, by rfl⟩ : syracuseStep 1655831 = 2483747) B2483747
theorem B1655851 : Blo 1655527 1655851 := bstep (se 1 (by rfl) ⟨1241888, by rfl⟩ : syracuseStep 1655851 = 2483777) B2483777
theorem B3982387 : Blo 1655527 3982387 := bstep (se 1 (by rfl) ⟨2986790, by rfl⟩ : syracuseStep 3982387 = 5973581) B5973581
theorem B1655863 : Blo 1655527 1655863 := bstep (se 1 (by rfl) ⟨1241897, by rfl⟩ : syracuseStep 1655863 = 2483795) B2483795
theorem B3540019 : Blo 1655527 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B1655883 : Blo 1655527 1655883 := bstep (se 1 (by rfl) ⟨1241912, by rfl⟩ : syracuseStep 1655883 = 2483825) B2483825
theorem B1655895 : Blo 1655527 1655895 := bstep (se 1 (by rfl) ⟨1241921, by rfl⟩ : syracuseStep 1655895 = 2483843) B2483843
theorem B1655915 : Blo 1655527 1655915 := bstep (se 1 (by rfl) ⟨1241936, by rfl⟩ : syracuseStep 1655915 = 2483873) B2483873
theorem B1655927 : Blo 1655527 1655927 := bstep (se 1 (by rfl) ⟨1241945, by rfl⟩ : syracuseStep 1655927 = 2483891) B2483891
theorem B2483339 : Blo 1655527 2483339 := bstep (se 1 (by rfl) ⟨1862504, by rfl⟩ : syracuseStep 2483339 = 3725009) B3725009
theorem B1655947 : Blo 1655527 1655947 := bstep (se 1 (by rfl) ⟨1241960, by rfl⟩ : syracuseStep 1655947 = 2483921) B2483921
theorem B2483351 : Blo 1655527 2483351 := bstep (se 1 (by rfl) ⟨1862513, by rfl⟩ : syracuseStep 2483351 = 3725027) B3725027
theorem B1655959 : Blo 1655527 1655959 := bstep (se 1 (by rfl) ⟨1241969, by rfl⟩ : syracuseStep 1655959 = 2483939) B2483939
theorem B3728537 : Blo 1655527 3728537 := bstep (se 2 (by rfl) ⟨1398201, by rfl⟩ : syracuseStep 3728537 = 2796403) B2796403
theorem B1655979 : Blo 1655527 1655979 := bstep (se 1 (by rfl) ⟨1241984, by rfl⟩ : syracuseStep 1655979 = 2483969) B2483969
theorem B1655991 : Blo 1655527 1655991 := bstep (se 1 (by rfl) ⟨1241993, by rfl⟩ : syracuseStep 1655991 = 2483987) B2483987
theorem B4719809 : Blo 1655527 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1656011 : Blo 1655527 1656011 := bstep (se 1 (by rfl) ⟨1242008, by rfl⟩ : syracuseStep 1656011 = 2484017) B2484017
theorem B1656023 : Blo 1655527 1656023 := bstep (se 1 (by rfl) ⟨1242017, by rfl⟩ : syracuseStep 1656023 = 2484035) B2484035
theorem B2483417 : Blo 1655527 2483417 := bstep (se 2 (by rfl) ⟨931281, by rfl⟩ : syracuseStep 2483417 = 1862563) B1862563
theorem B5588189 : Blo 1655527 5588189 := bstep (se 3 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 5588189 = 2095571) B2095571
theorem B1656043 : Blo 1655527 1656043 := bstep (se 1 (by rfl) ⟨1242032, by rfl⟩ : syracuseStep 1656043 = 2484065) B2484065
theorem B3728627 : Blo 1655527 3728627 := bstep (se 1 (by rfl) ⟨2796470, by rfl⟩ : syracuseStep 3728627 = 5592941) B5592941
theorem B1656055 : Blo 1655527 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1656075 : Blo 1655527 1656075 := bstep (se 1 (by rfl) ⟨1242056, by rfl⟩ : syracuseStep 1656075 = 2484113) B2484113
theorem B2794763 : Blo 1655527 2794763 := bstep (se 1 (by rfl) ⟨2096072, by rfl⟩ : syracuseStep 2794763 = 4192145) B4192145
theorem B1656087 : Blo 1655527 1656087 := bstep (se 1 (by rfl) ⟨1242065, by rfl⟩ : syracuseStep 1656087 = 2484131) B2484131
theorem B3728663 : Blo 1655527 3728663 := bstep (se 1 (by rfl) ⟨2796497, by rfl⟩ : syracuseStep 3728663 = 5592995) B5592995
theorem B3187993 : Blo 1655527 3187993 := bstep (se 2 (by rfl) ⟨1195497, by rfl⟩ : syracuseStep 3187993 = 2390995) B2390995
theorem B1656107 : Blo 1655527 1656107 := bstep (se 1 (by rfl) ⟨1242080, by rfl⟩ : syracuseStep 1656107 = 2484161) B2484161
theorem B1656119 : Blo 1655527 1656119 := bstep (se 1 (by rfl) ⟨1242089, by rfl⟩ : syracuseStep 1656119 = 2484179) B2484179
theorem B2483531 : Blo 1655527 2483531 := bstep (se 1 (by rfl) ⟨1862648, by rfl⟩ : syracuseStep 2483531 = 3725297) B3725297
theorem B1656139 : Blo 1655527 1656139 := bstep (se 1 (by rfl) ⟨1242104, by rfl⟩ : syracuseStep 1656139 = 2484209) B2484209
theorem B2483543 : Blo 1655527 2483543 := bstep (se 1 (by rfl) ⟨1862657, by rfl⟩ : syracuseStep 2483543 = 3725315) B3725315
theorem B1656151 : Blo 1655527 1656151 := bstep (se 1 (by rfl) ⟨1242113, by rfl⟩ : syracuseStep 1656151 = 2484227) B2484227
theorem B11937125 : Blo 1655527 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B30229859 : Blo 1655527 30229859 := bstep (se 1 (by rfl) ⟨22672394, by rfl⟩ : syracuseStep 30229859 = 45344789) B45344789
theorem B1656171 : Blo 1655527 1656171 := bstep (se 1 (by rfl) ⟨1242128, by rfl⟩ : syracuseStep 1656171 = 2484257) B2484257
theorem B1656183 : Blo 1655527 1656183 := bstep (se 1 (by rfl) ⟨1242137, by rfl⟩ : syracuseStep 1656183 = 2484275) B2484275
theorem B1656203 : Blo 1655527 1656203 := bstep (se 1 (by rfl) ⟨1242152, by rfl⟩ : syracuseStep 1656203 = 2484305) B2484305
theorem B2794891 : Blo 1655527 2794891 := bstep (se 1 (by rfl) ⟨2096168, by rfl⟩ : syracuseStep 2794891 = 4192337) B4192337
theorem B3777931 : Blo 1655527 3777931 := bstep (se 1 (by rfl) ⟨2833448, by rfl⟩ : syracuseStep 3777931 = 5666897) B5666897
theorem B1656215 : Blo 1655527 1656215 := bstep (se 1 (by rfl) ⟨1242161, by rfl⟩ : syracuseStep 1656215 = 2484323) B2484323
theorem B2483609 : Blo 1655527 2483609 := bstep (se 2 (by rfl) ⟨931353, by rfl⟩ : syracuseStep 2483609 = 1862707) B1862707
theorem B1656235 : Blo 1655527 1656235 := bstep (se 1 (by rfl) ⟨1242176, by rfl⟩ : syracuseStep 1656235 = 2484353) B2484353
theorem B15926705 : Blo 1655527 15926705 := bstep (se 2 (by rfl) ⟨5972514, by rfl⟩ : syracuseStep 15926705 = 11945029) B11945029
theorem B1656247 : Blo 1655527 1656247 := bstep (se 1 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 1656247 = 2484371) B2484371
theorem B1656267 : Blo 1655527 1656267 := bstep (se 1 (by rfl) ⟨1242200, by rfl⟩ : syracuseStep 1656267 = 2484401) B2484401
theorem B3728843 : Blo 1655527 3728843 := bstep (se 1 (by rfl) ⟨2796632, by rfl⟩ : syracuseStep 3728843 = 5593265) B5593265
theorem B1656279 : Blo 1655527 1656279 := bstep (se 1 (by rfl) ⟨1242209, by rfl⟩ : syracuseStep 1656279 = 2484419) B2484419
theorem B1656299 : Blo 1655527 1656299 := bstep (se 1 (by rfl) ⟨1242224, by rfl⟩ : syracuseStep 1656299 = 2484449) B2484449
theorem B1656311 : Blo 1655527 1656311 := bstep (se 1 (by rfl) ⟨1242233, by rfl⟩ : syracuseStep 1656311 = 2484467) B2484467
theorem B3728897 : Blo 1655527 3728897 := bstep (se 2 (by rfl) ⟨1398336, by rfl⟩ : syracuseStep 3728897 = 2796673) B2796673
theorem B2483723 : Blo 1655527 2483723 := bstep (se 1 (by rfl) ⟨1862792, by rfl⟩ : syracuseStep 2483723 = 3725585) B3725585
theorem B1656331 : Blo 1655527 1656331 := bstep (se 1 (by rfl) ⟨1242248, by rfl⟩ : syracuseStep 1656331 = 2484497) B2484497
theorem B32261645 : Blo 1655527 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B2483735 : Blo 1655527 2483735 := bstep (se 1 (by rfl) ⟨1862801, by rfl⟩ : syracuseStep 2483735 = 3725603) B3725603
theorem B1656343 : Blo 1655527 1656343 := bstep (se 1 (by rfl) ⟨1242257, by rfl⟩ : syracuseStep 1656343 = 2484515) B2484515
theorem B2795033 : Blo 1655527 2795033 := bstep (se 2 (by rfl) ⟨1048137, by rfl⟩ : syracuseStep 2795033 = 2096275) B2096275
theorem B12584483 : Blo 1655527 12584483 := bstep (se 1 (by rfl) ⟨9438362, by rfl⟩ : syracuseStep 12584483 = 18876725) B18876725
theorem B1656363 : Blo 1655527 1656363 := bstep (se 1 (by rfl) ⟨1242272, by rfl⟩ : syracuseStep 1656363 = 2484545) B2484545
theorem B2983475 : Blo 1655527 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B1656375 : Blo 1655527 1656375 := bstep (se 1 (by rfl) ⟨1242281, by rfl⟩ : syracuseStep 1656375 = 2484563) B2484563
theorem B1656395 : Blo 1655527 1656395 := bstep (se 1 (by rfl) ⟨1242296, by rfl⟩ : syracuseStep 1656395 = 2484593) B2484593
theorem B1656407 : Blo 1655527 1656407 := bstep (se 1 (by rfl) ⟨1242305, by rfl⟩ : syracuseStep 1656407 = 2484611) B2484611
theorem B2483801 : Blo 1655527 2483801 := bstep (se 2 (by rfl) ⟨931425, by rfl⟩ : syracuseStep 2483801 = 1862851) B1862851
theorem B8955485 : Blo 1655527 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B22668893 : Blo 1655527 22668893 := bstep (se 3 (by rfl) ⟨4250417, by rfl⟩ : syracuseStep 22668893 = 8500835) B8500835
theorem B1656427 : Blo 1655527 1656427 := bstep (se 1 (by rfl) ⟨1242320, by rfl⟩ : syracuseStep 1656427 = 2484641) B2484641
theorem B1656439 : Blo 1655527 1656439 := bstep (se 1 (by rfl) ⟨1242329, by rfl⟩ : syracuseStep 1656439 = 2484659) B2484659
theorem B6293123 : Blo 1655527 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B1656459 : Blo 1655527 1656459 := bstep (se 1 (by rfl) ⟨1242344, by rfl⟩ : syracuseStep 1656459 = 2484689) B2484689
theorem B1656471 : Blo 1655527 1656471 := bstep (se 1 (by rfl) ⟨1242353, by rfl⟩ : syracuseStep 1656471 = 2484707) B2484707
theorem B2795161 : Blo 1655527 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B1656491 : Blo 1655527 1656491 := bstep (se 1 (by rfl) ⟨1242368, by rfl⟩ : syracuseStep 1656491 = 2484737) B2484737
theorem B1656503 : Blo 1655527 1656503 := bstep (se 1 (by rfl) ⟨1242377, by rfl⟩ : syracuseStep 1656503 = 2484755) B2484755
theorem B2483915 : Blo 1655527 2483915 := bstep (se 1 (by rfl) ⟨1862936, by rfl⟩ : syracuseStep 2483915 = 3725873) B3725873
theorem B1656523 : Blo 1655527 1656523 := bstep (se 1 (by rfl) ⟨1242392, by rfl⟩ : syracuseStep 1656523 = 2484785) B2484785
theorem B2483927 : Blo 1655527 2483927 := bstep (se 1 (by rfl) ⟨1862945, by rfl⟩ : syracuseStep 2483927 = 3725891) B3725891
theorem B1656535 : Blo 1655527 1656535 := bstep (se 1 (by rfl) ⟨1242401, by rfl⟩ : syracuseStep 1656535 = 2484803) B2484803
theorem B3729113 : Blo 1655527 3729113 := bstep (se 2 (by rfl) ⟨1398417, by rfl⟩ : syracuseStep 3729113 = 2796835) B2796835
theorem B1656555 : Blo 1655527 1656555 := bstep (se 1 (by rfl) ⟨1242416, by rfl⟩ : syracuseStep 1656555 = 2484833) B2484833
theorem B1656567 : Blo 1655527 1656567 := bstep (se 1 (by rfl) ⟨1242425, by rfl⟩ : syracuseStep 1656567 = 2484851) B2484851
theorem B1656587 : Blo 1655527 1656587 := bstep (se 1 (by rfl) ⟨1242440, by rfl⟩ : syracuseStep 1656587 = 2484881) B2484881
theorem B1656599 : Blo 1655527 1656599 := bstep (se 1 (by rfl) ⟨1242449, by rfl⟩ : syracuseStep 1656599 = 2484899) B2484899
theorem B2483993 : Blo 1655527 2483993 := bstep (se 2 (by rfl) ⟨931497, by rfl⟩ : syracuseStep 2483993 = 1862995) B1862995
theorem B1656619 : Blo 1655527 1656619 := bstep (se 1 (by rfl) ⟨1242464, by rfl⟩ : syracuseStep 1656619 = 2484929) B2484929
theorem B7661357 : Blo 1655527 7661357 := bstep (se 3 (by rfl) ⟨1436504, by rfl⟩ : syracuseStep 7661357 = 2873009) B2873009
theorem B3729203 : Blo 1655527 3729203 := bstep (se 1 (by rfl) ⟨2796902, by rfl⟩ : syracuseStep 3729203 = 5593805) B5593805
theorem B1656631 : Blo 1655527 1656631 := bstep (se 1 (by rfl) ⟨1242473, by rfl⟩ : syracuseStep 1656631 = 2484947) B2484947
theorem B8390465 : Blo 1655527 8390465 := bstep (se 2 (by rfl) ⟨3146424, by rfl⟩ : syracuseStep 8390465 = 6292849) B6292849
theorem B7071563 : Blo 1655527 7071563 := bstep (se 1 (by rfl) ⟨5303672, by rfl⟩ : syracuseStep 7071563 = 10607345) B10607345
theorem B1656651 : Blo 1655527 1656651 := bstep (se 1 (by rfl) ⟨1242488, by rfl⟩ : syracuseStep 1656651 = 2484977) B2484977
theorem B1656663 : Blo 1655527 1656663 := bstep (se 1 (by rfl) ⟨1242497, by rfl⟩ : syracuseStep 1656663 = 2484995) B2484995
theorem B3729239 : Blo 1655527 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B54470501 : Blo 1655527 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B1656683 : Blo 1655527 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B1656695 : Blo 1655527 1656695 := bstep (se 1 (by rfl) ⟨1242521, by rfl⟩ : syracuseStep 1656695 = 2485043) B2485043
theorem B2484107 : Blo 1655527 2484107 := bstep (se 1 (by rfl) ⟨1863080, by rfl⟩ : syracuseStep 2484107 = 3726161) B3726161
theorem B1656715 : Blo 1655527 1656715 := bstep (se 1 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 1656715 = 2485073) B2485073
theorem B2484119 : Blo 1655527 2484119 := bstep (se 1 (by rfl) ⟨1863089, by rfl⟩ : syracuseStep 2484119 = 3726179) B3726179
theorem B1656727 : Blo 1655527 1656727 := bstep (se 1 (by rfl) ⟨1242545, by rfl⟩ : syracuseStep 1656727 = 2485091) B2485091
theorem B1656747 : Blo 1655527 1656747 := bstep (se 1 (by rfl) ⟨1242560, by rfl⟩ : syracuseStep 1656747 = 2485121) B2485121
theorem B1656759 : Blo 1655527 1656759 := bstep (se 1 (by rfl) ⟨1242569, by rfl⟩ : syracuseStep 1656759 = 2485139) B2485139
theorem B1656779 : Blo 1655527 1656779 := bstep (se 1 (by rfl) ⟨1242584, by rfl⟩ : syracuseStep 1656779 = 2485169) B2485169
theorem B1656791 : Blo 1655527 1656791 := bstep (se 1 (by rfl) ⟨1242593, by rfl⟩ : syracuseStep 1656791 = 2485187) B2485187
theorem B2484185 : Blo 1655527 2484185 := bstep (se 2 (by rfl) ⟨931569, by rfl⟩ : syracuseStep 2484185 = 1863139) B1863139
theorem B1656811 : Blo 1655527 1656811 := bstep (se 1 (by rfl) ⟨1242608, by rfl⟩ : syracuseStep 1656811 = 2485217) B2485217
theorem B1656823 : Blo 1655527 1656823 := bstep (se 1 (by rfl) ⟨1242617, by rfl⟩ : syracuseStep 1656823 = 2485235) B2485235
theorem B1656843 : Blo 1655527 1656843 := bstep (se 1 (by rfl) ⟨1242632, by rfl⟩ : syracuseStep 1656843 = 2485265) B2485265
theorem B3729419 : Blo 1655527 3729419 := bstep (se 1 (by rfl) ⟨2797064, by rfl⟩ : syracuseStep 3729419 = 5594129) B5594129
theorem B1656855 : Blo 1655527 1656855 := bstep (se 1 (by rfl) ⟨1242641, by rfl⟩ : syracuseStep 1656855 = 2485283) B2485283
theorem B1656875 : Blo 1655527 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B2983987 : Blo 1655527 2983987 := bstep (se 1 (by rfl) ⟨2237990, by rfl⟩ : syracuseStep 2983987 = 4475981) B4475981
theorem B1656887 : Blo 1655527 1656887 := bstep (se 1 (by rfl) ⟨1242665, by rfl⟩ : syracuseStep 1656887 = 2485331) B2485331
theorem B7079987 : Blo 1655527 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B3188801 : Blo 1655527 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B2484299 : Blo 1655527 2484299 := bstep (se 1 (by rfl) ⟨1863224, by rfl⟩ : syracuseStep 2484299 = 3726449) B3726449
theorem B1656907 : Blo 1655527 1656907 := bstep (se 1 (by rfl) ⟨1242680, by rfl⟩ : syracuseStep 1656907 = 2485361) B2485361
theorem B2484311 : Blo 1655527 2484311 := bstep (se 1 (by rfl) ⟨1863233, by rfl⟩ : syracuseStep 2484311 = 3726467) B3726467
theorem B1656919 : Blo 1655527 1656919 := bstep (se 1 (by rfl) ⟨1242689, by rfl⟩ : syracuseStep 1656919 = 2485379) B2485379
theorem B1656939 : Blo 1655527 1656939 := bstep (se 1 (by rfl) ⟨1242704, by rfl⟩ : syracuseStep 1656939 = 2485409) B2485409
theorem B2984051 : Blo 1655527 2984051 := bstep (se 1 (by rfl) ⟨2238038, by rfl⟩ : syracuseStep 2984051 = 4476077) B4476077
theorem B1656951 : Blo 1655527 1656951 := bstep (se 1 (by rfl) ⟨1242713, by rfl⟩ : syracuseStep 1656951 = 2485427) B2485427
theorem B1656971 : Blo 1655527 1656971 := bstep (se 1 (by rfl) ⟨1242728, by rfl⟩ : syracuseStep 1656971 = 2485457) B2485457
theorem B1656983 : Blo 1655527 1656983 := bstep (se 1 (by rfl) ⟨1242737, by rfl⟩ : syracuseStep 1656983 = 2485475) B2485475
theorem B2484377 : Blo 1655527 2484377 := bstep (se 2 (by rfl) ⟨931641, by rfl⟩ : syracuseStep 2484377 = 1863283) B1863283
theorem B1657003 : Blo 1655527 1657003 := bstep (se 1 (by rfl) ⟨1242752, by rfl⟩ : syracuseStep 1657003 = 2485505) B2485505
theorem B1657015 : Blo 1655527 1657015 := bstep (se 1 (by rfl) ⟨1242761, by rfl⟩ : syracuseStep 1657015 = 2485523) B2485523
theorem B5376203 : Blo 1655527 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B1657035 : Blo 1655527 1657035 := bstep (se 1 (by rfl) ⟨1242776, by rfl⟩ : syracuseStep 1657035 = 2485553) B2485553
theorem B2795735 : Blo 1655527 2795735 := bstep (se 1 (by rfl) ⟨2096801, by rfl⟩ : syracuseStep 2795735 = 4193603) B4193603
theorem B1657047 : Blo 1655527 1657047 := bstep (se 1 (by rfl) ⟨1242785, by rfl⟩ : syracuseStep 1657047 = 2485571) B2485571
theorem B1657067 : Blo 1655527 1657067 := bstep (se 1 (by rfl) ⟨1242800, by rfl⟩ : syracuseStep 1657067 = 2485601) B2485601
theorem B1657079 : Blo 1655527 1657079 := bstep (se 1 (by rfl) ⟨1242809, by rfl⟩ : syracuseStep 1657079 = 2485619) B2485619
theorem B2484491 : Blo 1655527 2484491 := bstep (se 1 (by rfl) ⟨1863368, by rfl⟩ : syracuseStep 2484491 = 3726737) B3726737
theorem B1657099 : Blo 1655527 1657099 := bstep (se 1 (by rfl) ⟨1242824, by rfl⟩ : syracuseStep 1657099 = 2485649) B2485649
theorem B2484503 : Blo 1655527 2484503 := bstep (se 1 (by rfl) ⟨1863377, by rfl⟩ : syracuseStep 2484503 = 3726755) B3726755
theorem B7555351 : Blo 1655527 7555351 := bstep (se 1 (by rfl) ⟨5666513, by rfl⟩ : syracuseStep 7555351 = 11333027) B11333027
theorem B1657111 : Blo 1655527 1657111 := bstep (se 1 (by rfl) ⟨1242833, by rfl⟩ : syracuseStep 1657111 = 2485667) B2485667
theorem B1657131 : Blo 1655527 1657131 := bstep (se 1 (by rfl) ⟨1242848, by rfl⟩ : syracuseStep 1657131 = 2485697) B2485697
theorem B1657143 : Blo 1655527 1657143 := bstep (se 1 (by rfl) ⟨1242857, by rfl⟩ : syracuseStep 1657143 = 2485715) B2485715
theorem B5589323 : Blo 1655527 5589323 := bstep (se 1 (by rfl) ⟨4191992, by rfl⟩ : syracuseStep 5589323 = 8383985) B8383985
theorem B1657163 : Blo 1655527 1657163 := bstep (se 1 (by rfl) ⟨1242872, by rfl⟩ : syracuseStep 1657163 = 2485745) B2485745
theorem B2795863 : Blo 1655527 2795863 := bstep (se 1 (by rfl) ⟨2096897, by rfl⟩ : syracuseStep 2795863 = 4193795) B4193795
theorem B1657175 : Blo 1655527 1657175 := bstep (se 1 (by rfl) ⟨1242881, by rfl⟩ : syracuseStep 1657175 = 2485763) B2485763
theorem B2484569 : Blo 1655527 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B1657195 : Blo 1655527 1657195 := bstep (se 1 (by rfl) ⟨1242896, by rfl⟩ : syracuseStep 1657195 = 2485793) B2485793
theorem B152947061 : Blo 1655527 152947061 := bstep (se 5 (by rfl) ⟨7169393, by rfl⟩ : syracuseStep 152947061 = 14338787) B14338787
theorem B1657207 : Blo 1655527 1657207 := bstep (se 1 (by rfl) ⟨1242905, by rfl⟩ : syracuseStep 1657207 = 2485811) B2485811
theorem B8382851 : Blo 1655527 8382851 := bstep (se 1 (by rfl) ⟨6287138, by rfl⟩ : syracuseStep 8382851 = 12574277) B12574277
theorem B1657227 : Blo 1655527 1657227 := bstep (se 1 (by rfl) ⟨1242920, by rfl⟩ : syracuseStep 1657227 = 2485841) B2485841
theorem B1657239 : Blo 1655527 1657239 := bstep (se 1 (by rfl) ⟨1242929, by rfl⟩ : syracuseStep 1657239 = 2485859) B2485859
theorem B1657259 : Blo 1655527 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B1657271 : Blo 1655527 1657271 := bstep (se 1 (by rfl) ⟨1242953, by rfl⟩ : syracuseStep 1657271 = 2485907) B2485907
theorem B5376449 : Blo 1655527 5376449 := bstep (se 2 (by rfl) ⟨2016168, by rfl⟩ : syracuseStep 5376449 = 4032337) B4032337
theorem B2484683 : Blo 1655527 2484683 := bstep (se 1 (by rfl) ⟨1863512, by rfl⟩ : syracuseStep 2484683 = 3727025) B3727025
theorem B1657291 : Blo 1655527 1657291 := bstep (se 1 (by rfl) ⟨1242968, by rfl⟩ : syracuseStep 1657291 = 2485937) B2485937
theorem B2484695 : Blo 1655527 2484695 := bstep (se 1 (by rfl) ⟨1863521, by rfl⟩ : syracuseStep 2484695 = 3727043) B3727043
theorem B1657303 : Blo 1655527 1657303 := bstep (se 1 (by rfl) ⟨1242977, by rfl⟩ : syracuseStep 1657303 = 2485955) B2485955
theorem B1657323 : Blo 1655527 1657323 := bstep (se 1 (by rfl) ⟨1242992, by rfl⟩ : syracuseStep 1657323 = 2485985) B2485985
theorem B1657335 : Blo 1655527 1657335 := bstep (se 1 (by rfl) ⟨1243001, by rfl⟩ : syracuseStep 1657335 = 2486003) B2486003
theorem B1657355 : Blo 1655527 1657355 := bstep (se 1 (by rfl) ⟨1243016, by rfl⟩ : syracuseStep 1657355 = 2486033) B2486033
theorem B7555607 : Blo 1655527 7555607 := bstep (se 1 (by rfl) ⟨5666705, by rfl⟩ : syracuseStep 7555607 = 11333411) B11333411
theorem B1657367 : Blo 1655527 1657367 := bstep (se 1 (by rfl) ⟨1243025, by rfl⟩ : syracuseStep 1657367 = 2486051) B2486051
theorem B2484761 : Blo 1655527 2484761 := bstep (se 2 (by rfl) ⟨931785, by rfl⟩ : syracuseStep 2484761 = 1863571) B1863571
theorem B1657387 : Blo 1655527 1657387 := bstep (se 1 (by rfl) ⟨1243040, by rfl⟩ : syracuseStep 1657387 = 2486081) B2486081
theorem B1657399 : Blo 1655527 1657399 := bstep (se 1 (by rfl) ⟨1243049, by rfl⟩ : syracuseStep 1657399 = 2486099) B2486099
theorem B4541003 : Blo 1655527 4541003 := bstep (se 1 (by rfl) ⟨3405752, by rfl⟩ : syracuseStep 4541003 = 6811505) B6811505
theorem B1657419 : Blo 1655527 1657419 := bstep (se 1 (by rfl) ⟨1243064, by rfl⟩ : syracuseStep 1657419 = 2486129) B2486129
theorem B1657431 : Blo 1655527 1657431 := bstep (se 1 (by rfl) ⟨1243073, by rfl⟩ : syracuseStep 1657431 = 2486147) B2486147
theorem B5589593 : Blo 1655527 5589593 := bstep (se 2 (by rfl) ⟨2096097, by rfl⟩ : syracuseStep 5589593 = 4192195) B4192195
theorem B1657451 : Blo 1655527 1657451 := bstep (se 1 (by rfl) ⟨1243088, by rfl⟩ : syracuseStep 1657451 = 2486177) B2486177
theorem B1657463 : Blo 1655527 1657463 := bstep (se 1 (by rfl) ⟨1243097, by rfl⟩ : syracuseStep 1657463 = 2486195) B2486195
theorem B2484875 : Blo 1655527 2484875 := bstep (se 1 (by rfl) ⟨1863656, by rfl⟩ : syracuseStep 2484875 = 3727313) B3727313
theorem B1657483 : Blo 1655527 1657483 := bstep (se 1 (by rfl) ⟨1243112, by rfl⟩ : syracuseStep 1657483 = 2486225) B2486225
theorem B2484887 : Blo 1655527 2484887 := bstep (se 1 (by rfl) ⟨1863665, by rfl⟩ : syracuseStep 2484887 = 3727331) B3727331
theorem B1657495 : Blo 1655527 1657495 := bstep (se 1 (by rfl) ⟨1243121, by rfl⟩ : syracuseStep 1657495 = 2486243) B2486243
theorem B1657515 : Blo 1655527 1657515 := bstep (se 1 (by rfl) ⟨1243136, by rfl⟩ : syracuseStep 1657515 = 2486273) B2486273
theorem B1657527 : Blo 1655527 1657527 := bstep (se 1 (by rfl) ⟨1243145, by rfl⟩ : syracuseStep 1657527 = 2486291) B2486291
theorem B2484953 : Blo 1655527 2484953 := bstep (se 2 (by rfl) ⟨931857, by rfl⟩ : syracuseStep 2484953 = 1863715) B1863715
theorem B6286045 : Blo 1655527 6286045 := bstep (se 3 (by rfl) ⟨1178633, by rfl⟩ : syracuseStep 6286045 = 2357267) B2357267
theorem B15117121 : Blo 1655527 15117121 := bstep (se 2 (by rfl) ⟨5668920, by rfl⟩ : syracuseStep 15117121 = 11337841) B11337841
theorem B2485067 : Blo 1655527 2485067 := bstep (se 1 (by rfl) ⟨1863800, by rfl⟩ : syracuseStep 2485067 = 3727601) B3727601
theorem B2485079 : Blo 1655527 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B2485145 : Blo 1655527 2485145 := bstep (se 2 (by rfl) ⟨931929, by rfl⟩ : syracuseStep 2485145 = 1863859) B1863859
theorem B2796491 : Blo 1655527 2796491 := bstep (se 1 (by rfl) ⟨2097368, by rfl⟩ : syracuseStep 2796491 = 4194737) B4194737
theorem B1862635 : Blo 1655527 1862635 := bstep (se 1 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 1862635 = 2793953) B2793953
theorem B2485259 : Blo 1655527 2485259 := bstep (se 1 (by rfl) ⟨1863944, by rfl⟩ : syracuseStep 2485259 = 3727889) B3727889
theorem B2485271 : Blo 1655527 2485271 := bstep (se 1 (by rfl) ⟨1863953, by rfl⟩ : syracuseStep 2485271 = 3727907) B3727907
theorem B2985025 : Blo 1655527 2985025 := bstep (se 2 (by rfl) ⟨1119384, by rfl⟩ : syracuseStep 2985025 = 2238769) B2238769
theorem B2796619 : Blo 1655527 2796619 := bstep (se 1 (by rfl) ⟨2097464, by rfl⟩ : syracuseStep 2796619 = 4194929) B4194929
theorem B1862743 : Blo 1655527 1862743 := bstep (se 1 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 1862743 = 2794115) B2794115
theorem B2485337 : Blo 1655527 2485337 := bstep (se 2 (by rfl) ⟨932001, by rfl⟩ : syracuseStep 2485337 = 1864003) B1864003
theorem B28691587 : Blo 1655527 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B2485451 : Blo 1655527 2485451 := bstep (se 1 (by rfl) ⟨1864088, by rfl⟩ : syracuseStep 2485451 = 3728177) B3728177
theorem B2485463 : Blo 1655527 2485463 := bstep (se 1 (by rfl) ⟨1864097, by rfl⟩ : syracuseStep 2485463 = 3728195) B3728195
theorem B2796761 : Blo 1655527 2796761 := bstep (se 2 (by rfl) ⟨1048785, by rfl⟩ : syracuseStep 2796761 = 2097571) B2097571
theorem B1862923 : Blo 1655527 1862923 := bstep (se 1 (by rfl) ⟨1397192, by rfl⟩ : syracuseStep 1862923 = 2794385) B2794385
theorem B5590295 : Blo 1655527 5590295 := bstep (se 1 (by rfl) ⟨4192721, by rfl⟩ : syracuseStep 5590295 = 8385443) B8385443
theorem B2485529 : Blo 1655527 2485529 := bstep (se 2 (by rfl) ⟨932073, by rfl⟩ : syracuseStep 2485529 = 1864147) B1864147
theorem B5967179 : Blo 1655527 5967179 := bstep (se 1 (by rfl) ⟨4475384, by rfl⟩ : syracuseStep 5967179 = 8950769) B8950769
theorem B9432395 : Blo 1655527 9432395 := bstep (se 1 (by rfl) ⟨7074296, by rfl⟩ : syracuseStep 9432395 = 14148593) B14148593
theorem B2796889 : Blo 1655527 2796889 := bstep (se 2 (by rfl) ⟨1048833, by rfl⟩ : syracuseStep 2796889 = 2097667) B2097667
theorem B1863031 : Blo 1655527 1863031 := bstep (se 1 (by rfl) ⟨1397273, by rfl⟩ : syracuseStep 1863031 = 2794547) B2794547
theorem B2485643 : Blo 1655527 2485643 := bstep (se 1 (by rfl) ⟨1864232, by rfl⟩ : syracuseStep 2485643 = 3728465) B3728465
theorem B4779415 : Blo 1655527 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B2485655 : Blo 1655527 2485655 := bstep (se 1 (by rfl) ⟨1864241, by rfl⟩ : syracuseStep 2485655 = 3728483) B3728483
theorem B7073203 : Blo 1655527 7073203 := bstep (se 1 (by rfl) ⟨5304902, by rfl⟩ : syracuseStep 7073203 = 10609805) B10609805
theorem B2485721 : Blo 1655527 2485721 := bstep (se 2 (by rfl) ⟨932145, by rfl⟩ : syracuseStep 2485721 = 1864291) B1864291
theorem B1863211 : Blo 1655527 1863211 := bstep (se 1 (by rfl) ⟨1397408, by rfl⟩ : syracuseStep 1863211 = 2794817) B2794817
theorem B2485835 : Blo 1655527 2485835 := bstep (se 1 (by rfl) ⟨1864376, by rfl⟩ : syracuseStep 2485835 = 3728753) B3728753
theorem B2485847 : Blo 1655527 2485847 := bstep (se 1 (by rfl) ⟨1864385, by rfl⟩ : syracuseStep 2485847 = 3728771) B3728771
theorem B1863319 : Blo 1655527 1863319 := bstep (se 1 (by rfl) ⟨1397489, by rfl⟩ : syracuseStep 1863319 = 2794979) B2794979
theorem B2485913 : Blo 1655527 2485913 := bstep (se 2 (by rfl) ⟨932217, by rfl⟩ : syracuseStep 2485913 = 1864435) B1864435
theorem B14143193 : Blo 1655527 14143193 := bstep (se 2 (by rfl) ⟨5303697, by rfl⟩ : syracuseStep 14143193 = 10607395) B10607395
theorem B2486027 : Blo 1655527 2486027 := bstep (se 1 (by rfl) ⟨1864520, by rfl⟩ : syracuseStep 2486027 = 3729041) B3729041
theorem B2486039 : Blo 1655527 2486039 := bstep (se 1 (by rfl) ⟨1864529, by rfl⟩ : syracuseStep 2486039 = 3729059) B3729059
theorem B5590835 : Blo 1655527 5590835 := bstep (se 1 (by rfl) ⟨4193126, by rfl⟩ : syracuseStep 5590835 = 8386253) B8386253
theorem B1863499 : Blo 1655527 1863499 := bstep (se 1 (by rfl) ⟨1397624, by rfl⟩ : syracuseStep 1863499 = 2795249) B2795249
theorem B2486105 : Blo 1655527 2486105 := bstep (se 2 (by rfl) ⟨932289, by rfl⟩ : syracuseStep 2486105 = 1864579) B1864579
theorem B13438871 : Blo 1655527 13438871 := bstep (se 1 (by rfl) ⟨10079153, by rfl⟩ : syracuseStep 13438871 = 20158307) B20158307
theorem B1863607 : Blo 1655527 1863607 := bstep (se 1 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 1863607 = 2795411) B2795411
theorem B4714433 : Blo 1655527 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B2486219 : Blo 1655527 2486219 := bstep (se 1 (by rfl) ⟨1864664, by rfl⟩ : syracuseStep 2486219 = 3729329) B3729329
theorem B6287321 : Blo 1655527 6287321 := bstep (se 2 (by rfl) ⟨2357745, by rfl⟩ : syracuseStep 6287321 = 4715491) B4715491
theorem B2486231 : Blo 1655527 2486231 := bstep (se 1 (by rfl) ⟨1864673, by rfl⟩ : syracuseStep 2486231 = 3729347) B3729347
theorem B7073837 : Blo 1655527 7073837 := bstep (se 3 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 7073837 = 2652689) B2652689
theorem B5591105 : Blo 1655527 5591105 := bstep (se 2 (by rfl) ⟨2096664, by rfl⟩ : syracuseStep 5591105 = 4193329) B4193329
theorem B30642245 : Blo 1655527 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B1863787 : Blo 1655527 1863787 := bstep (se 1 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 1863787 = 2795681) B2795681
theorem B15913091 : Blo 1655527 15913091 := bstep (se 1 (by rfl) ⟨11934818, by rfl⟩ : syracuseStep 15913091 = 23869637) B23869637
theorem B6049937 : Blo 1655527 6049937 := bstep (se 2 (by rfl) ⟨2268726, by rfl⟩ : syracuseStep 6049937 = 4537453) B4537453
theorem B30232781 : Blo 1655527 30232781 := bstep (se 3 (by rfl) ⟨5668646, by rfl⟩ : syracuseStep 30232781 = 11337293) B11337293
theorem B1863895 : Blo 1655527 1863895 := bstep (se 1 (by rfl) ⟨1397921, by rfl⟩ : syracuseStep 1863895 = 2795843) B2795843
theorem B14151941 : Blo 1655527 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B12579137 : Blo 1655527 12579137 := bstep (se 2 (by rfl) ⟨4717176, by rfl⟩ : syracuseStep 12579137 = 9434353) B9434353
theorem B5968217 : Blo 1655527 5968217 := bstep (se 2 (by rfl) ⟨2238081, by rfl⟩ : syracuseStep 5968217 = 4476163) B4476163
theorem B1864075 : Blo 1655527 1864075 := bstep (se 1 (by rfl) ⟨1398056, by rfl⟩ : syracuseStep 1864075 = 2796113) B2796113
theorem B5034419 : Blo 1655527 5034419 := bstep (se 1 (by rfl) ⟨3775814, by rfl⟩ : syracuseStep 5034419 = 7551629) B7551629
theorem B1864183 : Blo 1655527 1864183 := bstep (se 1 (by rfl) ⟨1398137, by rfl⟩ : syracuseStep 1864183 = 2796275) B2796275
theorem B5591645 : Blo 1655527 5591645 := bstep (se 3 (by rfl) ⟨1048433, by rfl⟩ : syracuseStep 5591645 = 2096867) B2096867
theorem B1864363 : Blo 1655527 1864363 := bstep (se 1 (by rfl) ⟨1398272, by rfl⟩ : syracuseStep 1864363 = 2796545) B2796545
theorem B4190899 : Blo 1655527 4190899 := bstep (se 1 (by rfl) ⟨3143174, by rfl⟩ : syracuseStep 4190899 = 6286349) B6286349
theorem B7959313 : Blo 1655527 7959313 := bstep (se 2 (by rfl) ⟨2984742, by rfl⟩ : syracuseStep 7959313 = 5969485) B5969485
theorem B1864471 : Blo 1655527 1864471 := bstep (se 1 (by rfl) ⟨1398353, by rfl⟩ : syracuseStep 1864471 = 2796707) B2796707
theorem B3978035 : Blo 1655527 3978035 := bstep (se 1 (by rfl) ⟨2983526, by rfl⟩ : syracuseStep 3978035 = 5967053) B5967053
theorem B4191041 : Blo 1655527 4191041 := bstep (se 2 (by rfl) ⟨1571640, by rfl⟩ : syracuseStep 4191041 = 3143281) B3143281
theorem B1864651 : Blo 1655527 1864651 := bstep (se 1 (by rfl) ⟨1398488, by rfl⟩ : syracuseStep 1864651 = 2796977) B2796977
theorem B7173137 : Blo 1655527 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B20141131 : Blo 1655527 20141131 := bstep (se 1 (by rfl) ⟨15105848, by rfl⟩ : syracuseStep 20141131 = 30211697) B30211697
theorem B3535987 : Blo 1655527 3535987 := bstep (se 1 (by rfl) ⟨2651990, by rfl⟩ : syracuseStep 3535987 = 5303981) B5303981
theorem B3536345 : Blo 1655527 3536345 := bstep (se 2 (by rfl) ⟨1326129, by rfl⟩ : syracuseStep 3536345 = 2652259) B2652259
theorem B27227609 : Blo 1655527 27227609 := bstep (se 2 (by rfl) ⟨10210353, by rfl⟩ : syracuseStep 27227609 = 20420707) B20420707
theorem B10618775 : Blo 1655527 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B3978803 : Blo 1655527 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B4716083 : Blo 1655527 4716083 := bstep (se 1 (by rfl) ⟨3537062, by rfl⟩ : syracuseStep 4716083 = 7074125) B7074125
theorem B6288947 : Blo 1655527 6288947 := bstep (se 1 (by rfl) ⟨4716710, by rfl⟩ : syracuseStep 6288947 = 9433421) B9433421
theorem B6288961 : Blo 1655527 6288961 := bstep (se 2 (by rfl) ⟨2358360, by rfl⟩ : syracuseStep 6288961 = 4716721) B4716721
theorem B4716107 : Blo 1655527 4716107 := bstep (se 1 (by rfl) ⟨3537080, by rfl⟩ : syracuseStep 4716107 = 7074161) B7074161
theorem B13620887 : Blo 1655527 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B5592779 : Blo 1655527 5592779 := bstep (se 1 (by rfl) ⟨4194584, by rfl⟩ : syracuseStep 5592779 = 8389169) B8389169
theorem B6715153 : Blo 1655527 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B3725081 : Blo 1655527 3725081 := bstep (se 2 (by rfl) ⟨1396905, by rfl⟩ : syracuseStep 3725081 = 2793811) B2793811
theorem B21239597 : Blo 1655527 21239597 := bstep (se 3 (by rfl) ⟨3982424, by rfl⟩ : syracuseStep 21239597 = 7964849) B7964849
theorem B3725171 : Blo 1655527 3725171 := bstep (se 1 (by rfl) ⟨2793878, by rfl⟩ : syracuseStep 3725171 = 5587757) B5587757
theorem B3143539 : Blo 1655527 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B3725207 : Blo 1655527 3725207 := bstep (se 1 (by rfl) ⟨2793905, by rfl⟩ : syracuseStep 3725207 = 5587811) B5587811
theorem B5593049 : Blo 1655527 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B8386577 : Blo 1655527 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B4192307 : Blo 1655527 4192307 := bstep (se 1 (by rfl) ⟨3144230, by rfl⟩ : syracuseStep 4192307 = 6288461) B6288461
theorem B3725387 : Blo 1655527 3725387 := bstep (se 1 (by rfl) ⟨2794040, by rfl⟩ : syracuseStep 3725387 = 5588081) B5588081
theorem B3143767 : Blo 1655527 3143767 := bstep (se 1 (by rfl) ⟨2357825, by rfl⟩ : syracuseStep 3143767 = 4715651) B4715651
theorem B3725441 : Blo 1655527 3725441 := bstep (se 2 (by rfl) ⟨1397040, by rfl⟩ : syracuseStep 3725441 = 2794081) B2794081
theorem B6715543 : Blo 1655527 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B8386739 : Blo 1655527 8386739 := bstep (se 1 (by rfl) ⟨6290054, by rfl⟩ : syracuseStep 8386739 = 12580109) B12580109
theorem B3143873 : Blo 1655527 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B12581081 : Blo 1655527 12581081 := bstep (se 2 (by rfl) ⟨4717905, by rfl⟩ : syracuseStep 12581081 = 9435811) B9435811
theorem B3979543 : Blo 1655527 3979543 := bstep (se 1 (by rfl) ⟨2984657, by rfl⟩ : syracuseStep 3979543 = 5969315) B5969315
theorem B3725657 : Blo 1655527 3725657 := bstep (se 2 (by rfl) ⟨1397121, by rfl⟩ : syracuseStep 3725657 = 2794243) B2794243
theorem B3144025 : Blo 1655527 3144025 := bstep (se 2 (by rfl) ⟨1179009, by rfl⟩ : syracuseStep 3144025 = 2358019) B2358019
theorem B4716893 : Blo 1655527 4716893 := bstep (se 3 (by rfl) ⟨884417, by rfl⟩ : syracuseStep 4716893 = 1768835) B1768835
theorem B3725747 : Blo 1655527 3725747 := bstep (se 1 (by rfl) ⟨2794310, by rfl⟩ : syracuseStep 3725747 = 5588621) B5588621
theorem B3725783 : Blo 1655527 3725783 := bstep (se 1 (by rfl) ⟨2794337, by rfl⟩ : syracuseStep 3725783 = 5588675) B5588675
theorem B2095627 : Blo 1655527 2095627 := bstep (se 1 (by rfl) ⟨1571720, by rfl⟩ : syracuseStep 2095627 = 3143441) B3143441
theorem B4192843 : Blo 1655527 4192843 := bstep (se 1 (by rfl) ⟨3144632, by rfl⟩ : syracuseStep 4192843 = 6289265) B6289265
theorem B3725963 : Blo 1655527 3725963 := bstep (se 1 (by rfl) ⟨2794472, by rfl⟩ : syracuseStep 3725963 = 5588945) B5588945
theorem B1768087 : Blo 1655527 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B10074775 : Blo 1655527 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B5593751 : Blo 1655527 5593751 := bstep (se 1 (by rfl) ⟨4195313, by rfl⟩ : syracuseStep 5593751 = 8390627) B8390627
theorem B3726017 : Blo 1655527 3726017 := bstep (se 2 (by rfl) ⟨1397256, by rfl⟩ : syracuseStep 3726017 = 2794513) B2794513
theorem B4192985 : Blo 1655527 4192985 := bstep (se 2 (by rfl) ⟨1572369, by rfl⟩ : syracuseStep 4192985 = 3144739) B3144739
theorem B4479709 : Blo 1655527 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B2095895 : Blo 1655527 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B1768267 : Blo 1655527 1768267 := bstep (se 1 (by rfl) ⟨1326200, by rfl⟩ : syracuseStep 1768267 = 2652401) B2652401
theorem B2653067 : Blo 1655527 2653067 := bstep (se 1 (by rfl) ⟨1989800, by rfl⟩ : syracuseStep 2653067 = 3979601) B3979601
theorem B2653079 : Blo 1655527 2653079 := bstep (se 1 (by rfl) ⟨1989809, by rfl⟩ : syracuseStep 2653079 = 3979619) B3979619
theorem B3726233 : Blo 1655527 3726233 := bstep (se 2 (by rfl) ⟨1397337, by rfl⟩ : syracuseStep 3726233 = 2794675) B2794675
theorem B21527513 : Blo 1655527 21527513 := bstep (se 2 (by rfl) ⟨8072817, by rfl⟩ : syracuseStep 21527513 = 16145635) B16145635
theorem B3726323 : Blo 1655527 3726323 := bstep (se 1 (by rfl) ⟨2794742, by rfl⟩ : syracuseStep 3726323 = 5589485) B5589485
theorem B3726359 : Blo 1655527 3726359 := bstep (se 1 (by rfl) ⟨2794769, by rfl⟩ : syracuseStep 3726359 = 5589539) B5589539
theorem B3726539 : Blo 1655527 3726539 := bstep (se 1 (by rfl) ⟨2794904, by rfl⟩ : syracuseStep 3726539 = 5589809) B5589809
theorem B3726593 : Blo 1655527 3726593 := bstep (se 2 (by rfl) ⟨1397472, by rfl⟩ : syracuseStep 3726593 = 2794945) B2794945
theorem B13434263 : Blo 1655527 13434263 := bstep (se 1 (by rfl) ⟨10075697, by rfl⟩ : syracuseStep 13434263 = 20151395) B20151395
theorem B8068531 : Blo 1655527 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B3538379 : Blo 1655527 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B6290891 : Blo 1655527 6290891 := bstep (se 1 (by rfl) ⟨4718168, by rfl⟩ : syracuseStep 6290891 = 9436337) B9436337
theorem B2096599 : Blo 1655527 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B3726809 : Blo 1655527 3726809 := bstep (se 2 (by rfl) ⟨1397553, by rfl⟩ : syracuseStep 3726809 = 2795107) B2795107
theorem B6290905 : Blo 1655527 6290905 := bstep (se 2 (by rfl) ⟨2359089, by rfl⟩ : syracuseStep 6290905 = 4718179) B4718179
theorem B4193815 : Blo 1655527 4193815 := bstep (se 1 (by rfl) ⟨3145361, by rfl⟩ : syracuseStep 4193815 = 6290723) B6290723
theorem B3726899 : Blo 1655527 3726899 := bstep (se 1 (by rfl) ⟨2795174, by rfl⟩ : syracuseStep 3726899 = 5590349) B5590349
theorem B2653771 : Blo 1655527 2653771 := bstep (se 1 (by rfl) ⟨1990328, by rfl⟩ : syracuseStep 2653771 = 3980657) B3980657
theorem B3726935 : Blo 1655527 3726935 := bstep (se 1 (by rfl) ⟨2795201, by rfl⟩ : syracuseStep 3726935 = 5590403) B5590403
theorem B14155357 : Blo 1655527 14155357 := bstep (se 3 (by rfl) ⟨2654129, by rfl⟩ : syracuseStep 14155357 = 5308259) B5308259
theorem B3145331 : Blo 1655527 3145331 := bstep (se 1 (by rfl) ⟨2358998, by rfl⟩ : syracuseStep 3145331 = 4717997) B4717997
theorem B5308055 : Blo 1655527 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B7077527 : Blo 1655527 7077527 := bstep (se 1 (by rfl) ⟨5308145, by rfl⟩ : syracuseStep 7077527 = 10616291) B10616291
theorem B3727115 : Blo 1655527 3727115 := bstep (se 1 (by rfl) ⟨2795336, by rfl⟩ : syracuseStep 3727115 = 5590673) B5590673
theorem B3145483 : Blo 1655527 3145483 := bstep (se 1 (by rfl) ⟨2359112, by rfl⟩ : syracuseStep 3145483 = 4718225) B4718225
theorem B5308183 : Blo 1655527 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B5971735 : Blo 1655527 5971735 := bstep (se 1 (by rfl) ⟨4478801, by rfl⟩ : syracuseStep 5971735 = 8957603) B8957603
theorem B3727169 : Blo 1655527 3727169 := bstep (se 2 (by rfl) ⟨1397688, by rfl⟩ : syracuseStep 3727169 = 2795377) B2795377
theorem B2654041 : Blo 1655527 2654041 := bstep (se 2 (by rfl) ⟨995265, by rfl⟩ : syracuseStep 2654041 = 1990531) B1990531
theorem B4194251 : Blo 1655527 4194251 := bstep (se 1 (by rfl) ⟨3145688, by rfl⟩ : syracuseStep 4194251 = 6291377) B6291377
theorem B3727403 : Blo 1655527 3727403 := bstep (se 1 (by rfl) ⟨2795552, by rfl⟩ : syracuseStep 3727403 = 5591105) B5591105
theorem B3145787 : Blo 1655527 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B1769531 : Blo 1655527 1769531 := bstep (se 1 (by rfl) ⟨1327148, by rfl⟩ : syracuseStep 1769531 = 2654297) B2654297
theorem B10608727 : Blo 1655527 10608727 := bstep (se 1 (by rfl) ⟨7956545, by rfl⟩ : syracuseStep 10608727 = 15913091) B15913091
theorem B8954057 : Blo 1655527 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B8388845 : Blo 1655527 8388845 := bstep (se 3 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 8388845 = 3145817) B3145817
theorem B4194575 : Blo 1655527 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B3727763 : Blo 1655527 3727763 := bstep (se 1 (by rfl) ⟨2795822, by rfl⟩ : syracuseStep 3727763 = 5591645) B5591645
theorem B2359739 : Blo 1655527 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B3727817 : Blo 1655527 3727817 := bstep (se 2 (by rfl) ⟨1397931, by rfl⟩ : syracuseStep 3727817 = 2795863) B2795863
theorem B3146273 : Blo 1655527 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B2794027 : Blo 1655527 2794027 := bstep (se 1 (by rfl) ⟨2095520, by rfl⟩ : syracuseStep 2794027 = 4191041) B4191041
theorem B2794169 : Blo 1655527 2794169 := bstep (se 2 (by rfl) ⟨1047813, by rfl⟩ : syracuseStep 2794169 = 2095627) B2095627
theorem B1655559 : Blo 1655527 1655559 := bstep (se 1 (by rfl) ⟨1241669, by rfl⟩ : syracuseStep 1655559 = 2483339) B2483339
theorem B1655567 : Blo 1655527 1655567 := bstep (se 1 (by rfl) ⟨1241675, by rfl⟩ : syracuseStep 1655567 = 2483351) B2483351
theorem B9429797 : Blo 1655527 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B3146539 : Blo 1655527 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B1655611 : Blo 1655527 1655611 := bstep (se 1 (by rfl) ⟨1241708, by rfl⟩ : syracuseStep 1655611 = 2483417) B2483417
theorem B1655687 : Blo 1655527 1655687 := bstep (se 1 (by rfl) ⟨1241765, by rfl⟩ : syracuseStep 1655687 = 2483531) B2483531
theorem B1655695 : Blo 1655527 1655695 := bstep (se 1 (by rfl) ⟨1241771, by rfl⟩ : syracuseStep 1655695 = 2483543) B2483543
theorem B5587865 : Blo 1655527 5587865 := bstep (se 2 (by rfl) ⟨2095449, by rfl⟩ : syracuseStep 5587865 = 4190899) B4190899
theorem B1655739 : Blo 1655527 1655739 := bstep (se 1 (by rfl) ⟨1241804, by rfl⟩ : syracuseStep 1655739 = 2483609) B2483609
theorem B4195273 : Blo 1655527 4195273 := bstep (se 2 (by rfl) ⟨1573227, by rfl⟩ : syracuseStep 4195273 = 3146455) B3146455
theorem B10617803 : Blo 1655527 10617803 := bstep (se 1 (by rfl) ⟨7963352, by rfl⟩ : syracuseStep 10617803 = 15926705) B15926705
theorem B8381393 : Blo 1655527 8381393 := bstep (se 2 (by rfl) ⟨3143022, by rfl⟩ : syracuseStep 8381393 = 6286045) B6286045
theorem B5972945 : Blo 1655527 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B1655815 : Blo 1655527 1655815 := bstep (se 1 (by rfl) ⟨1241861, by rfl⟩ : syracuseStep 1655815 = 2483723) B2483723
theorem B1655823 : Blo 1655527 1655823 := bstep (se 1 (by rfl) ⟨1241867, by rfl⟩ : syracuseStep 1655823 = 2483735) B2483735
theorem B8389655 : Blo 1655527 8389655 := bstep (se 1 (by rfl) ⟨6292241, by rfl⟩ : syracuseStep 8389655 = 12584483) B12584483
theorem B1655867 : Blo 1655527 1655867 := bstep (se 1 (by rfl) ⟨1241900, by rfl⟩ : syracuseStep 1655867 = 2483801) B2483801
theorem B12583997 : Blo 1655527 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B4195415 : Blo 1655527 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B1655943 : Blo 1655527 1655943 := bstep (se 1 (by rfl) ⟨1241957, by rfl⟩ : syracuseStep 1655943 = 2483915) B2483915
theorem B3728519 : Blo 1655527 3728519 := bstep (se 1 (by rfl) ⟨2796389, by rfl⟩ : syracuseStep 3728519 = 5592779) B5592779
theorem B1655951 : Blo 1655527 1655951 := bstep (se 1 (by rfl) ⟨1241963, by rfl⟩ : syracuseStep 1655951 = 2483927) B2483927
theorem B2483387 : Blo 1655527 2483387 := bstep (se 1 (by rfl) ⟨1862540, by rfl⟩ : syracuseStep 2483387 = 3725081) B3725081
theorem B1655995 : Blo 1655527 1655995 := bstep (se 1 (by rfl) ⟨1241996, by rfl⟩ : syracuseStep 1655995 = 2483993) B2483993
theorem B9077953 : Blo 1655527 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B9430253 : Blo 1655527 9430253 := bstep (se 3 (by rfl) ⟨1768172, by rfl⟩ : syracuseStep 9430253 = 3536345) B3536345
theorem B2483447 : Blo 1655527 2483447 := bstep (se 1 (by rfl) ⟨1862585, by rfl⟩ : syracuseStep 2483447 = 3725171) B3725171
theorem B1656071 : Blo 1655527 1656071 := bstep (se 1 (by rfl) ⟨1242053, by rfl⟩ : syracuseStep 1656071 = 2484107) B2484107
theorem B2483471 : Blo 1655527 2483471 := bstep (se 1 (by rfl) ⟨1862603, by rfl⟩ : syracuseStep 2483471 = 3725207) B3725207
theorem B1656079 : Blo 1655527 1656079 := bstep (se 1 (by rfl) ⟨1242059, by rfl⟩ : syracuseStep 1656079 = 2484119) B2484119
theorem B7079183 : Blo 1655527 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B2483513 : Blo 1655527 2483513 := bstep (se 2 (by rfl) ⟨931317, by rfl⟩ : syracuseStep 2483513 = 1862635) B1862635
theorem B1656123 : Blo 1655527 1656123 := bstep (se 1 (by rfl) ⟨1242092, by rfl⟩ : syracuseStep 1656123 = 2484185) B2484185
theorem B3728699 : Blo 1655527 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B2794871 : Blo 1655527 2794871 := bstep (se 1 (by rfl) ⟨2096153, by rfl⟩ : syracuseStep 2794871 = 4192307) B4192307
theorem B4719991 : Blo 1655527 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B2483591 : Blo 1655527 2483591 := bstep (se 1 (by rfl) ⟨1862693, by rfl⟩ : syracuseStep 2483591 = 3725387) B3725387
theorem B1656199 : Blo 1655527 1656199 := bstep (se 1 (by rfl) ⟨1242149, by rfl⟩ : syracuseStep 1656199 = 2484299) B2484299
theorem B1656207 : Blo 1655527 1656207 := bstep (se 1 (by rfl) ⟨1242155, by rfl⟩ : syracuseStep 1656207 = 2484311) B2484311
theorem B5309849 : Blo 1655527 5309849 := bstep (se 2 (by rfl) ⟨1991193, by rfl⟩ : syracuseStep 5309849 = 3982387) B3982387
theorem B4720025 : Blo 1655527 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B2483627 : Blo 1655527 2483627 := bstep (se 1 (by rfl) ⟨1862720, by rfl⟩ : syracuseStep 2483627 = 3725441) B3725441
theorem B26854841 : Blo 1655527 26854841 := bstep (se 2 (by rfl) ⟨10070565, by rfl⟩ : syracuseStep 26854841 = 20141131) B20141131
theorem B1656251 : Blo 1655527 1656251 := bstep (se 1 (by rfl) ⟨1242188, by rfl⟩ : syracuseStep 1656251 = 2484377) B2484377
theorem B3728825 : Blo 1655527 3728825 := bstep (se 2 (by rfl) ⟨1398309, by rfl⟩ : syracuseStep 3728825 = 2796619) B2796619
theorem B2483657 : Blo 1655527 2483657 := bstep (se 2 (by rfl) ⟨931371, by rfl⟩ : syracuseStep 2483657 = 1862743) B1862743
theorem B12576221 : Blo 1655527 12576221 := bstep (se 3 (by rfl) ⟨2358041, by rfl⟩ : syracuseStep 12576221 = 4716083) B4716083
theorem B1656327 : Blo 1655527 1656327 := bstep (se 1 (by rfl) ⟨1242245, by rfl⟩ : syracuseStep 1656327 = 2484491) B2484491
theorem B1656335 : Blo 1655527 1656335 := bstep (se 1 (by rfl) ⟨1242251, by rfl⟩ : syracuseStep 1656335 = 2484503) B2484503
theorem B14157341 : Blo 1655527 14157341 := bstep (se 3 (by rfl) ⟨2654501, by rfl⟩ : syracuseStep 14157341 = 5309003) B5309003
theorem B2483771 : Blo 1655527 2483771 := bstep (se 1 (by rfl) ⟨1862828, by rfl⟩ : syracuseStep 2483771 = 3725657) B3725657
theorem B1656379 : Blo 1655527 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B5588567 : Blo 1655527 5588567 := bstep (se 1 (by rfl) ⟨4191425, by rfl⟩ : syracuseStep 5588567 = 8382851) B8382851
theorem B2483831 : Blo 1655527 2483831 := bstep (se 1 (by rfl) ⟨1862873, by rfl⟩ : syracuseStep 2483831 = 3725747) B3725747
theorem B1656455 : Blo 1655527 1656455 := bstep (se 1 (by rfl) ⟨1242341, by rfl⟩ : syracuseStep 1656455 = 2484683) B2484683
theorem B2483855 : Blo 1655527 2483855 := bstep (se 1 (by rfl) ⟨1862891, by rfl⟩ : syracuseStep 2483855 = 3725783) B3725783
theorem B1656463 : Blo 1655527 1656463 := bstep (se 1 (by rfl) ⟨1242347, by rfl⟩ : syracuseStep 1656463 = 2484695) B2484695
theorem B2483897 : Blo 1655527 2483897 := bstep (se 2 (by rfl) ⟨931461, by rfl⟩ : syracuseStep 2483897 = 1862923) B1862923
theorem B1656507 : Blo 1655527 1656507 := bstep (se 1 (by rfl) ⟨1242380, by rfl⟩ : syracuseStep 1656507 = 2484761) B2484761
theorem B2483975 : Blo 1655527 2483975 := bstep (se 1 (by rfl) ⟨1862981, by rfl⟩ : syracuseStep 2483975 = 3725963) B3725963
theorem B1656583 : Blo 1655527 1656583 := bstep (se 1 (by rfl) ⟨1242437, by rfl⟩ : syracuseStep 1656583 = 2484875) B2484875
theorem B1656591 : Blo 1655527 1656591 := bstep (se 1 (by rfl) ⟨1242443, by rfl⟩ : syracuseStep 1656591 = 2484887) B2484887
theorem B3729167 : Blo 1655527 3729167 := bstep (se 1 (by rfl) ⟨2796875, by rfl⟩ : syracuseStep 3729167 = 5593751) B5593751
theorem B3729185 : Blo 1655527 3729185 := bstep (se 2 (by rfl) ⟨1398444, by rfl⟩ : syracuseStep 3729185 = 2796889) B2796889
theorem B2484011 : Blo 1655527 2484011 := bstep (se 1 (by rfl) ⟨1863008, by rfl⟩ : syracuseStep 2484011 = 3726017) B3726017
theorem B2795323 : Blo 1655527 2795323 := bstep (se 1 (by rfl) ⟨2096492, by rfl⟩ : syracuseStep 2795323 = 4192985) B4192985
theorem B1656635 : Blo 1655527 1656635 := bstep (se 1 (by rfl) ⟨1242476, by rfl⟩ : syracuseStep 1656635 = 2484953) B2484953
theorem B2484041 : Blo 1655527 2484041 := bstep (se 2 (by rfl) ⟨931515, by rfl⟩ : syracuseStep 2484041 = 1863031) B1863031
theorem B1656711 : Blo 1655527 1656711 := bstep (se 1 (by rfl) ⟨1242533, by rfl⟩ : syracuseStep 1656711 = 2485067) B2485067
theorem B1656719 : Blo 1655527 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B9430937 : Blo 1655527 9430937 := bstep (se 2 (by rfl) ⟨3536601, by rfl⟩ : syracuseStep 9430937 = 7073203) B7073203
theorem B10758041 : Blo 1655527 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B2484155 : Blo 1655527 2484155 := bstep (se 1 (by rfl) ⟨1863116, by rfl⟩ : syracuseStep 2484155 = 3726233) B3726233
theorem B1656763 : Blo 1655527 1656763 := bstep (se 1 (by rfl) ⟨1242572, by rfl⟩ : syracuseStep 1656763 = 2485145) B2485145
theorem B2795465 : Blo 1655527 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B2484215 : Blo 1655527 2484215 := bstep (se 1 (by rfl) ⟨1863161, by rfl⟩ : syracuseStep 2484215 = 3726323) B3726323
theorem B1656839 : Blo 1655527 1656839 := bstep (se 1 (by rfl) ⟨1242629, by rfl⟩ : syracuseStep 1656839 = 2485259) B2485259
theorem B2484239 : Blo 1655527 2484239 := bstep (se 1 (by rfl) ⟨1863179, by rfl⟩ : syracuseStep 2484239 = 3726359) B3726359
theorem B1656847 : Blo 1655527 1656847 := bstep (se 1 (by rfl) ⟨1242635, by rfl⟩ : syracuseStep 1656847 = 2485271) B2485271
theorem B2484281 : Blo 1655527 2484281 := bstep (se 2 (by rfl) ⟨931605, by rfl⟩ : syracuseStep 2484281 = 1863211) B1863211
theorem B1656891 : Blo 1655527 1656891 := bstep (se 1 (by rfl) ⟨1242668, by rfl⟩ : syracuseStep 1656891 = 2485337) B2485337
theorem B5589053 : Blo 1655527 5589053 := bstep (se 3 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 5589053 = 2095895) B2095895
theorem B2484359 : Blo 1655527 2484359 := bstep (se 1 (by rfl) ⟨1863269, by rfl⟩ : syracuseStep 2484359 = 3726539) B3726539
theorem B1656967 : Blo 1655527 1656967 := bstep (se 1 (by rfl) ⟨1242725, by rfl⟩ : syracuseStep 1656967 = 2485451) B2485451
theorem B1656975 : Blo 1655527 1656975 := bstep (se 1 (by rfl) ⟨1242731, by rfl⟩ : syracuseStep 1656975 = 2485463) B2485463
theorem B2484395 : Blo 1655527 2484395 := bstep (se 1 (by rfl) ⟨1863296, by rfl⟩ : syracuseStep 2484395 = 3726593) B3726593
theorem B1657019 : Blo 1655527 1657019 := bstep (se 1 (by rfl) ⟨1242764, by rfl⟩ : syracuseStep 1657019 = 2485529) B2485529
theorem B2484425 : Blo 1655527 2484425 := bstep (se 2 (by rfl) ⟨931659, by rfl⟩ : syracuseStep 2484425 = 1863319) B1863319
theorem B1657095 : Blo 1655527 1657095 := bstep (se 1 (by rfl) ⟨1242821, by rfl⟩ : syracuseStep 1657095 = 2485643) B2485643
theorem B8956175 : Blo 1655527 8956175 := bstep (se 1 (by rfl) ⟨6717131, by rfl⟩ : syracuseStep 8956175 = 13434263) B13434263
theorem B1657103 : Blo 1655527 1657103 := bstep (se 1 (by rfl) ⟨1242827, by rfl⟩ : syracuseStep 1657103 = 2485655) B2485655
theorem B2484539 : Blo 1655527 2484539 := bstep (se 1 (by rfl) ⟨1863404, by rfl⟩ : syracuseStep 2484539 = 3726809) B3726809
theorem B1657147 : Blo 1655527 1657147 := bstep (se 1 (by rfl) ⟨1242860, by rfl⟩ : syracuseStep 1657147 = 2485721) B2485721
theorem B2484599 : Blo 1655527 2484599 := bstep (se 1 (by rfl) ⟨1863449, by rfl⟩ : syracuseStep 2484599 = 3726899) B3726899
theorem B1657223 : Blo 1655527 1657223 := bstep (se 1 (by rfl) ⟨1242917, by rfl⟩ : syracuseStep 1657223 = 2485835) B2485835
theorem B2484623 : Blo 1655527 2484623 := bstep (se 1 (by rfl) ⟨1863467, by rfl⟩ : syracuseStep 2484623 = 3726935) B3726935
theorem B1657231 : Blo 1655527 1657231 := bstep (se 1 (by rfl) ⟨1242923, by rfl⟩ : syracuseStep 1657231 = 2485847) B2485847
theorem B2484665 : Blo 1655527 2484665 := bstep (se 2 (by rfl) ⟨931749, by rfl⟩ : syracuseStep 2484665 = 1863499) B1863499
theorem B1657275 : Blo 1655527 1657275 := bstep (se 1 (by rfl) ⟨1242956, by rfl⟩ : syracuseStep 1657275 = 2485913) B2485913
theorem B2484743 : Blo 1655527 2484743 := bstep (se 1 (by rfl) ⟨1863557, by rfl⟩ : syracuseStep 2484743 = 3727115) B3727115
theorem B1657351 : Blo 1655527 1657351 := bstep (se 1 (by rfl) ⟨1243013, by rfl⟩ : syracuseStep 1657351 = 2486027) B2486027
theorem B1657359 : Blo 1655527 1657359 := bstep (se 1 (by rfl) ⟨1243019, by rfl⟩ : syracuseStep 1657359 = 2486039) B2486039
theorem B2484779 : Blo 1655527 2484779 := bstep (se 1 (by rfl) ⟨1863584, by rfl⟩ : syracuseStep 2484779 = 3727169) B3727169
theorem B1657403 : Blo 1655527 1657403 := bstep (se 1 (by rfl) ⟨1243052, by rfl⟩ : syracuseStep 1657403 = 2486105) B2486105
theorem B2484809 : Blo 1655527 2484809 := bstep (se 2 (by rfl) ⟨931803, by rfl⟩ : syracuseStep 2484809 = 1863607) B1863607
theorem B2796167 : Blo 1655527 2796167 := bstep (se 1 (by rfl) ⟨2097125, by rfl⟩ : syracuseStep 2796167 = 4194251) B4194251
theorem B1657479 : Blo 1655527 1657479 := bstep (se 1 (by rfl) ⟨1243109, by rfl⟩ : syracuseStep 1657479 = 2486219) B2486219
theorem B1657487 : Blo 1655527 1657487 := bstep (se 1 (by rfl) ⟨1243115, by rfl⟩ : syracuseStep 1657487 = 2486231) B2486231
theorem B2484923 : Blo 1655527 2484923 := bstep (se 1 (by rfl) ⟨1863692, by rfl⟩ : syracuseStep 2484923 = 3727385) B3727385
theorem B2484983 : Blo 1655527 2484983 := bstep (se 1 (by rfl) ⟨1863737, by rfl⟩ : syracuseStep 2484983 = 3727475) B3727475
theorem B2485007 : Blo 1655527 2485007 := bstep (se 1 (by rfl) ⟨1863755, by rfl⟩ : syracuseStep 2485007 = 3727511) B3727511
theorem B20155187 : Blo 1655527 20155187 := bstep (se 1 (by rfl) ⟨15116390, by rfl⟩ : syracuseStep 20155187 = 30232781) B30232781
theorem B2485049 : Blo 1655527 2485049 := bstep (se 2 (by rfl) ⟨931893, by rfl⟩ : syracuseStep 2485049 = 1863787) B1863787
theorem B2485127 : Blo 1655527 2485127 := bstep (se 1 (by rfl) ⟨1863845, by rfl⟩ : syracuseStep 2485127 = 3727691) B3727691
theorem B2485163 : Blo 1655527 2485163 := bstep (se 1 (by rfl) ⟨1863872, by rfl⟩ : syracuseStep 2485163 = 3727745) B3727745
theorem B2485193 : Blo 1655527 2485193 := bstep (se 2 (by rfl) ⟨931947, by rfl⟩ : syracuseStep 2485193 = 1863895) B1863895
theorem B8383499 : Blo 1655527 8383499 := bstep (se 1 (by rfl) ⟨6287624, by rfl⟩ : syracuseStep 8383499 = 12575249) B12575249
theorem B1862671 : Blo 1655527 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B2518031 : Blo 1655527 2518031 := bstep (se 1 (by rfl) ⟨1888523, by rfl⟩ : syracuseStep 2518031 = 3777047) B3777047
theorem B16133165 : Blo 1655527 16133165 := bstep (se 3 (by rfl) ⟨3024968, by rfl⟩ : syracuseStep 16133165 = 6049937) B6049937
theorem B2485307 : Blo 1655527 2485307 := bstep (se 1 (by rfl) ⟨1863980, by rfl⟩ : syracuseStep 2485307 = 3727961) B3727961
theorem B2485367 : Blo 1655527 2485367 := bstep (se 1 (by rfl) ⟨1864025, by rfl⟩ : syracuseStep 2485367 = 3728051) B3728051
theorem B2485391 : Blo 1655527 2485391 := bstep (se 1 (by rfl) ⟨1864043, by rfl⟩ : syracuseStep 2485391 = 3728087) B3728087
theorem B8383661 : Blo 1655527 8383661 := bstep (se 3 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 8383661 = 3143873) B3143873
theorem B2485433 : Blo 1655527 2485433 := bstep (se 2 (by rfl) ⟨932037, by rfl⟩ : syracuseStep 2485433 = 1864075) B1864075
theorem B2485511 : Blo 1655527 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B2796815 : Blo 1655527 2796815 := bstep (se 1 (by rfl) ⟨2097611, by rfl⟩ : syracuseStep 2796815 = 4195223) B4195223
theorem B2485547 : Blo 1655527 2485547 := bstep (se 1 (by rfl) ⟨1864160, by rfl⟩ : syracuseStep 2485547 = 3728321) B3728321
theorem B2485577 : Blo 1655527 2485577 := bstep (se 2 (by rfl) ⟨932091, by rfl⟩ : syracuseStep 2485577 = 1864183) B1864183
theorem B5590457 : Blo 1655527 5590457 := bstep (se 2 (by rfl) ⟨2096421, by rfl⟩ : syracuseStep 5590457 = 4192843) B4192843
theorem B2485691 : Blo 1655527 2485691 := bstep (se 1 (by rfl) ⟨1864268, by rfl⟩ : syracuseStep 2485691 = 3728537) B3728537
theorem B2485751 : Blo 1655527 2485751 := bstep (se 1 (by rfl) ⟨1864313, by rfl⟩ : syracuseStep 2485751 = 3728627) B3728627
theorem B1863175 : Blo 1655527 1863175 := bstep (se 1 (by rfl) ⟨1397381, by rfl⟩ : syracuseStep 1863175 = 2794763) B2794763
theorem B2485775 : Blo 1655527 2485775 := bstep (se 1 (by rfl) ⟨1864331, by rfl⟩ : syracuseStep 2485775 = 3728663) B3728663
theorem B2485817 : Blo 1655527 2485817 := bstep (se 2 (by rfl) ⟨932181, by rfl⟩ : syracuseStep 2485817 = 1864363) B1864363
theorem B7958083 : Blo 1655527 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B80612957 : Blo 1655527 80612957 := bstep (se 3 (by rfl) ⟨15114929, by rfl⟩ : syracuseStep 80612957 = 30229859) B30229859
theorem B2485895 : Blo 1655527 2485895 := bstep (se 1 (by rfl) ⟨1864421, by rfl⟩ : syracuseStep 2485895 = 3728843) B3728843
theorem B2485931 : Blo 1655527 2485931 := bstep (se 1 (by rfl) ⟨1864448, by rfl⟩ : syracuseStep 2485931 = 3728897) B3728897
theorem B21507763 : Blo 1655527 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B1863355 : Blo 1655527 1863355 := bstep (se 1 (by rfl) ⟨1397516, by rfl⟩ : syracuseStep 1863355 = 2795033) B2795033
theorem B2485961 : Blo 1655527 2485961 := bstep (se 2 (by rfl) ⟨932235, by rfl⟩ : syracuseStep 2485961 = 1864471) B1864471
theorem B10071809 : Blo 1655527 10071809 := bstep (se 2 (by rfl) ⟨3776928, by rfl⟩ : syracuseStep 10071809 = 7553857) B7553857
theorem B9080591 : Blo 1655527 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B2486075 : Blo 1655527 2486075 := bstep (se 1 (by rfl) ⟨1864556, by rfl⟩ : syracuseStep 2486075 = 3729113) B3729113
theorem B5107571 : Blo 1655527 5107571 := bstep (se 1 (by rfl) ⟨3830678, by rfl⟩ : syracuseStep 5107571 = 7661357) B7661357
theorem B14159731 : Blo 1655527 14159731 := bstep (se 1 (by rfl) ⟨10619798, by rfl⟩ : syracuseStep 14159731 = 21239597) B21239597
theorem B2486135 : Blo 1655527 2486135 := bstep (se 1 (by rfl) ⟨1864601, by rfl⟩ : syracuseStep 2486135 = 3729203) B3729203
theorem B4714375 : Blo 1655527 4714375 := bstep (se 1 (by rfl) ⟨3535781, by rfl⟩ : syracuseStep 4714375 = 7071563) B7071563
theorem B2486159 : Blo 1655527 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B2486201 : Blo 1655527 2486201 := bstep (se 2 (by rfl) ⟨932325, by rfl⟩ : syracuseStep 2486201 = 1864651) B1864651
theorem B2486279 : Blo 1655527 2486279 := bstep (se 1 (by rfl) ⟨1864709, by rfl⟩ : syracuseStep 2486279 = 3729419) B3729419
theorem B5591051 : Blo 1655527 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B2125867 : Blo 1655527 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B5591159 : Blo 1655527 5591159 := bstep (se 1 (by rfl) ⟨4193369, by rfl⟩ : syracuseStep 5591159 = 8386739) B8386739
theorem B14160005 : Blo 1655527 14160005 := bstep (se 4 (by rfl) ⟨1327500, by rfl⟩ : syracuseStep 14160005 = 2655001) B2655001
theorem B3584135 : Blo 1655527 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B1863823 : Blo 1655527 1863823 := bstep (se 1 (by rfl) ⟨1397867, by rfl⟩ : syracuseStep 1863823 = 2795735) B2795735
theorem B4714649 : Blo 1655527 4714649 := bstep (se 2 (by rfl) ⟨1767993, by rfl⟩ : syracuseStep 4714649 = 3535987) B3535987
theorem B3584299 : Blo 1655527 3584299 := bstep (se 1 (by rfl) ⟨2688224, by rfl⟩ : syracuseStep 3584299 = 5376449) B5376449
theorem B3027335 : Blo 1655527 3027335 := bstep (se 1 (by rfl) ⟨2270501, by rfl⟩ : syracuseStep 3027335 = 4541003) B4541003
theorem B1864327 : Blo 1655527 1864327 := bstep (se 1 (by rfl) ⟨1398245, by rfl⟩ : syracuseStep 1864327 = 2796491) B2796491
theorem B5591753 : Blo 1655527 5591753 := bstep (se 2 (by rfl) ⟨2096907, by rfl⟩ : syracuseStep 5591753 = 4193815) B4193815
theorem B8385281 : Blo 1655527 8385281 := bstep (se 2 (by rfl) ⟨3144480, by rfl⟩ : syracuseStep 8385281 = 6288961) B6288961
theorem B1864507 : Blo 1655527 1864507 := bstep (se 1 (by rfl) ⟨1398380, by rfl⟩ : syracuseStep 1864507 = 2796761) B2796761
theorem B3978119 : Blo 1655527 3978119 := bstep (se 1 (by rfl) ⟨2983589, by rfl⟩ : syracuseStep 3978119 = 5967179) B5967179
theorem B6288263 : Blo 1655527 6288263 := bstep (se 1 (by rfl) ⟨4716197, by rfl⟩ : syracuseStep 6288263 = 9432395) B9432395
theorem B10073117 : Blo 1655527 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B7074877 : Blo 1655527 7074877 := bstep (se 3 (by rfl) ⟨1326539, by rfl⟩ : syracuseStep 7074877 = 2653079) B2653079
theorem B4191385 : Blo 1655527 4191385 := bstep (se 2 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 4191385 = 3143539) B3143539
theorem B8959247 : Blo 1655527 8959247 := bstep (se 1 (by rfl) ⟨6719435, by rfl⟩ : syracuseStep 8959247 = 13438871) B13438871
theorem B3142955 : Blo 1655527 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B4191547 : Blo 1655527 4191547 := bstep (se 1 (by rfl) ⟨3143660, by rfl⟩ : syracuseStep 4191547 = 6287321) B6287321
theorem B4715891 : Blo 1655527 4715891 := bstep (se 1 (by rfl) ⟨3536918, by rfl⟩ : syracuseStep 4715891 = 7073837) B7073837
theorem B20428163 : Blo 1655527 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B5592455 : Blo 1655527 5592455 := bstep (se 1 (by rfl) ⟨4194341, by rfl⟩ : syracuseStep 5592455 = 8388683) B8388683
theorem B3978649 : Blo 1655527 3978649 := bstep (se 2 (by rfl) ⟨1491993, by rfl⟩ : syracuseStep 3978649 = 2983987) B2983987
theorem B4191689 : Blo 1655527 4191689 := bstep (se 2 (by rfl) ⟨1571883, by rfl⟩ : syracuseStep 4191689 = 3143767) B3143767
theorem B9434627 : Blo 1655527 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B8386091 : Blo 1655527 8386091 := bstep (se 1 (by rfl) ⟨6289568, by rfl⟩ : syracuseStep 8386091 = 12579137) B12579137
theorem B3978811 : Blo 1655527 3978811 := bstep (se 1 (by rfl) ⟨2984108, by rfl⟩ : syracuseStep 3978811 = 5968217) B5968217
theorem B3356279 : Blo 1655527 3356279 := bstep (se 1 (by rfl) ⟨2517209, by rfl⟩ : syracuseStep 3356279 = 5034419) B5034419
theorem B5306057 : Blo 1655527 5306057 := bstep (se 2 (by rfl) ⟨1989771, by rfl⟩ : syracuseStep 5306057 = 3979543) B3979543
theorem B10073801 : Blo 1655527 10073801 := bstep (se 2 (by rfl) ⟨3777675, by rfl⟩ : syracuseStep 10073801 = 7555351) B7555351
theorem B5592833 : Blo 1655527 5592833 := bstep (se 2 (by rfl) ⟨2097312, by rfl⟩ : syracuseStep 5592833 = 4194625) B4194625
theorem B4192033 : Blo 1655527 4192033 := bstep (se 2 (by rfl) ⟨1572012, by rfl⟩ : syracuseStep 4192033 = 3144025) B3144025
theorem B3725099 : Blo 1655527 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B15324977 : Blo 1655527 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B2652023 : Blo 1655527 2652023 := bstep (se 1 (by rfl) ⟨1989017, by rfl⟩ : syracuseStep 2652023 = 3978035) B3978035
theorem B4782091 : Blo 1655527 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B3725459 : Blo 1655527 3725459 := bstep (se 1 (by rfl) ⟨2794094, by rfl⟩ : syracuseStep 3725459 = 5588189) B5588189
theorem B3725513 : Blo 1655527 3725513 := bstep (se 2 (by rfl) ⟨1397067, by rfl⟩ : syracuseStep 3725513 = 2794135) B2794135
theorem B13433033 : Blo 1655527 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B18151739 : Blo 1655527 18151739 := bstep (se 1 (by rfl) ⟨13613804, by rfl⟩ : syracuseStep 18151739 = 27227609) B27227609
theorem B1988983 : Blo 1655527 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B2652535 : Blo 1655527 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B4192631 : Blo 1655527 4192631 := bstep (se 1 (by rfl) ⟨3144473, by rfl⟩ : syracuseStep 4192631 = 6288947) B6288947
theorem B3144071 : Blo 1655527 3144071 := bstep (se 1 (by rfl) ⟨2358053, by rfl⟩ : syracuseStep 3144071 = 4716107) B4716107
theorem B5970323 : Blo 1655527 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B15112595 : Blo 1655527 15112595 := bstep (se 1 (by rfl) ⟨11334446, by rfl⟩ : syracuseStep 15112595 = 22668893) B22668893
theorem B2357689 : Blo 1655527 2357689 := bstep (se 2 (by rfl) ⟨884133, by rfl⟩ : syracuseStep 2357689 = 1768267) B1768267
theorem B5593643 : Blo 1655527 5593643 := bstep (se 1 (by rfl) ⟨4195232, by rfl⟩ : syracuseStep 5593643 = 8390465) B8390465
theorem B36313667 : Blo 1655527 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B1989367 : Blo 1655527 1989367 := bstep (se 1 (by rfl) ⟨1492025, by rfl⟩ : syracuseStep 1989367 = 2984051) B2984051
theorem B3980033 : Blo 1655527 3980033 := bstep (se 2 (by rfl) ⟨1492512, by rfl⟩ : syracuseStep 3980033 = 2985025) B2985025
theorem B42449669 : Blo 1655527 42449669 := bstep (se 4 (by rfl) ⟨3979656, by rfl⟩ : syracuseStep 42449669 = 7959313) B7959313
theorem B8387387 : Blo 1655527 8387387 := bstep (se 1 (by rfl) ⟨6290540, by rfl⟩ : syracuseStep 8387387 = 12581081) B12581081
theorem B38255449 : Blo 1655527 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B3726215 : Blo 1655527 3726215 := bstep (se 1 (by rfl) ⟨2794661, by rfl⟩ : syracuseStep 3726215 = 5589323) B5589323
theorem B3144595 : Blo 1655527 3144595 := bstep (se 1 (by rfl) ⟨2358446, by rfl⟩ : syracuseStep 3144595 = 4716893) B4716893
theorem B101964707 : Blo 1655527 101964707 := bstep (se 1 (by rfl) ⟨76473530, by rfl⟩ : syracuseStep 101964707 = 152947061) B152947061
theorem B8387549 : Blo 1655527 8387549 := bstep (se 3 (by rfl) ⟨1572665, by rfl⟩ : syracuseStep 8387549 = 3145331) B3145331
theorem B80624645 : Blo 1655527 80624645 := bstep (se 4 (by rfl) ⟨7558560, by rfl⟩ : syracuseStep 80624645 = 15117121) B15117121
theorem B5037071 : Blo 1655527 5037071 := bstep (se 1 (by rfl) ⟨3777803, by rfl⟩ : syracuseStep 5037071 = 7555607) B7555607
theorem B4250657 : Blo 1655527 4250657 := bstep (se 2 (by rfl) ⟨1593996, by rfl⟩ : syracuseStep 4250657 = 3187993) B3187993
theorem B3726395 : Blo 1655527 3726395 := bstep (se 1 (by rfl) ⟨2794796, by rfl⟩ : syracuseStep 3726395 = 5589593) B5589593
theorem B3726521 : Blo 1655527 3726521 := bstep (se 2 (by rfl) ⟨1397445, by rfl⟩ : syracuseStep 3726521 = 2794891) B2794891
theorem B5037241 : Blo 1655527 5037241 := bstep (se 2 (by rfl) ⟨1888965, by rfl⟩ : syracuseStep 5037241 = 3777931) B3777931
theorem B6372553 : Blo 1655527 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B1768711 : Blo 1655527 1768711 := bstep (se 1 (by rfl) ⟨1326533, by rfl⟩ : syracuseStep 1768711 = 2653067) B2653067
theorem B8387873 : Blo 1655527 8387873 := bstep (se 2 (by rfl) ⟨3145452, by rfl⟩ : syracuseStep 8387873 = 6290905) B6290905
theorem B14351675 : Blo 1655527 14351675 := bstep (se 1 (by rfl) ⟨10763756, by rfl⟩ : syracuseStep 14351675 = 21527513) B21527513
theorem B3538361 : Blo 1655527 3538361 := bstep (se 2 (by rfl) ⟨1326885, by rfl⟩ : syracuseStep 3538361 = 2653771) B2653771
theorem B18873809 : Blo 1655527 18873809 := bstep (se 2 (by rfl) ⟨7077678, by rfl⟩ : syracuseStep 18873809 = 14155357) B14155357
theorem B3726863 : Blo 1655527 3726863 := bstep (se 1 (by rfl) ⟨2795147, by rfl⟩ : syracuseStep 3726863 = 5590295) B5590295
theorem B3726881 : Blo 1655527 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B2358919 : Blo 1655527 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B4193927 : Blo 1655527 4193927 := bstep (se 1 (by rfl) ⟨3145445, by rfl⟩ : syracuseStep 4193927 = 6290891) B6290891
theorem B4193977 : Blo 1655527 4193977 := bstep (se 2 (by rfl) ⟨1572741, by rfl⟩ : syracuseStep 4193977 = 3145483) B3145483
theorem B8953537 : Blo 1655527 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B7077577 : Blo 1655527 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B7962313 : Blo 1655527 7962313 := bstep (se 2 (by rfl) ⟨2985867, by rfl⟩ : syracuseStep 7962313 = 5971735) B5971735
theorem B3538703 : Blo 1655527 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B4718351 : Blo 1655527 4718351 := bstep (se 1 (by rfl) ⟨3538763, by rfl⟩ : syracuseStep 4718351 = 7077527) B7077527
theorem B3538721 : Blo 1655527 3538721 := bstep (se 2 (by rfl) ⟨1327020, by rfl⟩ : syracuseStep 3538721 = 2654041) B2654041
theorem B9428795 : Blo 1655527 9428795 := bstep (se 1 (by rfl) ⟨7071596, by rfl⟩ : syracuseStep 9428795 = 14143193) B14143193
theorem B3727223 : Blo 1655527 3727223 := bstep (se 1 (by rfl) ⟨2795417, by rfl⟩ : syracuseStep 3727223 = 5590835) B5590835
theorem B3727367 : Blo 1655527 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B2097191 : Blo 1655527 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B2834489 : Blo 1655527 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B26861645 : Blo 1655527 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3727439 : Blo 1655527 3727439 := bstep (se 1 (by rfl) ⟨2795579, by rfl⟩ : syracuseStep 3727439 = 5591159) B5591159
theorem B4718749 : Blo 1655527 4718749 := bstep (se 3 (by rfl) ⟨884765, by rfl⟩ : syracuseStep 4718749 = 1769531) B1769531
theorem B2097515 : Blo 1655527 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B3727835 : Blo 1655527 3727835 := bstep (se 1 (by rfl) ⟨2795876, by rfl⟩ : syracuseStep 3727835 = 5591753) B5591753
theorem B7078535 : Blo 1655527 7078535 := bstep (se 1 (by rfl) ⟨5308901, by rfl⟩ : syracuseStep 7078535 = 10617803) B10617803
theorem B5587595 : Blo 1655527 5587595 := bstep (se 1 (by rfl) ⟨4190696, by rfl⟩ : syracuseStep 5587595 = 8381393) B8381393
theorem B8389331 : Blo 1655527 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B1655591 : Blo 1655527 1655591 := bstep (se 1 (by rfl) ⟨1241693, by rfl⟩ : syracuseStep 1655591 = 2483387) B2483387
theorem B1655631 : Blo 1655527 1655631 := bstep (se 1 (by rfl) ⟨1241723, by rfl⟩ : syracuseStep 1655631 = 2483447) B2483447
theorem B1655647 : Blo 1655527 1655647 := bstep (se 1 (by rfl) ⟨1241735, by rfl⟩ : syracuseStep 1655647 = 2483471) B2483471
theorem B5972831 : Blo 1655527 5972831 := bstep (se 1 (by rfl) ⟨4479623, by rfl⟩ : syracuseStep 5972831 = 8959247) B8959247
theorem B4719455 : Blo 1655527 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B1655675 : Blo 1655527 1655675 := bstep (se 1 (by rfl) ⟨1241756, by rfl⟩ : syracuseStep 1655675 = 2483513) B2483513
theorem B1655727 : Blo 1655527 1655727 := bstep (se 1 (by rfl) ⟨1241795, by rfl⟩ : syracuseStep 1655727 = 2483591) B2483591
theorem B3728303 : Blo 1655527 3728303 := bstep (se 1 (by rfl) ⟨2796227, by rfl⟩ : syracuseStep 3728303 = 5592455) B5592455
theorem B3539899 : Blo 1655527 3539899 := bstep (se 1 (by rfl) ⟨2654924, by rfl⟩ : syracuseStep 3539899 = 5309849) B5309849
theorem B3146683 : Blo 1655527 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B1655751 : Blo 1655527 1655751 := bstep (se 1 (by rfl) ⟨1241813, by rfl⟩ : syracuseStep 1655751 = 2483627) B2483627
theorem B1655771 : Blo 1655527 1655771 := bstep (se 1 (by rfl) ⟨1241828, by rfl⟩ : syracuseStep 1655771 = 2483657) B2483657
theorem B2794459 : Blo 1655527 2794459 := bstep (se 1 (by rfl) ⟨2095844, by rfl⟩ : syracuseStep 2794459 = 4191689) B4191689
theorem B9438227 : Blo 1655527 9438227 := bstep (se 1 (by rfl) ⟨7078670, by rfl⟩ : syracuseStep 9438227 = 14157341) B14157341
theorem B1655847 : Blo 1655527 1655847 := bstep (se 1 (by rfl) ⟨1241885, by rfl⟩ : syracuseStep 1655847 = 2483771) B2483771
theorem B4195385 : Blo 1655527 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B2237519 : Blo 1655527 2237519 := bstep (se 1 (by rfl) ⟨1678139, by rfl⟩ : syracuseStep 2237519 = 3356279) B3356279
theorem B1655887 : Blo 1655527 1655887 := bstep (se 1 (by rfl) ⟨1241915, by rfl⟩ : syracuseStep 1655887 = 2483831) B2483831
theorem B1655903 : Blo 1655527 1655903 := bstep (se 1 (by rfl) ⟨1241927, by rfl⟩ : syracuseStep 1655903 = 2483855) B2483855
theorem B1655931 : Blo 1655527 1655931 := bstep (se 1 (by rfl) ⟨1241948, by rfl⟩ : syracuseStep 1655931 = 2483897) B2483897
theorem B6292637 : Blo 1655527 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B3728555 : Blo 1655527 3728555 := bstep (se 1 (by rfl) ⟨2796416, by rfl⟩ : syracuseStep 3728555 = 5592833) B5592833
theorem B1655983 : Blo 1655527 1655983 := bstep (se 1 (by rfl) ⟨1241987, by rfl⟩ : syracuseStep 1655983 = 2483975) B2483975
theorem B2483399 : Blo 1655527 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B1656007 : Blo 1655527 1656007 := bstep (se 1 (by rfl) ⟨1242005, by rfl⟩ : syracuseStep 1656007 = 2484011) B2484011
theorem B10216651 : Blo 1655527 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B1656027 : Blo 1655527 1656027 := bstep (se 1 (by rfl) ⟨1242020, by rfl⟩ : syracuseStep 1656027 = 2484041) B2484041
theorem B10609957 : Blo 1655527 10609957 := bstep (se 4 (by rfl) ⟨994683, by rfl⟩ : syracuseStep 10609957 = 1989367) B1989367
theorem B1656103 : Blo 1655527 1656103 := bstep (se 1 (by rfl) ⟨1242077, by rfl⟩ : syracuseStep 1656103 = 2484155) B2484155
theorem B1656143 : Blo 1655527 1656143 := bstep (se 1 (by rfl) ⟨1242107, by rfl⟩ : syracuseStep 1656143 = 2484215) B2484215
theorem B1656159 : Blo 1655527 1656159 := bstep (se 1 (by rfl) ⟨1242119, by rfl⟩ : syracuseStep 1656159 = 2484239) B2484239
theorem B2483561 : Blo 1655527 2483561 := bstep (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) B1862671
theorem B1656187 : Blo 1655527 1656187 := bstep (se 1 (by rfl) ⟨1242140, by rfl⟩ : syracuseStep 1656187 = 2484281) B2484281
theorem B1656239 : Blo 1655527 1656239 := bstep (se 1 (by rfl) ⟨1242179, by rfl⟩ : syracuseStep 1656239 = 2484359) B2484359
theorem B2483639 : Blo 1655527 2483639 := bstep (se 1 (by rfl) ⟨1862729, by rfl⟩ : syracuseStep 2483639 = 3725459) B3725459
theorem B1656263 : Blo 1655527 1656263 := bstep (se 1 (by rfl) ⟨1242197, by rfl⟩ : syracuseStep 1656263 = 2484395) B2484395
theorem B2483675 : Blo 1655527 2483675 := bstep (se 1 (by rfl) ⟨1862756, by rfl⟩ : syracuseStep 2483675 = 3725513) B3725513
theorem B1656283 : Blo 1655527 1656283 := bstep (se 1 (by rfl) ⟨1242212, by rfl⟩ : syracuseStep 1656283 = 2484425) B2484425
theorem B8955355 : Blo 1655527 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B5588513 : Blo 1655527 5588513 := bstep (se 2 (by rfl) ⟨2095692, by rfl⟩ : syracuseStep 5588513 = 4191385) B4191385
theorem B12101159 : Blo 1655527 12101159 := bstep (se 1 (by rfl) ⟨9075869, by rfl⟩ : syracuseStep 12101159 = 18151739) B18151739
theorem B1656359 : Blo 1655527 1656359 := bstep (se 1 (by rfl) ⟨1242269, by rfl⟩ : syracuseStep 1656359 = 2484539) B2484539
theorem B2795087 : Blo 1655527 2795087 := bstep (se 1 (by rfl) ⟨2096315, by rfl⟩ : syracuseStep 2795087 = 4192631) B4192631
theorem B1656399 : Blo 1655527 1656399 := bstep (se 1 (by rfl) ⟨1242299, by rfl⟩ : syracuseStep 1656399 = 2484599) B2484599
theorem B1656415 : Blo 1655527 1656415 := bstep (se 1 (by rfl) ⟨1242311, by rfl⟩ : syracuseStep 1656415 = 2484623) B2484623
theorem B8496737 : Blo 1655527 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B1656443 : Blo 1655527 1656443 := bstep (se 1 (by rfl) ⟨1242332, by rfl⟩ : syracuseStep 1656443 = 2484665) B2484665
theorem B1656495 : Blo 1655527 1656495 := bstep (se 1 (by rfl) ⟨1242371, by rfl⟩ : syracuseStep 1656495 = 2484743) B2484743
theorem B1656519 : Blo 1655527 1656519 := bstep (se 1 (by rfl) ⟨1242389, by rfl⟩ : syracuseStep 1656519 = 2484779) B2484779
theorem B3729095 : Blo 1655527 3729095 := bstep (se 1 (by rfl) ⟨2796821, by rfl⟩ : syracuseStep 3729095 = 5593643) B5593643
theorem B24209111 : Blo 1655527 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B1656539 : Blo 1655527 1656539 := bstep (se 1 (by rfl) ⟨1242404, by rfl⟩ : syracuseStep 1656539 = 2484809) B2484809
theorem B5588729 : Blo 1655527 5588729 := bstep (se 2 (by rfl) ⟨2095773, by rfl⟩ : syracuseStep 5588729 = 4191547) B4191547
theorem B1656615 : Blo 1655527 1656615 := bstep (se 1 (by rfl) ⟨1242461, by rfl⟩ : syracuseStep 1656615 = 2484923) B2484923
theorem B6293321 : Blo 1655527 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B1656655 : Blo 1655527 1656655 := bstep (se 1 (by rfl) ⟨1242491, by rfl⟩ : syracuseStep 1656655 = 2484983) B2484983
theorem B1656671 : Blo 1655527 1656671 := bstep (se 1 (by rfl) ⟨1242503, by rfl⟩ : syracuseStep 1656671 = 2485007) B2485007
theorem B1656699 : Blo 1655527 1656699 := bstep (se 1 (by rfl) ⟨1242524, by rfl⟩ : syracuseStep 1656699 = 2485049) B2485049
theorem B2484143 : Blo 1655527 2484143 := bstep (se 1 (by rfl) ⟨1863107, by rfl⟩ : syracuseStep 2484143 = 3726215) B3726215
theorem B1656751 : Blo 1655527 1656751 := bstep (se 1 (by rfl) ⟨1242563, by rfl⟩ : syracuseStep 1656751 = 2485127) B2485127
theorem B1656775 : Blo 1655527 1656775 := bstep (se 1 (by rfl) ⟨1242581, by rfl⟩ : syracuseStep 1656775 = 2485163) B2485163
theorem B1656795 : Blo 1655527 1656795 := bstep (se 1 (by rfl) ⟨1242596, by rfl⟩ : syracuseStep 1656795 = 2485193) B2485193
theorem B53749763 : Blo 1655527 53749763 := bstep (se 1 (by rfl) ⟨40312322, by rfl⟩ : syracuseStep 53749763 = 80624645) B80624645
theorem B5588999 : Blo 1655527 5588999 := bstep (se 1 (by rfl) ⟨4191749, by rfl⟩ : syracuseStep 5588999 = 8383499) B8383499
theorem B2484233 : Blo 1655527 2484233 := bstep (se 2 (by rfl) ⟨931587, by rfl⟩ : syracuseStep 2484233 = 1863175) B1863175
theorem B2484263 : Blo 1655527 2484263 := bstep (se 1 (by rfl) ⟨1863197, by rfl⟩ : syracuseStep 2484263 = 3726395) B3726395
theorem B1656871 : Blo 1655527 1656871 := bstep (se 1 (by rfl) ⟨1242653, by rfl⟩ : syracuseStep 1656871 = 2485307) B2485307
theorem B1656911 : Blo 1655527 1656911 := bstep (se 1 (by rfl) ⟨1242683, by rfl⟩ : syracuseStep 1656911 = 2485367) B2485367
theorem B10610777 : Blo 1655527 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B1656927 : Blo 1655527 1656927 := bstep (se 1 (by rfl) ⟨1242695, by rfl⟩ : syracuseStep 1656927 = 2485391) B2485391
theorem B5589107 : Blo 1655527 5589107 := bstep (se 1 (by rfl) ⟨4191830, by rfl⟩ : syracuseStep 5589107 = 8383661) B8383661
theorem B2484347 : Blo 1655527 2484347 := bstep (se 1 (by rfl) ⟨1863260, by rfl⟩ : syracuseStep 2484347 = 3726521) B3726521
theorem B1656955 : Blo 1655527 1656955 := bstep (se 1 (by rfl) ⟨1242716, by rfl⟩ : syracuseStep 1656955 = 2485433) B2485433
theorem B1657007 : Blo 1655527 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B1657031 : Blo 1655527 1657031 := bstep (se 1 (by rfl) ⟨1242773, by rfl⟩ : syracuseStep 1657031 = 2485547) B2485547
theorem B1657051 : Blo 1655527 1657051 := bstep (se 1 (by rfl) ⟨1242788, by rfl⟩ : syracuseStep 1657051 = 2485577) B2485577
theorem B2484473 : Blo 1655527 2484473 := bstep (se 2 (by rfl) ⟨931677, by rfl⟩ : syracuseStep 2484473 = 1863355) B1863355
theorem B11938049 : Blo 1655527 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B1657127 : Blo 1655527 1657127 := bstep (se 1 (by rfl) ⟨1242845, by rfl⟩ : syracuseStep 1657127 = 2485691) B2485691
theorem B1657167 : Blo 1655527 1657167 := bstep (se 1 (by rfl) ⟨1242875, by rfl⟩ : syracuseStep 1657167 = 2485751) B2485751
theorem B2484575 : Blo 1655527 2484575 := bstep (se 1 (by rfl) ⟨1863431, by rfl⟩ : syracuseStep 2484575 = 3726863) B3726863
theorem B1657183 : Blo 1655527 1657183 := bstep (se 1 (by rfl) ⟨1242887, by rfl⟩ : syracuseStep 1657183 = 2485775) B2485775
theorem B2484587 : Blo 1655527 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B1657211 : Blo 1655527 1657211 := bstep (se 1 (by rfl) ⟨1242908, by rfl⟩ : syracuseStep 1657211 = 2485817) B2485817
theorem B5589377 : Blo 1655527 5589377 := bstep (se 2 (by rfl) ⟨2096016, by rfl⟩ : syracuseStep 5589377 = 4192033) B4192033
theorem B53741971 : Blo 1655527 53741971 := bstep (se 1 (by rfl) ⟨40306478, by rfl⟩ : syracuseStep 53741971 = 80612957) B80612957
theorem B2795951 : Blo 1655527 2795951 := bstep (se 1 (by rfl) ⟨2096963, by rfl⟩ : syracuseStep 2795951 = 4193927) B4193927
theorem B1657263 : Blo 1655527 1657263 := bstep (se 1 (by rfl) ⟨1242947, by rfl⟩ : syracuseStep 1657263 = 2485895) B2485895
theorem B1657287 : Blo 1655527 1657287 := bstep (se 1 (by rfl) ⟨1242965, by rfl⟩ : syracuseStep 1657287 = 2485931) B2485931
theorem B1657307 : Blo 1655527 1657307 := bstep (se 1 (by rfl) ⟨1242980, by rfl⟩ : syracuseStep 1657307 = 2485961) B2485961
theorem B6285833 : Blo 1655527 6285833 := bstep (se 2 (by rfl) ⟨2357187, by rfl⟩ : syracuseStep 6285833 = 4714375) B4714375
theorem B6285863 : Blo 1655527 6285863 := bstep (se 1 (by rfl) ⟨4714397, by rfl⟩ : syracuseStep 6285863 = 9428795) B9428795
theorem B1657383 : Blo 1655527 1657383 := bstep (se 1 (by rfl) ⟨1243037, by rfl⟩ : syracuseStep 1657383 = 2486075) B2486075
theorem B15927853 : Blo 1655527 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B2484815 : Blo 1655527 2484815 := bstep (se 1 (by rfl) ⟨1863611, by rfl⟩ : syracuseStep 2484815 = 3727223) B3727223
theorem B1657423 : Blo 1655527 1657423 := bstep (se 1 (by rfl) ⟨1243067, by rfl⟩ : syracuseStep 1657423 = 2486135) B2486135
theorem B1657439 : Blo 1655527 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B1657467 : Blo 1655527 1657467 := bstep (se 1 (by rfl) ⟨1243100, by rfl⟩ : syracuseStep 1657467 = 2486201) B2486201
theorem B1657519 : Blo 1655527 1657519 := bstep (se 1 (by rfl) ⟨1243139, by rfl⟩ : syracuseStep 1657519 = 2486279) B2486279
theorem B6376121 : Blo 1655527 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B2484935 : Blo 1655527 2484935 := bstep (se 1 (by rfl) ⟨1863701, by rfl⟩ : syracuseStep 2484935 = 3727403) B3727403
theorem B9440003 : Blo 1655527 9440003 := bstep (se 1 (by rfl) ⟨7080002, by rfl⟩ : syracuseStep 9440003 = 14160005) B14160005
theorem B2796383 : Blo 1655527 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B2485097 : Blo 1655527 2485097 := bstep (se 2 (by rfl) ⟨931911, by rfl⟩ : syracuseStep 2485097 = 1863823) B1863823
theorem B2485175 : Blo 1655527 2485175 := bstep (se 1 (by rfl) ⟨1863881, by rfl⟩ : syracuseStep 2485175 = 3727763) B3727763
theorem B2485211 : Blo 1655527 2485211 := bstep (se 1 (by rfl) ⟨1863908, by rfl⟩ : syracuseStep 2485211 = 3727817) B3727817
theorem B21220325 : Blo 1655527 21220325 := bstep (se 4 (by rfl) ⟨1989405, by rfl⟩ : syracuseStep 21220325 = 3978811) B3978811
theorem B4779065 : Blo 1655527 4779065 := bstep (se 2 (by rfl) ⟨1792149, by rfl⟩ : syracuseStep 4779065 = 3584299) B3584299
theorem B1862779 : Blo 1655527 1862779 := bstep (se 1 (by rfl) ⟨1397084, by rfl⟩ : syracuseStep 1862779 = 2794169) B2794169
theorem B5590187 : Blo 1655527 5590187 := bstep (se 1 (by rfl) ⟨4192640, by rfl⟩ : syracuseStep 5590187 = 8385281) B8385281
theorem B6286531 : Blo 1655527 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B23883133 : Blo 1655527 23883133 := bstep (se 3 (by rfl) ⟨4478087, by rfl⟩ : syracuseStep 23883133 = 8956175) B8956175
theorem B2796943 : Blo 1655527 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B2485679 : Blo 1655527 2485679 := bstep (se 1 (by rfl) ⟨1864259, by rfl⟩ : syracuseStep 2485679 = 3728519) B3728519
theorem B6286835 : Blo 1655527 6286835 := bstep (se 1 (by rfl) ⟨4715126, by rfl⟩ : syracuseStep 6286835 = 9430253) B9430253
theorem B2485769 : Blo 1655527 2485769 := bstep (se 2 (by rfl) ⟨932163, by rfl⟩ : syracuseStep 2485769 = 1864327) B1864327
theorem B2485799 : Blo 1655527 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B1863247 : Blo 1655527 1863247 := bstep (se 1 (by rfl) ⟨1397435, by rfl⟩ : syracuseStep 1863247 = 2794871) B2794871
theorem B13618775 : Blo 1655527 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B17903227 : Blo 1655527 17903227 := bstep (se 1 (by rfl) ⟨13427420, by rfl⟩ : syracuseStep 17903227 = 26854841) B26854841
theorem B2485883 : Blo 1655527 2485883 := bstep (se 1 (by rfl) ⟨1864412, by rfl⟩ : syracuseStep 2485883 = 3728825) B3728825
theorem B8384147 : Blo 1655527 8384147 := bstep (se 1 (by rfl) ⟨6288110, by rfl⟩ : syracuseStep 8384147 = 12576221) B12576221
theorem B8072893 : Blo 1655527 8072893 := bstep (se 3 (by rfl) ⟨1513667, by rfl⟩ : syracuseStep 8072893 = 3027335) B3027335
theorem B5590727 : Blo 1655527 5590727 := bstep (se 1 (by rfl) ⟨4193045, by rfl⟩ : syracuseStep 5590727 = 8386091) B8386091
theorem B40300253 : Blo 1655527 40300253 := bstep (se 3 (by rfl) ⟨7556297, by rfl⟩ : syracuseStep 40300253 = 15112595) B15112595
theorem B2486009 : Blo 1655527 2486009 := bstep (se 2 (by rfl) ⟨932253, by rfl⟩ : syracuseStep 2486009 = 1864507) B1864507
theorem B51007265 : Blo 1655527 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B2486111 : Blo 1655527 2486111 := bstep (se 1 (by rfl) ⟨1864583, by rfl⟩ : syracuseStep 2486111 = 3729167) B3729167
theorem B2486123 : Blo 1655527 2486123 := bstep (se 1 (by rfl) ⟨1864592, by rfl⟩ : syracuseStep 2486123 = 3729185) B3729185
theorem B6287291 : Blo 1655527 6287291 := bstep (se 1 (by rfl) ⟨4715468, by rfl⟩ : syracuseStep 6287291 = 9430937) B9430937
theorem B7172027 : Blo 1655527 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B1863643 : Blo 1655527 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B9433169 : Blo 1655527 9433169 := bstep (se 2 (by rfl) ⟨3537438, by rfl⟩ : syracuseStep 9433169 = 7074877) B7074877
theorem B12103937 : Blo 1655527 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B1864111 : Blo 1655527 1864111 := bstep (se 1 (by rfl) ⟨1398083, by rfl⟩ : syracuseStep 1864111 = 2796167) B2796167
theorem B28299779 : Blo 1655527 28299779 := bstep (se 1 (by rfl) ⟨21224834, by rfl⟩ : syracuseStep 28299779 = 42449669) B42449669
theorem B5304865 : Blo 1655527 5304865 := bstep (se 2 (by rfl) ⟨1989324, by rfl⟩ : syracuseStep 5304865 = 3978649) B3978649
theorem B5591591 : Blo 1655527 5591591 := bstep (se 1 (by rfl) ⟨4193693, by rfl⟩ : syracuseStep 5591591 = 8387387) B8387387
theorem B5591699 : Blo 1655527 5591699 := bstep (se 1 (by rfl) ⟨4193774, by rfl⟩ : syracuseStep 5591699 = 8387549) B8387549
theorem B1864543 : Blo 1655527 1864543 := bstep (se 1 (by rfl) ⟨1398407, by rfl⟩ : syracuseStep 1864543 = 2796815) B2796815
theorem B5591915 : Blo 1655527 5591915 := bstep (se 1 (by rfl) ⟨4193936, by rfl⟩ : syracuseStep 5591915 = 8387873) B8387873
theorem B28677017 : Blo 1655527 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B5591969 : Blo 1655527 5591969 := bstep (se 2 (by rfl) ⟨2096988, by rfl⟩ : syracuseStep 5591969 = 4193977) B4193977
theorem B18879641 : Blo 1655527 18879641 := bstep (se 2 (by rfl) ⟨7079865, by rfl⟩ : syracuseStep 18879641 = 14159731) B14159731
theorem B6714539 : Blo 1655527 6714539 := bstep (se 1 (by rfl) ⟨5035904, by rfl⟩ : syracuseStep 6714539 = 10071809) B10071809
theorem B3405047 : Blo 1655527 3405047 := bstep (se 1 (by rfl) ⟨2553785, by rfl⟩ : syracuseStep 3405047 = 5107571) B5107571
theorem B13432189 : Blo 1655527 13432189 := bstep (se 3 (by rfl) ⟨2518535, by rfl⟩ : syracuseStep 13432189 = 5037071) B5037071
theorem B11335085 : Blo 1655527 11335085 := bstep (se 3 (by rfl) ⟨2125328, by rfl⟩ : syracuseStep 11335085 = 4250657) B4250657
theorem B3143099 : Blo 1655527 3143099 := bstep (se 1 (by rfl) ⟨2357324, by rfl⟩ : syracuseStep 3143099 = 4714649) B4714649
theorem B14144969 : Blo 1655527 14144969 := bstep (se 2 (by rfl) ⟨5304363, by rfl⟩ : syracuseStep 14144969 = 10608727) B10608727
theorem B5969371 : Blo 1655527 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B5592563 : Blo 1655527 5592563 := bstep (se 1 (by rfl) ⟨4194422, by rfl⟩ : syracuseStep 5592563 = 8388845) B8388845
theorem B9557693 : Blo 1655527 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B2651977 : Blo 1655527 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B3536713 : Blo 1655527 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B3143585 : Blo 1655527 3143585 := bstep (se 2 (by rfl) ⟨1178844, by rfl⟩ : syracuseStep 3143585 = 2357689) B2357689
theorem B4192175 : Blo 1655527 4192175 := bstep (se 1 (by rfl) ⟨3144131, by rfl⟩ : syracuseStep 4192175 = 6288263) B6288263
theorem B3725243 : Blo 1655527 3725243 := bstep (se 1 (by rfl) ⟨2793932, by rfl⟩ : syracuseStep 3725243 = 5587865) B5587865
theorem B5593103 : Blo 1655527 5593103 := bstep (se 1 (by rfl) ⟨4194827, by rfl⟩ : syracuseStep 5593103 = 8389655) B8389655
theorem B3725369 : Blo 1655527 3725369 := bstep (se 2 (by rfl) ⟨1397013, by rfl⟩ : syracuseStep 3725369 = 2794027) B2794027
theorem B38271133 : Blo 1655527 38271133 := bstep (se 3 (by rfl) ⟨7175837, by rfl⟩ : syracuseStep 38271133 = 14351675) B14351675
theorem B2095303 : Blo 1655527 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B3143927 : Blo 1655527 3143927 := bstep (se 1 (by rfl) ⟨2357945, by rfl⟩ : syracuseStep 3143927 = 4715891) B4715891
theorem B6289751 : Blo 1655527 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B3725711 : Blo 1655527 3725711 := bstep (se 1 (by rfl) ⟨2794283, by rfl⟩ : syracuseStep 3725711 = 5588567) B5588567
theorem B3537371 : Blo 1655527 3537371 := bstep (se 1 (by rfl) ⟨2653028, by rfl⟩ : syracuseStep 3537371 = 5306057) B5306057
theorem B6715867 : Blo 1655527 6715867 := bstep (se 1 (by rfl) ⟨5036900, by rfl⟩ : syracuseStep 6715867 = 10073801) B10073801
theorem B9435629 : Blo 1655527 9435629 := bstep (se 3 (by rfl) ⟨1769180, by rfl⟩ : syracuseStep 9435629 = 3538361) B3538361
theorem B4192793 : Blo 1655527 4192793 := bstep (se 2 (by rfl) ⟨1572297, by rfl⟩ : syracuseStep 4192793 = 3144595) B3144595
theorem B1768015 : Blo 1655527 1768015 := bstep (se 1 (by rfl) ⟨1326011, by rfl⟩ : syracuseStep 1768015 = 2652023) B2652023
theorem B5593697 : Blo 1655527 5593697 := bstep (se 2 (by rfl) ⟨2097636, by rfl⟩ : syracuseStep 5593697 = 4195273) B4195273
theorem B3726035 : Blo 1655527 3726035 := bstep (se 1 (by rfl) ⟨2794526, by rfl⟩ : syracuseStep 3726035 = 5589053) B5589053
theorem B6716321 : Blo 1655527 6716321 := bstep (se 2 (by rfl) ⟨2518620, by rfl⟩ : syracuseStep 6716321 = 5037241) B5037241
theorem B2096047 : Blo 1655527 2096047 := bstep (se 1 (by rfl) ⟨1572035, by rfl⟩ : syracuseStep 2096047 = 3144071) B3144071
theorem B3980215 : Blo 1655527 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B2358281 : Blo 1655527 2358281 := bstep (se 2 (by rfl) ⟨884355, by rfl⟩ : syracuseStep 2358281 = 1768711) B1768711
theorem B2653355 : Blo 1655527 2653355 := bstep (se 1 (by rfl) ⟨1990016, by rfl⟩ : syracuseStep 2653355 = 3980033) B3980033
theorem B67976471 : Blo 1655527 67976471 := bstep (se 1 (by rfl) ⟨50982353, by rfl⟩ : syracuseStep 67976471 = 101964707) B101964707
theorem B1678687 : Blo 1655527 1678687 := bstep (se 1 (by rfl) ⟨1259015, by rfl⟩ : syracuseStep 1678687 = 2518031) B2518031
theorem B10755443 : Blo 1655527 10755443 := bstep (se 1 (by rfl) ⟨8066582, by rfl⟩ : syracuseStep 10755443 = 16133165) B16133165
theorem B24214909 : Blo 1655527 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B53747165 : Blo 1655527 53747165 := bstep (se 3 (by rfl) ⟨10077593, by rfl⟩ : syracuseStep 53747165 = 20155187) B20155187
theorem B3145225 : Blo 1655527 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B9436769 : Blo 1655527 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B10616417 : Blo 1655527 10616417 := bstep (se 2 (by rfl) ⟨3981156, by rfl⟩ : syracuseStep 10616417 = 7962313) B7962313
theorem B3726971 : Blo 1655527 3726971 := bstep (se 1 (by rfl) ⟨2795228, by rfl⟩ : syracuseStep 3726971 = 5590457) B5590457
theorem B12582539 : Blo 1655527 12582539 := bstep (se 1 (by rfl) ⟨9436904, by rfl⟩ : syracuseStep 12582539 = 18873809) B18873809
theorem B10608317 : Blo 1655527 10608317 := bstep (se 3 (by rfl) ⟨1989059, by rfl⟩ : syracuseStep 10608317 = 3978119) B3978119
theorem B3727097 : Blo 1655527 3727097 := bstep (se 2 (by rfl) ⟨1397661, by rfl⟩ : syracuseStep 3727097 = 2795323) B2795323
theorem B2359135 : Blo 1655527 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B3145567 : Blo 1655527 3145567 := bstep (se 1 (by rfl) ⟨2359175, by rfl⟩ : syracuseStep 3145567 = 4718351) B4718351
theorem B2359147 : Blo 1655527 2359147 := bstep (se 1 (by rfl) ⟨1769360, by rfl⟩ : syracuseStep 2359147 = 3538721) B3538721
theorem B8069291 : Blo 1655527 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B71631053 : Blo 1655527 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B6291665 : Blo 1655527 6291665 := bstep (se 2 (by rfl) ⟨2359374, by rfl⟩ : syracuseStep 6291665 = 4718749) B4718749
theorem B51028177 : Blo 1655527 51028177 := bstep (se 2 (by rfl) ⟨19135566, by rfl⟩ : syracuseStep 51028177 = 38271133) B38271133
theorem B28295405 : Blo 1655527 28295405 := bstep (se 3 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 28295405 = 10610777) B10610777
theorem B2793737 : Blo 1655527 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B18866519 : Blo 1655527 18866519 := bstep (se 1 (by rfl) ⟨14149889, by rfl⟩ : syracuseStep 18866519 = 28299779) B28299779
theorem B3727727 : Blo 1655527 3727727 := bstep (se 1 (by rfl) ⟨2795795, by rfl⟩ : syracuseStep 3727727 = 5591591) B5591591
theorem B4719023 : Blo 1655527 4719023 := bstep (se 1 (by rfl) ⟨3539267, by rfl⟩ : syracuseStep 4719023 = 7078535) B7078535
theorem B3727799 : Blo 1655527 3727799 := bstep (se 1 (by rfl) ⟨2795849, by rfl⟩ : syracuseStep 3727799 = 5591699) B5591699
theorem B71655961 : Blo 1655527 71655961 := bstep (se 2 (by rfl) ⟨26870985, by rfl⟩ : syracuseStep 71655961 = 53741971) B53741971
theorem B3981887 : Blo 1655527 3981887 := bstep (se 1 (by rfl) ⟨2986415, by rfl⟩ : syracuseStep 3981887 = 5972831) B5972831
theorem B3146303 : Blo 1655527 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B3727943 : Blo 1655527 3727943 := bstep (se 1 (by rfl) ⟨2795957, by rfl⟩ : syracuseStep 3727943 = 5591915) B5591915
theorem B3727979 : Blo 1655527 3727979 := bstep (se 1 (by rfl) ⟨2795984, by rfl⟩ : syracuseStep 3727979 = 5591969) B5591969
theorem B8954489 : Blo 1655527 8954489 := bstep (se 2 (by rfl) ⟨3357933, by rfl⟩ : syracuseStep 8954489 = 6715867) B6715867
theorem B6292151 : Blo 1655527 6292151 := bstep (se 1 (by rfl) ⟨4719113, by rfl⟩ : syracuseStep 6292151 = 9438227) B9438227
theorem B4195091 : Blo 1655527 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B1655599 : Blo 1655527 1655599 := bstep (se 1 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 1655599 = 2483399) B2483399
theorem B1655707 : Blo 1655527 1655707 := bstep (se 1 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 1655707 = 2483561) B2483561
theorem B1655759 : Blo 1655527 1655759 := bstep (se 1 (by rfl) ⟨1241819, by rfl⟩ : syracuseStep 1655759 = 2483639) B2483639
theorem B9429979 : Blo 1655527 9429979 := bstep (se 1 (by rfl) ⟨7072484, by rfl⟩ : syracuseStep 9429979 = 14144969) B14144969
theorem B1655783 : Blo 1655527 1655783 := bstep (se 1 (by rfl) ⟨1241837, by rfl⟩ : syracuseStep 1655783 = 2483675) B2483675
theorem B3728375 : Blo 1655527 3728375 := bstep (se 1 (by rfl) ⟨2796281, by rfl⟩ : syracuseStep 3728375 = 5592563) B5592563
theorem B16139407 : Blo 1655527 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B4195547 : Blo 1655527 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B2794729 : Blo 1655527 2794729 := bstep (se 2 (by rfl) ⟨1048023, by rfl⟩ : syracuseStep 2794729 = 2096047) B2096047
theorem B4719865 : Blo 1655527 4719865 := bstep (se 2 (by rfl) ⟨1769949, by rfl⟩ : syracuseStep 4719865 = 3539899) B3539899
theorem B4195577 : Blo 1655527 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B1656095 : Blo 1655527 1656095 := bstep (se 1 (by rfl) ⟨1242071, by rfl⟩ : syracuseStep 1656095 = 2484143) B2484143
theorem B2794783 : Blo 1655527 2794783 := bstep (se 1 (by rfl) ⟨2096087, by rfl⟩ : syracuseStep 2794783 = 4192175) B4192175
theorem B2483495 : Blo 1655527 2483495 := bstep (se 1 (by rfl) ⟨1862621, by rfl⟩ : syracuseStep 2483495 = 3725243) B3725243
theorem B35833175 : Blo 1655527 35833175 := bstep (se 1 (by rfl) ⟨26874881, by rfl⟩ : syracuseStep 35833175 = 53749763) B53749763
theorem B1656155 : Blo 1655527 1656155 := bstep (se 1 (by rfl) ⟨1242116, by rfl⟩ : syracuseStep 1656155 = 2484233) B2484233
theorem B3728735 : Blo 1655527 3728735 := bstep (se 1 (by rfl) ⟨2796551, by rfl⟩ : syracuseStep 3728735 = 5593103) B5593103
theorem B1656175 : Blo 1655527 1656175 := bstep (se 1 (by rfl) ⟨1242131, by rfl⟩ : syracuseStep 1656175 = 2484263) B2484263
theorem B2483579 : Blo 1655527 2483579 := bstep (se 1 (by rfl) ⟨1862684, by rfl⟩ : syracuseStep 2483579 = 3725369) B3725369
theorem B1656231 : Blo 1655527 1656231 := bstep (se 1 (by rfl) ⟨1242173, by rfl⟩ : syracuseStep 1656231 = 2484347) B2484347
theorem B2483705 : Blo 1655527 2483705 := bstep (se 2 (by rfl) ⟨931389, by rfl⟩ : syracuseStep 2483705 = 1862779) B1862779
theorem B1656315 : Blo 1655527 1656315 := bstep (se 1 (by rfl) ⟨1242236, by rfl⟩ : syracuseStep 1656315 = 2484473) B2484473
theorem B1656383 : Blo 1655527 1656383 := bstep (se 1 (by rfl) ⟨1242287, by rfl⟩ : syracuseStep 1656383 = 2484575) B2484575
theorem B1656391 : Blo 1655527 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B8382041 : Blo 1655527 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B2483807 : Blo 1655527 2483807 := bstep (se 1 (by rfl) ⟨1862855, by rfl⟩ : syracuseStep 2483807 = 3725711) B3725711
theorem B2795195 : Blo 1655527 2795195 := bstep (se 1 (by rfl) ⟨2096396, by rfl⟩ : syracuseStep 2795195 = 4192793) B4192793
theorem B1656543 : Blo 1655527 1656543 := bstep (se 1 (by rfl) ⟨1242407, by rfl⟩ : syracuseStep 1656543 = 2484815) B2484815
theorem B3729131 : Blo 1655527 3729131 := bstep (se 1 (by rfl) ⟨2796848, by rfl⟩ : syracuseStep 3729131 = 5593697) B5593697
theorem B1656623 : Blo 1655527 1656623 := bstep (se 1 (by rfl) ⟨1242467, by rfl⟩ : syracuseStep 1656623 = 2484935) B2484935
theorem B2484023 : Blo 1655527 2484023 := bstep (se 1 (by rfl) ⟨1863017, by rfl⟩ : syracuseStep 2484023 = 3726035) B3726035
theorem B17909585 : Blo 1655527 17909585 := bstep (se 2 (by rfl) ⟨6716094, by rfl⟩ : syracuseStep 17909585 = 13432189) B13432189
theorem B31844177 : Blo 1655527 31844177 := bstep (se 2 (by rfl) ⟨11941566, by rfl⟩ : syracuseStep 31844177 = 23883133) B23883133
theorem B32286545 : Blo 1655527 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B6293335 : Blo 1655527 6293335 := bstep (se 1 (by rfl) ⟨4720001, by rfl⟩ : syracuseStep 6293335 = 9440003) B9440003
theorem B3729257 : Blo 1655527 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B1656731 : Blo 1655527 1656731 := bstep (se 1 (by rfl) ⟨1242548, by rfl⟩ : syracuseStep 1656731 = 2485097) B2485097
theorem B1656783 : Blo 1655527 1656783 := bstep (se 1 (by rfl) ⟨1242587, by rfl⟩ : syracuseStep 1656783 = 2485175) B2485175
theorem B1656807 : Blo 1655527 1656807 := bstep (se 1 (by rfl) ⟨1242605, by rfl⟩ : syracuseStep 1656807 = 2485211) B2485211
theorem B2484329 : Blo 1655527 2484329 := bstep (se 2 (by rfl) ⟨931623, by rfl⟩ : syracuseStep 2484329 = 1863247) B1863247
theorem B7170295 : Blo 1655527 7170295 := bstep (se 1 (by rfl) ⟨5377721, by rfl⟩ : syracuseStep 7170295 = 10755443) B10755443
theorem B1657119 : Blo 1655527 1657119 := bstep (se 1 (by rfl) ⟨1242839, by rfl⟩ : syracuseStep 1657119 = 2485679) B2485679
theorem B1657179 : Blo 1655527 1657179 := bstep (se 1 (by rfl) ⟨1242884, by rfl⟩ : syracuseStep 1657179 = 2485769) B2485769
theorem B1657199 : Blo 1655527 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B9079183 : Blo 1655527 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B2484647 : Blo 1655527 2484647 := bstep (se 1 (by rfl) ⟨1863485, by rfl⟩ : syracuseStep 2484647 = 3726971) B3726971
theorem B1657255 : Blo 1655527 1657255 := bstep (se 1 (by rfl) ⟨1242941, by rfl⟩ : syracuseStep 1657255 = 2485883) B2485883
theorem B5589431 : Blo 1655527 5589431 := bstep (se 1 (by rfl) ⟨4192073, by rfl⟩ : syracuseStep 5589431 = 8384147) B8384147
theorem B7072211 : Blo 1655527 7072211 := bstep (se 1 (by rfl) ⟨5304158, by rfl⟩ : syracuseStep 7072211 = 10608317) B10608317
theorem B2484731 : Blo 1655527 2484731 := bstep (se 1 (by rfl) ⟨1863548, by rfl⟩ : syracuseStep 2484731 = 3727097) B3727097
theorem B1657339 : Blo 1655527 1657339 := bstep (se 1 (by rfl) ⟨1243004, by rfl⟩ : syracuseStep 1657339 = 2486009) B2486009
theorem B1657407 : Blo 1655527 1657407 := bstep (se 1 (by rfl) ⟨1243055, by rfl⟩ : syracuseStep 1657407 = 2486111) B2486111
theorem B1657415 : Blo 1655527 1657415 := bstep (se 1 (by rfl) ⟨1243061, by rfl⟩ : syracuseStep 1657415 = 2486123) B2486123
theorem B2484857 : Blo 1655527 2484857 := bstep (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) B1863643
theorem B2484911 : Blo 1655527 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B2484959 : Blo 1655527 2484959 := bstep (se 1 (by rfl) ⟨1863719, by rfl⟩ : syracuseStep 2484959 = 3727439) B3727439
theorem B5966717 : Blo 1655527 5966717 := bstep (se 3 (by rfl) ⟨1118759, by rfl⟩ : syracuseStep 5966717 = 2237519) B2237519
theorem B2485223 : Blo 1655527 2485223 := bstep (se 1 (by rfl) ⟨1863917, by rfl⟩ : syracuseStep 2485223 = 3727835) B3727835
theorem B2485481 : Blo 1655527 2485481 := bstep (se 2 (by rfl) ⟨932055, by rfl⟩ : syracuseStep 2485481 = 1864111) B1864111
theorem B2485535 : Blo 1655527 2485535 := bstep (se 1 (by rfl) ⟨1864151, by rfl⟩ : syracuseStep 2485535 = 3728303) B3728303
theorem B2796923 : Blo 1655527 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B7073153 : Blo 1655527 7073153 := bstep (se 2 (by rfl) ⟨2652432, by rfl⟩ : syracuseStep 7073153 = 5304865) B5304865
theorem B21237137 : Blo 1655527 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B12586427 : Blo 1655527 12586427 := bstep (se 1 (by rfl) ⟨9439820, by rfl⟩ : syracuseStep 12586427 = 18879641) B18879641
theorem B4476359 : Blo 1655527 4476359 := bstep (se 1 (by rfl) ⟨3357269, by rfl⟩ : syracuseStep 4476359 = 6714539) B6714539
theorem B2485703 : Blo 1655527 2485703 := bstep (se 1 (by rfl) ⟨1864277, by rfl⟩ : syracuseStep 2485703 = 3728555) B3728555
theorem B7556723 : Blo 1655527 7556723 := bstep (se 1 (by rfl) ⟨5667542, by rfl⟩ : syracuseStep 7556723 = 11335085) B11335085
theorem B1863391 : Blo 1655527 1863391 := bstep (se 1 (by rfl) ⟨1397543, by rfl⟩ : syracuseStep 1863391 = 2795087) B2795087
theorem B5664491 : Blo 1655527 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B2486057 : Blo 1655527 2486057 := bstep (se 2 (by rfl) ⟨932271, by rfl⟩ : syracuseStep 2486057 = 1864543) B1864543
theorem B2486063 : Blo 1655527 2486063 := bstep (se 1 (by rfl) ⟨1864547, by rfl⟩ : syracuseStep 2486063 = 3729095) B3729095
theorem B7958699 : Blo 1655527 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B1863967 : Blo 1655527 1863967 := bstep (se 1 (by rfl) ⟨1397975, by rfl⟩ : syracuseStep 1863967 = 2795951) B2795951
theorem B4190555 : Blo 1655527 4190555 := bstep (se 1 (by rfl) ⟨3142916, by rfl⟩ : syracuseStep 4190555 = 6285833) B6285833
theorem B4190575 : Blo 1655527 4190575 := bstep (se 1 (by rfl) ⟨3142931, by rfl⟩ : syracuseStep 4190575 = 6285863) B6285863
theorem B1864255 : Blo 1655527 1864255 := bstep (se 1 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 1864255 = 2796383) B2796383
theorem B4477547 : Blo 1655527 4477547 := bstep (se 1 (by rfl) ⟨3358160, by rfl⟩ : syracuseStep 4477547 = 6716321) B6716321
theorem B7959161 : Blo 1655527 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B11940473 : Blo 1655527 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B35811989 : Blo 1655527 35811989 := bstep (se 6 (by rfl) ⟨839343, by rfl⟩ : syracuseStep 35811989 = 1678687) B1678687
theorem B4191223 : Blo 1655527 4191223 := bstep (se 1 (by rfl) ⟨3143417, by rfl⟩ : syracuseStep 4191223 = 6286835) B6286835
theorem B3535969 : Blo 1655527 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B4715617 : Blo 1655527 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B26866835 : Blo 1655527 26866835 := bstep (se 1 (by rfl) ⟨20150126, by rfl⟩ : syracuseStep 26866835 = 40300253) B40300253
theorem B36320501 : Blo 1655527 36320501 := bstep (se 5 (by rfl) ⟨1702523, by rfl⟩ : syracuseStep 36320501 = 3405047) B3405047
theorem B4191527 : Blo 1655527 4191527 := bstep (se 1 (by rfl) ⟨3143645, by rfl⟩ : syracuseStep 4191527 = 6287291) B6287291
theorem B4781351 : Blo 1655527 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B6288749 : Blo 1655527 6288749 := bstep (se 3 (by rfl) ⟨1179140, by rfl⟩ : syracuseStep 6288749 = 2358281) B2358281
theorem B1889659 : Blo 1655527 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B6288779 : Blo 1655527 6288779 := bstep (se 1 (by rfl) ⟨4716584, by rfl⟩ : syracuseStep 6288779 = 9433169) B9433169
theorem B5592509 : Blo 1655527 5592509 := bstep (se 3 (by rfl) ⟨1048595, by rfl⟩ : syracuseStep 5592509 = 2097191) B2097191
theorem B12744173 : Blo 1655527 12744173 := bstep (se 3 (by rfl) ⟨2389532, by rfl⟩ : syracuseStep 12744173 = 4779065) B4779065
theorem B3725063 : Blo 1655527 3725063 := bstep (se 1 (by rfl) ⟨2793797, by rfl⟩ : syracuseStep 3725063 = 5587595) B5587595
theorem B7075613 : Blo 1655527 7075613 := bstep (se 3 (by rfl) ⟨1326677, by rfl⟩ : syracuseStep 7075613 = 2653355) B2653355
theorem B5592887 : Blo 1655527 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B2357353 : Blo 1655527 2357353 := bstep (se 2 (by rfl) ⟨884007, by rfl⟩ : syracuseStep 2357353 = 1768015) B1768015
theorem B5593373 : Blo 1655527 5593373 := bstep (se 3 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 5593373 = 2097515) B2097515
theorem B2095399 : Blo 1655527 2095399 := bstep (se 1 (by rfl) ⟨1571549, by rfl⟩ : syracuseStep 2095399 = 3143099) B3143099
theorem B3725675 : Blo 1655527 3725675 := bstep (se 1 (by rfl) ⟨2794256, by rfl⟩ : syracuseStep 3725675 = 5588513) B5588513
theorem B8067439 : Blo 1655527 8067439 := bstep (se 1 (by rfl) ⟨6050579, by rfl⟩ : syracuseStep 8067439 = 12101159) B12101159
theorem B6371795 : Blo 1655527 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B3725819 : Blo 1655527 3725819 := bstep (se 1 (by rfl) ⟨2794364, by rfl⟩ : syracuseStep 3725819 = 5588729) B5588729
theorem B5306953 : Blo 1655527 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B2095723 : Blo 1655527 2095723 := bstep (se 1 (by rfl) ⟨1571792, by rfl⟩ : syracuseStep 2095723 = 3143585) B3143585
theorem B3725945 : Blo 1655527 3725945 := bstep (se 2 (by rfl) ⟨1397229, by rfl⟩ : syracuseStep 3725945 = 2794459) B2794459
theorem B3725999 : Blo 1655527 3725999 := bstep (se 1 (by rfl) ⟨2794499, by rfl⟩ : syracuseStep 3725999 = 5588999) B5588999
theorem B3726071 : Blo 1655527 3726071 := bstep (se 1 (by rfl) ⟨2794553, by rfl⟩ : syracuseStep 3726071 = 5589107) B5589107
theorem B2095951 : Blo 1655527 2095951 := bstep (se 1 (by rfl) ⟨1571963, by rfl⟩ : syracuseStep 2095951 = 3143927) B3143927
theorem B4193167 : Blo 1655527 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B3726251 : Blo 1655527 3726251 := bstep (se 1 (by rfl) ⟨2794688, by rfl⟩ : syracuseStep 3726251 = 5589377) B5589377
theorem B13622201 : Blo 1655527 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B2358247 : Blo 1655527 2358247 := bstep (se 1 (by rfl) ⟨1768685, by rfl⟩ : syracuseStep 2358247 = 3537371) B3537371
theorem B6290419 : Blo 1655527 6290419 := bstep (se 1 (by rfl) ⟨4717814, by rfl⟩ : syracuseStep 6290419 = 9435629) B9435629
theorem B14146609 : Blo 1655527 14146609 := bstep (se 2 (by rfl) ⟨5304978, by rfl⟩ : syracuseStep 14146609 = 10609957) B10609957
theorem B4250747 : Blo 1655527 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B12582053 : Blo 1655527 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B14146883 : Blo 1655527 14146883 := bstep (se 1 (by rfl) ⟨10610162, by rfl⟩ : syracuseStep 14146883 = 21220325) B21220325
theorem B4193633 : Blo 1655527 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B3726791 : Blo 1655527 3726791 := bstep (se 1 (by rfl) ⟨2795093, by rfl⟩ : syracuseStep 3726791 = 5590187) B5590187
theorem B23870969 : Blo 1655527 23870969 := bstep (se 2 (by rfl) ⟨8951613, by rfl⟩ : syracuseStep 23870969 = 17903227) B17903227
theorem B45317647 : Blo 1655527 45317647 := bstep (se 1 (by rfl) ⟨33988235, by rfl⟩ : syracuseStep 45317647 = 67976471) B67976471
theorem B10763857 : Blo 1655527 10763857 := bstep (se 2 (by rfl) ⟨4036446, by rfl⟩ : syracuseStep 10763857 = 8072893) B8072893
theorem B35831443 : Blo 1655527 35831443 := bstep (se 1 (by rfl) ⟨26873582, by rfl⟩ : syracuseStep 35831443 = 53747165) B53747165
theorem B6291179 : Blo 1655527 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B7077611 : Blo 1655527 7077611 := bstep (se 1 (by rfl) ⟨5308208, by rfl⟩ : syracuseStep 7077611 = 10616417) B10616417
theorem B76472045 : Blo 1655527 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B8388359 : Blo 1655527 8388359 := bstep (se 1 (by rfl) ⟨6291269, by rfl⟩ : syracuseStep 8388359 = 12582539) B12582539
theorem B4194089 : Blo 1655527 4194089 := bstep (se 2 (by rfl) ⟨1572783, by rfl⟩ : syracuseStep 4194089 = 3145567) B3145567
theorem B3727151 : Blo 1655527 3727151 := bstep (se 1 (by rfl) ⟨2795363, by rfl⟩ : syracuseStep 3727151 = 5590727) B5590727
theorem B3145529 : Blo 1655527 3145529 := bstep (se 2 (by rfl) ⟨1179573, by rfl⟩ : syracuseStep 3145529 = 2359147) B2359147
theorem B34004843 : Blo 1655527 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B4194443 : Blo 1655527 4194443 := bstep (se 1 (by rfl) ⟨3145832, by rfl⟩ : syracuseStep 4194443 = 6291665) B6291665
theorem B2793703 : Blo 1655527 2793703 := bstep (se 1 (by rfl) ⟨2095277, by rfl⟩ : syracuseStep 2793703 = 4190555) B4190555
theorem B3146015 : Blo 1655527 3146015 := bstep (se 1 (by rfl) ⟨2359511, by rfl⟩ : syracuseStep 3146015 = 4719023) B4719023
theorem B9560393 : Blo 1655527 9560393 := bstep (se 2 (by rfl) ⟨3585147, by rfl⟩ : syracuseStep 9560393 = 7170295) B7170295
theorem B2654591 : Blo 1655527 2654591 := bstep (se 1 (by rfl) ⟨1990943, by rfl⟩ : syracuseStep 2654591 = 3981887) B3981887
theorem B2793865 : Blo 1655527 2793865 := bstep (se 2 (by rfl) ⟨1047699, by rfl⟩ : syracuseStep 2793865 = 2095399) B2095399
theorem B4194767 : Blo 1655527 4194767 := bstep (se 1 (by rfl) ⟨3146075, by rfl⟩ : syracuseStep 4194767 = 6292151) B6292151
theorem B5587433 : Blo 1655527 5587433 := bstep (se 2 (by rfl) ⟨2095287, by rfl⟩ : syracuseStep 5587433 = 4190575) B4190575
theorem B10756585 : Blo 1655527 10756585 := bstep (se 2 (by rfl) ⟨4033719, by rfl⟩ : syracuseStep 10756585 = 8067439) B8067439
theorem B2794297 : Blo 1655527 2794297 := bstep (se 2 (by rfl) ⟨1047861, by rfl⟩ : syracuseStep 2794297 = 2095723) B2095723
theorem B1655663 : Blo 1655527 1655663 := bstep (se 1 (by rfl) ⟨1241747, by rfl⟩ : syracuseStep 1655663 = 2483495) B2483495
theorem B2794351 : Blo 1655527 2794351 := bstep (se 1 (by rfl) ⟨2095763, by rfl⟩ : syracuseStep 2794351 = 4191527) B4191527
theorem B3187567 : Blo 1655527 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B23888783 : Blo 1655527 23888783 := bstep (se 1 (by rfl) ⟨17916587, by rfl⟩ : syracuseStep 23888783 = 35833175) B35833175
theorem B1655719 : Blo 1655527 1655719 := bstep (se 1 (by rfl) ⟨1241789, by rfl⟩ : syracuseStep 1655719 = 2483579) B2483579
theorem B3728339 : Blo 1655527 3728339 := bstep (se 1 (by rfl) ⟨2796254, by rfl⟩ : syracuseStep 3728339 = 5592509) B5592509
theorem B1655803 : Blo 1655527 1655803 := bstep (se 1 (by rfl) ⟨1241852, by rfl⟩ : syracuseStep 1655803 = 2483705) B2483705
theorem B5588027 : Blo 1655527 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B1655871 : Blo 1655527 1655871 := bstep (se 1 (by rfl) ⟨1241903, by rfl⟩ : syracuseStep 1655871 = 2483807) B2483807
theorem B2794601 : Blo 1655527 2794601 := bstep (se 2 (by rfl) ⟨1047975, by rfl⟩ : syracuseStep 2794601 = 2095951) B2095951
theorem B2483375 : Blo 1655527 2483375 := bstep (se 1 (by rfl) ⟨1862531, by rfl⟩ : syracuseStep 2483375 = 3725063) B3725063
theorem B1656015 : Blo 1655527 1656015 := bstep (se 1 (by rfl) ⟨1242011, by rfl⟩ : syracuseStep 1656015 = 2484023) B2484023
theorem B3728591 : Blo 1655527 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B16991453 : Blo 1655527 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B18859229 : Blo 1655527 18859229 := bstep (se 3 (by rfl) ⟨3536105, by rfl⟩ : syracuseStep 18859229 = 7072211) B7072211
theorem B5588297 : Blo 1655527 5588297 := bstep (se 2 (by rfl) ⟨2095611, by rfl⟩ : syracuseStep 5588297 = 4191223) B4191223
theorem B1656219 : Blo 1655527 1656219 := bstep (se 1 (by rfl) ⟨1242164, by rfl⟩ : syracuseStep 1656219 = 2484329) B2484329
theorem B8390141 : Blo 1655527 8390141 := bstep (se 3 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 8390141 = 3146303) B3146303
theorem B3728915 : Blo 1655527 3728915 := bstep (se 1 (by rfl) ⟨2796686, by rfl⟩ : syracuseStep 3728915 = 5593373) B5593373
theorem B2483783 : Blo 1655527 2483783 := bstep (se 1 (by rfl) ⟨1862837, by rfl⟩ : syracuseStep 2483783 = 3725675) B3725675
theorem B1656431 : Blo 1655527 1656431 := bstep (se 1 (by rfl) ⟨1242323, by rfl⟩ : syracuseStep 1656431 = 2484647) B2484647
theorem B6293153 : Blo 1655527 6293153 := bstep (se 2 (by rfl) ⟨2359932, by rfl⟩ : syracuseStep 6293153 = 4719865) B4719865
theorem B2483879 : Blo 1655527 2483879 := bstep (se 1 (by rfl) ⟨1862909, by rfl⟩ : syracuseStep 2483879 = 3725819) B3725819
theorem B1656487 : Blo 1655527 1656487 := bstep (se 1 (by rfl) ⟨1242365, by rfl⟩ : syracuseStep 1656487 = 2484731) B2484731
theorem B2483963 : Blo 1655527 2483963 := bstep (se 1 (by rfl) ⟨1862972, by rfl⟩ : syracuseStep 2483963 = 3725945) B3725945
theorem B1656571 : Blo 1655527 1656571 := bstep (se 1 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 1656571 = 2484857) B2484857
theorem B2483999 : Blo 1655527 2483999 := bstep (se 1 (by rfl) ⟨1862999, by rfl⟩ : syracuseStep 2483999 = 3725999) B3725999
theorem B1656607 : Blo 1655527 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B1656639 : Blo 1655527 1656639 := bstep (se 1 (by rfl) ⟨1242479, by rfl⟩ : syracuseStep 1656639 = 2484959) B2484959
theorem B2484047 : Blo 1655527 2484047 := bstep (se 1 (by rfl) ⟨1863035, by rfl⟩ : syracuseStep 2484047 = 3726071) B3726071
theorem B2484167 : Blo 1655527 2484167 := bstep (se 1 (by rfl) ⟨1863125, by rfl⟩ : syracuseStep 2484167 = 3726251) B3726251
theorem B10078181 : Blo 1655527 10078181 := bstep (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) B1889659
theorem B1656815 : Blo 1655527 1656815 := bstep (se 1 (by rfl) ⟨1242611, by rfl⟩ : syracuseStep 1656815 = 2485223) B2485223
theorem B1656987 : Blo 1655527 1656987 := bstep (se 1 (by rfl) ⟨1242740, by rfl⟩ : syracuseStep 1656987 = 2485481) B2485481
theorem B1657023 : Blo 1655527 1657023 := bstep (se 1 (by rfl) ⟨1242767, by rfl⟩ : syracuseStep 1657023 = 2485535) B2485535
theorem B9431255 : Blo 1655527 9431255 := bstep (se 1 (by rfl) ⟨7073441, by rfl⟩ : syracuseStep 9431255 = 14146883) B14146883
theorem B2795755 : Blo 1655527 2795755 := bstep (se 1 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 2795755 = 4193633) B4193633
theorem B14158091 : Blo 1655527 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B8390951 : Blo 1655527 8390951 := bstep (se 1 (by rfl) ⟨6293213, by rfl⟩ : syracuseStep 8390951 = 12586427) B12586427
theorem B2484521 : Blo 1655527 2484521 := bstep (se 2 (by rfl) ⟨931695, by rfl⟩ : syracuseStep 2484521 = 1863391) B1863391
theorem B2984239 : Blo 1655527 2984239 := bstep (se 1 (by rfl) ⟨2238179, by rfl⟩ : syracuseStep 2984239 = 4476359) B4476359
theorem B2484527 : Blo 1655527 2484527 := bstep (se 1 (by rfl) ⟨1863395, by rfl⟩ : syracuseStep 2484527 = 3726791) B3726791
theorem B1657135 : Blo 1655527 1657135 := bstep (se 1 (by rfl) ⟨1242851, by rfl⟩ : syracuseStep 1657135 = 2485703) B2485703
theorem B15911245 : Blo 1655527 15911245 := bstep (se 3 (by rfl) ⟨2983358, by rfl⟩ : syracuseStep 15911245 = 5966717) B5966717
theorem B8391113 : Blo 1655527 8391113 := bstep (se 2 (by rfl) ⟨3146667, by rfl⟩ : syracuseStep 8391113 = 6293335) B6293335
theorem B50981363 : Blo 1655527 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B2796059 : Blo 1655527 2796059 := bstep (se 1 (by rfl) ⟨2097044, by rfl⟩ : syracuseStep 2796059 = 4194089) B4194089
theorem B1657371 : Blo 1655527 1657371 := bstep (se 1 (by rfl) ⟨1243028, by rfl⟩ : syracuseStep 1657371 = 2486057) B2486057
theorem B2484767 : Blo 1655527 2484767 := bstep (se 1 (by rfl) ⟨1863575, by rfl⟩ : syracuseStep 2484767 = 3727151) B3727151
theorem B1657375 : Blo 1655527 1657375 := bstep (se 1 (by rfl) ⟨1243031, by rfl⟩ : syracuseStep 1657375 = 2486063) B2486063
theorem B22669895 : Blo 1655527 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B47754035 : Blo 1655527 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1862491 : Blo 1655527 1862491 := bstep (se 1 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 1862491 = 2793737) B2793737
theorem B12577679 : Blo 1655527 12577679 := bstep (se 1 (by rfl) ⟨9433259, by rfl⟩ : syracuseStep 12577679 = 18866519) B18866519
theorem B2485151 : Blo 1655527 2485151 := bstep (se 1 (by rfl) ⟨1863863, by rfl⟩ : syracuseStep 2485151 = 3727727) B3727727
theorem B68037569 : Blo 1655527 68037569 := bstep (se 2 (by rfl) ⟨25514088, by rfl⟩ : syracuseStep 68037569 = 51028177) B51028177
theorem B2485199 : Blo 1655527 2485199 := bstep (se 1 (by rfl) ⟨1863899, by rfl⟩ : syracuseStep 2485199 = 3727799) B3727799
theorem B2485289 : Blo 1655527 2485289 := bstep (se 2 (by rfl) ⟨931983, by rfl⟩ : syracuseStep 2485289 = 1863967) B1863967
theorem B2485295 : Blo 1655527 2485295 := bstep (se 1 (by rfl) ⟨1863971, by rfl⟩ : syracuseStep 2485295 = 3727943) B3727943
theorem B2985031 : Blo 1655527 2985031 := bstep (se 1 (by rfl) ⟨2238773, by rfl⟩ : syracuseStep 2985031 = 4477547) B4477547
theorem B2485319 : Blo 1655527 2485319 := bstep (se 1 (by rfl) ⟨1863989, by rfl⟩ : syracuseStep 2485319 = 3727979) B3727979
theorem B23874659 : Blo 1655527 23874659 := bstep (se 1 (by rfl) ⟨17905994, by rfl⟩ : syracuseStep 23874659 = 35811989) B35811989
theorem B2796727 : Blo 1655527 2796727 := bstep (se 1 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 2796727 = 4195091) B4195091
theorem B2485583 : Blo 1655527 2485583 := bstep (se 1 (by rfl) ⟨1864187, by rfl⟩ : syracuseStep 2485583 = 3728375) B3728375
theorem B2485673 : Blo 1655527 2485673 := bstep (se 2 (by rfl) ⟨932127, by rfl⟩ : syracuseStep 2485673 = 1864255) B1864255
theorem B17911223 : Blo 1655527 17911223 := bstep (se 1 (by rfl) ⟨13433417, by rfl⟩ : syracuseStep 17911223 = 26866835) B26866835
theorem B2797031 : Blo 1655527 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B2797051 : Blo 1655527 2797051 := bstep (se 1 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 2797051 = 4195577) B4195577
theorem B2485823 : Blo 1655527 2485823 := bstep (se 1 (by rfl) ⟨1864367, by rfl⟩ : syracuseStep 2485823 = 3728735) B3728735
theorem B1863463 : Blo 1655527 1863463 := bstep (se 1 (by rfl) ⟨1397597, by rfl⟩ : syracuseStep 1863463 = 2795195) B2795195
theorem B2486087 : Blo 1655527 2486087 := bstep (se 1 (by rfl) ⟨1864565, by rfl⟩ : syracuseStep 2486087 = 3729131) B3729131
theorem B5590889 : Blo 1655527 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B11939723 : Blo 1655527 11939723 := bstep (se 1 (by rfl) ⟨8954792, by rfl⟩ : syracuseStep 11939723 = 17909585) B17909585
theorem B21229451 : Blo 1655527 21229451 := bstep (se 1 (by rfl) ⟨15922088, by rfl⟩ : syracuseStep 21229451 = 31844177) B31844177
theorem B21524363 : Blo 1655527 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B2486171 : Blo 1655527 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B33984461 : Blo 1655527 33984461 := bstep (se 3 (by rfl) ⟨6372086, by rfl⟩ : syracuseStep 33984461 = 12744173) B12744173
theorem B18862145 : Blo 1655527 18862145 := bstep (se 2 (by rfl) ⟨7073304, by rfl⟩ : syracuseStep 18862145 = 14146609) B14146609
theorem B4714625 : Blo 1655527 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B6287489 : Blo 1655527 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B9081467 : Blo 1655527 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B1864615 : Blo 1655527 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B4715435 : Blo 1655527 4715435 := bstep (se 1 (by rfl) ⟨3536576, by rfl⟩ : syracuseStep 4715435 = 7073153) B7073153
theorem B15913979 : Blo 1655527 15913979 := bstep (se 1 (by rfl) ⟨11935484, by rfl⟩ : syracuseStep 15913979 = 23870969) B23870969
theorem B5592239 : Blo 1655527 5592239 := bstep (se 1 (by rfl) ⟨4194179, by rfl⟩ : syracuseStep 5592239 = 8388359) B8388359
theorem B5305799 : Blo 1655527 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B5379527 : Blo 1655527 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B3143137 : Blo 1655527 3143137 := bstep (se 2 (by rfl) ⟨1178676, by rfl⟩ : syracuseStep 3143137 = 2357353) B2357353
theorem B18863603 : Blo 1655527 18863603 := bstep (se 1 (by rfl) ⟨14147702, by rfl⟩ : syracuseStep 18863603 = 28295405) B28295405
theorem B5306107 : Blo 1655527 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7960315 : Blo 1655527 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B57407237 : Blo 1655527 57407237 := bstep (se 4 (by rfl) ⟨5381928, by rfl⟩ : syracuseStep 57407237 = 10763857) B10763857
theorem B12105577 : Blo 1655527 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B95541281 : Blo 1655527 95541281 := bstep (se 2 (by rfl) ⟨35827980, by rfl⟩ : syracuseStep 95541281 = 71655961) B71655961
theorem B7075937 : Blo 1655527 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B24213667 : Blo 1655527 24213667 := bstep (se 1 (by rfl) ⟨18160250, by rfl⟩ : syracuseStep 24213667 = 36320501) B36320501
theorem B4192499 : Blo 1655527 4192499 := bstep (se 1 (by rfl) ⟨3144374, by rfl⟩ : syracuseStep 4192499 = 6288749) B6288749
theorem B4192519 : Blo 1655527 4192519 := bstep (se 1 (by rfl) ⟨3144389, by rfl⟩ : syracuseStep 4192519 = 6288779) B6288779
theorem B4717075 : Blo 1655527 4717075 := bstep (se 1 (by rfl) ⟨3537806, by rfl⟩ : syracuseStep 4717075 = 7075613) B7075613
theorem B12573305 : Blo 1655527 12573305 := bstep (se 2 (by rfl) ⟨4714989, by rfl⟩ : syracuseStep 12573305 = 9429979) B9429979
theorem B3144329 : Blo 1655527 3144329 := bstep (se 2 (by rfl) ⟨1179123, by rfl⟩ : syracuseStep 3144329 = 2358247) B2358247
theorem B8387225 : Blo 1655527 8387225 := bstep (se 2 (by rfl) ⟨3145209, by rfl⟩ : syracuseStep 8387225 = 6290419) B6290419
theorem B21519209 : Blo 1655527 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B3726287 : Blo 1655527 3726287 := bstep (se 1 (by rfl) ⟨2794715, by rfl⟩ : syracuseStep 3726287 = 5589431) B5589431
theorem B3726305 : Blo 1655527 3726305 := bstep (se 2 (by rfl) ⟨1397364, by rfl⟩ : syracuseStep 3726305 = 2794729) B2794729
theorem B23878637 : Blo 1655527 23878637 := bstep (se 3 (by rfl) ⟨4477244, by rfl⟩ : syracuseStep 23878637 = 8954489) B8954489
theorem B3726377 : Blo 1655527 3726377 := bstep (se 2 (by rfl) ⟨1397391, by rfl⟩ : syracuseStep 3726377 = 2794783) B2794783
theorem B60423529 : Blo 1655527 60423529 := bstep (se 2 (by rfl) ⟨22658823, by rfl⟩ : syracuseStep 60423529 = 45317647) B45317647
theorem B2833831 : Blo 1655527 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B8388035 : Blo 1655527 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B47775257 : Blo 1655527 47775257 := bstep (se 2 (by rfl) ⟨17915721, by rfl⟩ : syracuseStep 47775257 = 35831443) B35831443
theorem B5037815 : Blo 1655527 5037815 := bstep (se 1 (by rfl) ⟨3778361, by rfl⟩ : syracuseStep 5037815 = 7556723) B7556723
theorem B3776327 : Blo 1655527 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B4194119 : Blo 1655527 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B4718407 : Blo 1655527 4718407 := bstep (se 1 (by rfl) ⟨3538805, by rfl⟩ : syracuseStep 4718407 = 7077611) B7077611
theorem B2097019 : Blo 1655527 2097019 := bstep (se 1 (by rfl) ⟨1572764, by rfl⟩ : syracuseStep 2097019 = 3145529) B3145529
theorem B12574763 : Blo 1655527 12574763 := bstep (se 1 (by rfl) ⟨9431072, by rfl⟩ : syracuseStep 12574763 = 18862145) B18862145
theorem B2097343 : Blo 1655527 2097343 := bstep (se 1 (by rfl) ⟨1573007, by rfl⟩ : syracuseStep 2097343 = 3146015) B3146015
theorem B32284889 : Blo 1655527 32284889 := bstep (se 2 (by rfl) ⟨12106833, by rfl⟩ : syracuseStep 32284889 = 24213667) B24213667
theorem B6373595 : Blo 1655527 6373595 := bstep (se 1 (by rfl) ⟨4780196, by rfl⟩ : syracuseStep 6373595 = 9560393) B9560393
theorem B3727673 : Blo 1655527 3727673 := bstep (se 2 (by rfl) ⟨1397877, by rfl⟩ : syracuseStep 3727673 = 2795755) B2795755
theorem B6054311 : Blo 1655527 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B15925855 : Blo 1655527 15925855 := bstep (se 1 (by rfl) ⟨11944391, by rfl⟩ : syracuseStep 15925855 = 23888783) B23888783
theorem B10609319 : Blo 1655527 10609319 := bstep (se 1 (by rfl) ⟨7956989, by rfl⟩ : syracuseStep 10609319 = 15913979) B15913979
theorem B1655583 : Blo 1655527 1655583 := bstep (se 1 (by rfl) ⟨1241687, by rfl⟩ : syracuseStep 1655583 = 2483375) B2483375
theorem B3728159 : Blo 1655527 3728159 := bstep (se 1 (by rfl) ⟨2796119, by rfl⟩ : syracuseStep 3728159 = 5592239) B5592239
theorem B12575735 : Blo 1655527 12575735 := bstep (se 1 (by rfl) ⟨9431801, by rfl⟩ : syracuseStep 12575735 = 18863603) B18863603
theorem B7078909 : Blo 1655527 7078909 := bstep (se 3 (by rfl) ⟨1327295, by rfl⟩ : syracuseStep 7078909 = 2654591) B2654591
theorem B1655855 : Blo 1655527 1655855 := bstep (se 1 (by rfl) ⟨1241891, by rfl⟩ : syracuseStep 1655855 = 2483783) B2483783
theorem B4195435 : Blo 1655527 4195435 := bstep (se 1 (by rfl) ⟨3146576, by rfl⟩ : syracuseStep 4195435 = 6293153) B6293153
theorem B1655919 : Blo 1655527 1655919 := bstep (se 1 (by rfl) ⟨1241939, by rfl⟩ : syracuseStep 1655919 = 2483879) B2483879
theorem B2483321 : Blo 1655527 2483321 := bstep (se 2 (by rfl) ⟨931245, by rfl⟩ : syracuseStep 2483321 = 1862491) B1862491
theorem B1655975 : Blo 1655527 1655975 := bstep (se 1 (by rfl) ⟨1241981, by rfl⟩ : syracuseStep 1655975 = 2483963) B2483963
theorem B1655999 : Blo 1655527 1655999 := bstep (se 1 (by rfl) ⟨1241999, by rfl⟩ : syracuseStep 1655999 = 2483999) B2483999
theorem B1656031 : Blo 1655527 1656031 := bstep (se 1 (by rfl) ⟨1242023, by rfl⟩ : syracuseStep 1656031 = 2484047) B2484047
theorem B1656111 : Blo 1655527 1656111 := bstep (se 1 (by rfl) ⟨1242083, by rfl⟩ : syracuseStep 1656111 = 2484167) B2484167
theorem B6718787 : Blo 1655527 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B63694187 : Blo 1655527 63694187 := bstep (se 1 (by rfl) ⟨47770640, by rfl⟩ : syracuseStep 63694187 = 95541281) B95541281
theorem B2794999 : Blo 1655527 2794999 := bstep (se 1 (by rfl) ⟨2096249, by rfl⟩ : syracuseStep 2794999 = 4192499) B4192499
theorem B9438727 : Blo 1655527 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B1656347 : Blo 1655527 1656347 := bstep (se 1 (by rfl) ⟨1242260, by rfl⟩ : syracuseStep 1656347 = 2484521) B2484521
theorem B1656351 : Blo 1655527 1656351 := bstep (se 1 (by rfl) ⟨1242263, by rfl⟩ : syracuseStep 1656351 = 2484527) B2484527
theorem B3728969 : Blo 1655527 3728969 := bstep (se 2 (by rfl) ⟨1398363, by rfl⟩ : syracuseStep 3728969 = 2796727) B2796727
theorem B1656511 : Blo 1655527 1656511 := bstep (se 1 (by rfl) ⟨1242383, by rfl⟩ : syracuseStep 1656511 = 2484767) B2484767
theorem B8382203 : Blo 1655527 8382203 := bstep (se 1 (by rfl) ⟨6286652, by rfl⟩ : syracuseStep 8382203 = 12573305) B12573305
theorem B31836023 : Blo 1655527 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B64563077 : Blo 1655527 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B1656767 : Blo 1655527 1656767 := bstep (se 1 (by rfl) ⟨1242575, by rfl⟩ : syracuseStep 1656767 = 2485151) B2485151
theorem B2484191 : Blo 1655527 2484191 := bstep (se 1 (by rfl) ⟨1863143, by rfl⟩ : syracuseStep 2484191 = 3726287) B3726287
theorem B1656799 : Blo 1655527 1656799 := bstep (se 1 (by rfl) ⟨1242599, by rfl⟩ : syracuseStep 1656799 = 2485199) B2485199
theorem B2484203 : Blo 1655527 2484203 := bstep (se 1 (by rfl) ⟨1863152, by rfl⟩ : syracuseStep 2484203 = 3726305) B3726305
theorem B15919091 : Blo 1655527 15919091 := bstep (se 1 (by rfl) ⟨11939318, by rfl⟩ : syracuseStep 15919091 = 23878637) B23878637
theorem B3729401 : Blo 1655527 3729401 := bstep (se 2 (by rfl) ⟨1398525, by rfl⟩ : syracuseStep 3729401 = 2797051) B2797051
theorem B2484251 : Blo 1655527 2484251 := bstep (se 1 (by rfl) ⟨1863188, by rfl⟩ : syracuseStep 2484251 = 3726377) B3726377
theorem B1656859 : Blo 1655527 1656859 := bstep (se 1 (by rfl) ⟨1242644, by rfl⟩ : syracuseStep 1656859 = 2485289) B2485289
theorem B1656863 : Blo 1655527 1656863 := bstep (se 1 (by rfl) ⟨1242647, by rfl⟩ : syracuseStep 1656863 = 2485295) B2485295
theorem B1656879 : Blo 1655527 1656879 := bstep (se 1 (by rfl) ⟨1242659, by rfl⟩ : syracuseStep 1656879 = 2485319) B2485319
theorem B1657055 : Blo 1655527 1657055 := bstep (se 1 (by rfl) ⟨1242791, by rfl⟩ : syracuseStep 1657055 = 2485583) B2485583
theorem B1657115 : Blo 1655527 1657115 := bstep (se 1 (by rfl) ⟨1242836, by rfl⟩ : syracuseStep 1657115 = 2485673) B2485673
theorem B1657215 : Blo 1655527 1657215 := bstep (se 1 (by rfl) ⟨1242911, by rfl⟩ : syracuseStep 1657215 = 2485823) B2485823
theorem B2484617 : Blo 1655527 2484617 := bstep (se 2 (by rfl) ⟨931731, by rfl⟩ : syracuseStep 2484617 = 1863463) B1863463
theorem B2796025 : Blo 1655527 2796025 := bstep (se 2 (by rfl) ⟨1048509, by rfl⟩ : syracuseStep 2796025 = 2097019) B2097019
theorem B2517551 : Blo 1655527 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B2796079 : Blo 1655527 2796079 := bstep (se 1 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 2796079 = 4194119) B4194119
theorem B1657391 : Blo 1655527 1657391 := bstep (se 1 (by rfl) ⟨1243043, by rfl⟩ : syracuseStep 1657391 = 2486087) B2486087
theorem B1657447 : Blo 1655527 1657447 := bstep (se 1 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 1657447 = 2486171) B2486171
theorem B2796295 : Blo 1655527 2796295 := bstep (se 1 (by rfl) ⟨2097221, by rfl⟩ : syracuseStep 2796295 = 4194443) B4194443
theorem B2796511 : Blo 1655527 2796511 := bstep (se 1 (by rfl) ⟨2097383, by rfl⟩ : syracuseStep 2796511 = 4194767) B4194767
theorem B5590025 : Blo 1655527 5590025 := bstep (se 2 (by rfl) ⟨2096259, by rfl⟩ : syracuseStep 5590025 = 4192519) B4192519
theorem B15920165 : Blo 1655527 15920165 := bstep (se 4 (by rfl) ⟨1492515, by rfl⟩ : syracuseStep 15920165 = 2985031) B2985031
theorem B2485559 : Blo 1655527 2485559 := bstep (se 1 (by rfl) ⟨1864169, by rfl⟩ : syracuseStep 2485559 = 3728339) B3728339
theorem B1863067 : Blo 1655527 1863067 := bstep (se 1 (by rfl) ⟨1397300, by rfl⟩ : syracuseStep 1863067 = 2794601) B2794601
theorem B2485727 : Blo 1655527 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B2485943 : Blo 1655527 2485943 := bstep (se 1 (by rfl) ⟨1864457, by rfl⟩ : syracuseStep 2485943 = 3728915) B3728915
theorem B2486153 : Blo 1655527 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B6287503 : Blo 1655527 6287503 := bstep (se 1 (by rfl) ⟨4715627, by rfl⟩ : syracuseStep 6287503 = 9431255) B9431255
theorem B1864039 : Blo 1655527 1864039 := bstep (se 1 (by rfl) ⟨1398029, by rfl⟩ : syracuseStep 1864039 = 2796059) B2796059
theorem B5591483 : Blo 1655527 5591483 := bstep (se 1 (by rfl) ⟨4193612, by rfl⟩ : syracuseStep 5591483 = 8387225) B8387225
theorem B80564705 : Blo 1655527 80564705 := bstep (se 2 (by rfl) ⟨30211764, by rfl⟩ : syracuseStep 80564705 = 60423529) B60423529
theorem B8385119 : Blo 1655527 8385119 := bstep (se 1 (by rfl) ⟨6288839, by rfl⟩ : syracuseStep 8385119 = 12577679) B12577679
theorem B4190849 : Blo 1655527 4190849 := bstep (se 2 (by rfl) ⟨1571568, by rfl⟩ : syracuseStep 4190849 = 3143137) B3143137
theorem B11940815 : Blo 1655527 11940815 := bstep (se 1 (by rfl) ⟨8955611, by rfl⟩ : syracuseStep 11940815 = 17911223) B17911223
theorem B5592023 : Blo 1655527 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B1864687 : Blo 1655527 1864687 := bstep (se 1 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 1864687 = 2797031) B2797031
theorem B7074809 : Blo 1655527 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B10613753 : Blo 1655527 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B7959815 : Blo 1655527 7959815 := bstep (se 1 (by rfl) ⟨5969861, by rfl⟩ : syracuseStep 7959815 = 11939723) B11939723
theorem B14152967 : Blo 1655527 14152967 := bstep (se 1 (by rfl) ⟨10614725, by rfl⟩ : syracuseStep 14152967 = 21229451) B21229451
theorem B14349575 : Blo 1655527 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B22656307 : Blo 1655527 22656307 := bstep (se 1 (by rfl) ⟨16992230, by rfl⟩ : syracuseStep 22656307 = 33984461) B33984461
theorem B4191659 : Blo 1655527 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B3724937 : Blo 1655527 3724937 := bstep (se 2 (by rfl) ⟨1396851, by rfl⟩ : syracuseStep 3724937 = 2793703) B2793703
theorem B3724955 : Blo 1655527 3724955 := bstep (se 1 (by rfl) ⟨2793716, by rfl⟩ : syracuseStep 3724955 = 5587433) B5587433
theorem B12572333 : Blo 1655527 12572333 := bstep (se 3 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 12572333 = 4714625) B4714625
theorem B3978985 : Blo 1655527 3978985 := bstep (se 2 (by rfl) ⟨1492119, by rfl⟩ : syracuseStep 3978985 = 2984239) B2984239
theorem B21214993 : Blo 1655527 21214993 := bstep (se 2 (by rfl) ⟨7955622, by rfl⟩ : syracuseStep 21214993 = 15911245) B15911245
theorem B3725153 : Blo 1655527 3725153 := bstep (se 2 (by rfl) ⟨1396932, by rfl⟩ : syracuseStep 3725153 = 2793865) B2793865
theorem B3143623 : Blo 1655527 3143623 := bstep (se 1 (by rfl) ⟨2357717, by rfl⟩ : syracuseStep 3143623 = 4715435) B4715435
theorem B14342113 : Blo 1655527 14342113 := bstep (se 2 (by rfl) ⟨5378292, by rfl⟩ : syracuseStep 14342113 = 10756585) B10756585
theorem B6289433 : Blo 1655527 6289433 := bstep (se 2 (by rfl) ⟨2358537, by rfl⟩ : syracuseStep 6289433 = 4717075) B4717075
theorem B3725351 : Blo 1655527 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B11327635 : Blo 1655527 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B12572819 : Blo 1655527 12572819 := bstep (se 1 (by rfl) ⟨9429614, by rfl⟩ : syracuseStep 12572819 = 18859229) B18859229
theorem B3725531 : Blo 1655527 3725531 := bstep (se 1 (by rfl) ⟨2794148, by rfl⟩ : syracuseStep 3725531 = 5588297) B5588297
theorem B3537199 : Blo 1655527 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B3586351 : Blo 1655527 3586351 := bstep (se 1 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 3586351 = 5379527) B5379527
theorem B5593427 : Blo 1655527 5593427 := bstep (se 1 (by rfl) ⟨4195070, by rfl⟩ : syracuseStep 5593427 = 8390141) B8390141
theorem B3725729 : Blo 1655527 3725729 := bstep (se 2 (by rfl) ⟨1397148, by rfl⟩ : syracuseStep 3725729 = 2794297) B2794297
theorem B3725801 : Blo 1655527 3725801 := bstep (se 2 (by rfl) ⟨1397175, by rfl⟩ : syracuseStep 3725801 = 2794351) B2794351
theorem B4250089 : Blo 1655527 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B38271491 : Blo 1655527 38271491 := bstep (se 1 (by rfl) ⟨28703618, by rfl⟩ : syracuseStep 38271491 = 57407237) B57407237
theorem B4717291 : Blo 1655527 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B5593967 : Blo 1655527 5593967 := bstep (se 1 (by rfl) ⟨4195475, by rfl⟩ : syracuseStep 5593967 = 8390951) B8390951
theorem B5594075 : Blo 1655527 5594075 := bstep (se 1 (by rfl) ⟨4195556, by rfl⟩ : syracuseStep 5594075 = 8391113) B8391113
theorem B33987575 : Blo 1655527 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B15113263 : Blo 1655527 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B2096219 : Blo 1655527 2096219 := bstep (se 1 (by rfl) ⟨1572164, by rfl⟩ : syracuseStep 2096219 = 3144329) B3144329
theorem B45358379 : Blo 1655527 45358379 := bstep (se 1 (by rfl) ⟨34018784, by rfl⟩ : syracuseStep 45358379 = 68037569) B68037569
theorem B13434173 : Blo 1655527 13434173 := bstep (se 3 (by rfl) ⟨2518907, by rfl⟩ : syracuseStep 13434173 = 5037815) B5037815
theorem B15916439 : Blo 1655527 15916439 := bstep (se 1 (by rfl) ⟨11937329, by rfl⟩ : syracuseStep 15916439 = 23874659) B23874659
theorem B15113765 : Blo 1655527 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B57384557 : Blo 1655527 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B31850171 : Blo 1655527 31850171 := bstep (se 1 (by rfl) ⟨23887628, by rfl⟩ : syracuseStep 31850171 = 47775257) B47775257
theorem B6291209 : Blo 1655527 6291209 := bstep (se 2 (by rfl) ⟨2359203, by rfl⟩ : syracuseStep 6291209 = 4718407) B4718407
theorem B3727259 : Blo 1655527 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B3727655 : Blo 1655527 3727655 := bstep (se 1 (by rfl) ⟨2795741, by rfl⟩ : syracuseStep 3727655 = 5591483) B5591483
theorem B2793899 : Blo 1655527 2793899 := bstep (se 1 (by rfl) ⟨2095424, by rfl⟩ : syracuseStep 2793899 = 4190849) B4190849
theorem B3728015 : Blo 1655527 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B3728033 : Blo 1655527 3728033 := bstep (se 2 (by rfl) ⟨1398012, by rfl⟩ : syracuseStep 3728033 = 2796025) B2796025
theorem B3728105 : Blo 1655527 3728105 := bstep (se 2 (by rfl) ⟨1398039, by rfl⟩ : syracuseStep 3728105 = 2796079) B2796079
theorem B1655547 : Blo 1655527 1655547 := bstep (se 1 (by rfl) ⟨1241660, by rfl⟩ : syracuseStep 1655547 = 2483321) B2483321
theorem B21234473 : Blo 1655527 21234473 := bstep (se 2 (by rfl) ⟨7962927, by rfl⟩ : syracuseStep 21234473 = 15925855) B15925855
theorem B2794439 : Blo 1655527 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B3728393 : Blo 1655527 3728393 := bstep (se 2 (by rfl) ⟨1398147, by rfl⟩ : syracuseStep 3728393 = 2796295) B2796295
theorem B2483291 : Blo 1655527 2483291 := bstep (se 1 (by rfl) ⟨1862468, by rfl⟩ : syracuseStep 2483291 = 3724937) B3724937
theorem B2483303 : Blo 1655527 2483303 := bstep (se 1 (by rfl) ⟨1862477, by rfl⟩ : syracuseStep 2483303 = 3724955) B3724955
theorem B8381555 : Blo 1655527 8381555 := bstep (se 1 (by rfl) ⟨6286166, by rfl⟩ : syracuseStep 8381555 = 12572333) B12572333
theorem B5588135 : Blo 1655527 5588135 := bstep (se 1 (by rfl) ⟨4191101, by rfl⟩ : syracuseStep 5588135 = 8382203) B8382203
theorem B2483435 : Blo 1655527 2483435 := bstep (se 1 (by rfl) ⟨1862576, by rfl⟩ : syracuseStep 2483435 = 3725153) B3725153
theorem B43042051 : Blo 1655527 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B3728681 : Blo 1655527 3728681 := bstep (se 2 (by rfl) ⟨1398255, by rfl⟩ : syracuseStep 3728681 = 2796511) B2796511
theorem B1656127 : Blo 1655527 1656127 := bstep (se 1 (by rfl) ⟨1242095, by rfl⟩ : syracuseStep 1656127 = 2484191) B2484191
theorem B1656135 : Blo 1655527 1656135 := bstep (se 1 (by rfl) ⟨1242101, by rfl⟩ : syracuseStep 1656135 = 2484203) B2484203
theorem B9438545 : Blo 1655527 9438545 := bstep (se 2 (by rfl) ⟨3539454, by rfl⟩ : syracuseStep 9438545 = 7078909) B7078909
theorem B1656167 : Blo 1655527 1656167 := bstep (se 1 (by rfl) ⟨1242125, by rfl⟩ : syracuseStep 1656167 = 2484251) B2484251
theorem B2483567 : Blo 1655527 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B8381879 : Blo 1655527 8381879 := bstep (se 1 (by rfl) ⟨6286409, by rfl⟩ : syracuseStep 8381879 = 12572819) B12572819
theorem B2483687 : Blo 1655527 2483687 := bstep (se 1 (by rfl) ⟨1862765, by rfl⟩ : syracuseStep 2483687 = 3725531) B3725531
theorem B3728951 : Blo 1655527 3728951 := bstep (se 1 (by rfl) ⟨2796713, by rfl⟩ : syracuseStep 3728951 = 5593427) B5593427
theorem B1656411 : Blo 1655527 1656411 := bstep (se 1 (by rfl) ⟨1242308, by rfl⟩ : syracuseStep 1656411 = 2484617) B2484617
theorem B2483819 : Blo 1655527 2483819 := bstep (se 1 (by rfl) ⟨1862864, by rfl⟩ : syracuseStep 2483819 = 3725729) B3725729
theorem B2483867 : Blo 1655527 2483867 := bstep (se 1 (by rfl) ⟨1862900, by rfl⟩ : syracuseStep 2483867 = 3725801) B3725801
theorem B2484089 : Blo 1655527 2484089 := bstep (se 2 (by rfl) ⟨931533, by rfl⟩ : syracuseStep 2484089 = 1863067) B1863067
theorem B3729311 : Blo 1655527 3729311 := bstep (se 1 (by rfl) ⟨2796983, by rfl⟩ : syracuseStep 3729311 = 5593967) B5593967
theorem B3729383 : Blo 1655527 3729383 := bstep (se 1 (by rfl) ⟨2797037, by rfl⟩ : syracuseStep 3729383 = 5594075) B5594075
theorem B12584969 : Blo 1655527 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B30238919 : Blo 1655527 30238919 := bstep (se 1 (by rfl) ⟨22679189, by rfl⟩ : syracuseStep 30238919 = 45358379) B45358379
theorem B1657039 : Blo 1655527 1657039 := bstep (se 1 (by rfl) ⟨1242779, by rfl⟩ : syracuseStep 1657039 = 2485559) B2485559
theorem B8956115 : Blo 1655527 8956115 := bstep (se 1 (by rfl) ⟨6717086, by rfl⟩ : syracuseStep 8956115 = 13434173) B13434173
theorem B10610959 : Blo 1655527 10610959 := bstep (se 1 (by rfl) ⟨7958219, by rfl⟩ : syracuseStep 10610959 = 15916439) B15916439
theorem B1657151 : Blo 1655527 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B1657295 : Blo 1655527 1657295 := bstep (se 1 (by rfl) ⟨1242971, by rfl⟩ : syracuseStep 1657295 = 2485943) B2485943
theorem B1657435 : Blo 1655527 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B2484839 : Blo 1655527 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B19122817 : Blo 1655527 19122817 := bstep (se 2 (by rfl) ⟨7171056, by rfl⟩ : syracuseStep 19122817 = 14342113) B14342113
theorem B8383175 : Blo 1655527 8383175 := bstep (se 1 (by rfl) ⟨6287381, by rfl⟩ : syracuseStep 8383175 = 12574763) B12574763
theorem B21523259 : Blo 1655527 21523259 := bstep (se 1 (by rfl) ⟨16142444, by rfl⟩ : syracuseStep 21523259 = 32284889) B32284889
theorem B8383337 : Blo 1655527 8383337 := bstep (se 2 (by rfl) ⟨3143751, by rfl⟩ : syracuseStep 8383337 = 6287503) B6287503
theorem B2485115 : Blo 1655527 2485115 := bstep (se 1 (by rfl) ⟨1863836, by rfl⟩ : syracuseStep 2485115 = 3727673) B3727673
theorem B5589917 : Blo 1655527 5589917 := bstep (se 3 (by rfl) ⟨1048109, by rfl⟩ : syracuseStep 5589917 = 2096219) B2096219
theorem B2796457 : Blo 1655527 2796457 := bstep (se 2 (by rfl) ⟨1048671, by rfl⟩ : syracuseStep 2796457 = 2097343) B2097343
theorem B53709803 : Blo 1655527 53709803 := bstep (se 1 (by rfl) ⟨40282352, by rfl⟩ : syracuseStep 53709803 = 80564705) B80564705
theorem B5590079 : Blo 1655527 5590079 := bstep (se 1 (by rfl) ⟨4192559, by rfl⟩ : syracuseStep 5590079 = 8385119) B8385119
theorem B7072879 : Blo 1655527 7072879 := bstep (se 1 (by rfl) ⟨5304659, by rfl⟩ : syracuseStep 7072879 = 10609319) B10609319
theorem B2485385 : Blo 1655527 2485385 := bstep (se 2 (by rfl) ⟨932019, by rfl⟩ : syracuseStep 2485385 = 1864039) B1864039
theorem B2485439 : Blo 1655527 2485439 := bstep (se 1 (by rfl) ⟨1864079, by rfl⟩ : syracuseStep 2485439 = 3728159) B3728159
theorem B8383823 : Blo 1655527 8383823 := bstep (se 1 (by rfl) ⟨6287867, by rfl⟩ : syracuseStep 8383823 = 12575735) B12575735
theorem B42462791 : Blo 1655527 42462791 := bstep (se 1 (by rfl) ⟨31847093, by rfl⟩ : syracuseStep 42462791 = 63694187) B63694187
theorem B76508821 : Blo 1655527 76508821 := bstep (se 6 (by rfl) ⟨1793175, by rfl⟩ : syracuseStep 76508821 = 3586351) B3586351
theorem B2485979 : Blo 1655527 2485979 := bstep (se 1 (by rfl) ⟨1864484, by rfl⟩ : syracuseStep 2485979 = 3728969) B3728969
theorem B2486249 : Blo 1655527 2486249 := bstep (se 2 (by rfl) ⟨932343, by rfl⟩ : syracuseStep 2486249 = 1864687) B1864687
theorem B10612727 : Blo 1655527 10612727 := bstep (se 1 (by rfl) ⟨7959545, by rfl⟩ : syracuseStep 10612727 = 15919091) B15919091
theorem B2486267 : Blo 1655527 2486267 := bstep (se 1 (by rfl) ⟨1864700, by rfl⟩ : syracuseStep 2486267 = 3729401) B3729401
theorem B25514327 : Blo 1655527 25514327 := bstep (se 1 (by rfl) ⟨19135745, by rfl⟩ : syracuseStep 25514327 = 38271491) B38271491
theorem B30208409 : Blo 1655527 30208409 := bstep (se 2 (by rfl) ⟨11328153, by rfl⟩ : syracuseStep 30208409 = 22656307) B22656307
theorem B10613443 : Blo 1655527 10613443 := bstep (se 1 (by rfl) ⟨7960082, by rfl⟩ : syracuseStep 10613443 = 15920165) B15920165
theorem B5305313 : Blo 1655527 5305313 := bstep (se 2 (by rfl) ⟨1989492, by rfl⟩ : syracuseStep 5305313 = 3978985) B3978985
theorem B4191497 : Blo 1655527 4191497 := bstep (se 2 (by rfl) ⟨1571811, by rfl⟩ : syracuseStep 4191497 = 3143623) B3143623
theorem B4249063 : Blo 1655527 4249063 := bstep (se 1 (by rfl) ⟨3186797, by rfl⟩ : syracuseStep 4249063 = 6373595) B6373595
theorem B15103513 : Blo 1655527 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B4716539 : Blo 1655527 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B7075835 : Blo 1655527 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B5306543 : Blo 1655527 5306543 := bstep (se 1 (by rfl) ⟨3979907, by rfl⟩ : syracuseStep 5306543 = 7959815) B7959815
theorem B9435311 : Blo 1655527 9435311 := bstep (se 1 (by rfl) ⟨7076483, by rfl⟩ : syracuseStep 9435311 = 14152967) B14152967
theorem B9566383 : Blo 1655527 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B4479191 : Blo 1655527 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B6289721 : Blo 1655527 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B16144829 : Blo 1655527 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B21224015 : Blo 1655527 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B4192955 : Blo 1655527 4192955 := bstep (se 1 (by rfl) ⟨3144716, by rfl⟩ : syracuseStep 4192955 = 6289433) B6289433
theorem B20151017 : Blo 1655527 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B5593913 : Blo 1655527 5593913 := bstep (se 2 (by rfl) ⟨2097717, by rfl⟩ : syracuseStep 5593913 = 4195435) B4195435
theorem B18865061 : Blo 1655527 18865061 := bstep (se 4 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 18865061 = 3537199) B3537199
theorem B1678367 : Blo 1655527 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B3726665 : Blo 1655527 3726665 := bstep (se 2 (by rfl) ⟨1397499, by rfl⟩ : syracuseStep 3726665 = 2794999) B2794999
theorem B22658383 : Blo 1655527 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B3726683 : Blo 1655527 3726683 := bstep (se 1 (by rfl) ⟨2795012, by rfl⟩ : syracuseStep 3726683 = 5590025) B5590025
theorem B28286657 : Blo 1655527 28286657 := bstep (se 2 (by rfl) ⟨10607496, by rfl⟩ : syracuseStep 28286657 = 21214993) B21214993
theorem B10075843 : Blo 1655527 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B38256371 : Blo 1655527 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B21233447 : Blo 1655527 21233447 := bstep (se 1 (by rfl) ⟨15925085, by rfl⟩ : syracuseStep 21233447 = 31850171) B31850171
theorem B4194139 : Blo 1655527 4194139 := bstep (se 1 (by rfl) ⟨3145604, by rfl⟩ : syracuseStep 4194139 = 6291209) B6291209
theorem B31842173 : Blo 1655527 31842173 := bstep (se 3 (by rfl) ⟨5970407, by rfl⟩ : syracuseStep 31842173 = 11940815) B11940815
theorem B22667141 : Blo 1655527 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B12755177 : Blo 1655527 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B14147945 : Blo 1655527 14147945 := bstep (se 2 (by rfl) ⟨5305479, by rfl⟩ : syracuseStep 14147945 = 10610959) B10610959
theorem B14156315 : Blo 1655527 14156315 := bstep (se 1 (by rfl) ⟨10617236, by rfl⟩ : syracuseStep 14156315 = 21234473) B21234473
theorem B1655527 : Blo 1655527 1655527 := bstep (se 1 (by rfl) ⟨1241645, by rfl⟩ : syracuseStep 1655527 = 2483291) B2483291
theorem B1655535 : Blo 1655527 1655535 := bstep (se 1 (by rfl) ⟨1241651, by rfl⟩ : syracuseStep 1655535 = 2483303) B2483303
theorem B5587703 : Blo 1655527 5587703 := bstep (se 1 (by rfl) ⟨4190777, by rfl⟩ : syracuseStep 5587703 = 8381555) B8381555
theorem B1655623 : Blo 1655527 1655623 := bstep (se 1 (by rfl) ⟨1241717, by rfl⟩ : syracuseStep 1655623 = 2483435) B2483435
theorem B2794331 : Blo 1655527 2794331 := bstep (se 1 (by rfl) ⟨2095748, by rfl⟩ : syracuseStep 2794331 = 4191497) B4191497
theorem B6292363 : Blo 1655527 6292363 := bstep (se 1 (by rfl) ⟨4719272, by rfl⟩ : syracuseStep 6292363 = 9438545) B9438545
theorem B1655711 : Blo 1655527 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B5587919 : Blo 1655527 5587919 := bstep (se 1 (by rfl) ⟨4190939, by rfl⟩ : syracuseStep 5587919 = 8381879) B8381879
theorem B1655791 : Blo 1655527 1655791 := bstep (se 1 (by rfl) ⟨1241843, by rfl⟩ : syracuseStep 1655791 = 2483687) B2483687
theorem B1655879 : Blo 1655527 1655879 := bstep (se 1 (by rfl) ⟨1241909, by rfl⟩ : syracuseStep 1655879 = 2483819) B2483819
theorem B1655911 : Blo 1655527 1655911 := bstep (se 1 (by rfl) ⟨1241933, by rfl⟩ : syracuseStep 1655911 = 2483867) B2483867
theorem B3728609 : Blo 1655527 3728609 := bstep (se 2 (by rfl) ⟨1398228, by rfl⟩ : syracuseStep 3728609 = 2796457) B2796457
theorem B1656059 : Blo 1655527 1656059 := bstep (se 1 (by rfl) ⟨1242044, by rfl⟩ : syracuseStep 1656059 = 2484089) B2484089
theorem B8389979 : Blo 1655527 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B9430505 : Blo 1655527 9430505 := bstep (se 2 (by rfl) ⟨3536439, by rfl⟩ : syracuseStep 9430505 = 7072879) B7072879
theorem B14149343 : Blo 1655527 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B1656559 : Blo 1655527 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B2795303 : Blo 1655527 2795303 := bstep (se 1 (by rfl) ⟨2096477, by rfl⟩ : syracuseStep 2795303 = 4192955) B4192955
theorem B5588783 : Blo 1655527 5588783 := bstep (se 1 (by rfl) ⟨4191587, by rfl⟩ : syracuseStep 5588783 = 8383175) B8383175
theorem B3729275 : Blo 1655527 3729275 := bstep (se 1 (by rfl) ⟨2796956, by rfl⟩ : syracuseStep 3729275 = 5593913) B5593913
theorem B5588891 : Blo 1655527 5588891 := bstep (se 1 (by rfl) ⟨4191668, by rfl⟩ : syracuseStep 5588891 = 8383337) B8383337
theorem B1656743 : Blo 1655527 1656743 := bstep (se 1 (by rfl) ⟨1242557, by rfl⟩ : syracuseStep 1656743 = 2485115) B2485115
theorem B12576707 : Blo 1655527 12576707 := bstep (se 1 (by rfl) ⟨9432530, by rfl⟩ : syracuseStep 12576707 = 18865061) B18865061
theorem B20138017 : Blo 1655527 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B1656923 : Blo 1655527 1656923 := bstep (se 1 (by rfl) ⟨1242692, by rfl⟩ : syracuseStep 1656923 = 2485385) B2485385
theorem B1656959 : Blo 1655527 1656959 := bstep (se 1 (by rfl) ⟨1242719, by rfl⟩ : syracuseStep 1656959 = 2485439) B2485439
theorem B2484443 : Blo 1655527 2484443 := bstep (se 1 (by rfl) ⟨1863332, by rfl⟩ : syracuseStep 2484443 = 3726665) B3726665
theorem B5589215 : Blo 1655527 5589215 := bstep (se 1 (by rfl) ⟨4191911, by rfl⟩ : syracuseStep 5589215 = 8383823) B8383823
theorem B2484455 : Blo 1655527 2484455 := bstep (se 1 (by rfl) ⟨1863341, by rfl⟩ : syracuseStep 2484455 = 3726683) B3726683
theorem B1657319 : Blo 1655527 1657319 := bstep (se 1 (by rfl) ⟨1242989, by rfl⟩ : syracuseStep 1657319 = 2485979) B2485979
theorem B25504247 : Blo 1655527 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B22661669 : Blo 1655527 22661669 := bstep (se 4 (by rfl) ⟨2124531, by rfl⟩ : syracuseStep 22661669 = 4249063) B4249063
theorem B21228115 : Blo 1655527 21228115 := bstep (se 1 (by rfl) ⟨15921086, by rfl⟩ : syracuseStep 21228115 = 31842173) B31842173
theorem B1657499 : Blo 1655527 1657499 := bstep (se 1 (by rfl) ⟨1243124, by rfl⟩ : syracuseStep 1657499 = 2486249) B2486249
theorem B1657511 : Blo 1655527 1657511 := bstep (se 1 (by rfl) ⟨1243133, by rfl⟩ : syracuseStep 1657511 = 2486267) B2486267
theorem B4475645 : Blo 1655527 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B2485103 : Blo 1655527 2485103 := bstep (se 1 (by rfl) ⟨1863827, by rfl⟩ : syracuseStep 2485103 = 3727655) B3727655
theorem B17009551 : Blo 1655527 17009551 := bstep (se 1 (by rfl) ⟨12757163, by rfl⟩ : syracuseStep 17009551 = 25514327) B25514327
theorem B20138939 : Blo 1655527 20138939 := bstep (se 1 (by rfl) ⟨15104204, by rfl⟩ : syracuseStep 20138939 = 30208409) B30208409
theorem B1862599 : Blo 1655527 1862599 := bstep (se 1 (by rfl) ⟨1396949, by rfl⟩ : syracuseStep 1862599 = 2793899) B2793899
theorem B2485343 : Blo 1655527 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B2485355 : Blo 1655527 2485355 := bstep (se 1 (by rfl) ⟨1864016, by rfl⟩ : syracuseStep 2485355 = 3728033) B3728033
theorem B2485403 : Blo 1655527 2485403 := bstep (se 1 (by rfl) ⟨1864052, by rfl⟩ : syracuseStep 2485403 = 3728105) B3728105
theorem B1862959 : Blo 1655527 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B2485595 : Blo 1655527 2485595 := bstep (se 1 (by rfl) ⟨1864196, by rfl⟩ : syracuseStep 2485595 = 3728393) B3728393
theorem B25497089 : Blo 1655527 25497089 := bstep (se 2 (by rfl) ⟨9561408, by rfl⟩ : syracuseStep 25497089 = 19122817) B19122817
theorem B2485787 : Blo 1655527 2485787 := bstep (se 1 (by rfl) ⟨1864340, by rfl⟩ : syracuseStep 2485787 = 3728681) B3728681
theorem B14151257 : Blo 1655527 14151257 := bstep (se 2 (by rfl) ⟨5306721, by rfl⟩ : syracuseStep 14151257 = 10613443) B10613443
theorem B2485967 : Blo 1655527 2485967 := bstep (se 1 (by rfl) ⟨1864475, by rfl⟩ : syracuseStep 2485967 = 3728951) B3728951
theorem B2486207 : Blo 1655527 2486207 := bstep (se 1 (by rfl) ⟨1864655, by rfl⟩ : syracuseStep 2486207 = 3729311) B3729311
theorem B2486255 : Blo 1655527 2486255 := bstep (se 1 (by rfl) ⟨1864691, by rfl⟩ : syracuseStep 2486255 = 3729383) B3729383
theorem B2986127 : Blo 1655527 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B57389401 : Blo 1655527 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B14348839 : Blo 1655527 14348839 := bstep (se 1 (by rfl) ⟨10761629, by rfl⟩ : syracuseStep 14348839 = 21523259) B21523259
theorem B102011761 : Blo 1655527 102011761 := bstep (se 2 (by rfl) ⟨38254410, by rfl⟩ : syracuseStep 102011761 = 76508821) B76508821
theorem B60445709 : Blo 1655527 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B28308527 : Blo 1655527 28308527 := bstep (se 1 (by rfl) ⟨21231395, by rfl⟩ : syracuseStep 28308527 = 42462791) B42462791
theorem B5592185 : Blo 1655527 5592185 := bstep (se 2 (by rfl) ⟨2097069, by rfl⟩ : syracuseStep 5592185 = 4194139) B4194139
theorem B7075151 : Blo 1655527 7075151 := bstep (se 1 (by rfl) ⟨5306363, by rfl⟩ : syracuseStep 7075151 = 10612727) B10612727
theorem B3536875 : Blo 1655527 3536875 := bstep (se 1 (by rfl) ⟨2652656, by rfl⟩ : syracuseStep 3536875 = 5305313) B5305313
theorem B3725423 : Blo 1655527 3725423 := bstep (se 1 (by rfl) ⟨2794067, by rfl⟩ : syracuseStep 3725423 = 5588135) B5588135
theorem B3144359 : Blo 1655527 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4717223 : Blo 1655527 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B3537695 : Blo 1655527 3537695 := bstep (se 1 (by rfl) ⟨2653271, by rfl⟩ : syracuseStep 3537695 = 5306543) B5306543
theorem B6290207 : Blo 1655527 6290207 := bstep (se 1 (by rfl) ⟨4717655, by rfl⟩ : syracuseStep 6290207 = 9435311) B9435311
theorem B20159279 : Blo 1655527 20159279 := bstep (se 1 (by rfl) ⟨15119459, by rfl⟩ : syracuseStep 20159279 = 30238919) B30238919
theorem B5970743 : Blo 1655527 5970743 := bstep (se 1 (by rfl) ⟨4478057, by rfl⟩ : syracuseStep 5970743 = 8956115) B8956115
theorem B4193147 : Blo 1655527 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B10763219 : Blo 1655527 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B30211177 : Blo 1655527 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B13434011 : Blo 1655527 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B3726611 : Blo 1655527 3726611 := bstep (se 1 (by rfl) ⟨2794958, by rfl⟩ : syracuseStep 3726611 = 5589917) B5589917
theorem B35806535 : Blo 1655527 35806535 := bstep (se 1 (by rfl) ⟨26854901, by rfl⟩ : syracuseStep 35806535 = 53709803) B53709803
theorem B3726719 : Blo 1655527 3726719 := bstep (se 1 (by rfl) ⟨2795039, by rfl⟩ : syracuseStep 3726719 = 5590079) B5590079
theorem B13434457 : Blo 1655527 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B18857771 : Blo 1655527 18857771 := bstep (se 1 (by rfl) ⟨14143328, by rfl⟩ : syracuseStep 18857771 = 28286657) B28286657
theorem B14155631 : Blo 1655527 14155631 := bstep (se 1 (by rfl) ⟨10616723, by rfl⟩ : syracuseStep 14155631 = 21233447) B21233447
theorem B1990751 : Blo 1655527 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B8503451 : Blo 1655527 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B9437543 : Blo 1655527 9437543 := bstep (se 1 (by rfl) ⟨7078157, by rfl⟩ : syracuseStep 9437543 = 14156315) B14156315
theorem B40297139 : Blo 1655527 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B3728123 : Blo 1655527 3728123 := bstep (se 1 (by rfl) ⟨2796092, by rfl⟩ : syracuseStep 3728123 = 5592185) B5592185
theorem B28304153 : Blo 1655527 28304153 := bstep (se 2 (by rfl) ⟨10614057, by rfl⟩ : syracuseStep 28304153 = 21228115) B21228115
theorem B8389817 : Blo 1655527 8389817 := bstep (se 2 (by rfl) ⟨3146181, by rfl⟩ : syracuseStep 8389817 = 6292363) B6292363
theorem B2483465 : Blo 1655527 2483465 := bstep (se 2 (by rfl) ⟨931299, by rfl⟩ : syracuseStep 2483465 = 1862599) B1862599
theorem B2483615 : Blo 1655527 2483615 := bstep (se 1 (by rfl) ⟨1862711, by rfl⟩ : syracuseStep 2483615 = 3725423) B3725423
theorem B40281569 : Blo 1655527 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B1656295 : Blo 1655527 1656295 := bstep (se 1 (by rfl) ⟨1242221, by rfl⟩ : syracuseStep 1656295 = 2484443) B2484443
theorem B1656303 : Blo 1655527 1656303 := bstep (se 1 (by rfl) ⟨1242227, by rfl⟩ : syracuseStep 1656303 = 2484455) B2484455
theorem B15107779 : Blo 1655527 15107779 := bstep (se 1 (by rfl) ⟨11330834, by rfl⟩ : syracuseStep 15107779 = 22661669) B22661669
theorem B2483945 : Blo 1655527 2483945 := bstep (se 2 (by rfl) ⟨931479, by rfl⟩ : syracuseStep 2483945 = 1862959) B1862959
theorem B2983763 : Blo 1655527 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B1656735 : Blo 1655527 1656735 := bstep (se 1 (by rfl) ⟨1242551, by rfl⟩ : syracuseStep 1656735 = 2485103) B2485103
theorem B2795431 : Blo 1655527 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B1656895 : Blo 1655527 1656895 := bstep (se 1 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 1656895 = 2485343) B2485343
theorem B1656903 : Blo 1655527 1656903 := bstep (se 1 (by rfl) ⟨1242677, by rfl⟩ : syracuseStep 1656903 = 2485355) B2485355
theorem B8956007 : Blo 1655527 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B1656935 : Blo 1655527 1656935 := bstep (se 1 (by rfl) ⟨1242701, by rfl⟩ : syracuseStep 1656935 = 2485403) B2485403
theorem B2484407 : Blo 1655527 2484407 := bstep (se 1 (by rfl) ⟨1863305, by rfl⟩ : syracuseStep 2484407 = 3726611) B3726611
theorem B1657063 : Blo 1655527 1657063 := bstep (se 1 (by rfl) ⟨1242797, by rfl⟩ : syracuseStep 1657063 = 2485595) B2485595
theorem B2484479 : Blo 1655527 2484479 := bstep (se 1 (by rfl) ⟨1863359, by rfl⟩ : syracuseStep 2484479 = 3726719) B3726719
theorem B1657191 : Blo 1655527 1657191 := bstep (se 1 (by rfl) ⟨1242893, by rfl⟩ : syracuseStep 1657191 = 2485787) B2485787
theorem B1657311 : Blo 1655527 1657311 := bstep (se 1 (by rfl) ⟨1242983, by rfl⟩ : syracuseStep 1657311 = 2485967) B2485967
theorem B1657471 : Blo 1655527 1657471 := bstep (se 1 (by rfl) ⟨1243103, by rfl⟩ : syracuseStep 1657471 = 2486207) B2486207
theorem B1657503 : Blo 1655527 1657503 := bstep (se 1 (by rfl) ⟨1243127, by rfl⟩ : syracuseStep 1657503 = 2486255) B2486255
theorem B9431963 : Blo 1655527 9431963 := bstep (se 1 (by rfl) ⟨7073972, by rfl⟩ : syracuseStep 9431963 = 14147945) B14147945
theorem B1862887 : Blo 1655527 1862887 := bstep (se 1 (by rfl) ⟨1397165, by rfl⟩ : syracuseStep 1862887 = 2794331) B2794331
theorem B19131785 : Blo 1655527 19131785 := bstep (se 2 (by rfl) ⟨7174419, by rfl⟩ : syracuseStep 19131785 = 14348839) B14348839
theorem B2485739 : Blo 1655527 2485739 := bstep (se 1 (by rfl) ⟨1864304, by rfl⟩ : syracuseStep 2485739 = 3728609) B3728609
theorem B6287003 : Blo 1655527 6287003 := bstep (se 1 (by rfl) ⟨4715252, by rfl⟩ : syracuseStep 6287003 = 9430505) B9430505
theorem B9432895 : Blo 1655527 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B136015681 : Blo 1655527 136015681 := bstep (se 2 (by rfl) ⟨51005880, by rfl⟩ : syracuseStep 136015681 = 102011761) B102011761
theorem B22679401 : Blo 1655527 22679401 := bstep (se 2 (by rfl) ⟨8504775, by rfl⟩ : syracuseStep 22679401 = 17009551) B17009551
theorem B1863535 : Blo 1655527 1863535 := bstep (se 1 (by rfl) ⟨1397651, by rfl⟩ : syracuseStep 1863535 = 2795303) B2795303
theorem B2486183 : Blo 1655527 2486183 := bstep (se 1 (by rfl) ⟨1864637, by rfl⟩ : syracuseStep 2486183 = 3729275) B3729275
theorem B8384471 : Blo 1655527 8384471 := bstep (se 1 (by rfl) ⟨6288353, by rfl⟩ : syracuseStep 8384471 = 12576707) B12576707
theorem B17002831 : Blo 1655527 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B8384957 : Blo 1655527 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B13439519 : Blo 1655527 13439519 := bstep (se 1 (by rfl) ⟨10079639, by rfl⟩ : syracuseStep 13439519 = 20159279) B20159279
theorem B9433853 : Blo 1655527 9433853 := bstep (se 3 (by rfl) ⟨1768847, by rfl⟩ : syracuseStep 9433853 = 3537695) B3537695
theorem B17912609 : Blo 1655527 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B9434171 : Blo 1655527 9434171 := bstep (se 1 (by rfl) ⟨7075628, by rfl⟩ : syracuseStep 9434171 = 14151257) B14151257
theorem B12571847 : Blo 1655527 12571847 := bstep (se 1 (by rfl) ⟨9428885, by rfl⟩ : syracuseStep 12571847 = 18857771) B18857771
theorem B4715833 : Blo 1655527 4715833 := bstep (se 2 (by rfl) ⟨1768437, by rfl⟩ : syracuseStep 4715833 = 3536875) B3536875
theorem B26850689 : Blo 1655527 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B76519201 : Blo 1655527 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B3725135 : Blo 1655527 3725135 := bstep (se 1 (by rfl) ⟨2793851, by rfl⟩ : syracuseStep 3725135 = 5587703) B5587703
theorem B3725279 : Blo 1655527 3725279 := bstep (se 1 (by rfl) ⟨2793959, by rfl⟩ : syracuseStep 3725279 = 5587919) B5587919
theorem B18872351 : Blo 1655527 18872351 := bstep (se 1 (by rfl) ⟨14154263, by rfl⟩ : syracuseStep 18872351 = 28308527) B28308527
theorem B4716767 : Blo 1655527 4716767 := bstep (se 1 (by rfl) ⟨3537575, by rfl⟩ : syracuseStep 4716767 = 7075151) B7075151
theorem B5593319 : Blo 1655527 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B3725855 : Blo 1655527 3725855 := bstep (se 1 (by rfl) ⟨2794391, by rfl⟩ : syracuseStep 3725855 = 5588783) B5588783
theorem B3725927 : Blo 1655527 3725927 := bstep (se 1 (by rfl) ⟨2794445, by rfl⟩ : syracuseStep 3725927 = 5588891) B5588891
theorem B3726143 : Blo 1655527 3726143 := bstep (se 1 (by rfl) ⟨2794607, by rfl⟩ : syracuseStep 3726143 = 5589215) B5589215
theorem B3144815 : Blo 1655527 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B4193471 : Blo 1655527 4193471 := bstep (se 1 (by rfl) ⟨3145103, by rfl⟩ : syracuseStep 4193471 = 6290207) B6290207
theorem B3980495 : Blo 1655527 3980495 := bstep (se 1 (by rfl) ⟨2985371, by rfl⟩ : syracuseStep 3980495 = 5970743) B5970743
theorem B13425959 : Blo 1655527 13425959 := bstep (se 1 (by rfl) ⟨10069469, by rfl⟩ : syracuseStep 13425959 = 20138939) B20138939
theorem B7175479 : Blo 1655527 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B23871023 : Blo 1655527 23871023 := bstep (se 1 (by rfl) ⟨17903267, by rfl⟩ : syracuseStep 23871023 = 35806535) B35806535
theorem B16998059 : Blo 1655527 16998059 := bstep (se 1 (by rfl) ⟨12748544, by rfl⟩ : syracuseStep 16998059 = 25497089) B25497089
theorem B9437087 : Blo 1655527 9437087 := bstep (se 1 (by rfl) ⟨7077815, by rfl⟩ : syracuseStep 9437087 = 14155631) B14155631
theorem B5668967 : Blo 1655527 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B6291695 : Blo 1655527 6291695 := bstep (se 1 (by rfl) ⟨4718771, by rfl⟩ : syracuseStep 6291695 = 9437543) B9437543
theorem B5308669 : Blo 1655527 5308669 := bstep (se 3 (by rfl) ⟨995375, by rfl⟩ : syracuseStep 5308669 = 1990751) B1990751
theorem B8381231 : Blo 1655527 8381231 := bstep (se 1 (by rfl) ⟨6285923, by rfl⟩ : syracuseStep 8381231 = 12571847) B12571847
theorem B1655643 : Blo 1655527 1655643 := bstep (se 1 (by rfl) ⟨1241732, by rfl⟩ : syracuseStep 1655643 = 2483465) B2483465
theorem B17900459 : Blo 1655527 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B1655743 : Blo 1655527 1655743 := bstep (se 1 (by rfl) ⟨1241807, by rfl⟩ : syracuseStep 1655743 = 2483615) B2483615
theorem B26854379 : Blo 1655527 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B1655963 : Blo 1655527 1655963 := bstep (se 1 (by rfl) ⟨1241972, by rfl⟩ : syracuseStep 1655963 = 2483945) B2483945
theorem B2483423 : Blo 1655527 2483423 := bstep (se 1 (by rfl) ⟨1862567, by rfl⟩ : syracuseStep 2483423 = 3725135) B3725135
theorem B2483519 : Blo 1655527 2483519 := bstep (se 1 (by rfl) ⟨1862639, by rfl⟩ : syracuseStep 2483519 = 3725279) B3725279
theorem B1656271 : Blo 1655527 1656271 := bstep (se 1 (by rfl) ⟨1242203, by rfl⟩ : syracuseStep 1656271 = 2484407) B2484407
theorem B3728879 : Blo 1655527 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B1656319 : Blo 1655527 1656319 := bstep (se 1 (by rfl) ⟨1242239, by rfl⟩ : syracuseStep 1656319 = 2484479) B2484479
theorem B2483849 : Blo 1655527 2483849 := bstep (se 2 (by rfl) ⟨931443, by rfl⟩ : syracuseStep 2483849 = 1862887) B1862887
theorem B2483903 : Blo 1655527 2483903 := bstep (se 1 (by rfl) ⟨1862927, by rfl⟩ : syracuseStep 2483903 = 3725855) B3725855
theorem B2483951 : Blo 1655527 2483951 := bstep (se 1 (by rfl) ⟨1862963, by rfl⟩ : syracuseStep 2483951 = 3725927) B3725927
theorem B45328157 : Blo 1655527 45328157 := bstep (se 3 (by rfl) ⟨8499029, by rfl⟩ : syracuseStep 45328157 = 16998059) B16998059
theorem B2484095 : Blo 1655527 2484095 := bstep (se 1 (by rfl) ⟨1863071, by rfl⟩ : syracuseStep 2484095 = 3726143) B3726143
theorem B2795647 : Blo 1655527 2795647 := bstep (se 1 (by rfl) ⟨2096735, by rfl⟩ : syracuseStep 2795647 = 4193471) B4193471
theorem B7956701 : Blo 1655527 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B1657159 : Blo 1655527 1657159 := bstep (se 1 (by rfl) ⟨1242869, by rfl⟩ : syracuseStep 1657159 = 2485739) B2485739
theorem B102025601 : Blo 1655527 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B12577193 : Blo 1655527 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B30239201 : Blo 1655527 30239201 := bstep (se 2 (by rfl) ⟨11339700, by rfl⟩ : syracuseStep 30239201 = 22679401) B22679401
theorem B2484713 : Blo 1655527 2484713 := bstep (se 2 (by rfl) ⟨931767, by rfl⟩ : syracuseStep 2484713 = 1863535) B1863535
theorem B1657455 : Blo 1655527 1657455 := bstep (se 1 (by rfl) ⟨1243091, by rfl⟩ : syracuseStep 1657455 = 2486183) B2486183
theorem B5589647 : Blo 1655527 5589647 := bstep (se 1 (by rfl) ⟨4192235, by rfl⟩ : syracuseStep 5589647 = 8384471) B8384471
theorem B5589971 : Blo 1655527 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B22670441 : Blo 1655527 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B26864759 : Blo 1655527 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B2485415 : Blo 1655527 2485415 := bstep (se 1 (by rfl) ⟨1864061, by rfl⟩ : syracuseStep 2485415 = 3728123) B3728123
theorem B18869435 : Blo 1655527 18869435 := bstep (se 1 (by rfl) ⟨14152076, by rfl⟩ : syracuseStep 18869435 = 28304153) B28304153
theorem B35802557 : Blo 1655527 35802557 := bstep (se 3 (by rfl) ⟨6712979, by rfl⟩ : syracuseStep 35802557 = 13425959) B13425959
theorem B6287777 : Blo 1655527 6287777 := bstep (se 2 (by rfl) ⟨2357916, by rfl⟩ : syracuseStep 6287777 = 4715833) B4715833
theorem B6287975 : Blo 1655527 6287975 := bstep (se 1 (by rfl) ⟨4715981, by rfl⟩ : syracuseStep 6287975 = 9431963) B9431963
theorem B15914015 : Blo 1655527 15914015 := bstep (se 1 (by rfl) ⟨11935511, by rfl⟩ : syracuseStep 15914015 = 23871023) B23871023
theorem B4191335 : Blo 1655527 4191335 := bstep (se 1 (by rfl) ⟨3143501, by rfl⟩ : syracuseStep 4191335 = 6287003) B6287003
theorem B8959679 : Blo 1655527 8959679 := bstep (se 1 (by rfl) ⟨6719759, by rfl⟩ : syracuseStep 8959679 = 13439519) B13439519
theorem B6289235 : Blo 1655527 6289235 := bstep (se 1 (by rfl) ⟨4716926, by rfl⟩ : syracuseStep 6289235 = 9433853) B9433853
theorem B11941739 : Blo 1655527 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B6289447 : Blo 1655527 6289447 := bstep (se 1 (by rfl) ⟨4717085, by rfl⟩ : syracuseStep 6289447 = 9434171) B9434171
theorem B5593211 : Blo 1655527 5593211 := bstep (se 1 (by rfl) ⟨4194908, by rfl⟩ : syracuseStep 5593211 = 8389817) B8389817
theorem B80574821 : Blo 1655527 80574821 := bstep (se 4 (by rfl) ⟨7553889, by rfl⟩ : syracuseStep 80574821 = 15107779) B15107779
theorem B12581567 : Blo 1655527 12581567 := bstep (se 1 (by rfl) ⟨9436175, by rfl⟩ : syracuseStep 12581567 = 18872351) B18872351
theorem B5970671 : Blo 1655527 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B3144511 : Blo 1655527 3144511 := bstep (se 1 (by rfl) ⟨2358383, by rfl⟩ : syracuseStep 3144511 = 4716767) B4716767
theorem B9567305 : Blo 1655527 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B2096543 : Blo 1655527 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B2653663 : Blo 1655527 2653663 := bstep (se 1 (by rfl) ⟨1990247, by rfl⟩ : syracuseStep 2653663 = 3980495) B3980495
theorem B12754523 : Blo 1655527 12754523 := bstep (se 1 (by rfl) ⟨9565892, by rfl⟩ : syracuseStep 12754523 = 19131785) B19131785
theorem B181354241 : Blo 1655527 181354241 := bstep (se 2 (by rfl) ⟨68007840, by rfl⟩ : syracuseStep 181354241 = 136015681) B136015681
theorem B3727241 : Blo 1655527 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B6291391 : Blo 1655527 6291391 := bstep (se 1 (by rfl) ⟨4718543, by rfl⟩ : syracuseStep 6291391 = 9437087) B9437087
theorem B4194463 : Blo 1655527 4194463 := bstep (se 1 (by rfl) ⟨3145847, by rfl⟩ : syracuseStep 4194463 = 6291695) B6291695
theorem B3727529 : Blo 1655527 3727529 := bstep (se 2 (by rfl) ⟨1397823, by rfl⟩ : syracuseStep 3727529 = 2795647) B2795647
theorem B5587487 : Blo 1655527 5587487 := bstep (se 1 (by rfl) ⟨4190615, by rfl⟩ : syracuseStep 5587487 = 8381231) B8381231
theorem B10609343 : Blo 1655527 10609343 := bstep (se 1 (by rfl) ⟨7957007, by rfl⟩ : syracuseStep 10609343 = 15914015) B15914015
theorem B2794223 : Blo 1655527 2794223 := bstep (se 1 (by rfl) ⟨2095667, by rfl⟩ : syracuseStep 2794223 = 4191335) B4191335
theorem B1655615 : Blo 1655527 1655615 := bstep (se 1 (by rfl) ⟨1241711, by rfl⟩ : syracuseStep 1655615 = 2483423) B2483423
theorem B1655679 : Blo 1655527 1655679 := bstep (se 1 (by rfl) ⟨1241759, by rfl⟩ : syracuseStep 1655679 = 2483519) B2483519
theorem B1655899 : Blo 1655527 1655899 := bstep (se 1 (by rfl) ⟨1241924, by rfl⟩ : syracuseStep 1655899 = 2483849) B2483849
theorem B1655935 : Blo 1655527 1655935 := bstep (se 1 (by rfl) ⟨1241951, by rfl⟩ : syracuseStep 1655935 = 2483903) B2483903
theorem B5973119 : Blo 1655527 5973119 := bstep (se 1 (by rfl) ⟨4479839, by rfl⟩ : syracuseStep 5973119 = 8959679) B8959679
theorem B1655967 : Blo 1655527 1655967 := bstep (se 1 (by rfl) ⟨1241975, by rfl⟩ : syracuseStep 1655967 = 2483951) B2483951
theorem B1656063 : Blo 1655527 1656063 := bstep (se 1 (by rfl) ⟨1242047, by rfl⟩ : syracuseStep 1656063 = 2484095) B2484095
theorem B28312901 : Blo 1655527 28312901 := bstep (se 4 (by rfl) ⟨2654334, by rfl⟩ : syracuseStep 28312901 = 5308669) B5308669
theorem B3728807 : Blo 1655527 3728807 := bstep (se 1 (by rfl) ⟨2796605, by rfl⟩ : syracuseStep 3728807 = 5593211) B5593211
theorem B53716547 : Blo 1655527 53716547 := bstep (se 1 (by rfl) ⟨40287410, by rfl⟩ : syracuseStep 53716547 = 80574821) B80574821
theorem B1656475 : Blo 1655527 1656475 := bstep (se 1 (by rfl) ⟨1242356, by rfl⟩ : syracuseStep 1656475 = 2484713) B2484713
theorem B17909839 : Blo 1655527 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B1656943 : Blo 1655527 1656943 := bstep (se 1 (by rfl) ⟨1242707, by rfl⟩ : syracuseStep 1656943 = 2485415) B2485415
theorem B2484827 : Blo 1655527 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B3779311 : Blo 1655527 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B17902919 : Blo 1655527 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B2485919 : Blo 1655527 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B5590781 : Blo 1655527 5590781 := bstep (se 3 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 5590781 = 2096543) B2096543
theorem B80637869 : Blo 1655527 80637869 := bstep (se 3 (by rfl) ⟨15119600, by rfl⟩ : syracuseStep 80637869 = 30239201) B30239201
theorem B5304467 : Blo 1655527 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B8384795 : Blo 1655527 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B6378203 : Blo 1655527 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B12579623 : Blo 1655527 12579623 := bstep (se 1 (by rfl) ⟨9434717, by rfl⟩ : syracuseStep 12579623 = 18869435) B18869435
theorem B23868371 : Blo 1655527 23868371 := bstep (se 1 (by rfl) ⟨17901278, by rfl⟩ : syracuseStep 23868371 = 35802557) B35802557
theorem B120902827 : Blo 1655527 120902827 := bstep (se 1 (by rfl) ⟨90677120, by rfl⟩ : syracuseStep 120902827 = 181354241) B181354241
theorem B8385929 : Blo 1655527 8385929 := bstep (se 2 (by rfl) ⟨3144723, by rfl⟩ : syracuseStep 8385929 = 6289447) B6289447
theorem B4191851 : Blo 1655527 4191851 := bstep (se 1 (by rfl) ⟨3143888, by rfl⟩ : syracuseStep 4191851 = 6287777) B6287777
theorem B4191983 : Blo 1655527 4191983 := bstep (se 1 (by rfl) ⟨3143987, by rfl⟩ : syracuseStep 4191983 = 6287975) B6287975
theorem B11933639 : Blo 1655527 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B4192681 : Blo 1655527 4192681 := bstep (se 2 (by rfl) ⟨1572255, by rfl⟩ : syracuseStep 4192681 = 3144511) B3144511
theorem B30218771 : Blo 1655527 30218771 := bstep (se 1 (by rfl) ⟨22664078, by rfl⟩ : syracuseStep 30218771 = 45328157) B45328157
theorem B4192823 : Blo 1655527 4192823 := bstep (se 1 (by rfl) ⟨3144617, by rfl⟩ : syracuseStep 4192823 = 6289235) B6289235
theorem B7961159 : Blo 1655527 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B68017067 : Blo 1655527 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B3726431 : Blo 1655527 3726431 := bstep (se 1 (by rfl) ⟨2794823, by rfl⟩ : syracuseStep 3726431 = 5589647) B5589647
theorem B8387711 : Blo 1655527 8387711 := bstep (se 1 (by rfl) ⟨6290783, by rfl⟩ : syracuseStep 8387711 = 12581567) B12581567
theorem B3980447 : Blo 1655527 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B3538217 : Blo 1655527 3538217 := bstep (se 2 (by rfl) ⟨1326831, by rfl⟩ : syracuseStep 3538217 = 2653663) B2653663
theorem B3726647 : Blo 1655527 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B15113627 : Blo 1655527 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B8503015 : Blo 1655527 8503015 := bstep (se 1 (by rfl) ⟨6377261, by rfl⟩ : syracuseStep 8503015 = 12754523) B12754523
theorem B8388521 : Blo 1655527 8388521 := bstep (se 2 (by rfl) ⟨3145695, by rfl⟩ : syracuseStep 8388521 = 6291391) B6291391
theorem B23879785 : Blo 1655527 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B3982079 : Blo 1655527 3982079 := bstep (se 1 (by rfl) ⟨2986559, by rfl⟩ : syracuseStep 3982079 = 5973119) B5973119
theorem B18875267 : Blo 1655527 18875267 := bstep (se 1 (by rfl) ⟨14156450, by rfl⟩ : syracuseStep 18875267 = 28312901) B28312901
theorem B5039081 : Blo 1655527 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B2794567 : Blo 1655527 2794567 := bstep (se 1 (by rfl) ⟨2095925, by rfl⟩ : syracuseStep 2794567 = 4191851) B4191851
theorem B2794655 : Blo 1655527 2794655 := bstep (se 1 (by rfl) ⟨2095991, by rfl⟩ : syracuseStep 2794655 = 4191983) B4191983
theorem B7955759 : Blo 1655527 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B161203769 : Blo 1655527 161203769 := bstep (se 2 (by rfl) ⟨60451413, by rfl⟩ : syracuseStep 161203769 = 120902827) B120902827
theorem B20145847 : Blo 1655527 20145847 := bstep (se 1 (by rfl) ⟨15109385, by rfl⟩ : syracuseStep 20145847 = 30218771) B30218771
theorem B2795215 : Blo 1655527 2795215 := bstep (se 1 (by rfl) ⟨2096411, by rfl⟩ : syracuseStep 2795215 = 4192823) B4192823
theorem B1656551 : Blo 1655527 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B17008541 : Blo 1655527 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B45344711 : Blo 1655527 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B2484287 : Blo 1655527 2484287 := bstep (se 1 (by rfl) ⟨1863215, by rfl⟩ : syracuseStep 2484287 = 3726431) B3726431
theorem B2484431 : Blo 1655527 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B1657279 : Blo 1655527 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B53758579 : Blo 1655527 53758579 := bstep (se 1 (by rfl) ⟨40318934, by rfl⟩ : syracuseStep 53758579 = 80637869) B80637869
theorem B2485019 : Blo 1655527 2485019 := bstep (se 1 (by rfl) ⟨1863764, by rfl⟩ : syracuseStep 2485019 = 3727529) B3727529
theorem B5589863 : Blo 1655527 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B7072895 : Blo 1655527 7072895 := bstep (se 1 (by rfl) ⟨5304671, by rfl⟩ : syracuseStep 7072895 = 10609343) B10609343
theorem B1862815 : Blo 1655527 1862815 := bstep (se 1 (by rfl) ⟨1397111, by rfl⟩ : syracuseStep 1862815 = 2794223) B2794223
theorem B5590241 : Blo 1655527 5590241 := bstep (se 2 (by rfl) ⟨2096340, by rfl⟩ : syracuseStep 5590241 = 4192681) B4192681
theorem B15912247 : Blo 1655527 15912247 := bstep (se 1 (by rfl) ⟨11934185, by rfl⟩ : syracuseStep 15912247 = 23868371) B23868371
theorem B5590619 : Blo 1655527 5590619 := bstep (se 1 (by rfl) ⟨4192964, by rfl⟩ : syracuseStep 5590619 = 8385929) B8385929
theorem B2485871 : Blo 1655527 2485871 := bstep (se 1 (by rfl) ⟨1864403, by rfl⟩ : syracuseStep 2485871 = 3728807) B3728807
theorem B35811031 : Blo 1655527 35811031 := bstep (se 1 (by rfl) ⟨26858273, by rfl⟩ : syracuseStep 35811031 = 53716547) B53716547
theorem B5591807 : Blo 1655527 5591807 := bstep (se 1 (by rfl) ⟨4193855, by rfl⟩ : syracuseStep 5591807 = 8387711) B8387711
theorem B5592347 : Blo 1655527 5592347 := bstep (se 1 (by rfl) ⟨4194260, by rfl⟩ : syracuseStep 5592347 = 8388521) B8388521
theorem B3536311 : Blo 1655527 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B5592617 : Blo 1655527 5592617 := bstep (se 2 (by rfl) ⟨2097231, by rfl⟩ : syracuseStep 5592617 = 4194463) B4194463
theorem B3724991 : Blo 1655527 3724991 := bstep (se 1 (by rfl) ⟨2793743, by rfl⟩ : syracuseStep 3724991 = 5587487) B5587487
theorem B8386415 : Blo 1655527 8386415 := bstep (se 1 (by rfl) ⟨6289811, by rfl⟩ : syracuseStep 8386415 = 12579623) B12579623
theorem B5307439 : Blo 1655527 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B2653631 : Blo 1655527 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B2358811 : Blo 1655527 2358811 := bstep (se 1 (by rfl) ⟨1769108, by rfl⟩ : syracuseStep 2358811 = 3538217) B3538217
theorem B11935279 : Blo 1655527 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B10075751 : Blo 1655527 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B11337353 : Blo 1655527 11337353 := bstep (se 2 (by rfl) ⟨4251507, by rfl⟩ : syracuseStep 11337353 = 8503015) B8503015
theorem B3727187 : Blo 1655527 3727187 := bstep (se 1 (by rfl) ⟨2795390, by rfl⟩ : syracuseStep 3727187 = 5590781) B5590781
theorem B3727871 : Blo 1655527 3727871 := bstep (se 1 (by rfl) ⟨2795903, by rfl⟩ : syracuseStep 3727871 = 5591807) B5591807
theorem B12583511 : Blo 1655527 12583511 := bstep (se 1 (by rfl) ⟨9437633, by rfl⟩ : syracuseStep 12583511 = 18875267) B18875267
theorem B3359387 : Blo 1655527 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B3728231 : Blo 1655527 3728231 := bstep (se 1 (by rfl) ⟨2796173, by rfl⟩ : syracuseStep 3728231 = 5592347) B5592347
theorem B3728411 : Blo 1655527 3728411 := bstep (se 1 (by rfl) ⟨2796308, by rfl⟩ : syracuseStep 3728411 = 5592617) B5592617
theorem B2483327 : Blo 1655527 2483327 := bstep (se 1 (by rfl) ⟨1862495, by rfl⟩ : syracuseStep 2483327 = 3724991) B3724991
theorem B11339027 : Blo 1655527 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B30229807 : Blo 1655527 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B1656191 : Blo 1655527 1656191 := bstep (se 1 (by rfl) ⟨1242143, by rfl⟩ : syracuseStep 1656191 = 2484287) B2484287
theorem B1656287 : Blo 1655527 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B2483753 : Blo 1655527 2483753 := bstep (se 2 (by rfl) ⟨931407, by rfl⟩ : syracuseStep 2483753 = 1862815) B1862815
theorem B1656679 : Blo 1655527 1656679 := bstep (se 1 (by rfl) ⟨1242509, by rfl⟩ : syracuseStep 1656679 = 2485019) B2485019
theorem B10618877 : Blo 1655527 10618877 := bstep (se 3 (by rfl) ⟨1991039, by rfl⟩ : syracuseStep 10618877 = 3982079) B3982079
theorem B1657247 : Blo 1655527 1657247 := bstep (se 1 (by rfl) ⟨1242935, by rfl⟩ : syracuseStep 1657247 = 2485871) B2485871
theorem B2484791 : Blo 1655527 2484791 := bstep (se 1 (by rfl) ⟨1863593, by rfl⟩ : syracuseStep 2484791 = 3727187) B3727187
theorem B63654821 : Blo 1655527 63654821 := bstep (se 4 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 63654821 = 11935279) B11935279
theorem B1863103 : Blo 1655527 1863103 := bstep (se 1 (by rfl) ⟨1397327, by rfl⟩ : syracuseStep 1863103 = 2794655) B2794655
theorem B5590943 : Blo 1655527 5590943 := bstep (se 1 (by rfl) ⟨4193207, by rfl⟩ : syracuseStep 5590943 = 8386415) B8386415
theorem B4715081 : Blo 1655527 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B4715263 : Blo 1655527 4715263 := bstep (se 1 (by rfl) ⟨3536447, by rfl⟩ : syracuseStep 4715263 = 7072895) B7072895
theorem B47748041 : Blo 1655527 47748041 := bstep (se 2 (by rfl) ⟨17905515, by rfl⟩ : syracuseStep 47748041 = 35811031) B35811031
theorem B7558235 : Blo 1655527 7558235 := bstep (se 1 (by rfl) ⟨5668676, by rfl⟩ : syracuseStep 7558235 = 11337353) B11337353
theorem B31839713 : Blo 1655527 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B21215357 : Blo 1655527 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B71678105 : Blo 1655527 71678105 := bstep (se 2 (by rfl) ⟨26879289, by rfl⟩ : syracuseStep 71678105 = 53758579) B53758579
theorem B107469179 : Blo 1655527 107469179 := bstep (se 1 (by rfl) ⟨80601884, by rfl⟩ : syracuseStep 107469179 = 161203769) B161203769
theorem B7076585 : Blo 1655527 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B3726089 : Blo 1655527 3726089 := bstep (se 2 (by rfl) ⟨1397283, by rfl⟩ : syracuseStep 3726089 = 2794567) B2794567
theorem B21216329 : Blo 1655527 21216329 := bstep (se 2 (by rfl) ⟨7956123, by rfl⟩ : syracuseStep 21216329 = 15912247) B15912247
theorem B3726575 : Blo 1655527 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B3145081 : Blo 1655527 3145081 := bstep (se 2 (by rfl) ⟨1179405, by rfl⟩ : syracuseStep 3145081 = 2358811) B2358811
theorem B3726827 : Blo 1655527 3726827 := bstep (se 1 (by rfl) ⟨2795120, by rfl⟩ : syracuseStep 3726827 = 5590241) B5590241
theorem B26861129 : Blo 1655527 26861129 := bstep (se 2 (by rfl) ⟨10072923, by rfl⟩ : syracuseStep 26861129 = 20145847) B20145847
theorem B3726953 : Blo 1655527 3726953 := bstep (se 2 (by rfl) ⟨1397607, by rfl⟩ : syracuseStep 3726953 = 2795215) B2795215
theorem B1769087 : Blo 1655527 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B3727079 : Blo 1655527 3727079 := bstep (se 1 (by rfl) ⟨2795309, by rfl⟩ : syracuseStep 3727079 = 5590619) B5590619
theorem B6717167 : Blo 1655527 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B8389007 : Blo 1655527 8389007 := bstep (se 1 (by rfl) ⟨6291755, by rfl⟩ : syracuseStep 8389007 = 12583511) B12583511
theorem B5038823 : Blo 1655527 5038823 := bstep (se 1 (by rfl) ⟨3779117, by rfl⟩ : syracuseStep 5038823 = 7558235) B7558235
theorem B1655551 : Blo 1655527 1655551 := bstep (se 1 (by rfl) ⟨1241663, by rfl⟩ : syracuseStep 1655551 = 2483327) B2483327
theorem B21226475 : Blo 1655527 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B1655835 : Blo 1655527 1655835 := bstep (se 1 (by rfl) ⟨1241876, by rfl⟩ : syracuseStep 1655835 = 2483753) B2483753
theorem B7079251 : Blo 1655527 7079251 := bstep (se 1 (by rfl) ⟨5309438, by rfl⟩ : syracuseStep 7079251 = 10618877) B10618877
theorem B47785403 : Blo 1655527 47785403 := bstep (se 1 (by rfl) ⟨35839052, by rfl⟩ : syracuseStep 47785403 = 71678105) B71678105
theorem B1656527 : Blo 1655527 1656527 := bstep (se 1 (by rfl) ⟨1242395, by rfl⟩ : syracuseStep 1656527 = 2484791) B2484791
theorem B40306409 : Blo 1655527 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B2484059 : Blo 1655527 2484059 := bstep (se 1 (by rfl) ⟨1863044, by rfl⟩ : syracuseStep 2484059 = 3726089) B3726089
theorem B2484137 : Blo 1655527 2484137 := bstep (se 2 (by rfl) ⟨931551, by rfl⟩ : syracuseStep 2484137 = 1863103) B1863103
theorem B42436547 : Blo 1655527 42436547 := bstep (se 1 (by rfl) ⟨31827410, by rfl⟩ : syracuseStep 42436547 = 63654821) B63654821
theorem B2484383 : Blo 1655527 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2484551 : Blo 1655527 2484551 := bstep (se 1 (by rfl) ⟨1863413, by rfl⟩ : syracuseStep 2484551 = 3726827) B3726827
theorem B2484635 : Blo 1655527 2484635 := bstep (se 1 (by rfl) ⟨1863476, by rfl⟩ : syracuseStep 2484635 = 3726953) B3726953
theorem B2484719 : Blo 1655527 2484719 := bstep (se 1 (by rfl) ⟨1863539, by rfl⟩ : syracuseStep 2484719 = 3727079) B3727079
theorem B2485247 : Blo 1655527 2485247 := bstep (se 1 (by rfl) ⟨1863935, by rfl⟩ : syracuseStep 2485247 = 3727871) B3727871
theorem B2239591 : Blo 1655527 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B2485487 : Blo 1655527 2485487 := bstep (se 1 (by rfl) ⟨1864115, by rfl⟩ : syracuseStep 2485487 = 3728231) B3728231
theorem B2485607 : Blo 1655527 2485607 := bstep (se 1 (by rfl) ⟨1864205, by rfl⟩ : syracuseStep 2485607 = 3728411) B3728411
theorem B6287017 : Blo 1655527 6287017 := bstep (se 2 (by rfl) ⟨2357631, by rfl⟩ : syracuseStep 6287017 = 4715263) B4715263
theorem B14143571 : Blo 1655527 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B18870893 : Blo 1655527 18870893 := bstep (se 3 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 18870893 = 7076585) B7076585
theorem B14144219 : Blo 1655527 14144219 := bstep (se 1 (by rfl) ⟨10608164, by rfl⟩ : syracuseStep 14144219 = 21216329) B21216329
theorem B4478111 : Blo 1655527 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B3143387 : Blo 1655527 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B31832027 : Blo 1655527 31832027 := bstep (se 1 (by rfl) ⟨23874020, by rfl⟩ : syracuseStep 31832027 = 47748041) B47748041
theorem B7559351 : Blo 1655527 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B71646119 : Blo 1655527 71646119 := bstep (se 1 (by rfl) ⟨53734589, by rfl⟩ : syracuseStep 71646119 = 107469179) B107469179
theorem B4717565 : Blo 1655527 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B4193441 : Blo 1655527 4193441 := bstep (se 2 (by rfl) ⟨1572540, by rfl⟩ : syracuseStep 4193441 = 3145081) B3145081
theorem B17907419 : Blo 1655527 17907419 := bstep (se 1 (by rfl) ⟨13430564, by rfl⟩ : syracuseStep 17907419 = 26861129) B26861129
theorem B3727295 : Blo 1655527 3727295 := bstep (se 1 (by rfl) ⟨2795471, by rfl⟩ : syracuseStep 3727295 = 5590943) B5590943
theorem B9429047 : Blo 1655527 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B9429479 : Blo 1655527 9429479 := bstep (se 1 (by rfl) ⟨7072109, by rfl⟩ : syracuseStep 9429479 = 14144219) B14144219
theorem B3359215 : Blo 1655527 3359215 := bstep (se 1 (by rfl) ⟨2519411, by rfl⟩ : syracuseStep 3359215 = 5038823) B5038823
theorem B26870939 : Blo 1655527 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B1656039 : Blo 1655527 1656039 := bstep (se 1 (by rfl) ⟨1242029, by rfl⟩ : syracuseStep 1656039 = 2484059) B2484059
theorem B1656091 : Blo 1655527 1656091 := bstep (se 1 (by rfl) ⟨1242068, by rfl⟩ : syracuseStep 1656091 = 2484137) B2484137
theorem B1656255 : Blo 1655527 1656255 := bstep (se 1 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 1656255 = 2484383) B2484383
theorem B5039567 : Blo 1655527 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B1656367 : Blo 1655527 1656367 := bstep (se 1 (by rfl) ⟨1242275, by rfl⟩ : syracuseStep 1656367 = 2484551) B2484551
theorem B1656423 : Blo 1655527 1656423 := bstep (se 1 (by rfl) ⟨1242317, by rfl⟩ : syracuseStep 1656423 = 2484635) B2484635
theorem B1656479 : Blo 1655527 1656479 := bstep (se 1 (by rfl) ⟨1242359, by rfl⟩ : syracuseStep 1656479 = 2484719) B2484719
theorem B9439001 : Blo 1655527 9439001 := bstep (se 2 (by rfl) ⟨3539625, by rfl⟩ : syracuseStep 9439001 = 7079251) B7079251
theorem B8382365 : Blo 1655527 8382365 := bstep (se 3 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 8382365 = 3143387) B3143387
theorem B1656831 : Blo 1655527 1656831 := bstep (se 1 (by rfl) ⟨1242623, by rfl⟩ : syracuseStep 1656831 = 2485247) B2485247
theorem B2795627 : Blo 1655527 2795627 := bstep (se 1 (by rfl) ⟨2096720, by rfl⟩ : syracuseStep 2795627 = 4193441) B4193441
theorem B1656991 : Blo 1655527 1656991 := bstep (se 1 (by rfl) ⟨1242743, by rfl⟩ : syracuseStep 1656991 = 2485487) B2485487
theorem B8382689 : Blo 1655527 8382689 := bstep (se 2 (by rfl) ⟨3143508, by rfl⟩ : syracuseStep 8382689 = 6287017) B6287017
theorem B1657071 : Blo 1655527 1657071 := bstep (se 1 (by rfl) ⟨1242803, by rfl⟩ : syracuseStep 1657071 = 2485607) B2485607
theorem B11938279 : Blo 1655527 11938279 := bstep (se 1 (by rfl) ⟨8953709, by rfl⟩ : syracuseStep 11938279 = 17907419) B17907419
theorem B2484863 : Blo 1655527 2484863 := bstep (se 1 (by rfl) ⟨1863647, by rfl⟩ : syracuseStep 2484863 = 3727295) B3727295
theorem B14150983 : Blo 1655527 14150983 := bstep (se 1 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 14150983 = 21226475) B21226475
theorem B2985407 : Blo 1655527 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B28291031 : Blo 1655527 28291031 := bstep (se 1 (by rfl) ⟨21218273, by rfl⟩ : syracuseStep 28291031 = 42436547) B42436547
theorem B21221351 : Blo 1655527 21221351 := bstep (se 1 (by rfl) ⟨15916013, by rfl⟩ : syracuseStep 21221351 = 31832027) B31832027
theorem B2986121 : Blo 1655527 2986121 := bstep (se 2 (by rfl) ⟨1119795, by rfl⟩ : syracuseStep 2986121 = 2239591) B2239591
theorem B47764079 : Blo 1655527 47764079 := bstep (se 1 (by rfl) ⟨35823059, by rfl⟩ : syracuseStep 47764079 = 71646119) B71646119
theorem B5592671 : Blo 1655527 5592671 := bstep (se 1 (by rfl) ⟨4194503, by rfl⟩ : syracuseStep 5592671 = 8389007) B8389007
theorem B12580595 : Blo 1655527 12580595 := bstep (se 1 (by rfl) ⟨9435446, by rfl⟩ : syracuseStep 12580595 = 18870893) B18870893
theorem B31856935 : Blo 1655527 31856935 := bstep (se 1 (by rfl) ⟨23892701, by rfl⟩ : syracuseStep 31856935 = 47785403) B47785403
theorem B3145043 : Blo 1655527 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B1990747 : Blo 1655527 1990747 := bstep (se 1 (by rfl) ⟨1493060, by rfl⟩ : syracuseStep 1990747 = 2986121) B2986121
theorem B42475913 : Blo 1655527 42475913 := bstep (se 2 (by rfl) ⟨15928467, by rfl⟩ : syracuseStep 42475913 = 31856935) B31856935
theorem B31842719 : Blo 1655527 31842719 := bstep (se 1 (by rfl) ⟨23882039, by rfl⟩ : syracuseStep 31842719 = 47764079) B47764079
theorem B15917705 : Blo 1655527 15917705 := bstep (se 2 (by rfl) ⟨5969139, by rfl⟩ : syracuseStep 15917705 = 11938279) B11938279
theorem B3359711 : Blo 1655527 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B3728447 : Blo 1655527 3728447 := bstep (se 1 (by rfl) ⟨2796335, by rfl⟩ : syracuseStep 3728447 = 5592671) B5592671
theorem B6292667 : Blo 1655527 6292667 := bstep (se 1 (by rfl) ⟨4719500, by rfl⟩ : syracuseStep 6292667 = 9439001) B9439001
theorem B5588243 : Blo 1655527 5588243 := bstep (se 1 (by rfl) ⟨4191182, by rfl⟩ : syracuseStep 5588243 = 8382365) B8382365
theorem B5588459 : Blo 1655527 5588459 := bstep (se 1 (by rfl) ⟨4191344, by rfl⟩ : syracuseStep 5588459 = 8382689) B8382689
theorem B1656575 : Blo 1655527 1656575 := bstep (se 1 (by rfl) ⟨1242431, by rfl⟩ : syracuseStep 1656575 = 2484863) B2484863
theorem B18867977 : Blo 1655527 18867977 := bstep (se 2 (by rfl) ⟨7075491, by rfl⟩ : syracuseStep 18867977 = 14150983) B14150983
theorem B18860687 : Blo 1655527 18860687 := bstep (se 1 (by rfl) ⟨14145515, by rfl⟩ : syracuseStep 18860687 = 28291031) B28291031
theorem B6286031 : Blo 1655527 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B6286319 : Blo 1655527 6286319 := bstep (se 1 (by rfl) ⟨4714739, by rfl⟩ : syracuseStep 6286319 = 9429479) B9429479
theorem B1863751 : Blo 1655527 1863751 := bstep (se 1 (by rfl) ⟨1397813, by rfl⟩ : syracuseStep 1863751 = 2795627) B2795627
theorem B17913959 : Blo 1655527 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B8387063 : Blo 1655527 8387063 := bstep (se 1 (by rfl) ⟨6290297, by rfl⟩ : syracuseStep 8387063 = 12580595) B12580595
theorem B2096695 : Blo 1655527 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B1990271 : Blo 1655527 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B17915813 : Blo 1655527 17915813 := bstep (se 4 (by rfl) ⟨1679607, by rfl⟩ : syracuseStep 17915813 = 3359215) B3359215
theorem B14147567 : Blo 1655527 14147567 := bstep (se 1 (by rfl) ⟨10610675, by rfl⟩ : syracuseStep 14147567 = 21221351) B21221351
theorem B10617317 : Blo 1655527 10617317 := bstep (se 4 (by rfl) ⟨995373, by rfl⟩ : syracuseStep 10617317 = 1990747) B1990747
theorem B4195111 : Blo 1655527 4195111 := bstep (se 1 (by rfl) ⟨3146333, by rfl⟩ : syracuseStep 4195111 = 6292667) B6292667
theorem B2795593 : Blo 1655527 2795593 := bstep (se 2 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 2795593 = 2096695) B2096695
theorem B9431711 : Blo 1655527 9431711 := bstep (se 1 (by rfl) ⟨7073783, by rfl⟩ : syracuseStep 9431711 = 14147567) B14147567
theorem B2485001 : Blo 1655527 2485001 := bstep (se 2 (by rfl) ⟨931875, by rfl⟩ : syracuseStep 2485001 = 1863751) B1863751
theorem B21228479 : Blo 1655527 21228479 := bstep (se 1 (by rfl) ⟨15921359, by rfl⟩ : syracuseStep 21228479 = 31842719) B31842719
theorem B10611803 : Blo 1655527 10611803 := bstep (se 1 (by rfl) ⟨7958852, by rfl⟩ : syracuseStep 10611803 = 15917705) B15917705
theorem B2239807 : Blo 1655527 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B2485631 : Blo 1655527 2485631 := bstep (se 1 (by rfl) ⟨1864223, by rfl⟩ : syracuseStep 2485631 = 3728447) B3728447
theorem B12578651 : Blo 1655527 12578651 := bstep (se 1 (by rfl) ⟨9433988, by rfl⟩ : syracuseStep 12578651 = 18867977) B18867977
theorem B5591375 : Blo 1655527 5591375 := bstep (se 1 (by rfl) ⟨4193531, by rfl⟩ : syracuseStep 5591375 = 8387063) B8387063
theorem B4190687 : Blo 1655527 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B4190879 : Blo 1655527 4190879 := bstep (se 1 (by rfl) ⟨3143159, by rfl⟩ : syracuseStep 4190879 = 6286319) B6286319
theorem B28317275 : Blo 1655527 28317275 := bstep (se 1 (by rfl) ⟨21237956, by rfl⟩ : syracuseStep 28317275 = 42475913) B42475913
theorem B3725495 : Blo 1655527 3725495 := bstep (se 1 (by rfl) ⟨2794121, by rfl⟩ : syracuseStep 3725495 = 5588243) B5588243
theorem B3725639 : Blo 1655527 3725639 := bstep (se 1 (by rfl) ⟨2794229, by rfl⟩ : syracuseStep 3725639 = 5588459) B5588459
theorem B11942639 : Blo 1655527 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B5307389 : Blo 1655527 5307389 := bstep (se 3 (by rfl) ⟨995135, by rfl⟩ : syracuseStep 5307389 = 1990271) B1990271
theorem B12573791 : Blo 1655527 12573791 := bstep (se 1 (by rfl) ⟨9430343, by rfl⟩ : syracuseStep 12573791 = 18860687) B18860687
theorem B11943875 : Blo 1655527 11943875 := bstep (se 1 (by rfl) ⟨8957906, by rfl⟩ : syracuseStep 11943875 = 17915813) B17915813
theorem B3727457 : Blo 1655527 3727457 := bstep (se 2 (by rfl) ⟨1397796, by rfl⟩ : syracuseStep 3727457 = 2795593) B2795593
theorem B3727583 : Blo 1655527 3727583 := bstep (se 1 (by rfl) ⟨2795687, by rfl⟩ : syracuseStep 3727583 = 5591375) B5591375
theorem B2793791 : Blo 1655527 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B7078211 : Blo 1655527 7078211 := bstep (se 1 (by rfl) ⟨5308658, by rfl⟩ : syracuseStep 7078211 = 10617317) B10617317
theorem B2793919 : Blo 1655527 2793919 := bstep (se 1 (by rfl) ⟨2095439, by rfl⟩ : syracuseStep 2793919 = 4190879) B4190879
theorem B2483663 : Blo 1655527 2483663 := bstep (se 1 (by rfl) ⟨1862747, by rfl⟩ : syracuseStep 2483663 = 3725495) B3725495
theorem B2483759 : Blo 1655527 2483759 := bstep (se 1 (by rfl) ⟨1862819, by rfl⟩ : syracuseStep 2483759 = 3725639) B3725639
theorem B1656667 : Blo 1655527 1656667 := bstep (se 1 (by rfl) ⟨1242500, by rfl⟩ : syracuseStep 1656667 = 2485001) B2485001
theorem B8382527 : Blo 1655527 8382527 := bstep (se 1 (by rfl) ⟨6286895, by rfl⟩ : syracuseStep 8382527 = 12573791) B12573791
theorem B1657087 : Blo 1655527 1657087 := bstep (se 1 (by rfl) ⟨1242815, by rfl⟩ : syracuseStep 1657087 = 2485631) B2485631
theorem B18878183 : Blo 1655527 18878183 := bstep (se 1 (by rfl) ⟨14158637, by rfl⟩ : syracuseStep 18878183 = 28317275) B28317275
theorem B2986409 : Blo 1655527 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B6287807 : Blo 1655527 6287807 := bstep (se 1 (by rfl) ⟨4715855, by rfl⟩ : syracuseStep 6287807 = 9431711) B9431711
theorem B14152319 : Blo 1655527 14152319 := bstep (se 1 (by rfl) ⟨10614239, by rfl⟩ : syracuseStep 14152319 = 21228479) B21228479
theorem B7074535 : Blo 1655527 7074535 := bstep (se 1 (by rfl) ⟨5305901, by rfl⟩ : syracuseStep 7074535 = 10611803) B10611803
theorem B8385767 : Blo 1655527 8385767 := bstep (se 1 (by rfl) ⟨6289325, by rfl⟩ : syracuseStep 8385767 = 12578651) B12578651
theorem B5593481 : Blo 1655527 5593481 := bstep (se 2 (by rfl) ⟨2097555, by rfl⟩ : syracuseStep 5593481 = 4195111) B4195111
theorem B7961759 : Blo 1655527 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B3538259 : Blo 1655527 3538259 := bstep (se 1 (by rfl) ⟨2653694, by rfl⟩ : syracuseStep 3538259 = 5307389) B5307389
theorem B7962583 : Blo 1655527 7962583 := bstep (se 1 (by rfl) ⟨5971937, by rfl⟩ : syracuseStep 7962583 = 11943875) B11943875
theorem B4718807 : Blo 1655527 4718807 := bstep (se 1 (by rfl) ⟨3539105, by rfl⟩ : syracuseStep 4718807 = 7078211) B7078211
theorem B1655775 : Blo 1655527 1655775 := bstep (se 1 (by rfl) ⟨1241831, by rfl⟩ : syracuseStep 1655775 = 2483663) B2483663
theorem B1655839 : Blo 1655527 1655839 := bstep (se 1 (by rfl) ⟨1241879, by rfl⟩ : syracuseStep 1655839 = 2483759) B2483759
theorem B7963757 : Blo 1655527 7963757 := bstep (se 3 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 7963757 = 2986409) B2986409
theorem B5588351 : Blo 1655527 5588351 := bstep (se 1 (by rfl) ⟨4191263, by rfl⟩ : syracuseStep 5588351 = 8382527) B8382527
theorem B3728987 : Blo 1655527 3728987 := bstep (se 1 (by rfl) ⟨2796740, by rfl⟩ : syracuseStep 3728987 = 5593481) B5593481
theorem B12585455 : Blo 1655527 12585455 := bstep (se 1 (by rfl) ⟨9439091, by rfl⟩ : syracuseStep 12585455 = 18878183) B18878183
theorem B2484971 : Blo 1655527 2484971 := bstep (se 1 (by rfl) ⟨1863728, by rfl⟩ : syracuseStep 2484971 = 3727457) B3727457
theorem B2485055 : Blo 1655527 2485055 := bstep (se 1 (by rfl) ⟨1863791, by rfl⟩ : syracuseStep 2485055 = 3727583) B3727583
theorem B1862527 : Blo 1655527 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B5590511 : Blo 1655527 5590511 := bstep (se 1 (by rfl) ⟨4192883, by rfl⟩ : syracuseStep 5590511 = 8385767) B8385767
theorem B9432713 : Blo 1655527 9432713 := bstep (se 2 (by rfl) ⟨3537267, by rfl⟩ : syracuseStep 9432713 = 7074535) B7074535
theorem B4191871 : Blo 1655527 4191871 := bstep (se 1 (by rfl) ⟨3143903, by rfl⟩ : syracuseStep 4191871 = 6287807) B6287807
theorem B9434879 : Blo 1655527 9434879 := bstep (se 1 (by rfl) ⟨7076159, by rfl⟩ : syracuseStep 9434879 = 14152319) B14152319
theorem B3725225 : Blo 1655527 3725225 := bstep (se 2 (by rfl) ⟨1396959, by rfl⟩ : syracuseStep 3725225 = 2793919) B2793919
theorem B5307839 : Blo 1655527 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B2358839 : Blo 1655527 2358839 := bstep (se 1 (by rfl) ⟨1769129, by rfl⟩ : syracuseStep 2358839 = 3538259) B3538259
theorem B10616777 : Blo 1655527 10616777 := bstep (se 2 (by rfl) ⟨3981291, by rfl⟩ : syracuseStep 10616777 = 7962583) B7962583
theorem B3145871 : Blo 1655527 3145871 := bstep (se 1 (by rfl) ⟨2359403, by rfl⟩ : syracuseStep 3145871 = 4718807) B4718807
theorem B5309171 : Blo 1655527 5309171 := bstep (se 1 (by rfl) ⟨3981878, by rfl⟩ : syracuseStep 5309171 = 7963757) B7963757
theorem B2483369 : Blo 1655527 2483369 := bstep (se 2 (by rfl) ⟨931263, by rfl⟩ : syracuseStep 2483369 = 1862527) B1862527
theorem B2483483 : Blo 1655527 2483483 := bstep (se 1 (by rfl) ⟨1862612, by rfl⟩ : syracuseStep 2483483 = 3725225) B3725225
theorem B8390303 : Blo 1655527 8390303 := bstep (se 1 (by rfl) ⟨6292727, by rfl⟩ : syracuseStep 8390303 = 12585455) B12585455
theorem B1656647 : Blo 1655527 1656647 := bstep (se 1 (by rfl) ⟨1242485, by rfl⟩ : syracuseStep 1656647 = 2484971) B2484971
theorem B1656703 : Blo 1655527 1656703 := bstep (se 1 (by rfl) ⟨1242527, by rfl⟩ : syracuseStep 1656703 = 2485055) B2485055
theorem B5589161 : Blo 1655527 5589161 := bstep (se 2 (by rfl) ⟨2095935, by rfl⟩ : syracuseStep 5589161 = 4191871) B4191871
theorem B2485991 : Blo 1655527 2485991 := bstep (se 1 (by rfl) ⟨1864493, by rfl⟩ : syracuseStep 2485991 = 3728987) B3728987
theorem B6288475 : Blo 1655527 6288475 := bstep (se 1 (by rfl) ⟨4716356, by rfl⟩ : syracuseStep 6288475 = 9432713) B9432713
theorem B3725567 : Blo 1655527 3725567 := bstep (se 1 (by rfl) ⟨2794175, by rfl⟩ : syracuseStep 3725567 = 5588351) B5588351
theorem B6289919 : Blo 1655527 6289919 := bstep (se 1 (by rfl) ⟨4717439, by rfl⟩ : syracuseStep 6289919 = 9434879) B9434879
theorem B6290237 : Blo 1655527 6290237 := bstep (se 3 (by rfl) ⟨1179419, by rfl⟩ : syracuseStep 6290237 = 2358839) B2358839
theorem B3538559 : Blo 1655527 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B3727007 : Blo 1655527 3727007 := bstep (se 1 (by rfl) ⟨2795255, by rfl⟩ : syracuseStep 3727007 = 5590511) B5590511
theorem B7077851 : Blo 1655527 7077851 := bstep (se 1 (by rfl) ⟨5308388, by rfl⟩ : syracuseStep 7077851 = 10616777) B10616777
theorem B2097247 : Blo 1655527 2097247 := bstep (se 1 (by rfl) ⟨1572935, by rfl⟩ : syracuseStep 2097247 = 3145871) B3145871
theorem B3539447 : Blo 1655527 3539447 := bstep (se 1 (by rfl) ⟨2654585, by rfl⟩ : syracuseStep 3539447 = 5309171) B5309171
theorem B1655579 : Blo 1655527 1655579 := bstep (se 1 (by rfl) ⟨1241684, by rfl⟩ : syracuseStep 1655579 = 2483369) B2483369
theorem B1655655 : Blo 1655527 1655655 := bstep (se 1 (by rfl) ⟨1241741, by rfl⟩ : syracuseStep 1655655 = 2483483) B2483483
theorem B2483711 : Blo 1655527 2483711 := bstep (se 1 (by rfl) ⟨1862783, by rfl⟩ : syracuseStep 2483711 = 3725567) B3725567
theorem B2484671 : Blo 1655527 2484671 := bstep (se 1 (by rfl) ⟨1863503, by rfl⟩ : syracuseStep 2484671 = 3727007) B3727007
theorem B1657327 : Blo 1655527 1657327 := bstep (se 1 (by rfl) ⟨1242995, by rfl⟩ : syracuseStep 1657327 = 2485991) B2485991
theorem B8384633 : Blo 1655527 8384633 := bstep (se 2 (by rfl) ⟨3144237, by rfl⟩ : syracuseStep 8384633 = 6288475) B6288475
theorem B5593535 : Blo 1655527 5593535 := bstep (se 1 (by rfl) ⟨4195151, by rfl⟩ : syracuseStep 5593535 = 8390303) B8390303
theorem B3726107 : Blo 1655527 3726107 := bstep (se 1 (by rfl) ⟨2794580, by rfl⟩ : syracuseStep 3726107 = 5589161) B5589161
theorem B4193279 : Blo 1655527 4193279 := bstep (se 1 (by rfl) ⟨3144959, by rfl⟩ : syracuseStep 4193279 = 6289919) B6289919
theorem B4193491 : Blo 1655527 4193491 := bstep (se 1 (by rfl) ⟨3145118, by rfl⟩ : syracuseStep 4193491 = 6290237) B6290237
theorem B2359039 : Blo 1655527 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B4718567 : Blo 1655527 4718567 := bstep (se 1 (by rfl) ⟨3538925, by rfl⟩ : syracuseStep 4718567 = 7077851) B7077851
theorem B2359631 : Blo 1655527 2359631 := bstep (se 1 (by rfl) ⟨1769723, by rfl⟩ : syracuseStep 2359631 = 3539447) B3539447
theorem B1655807 : Blo 1655527 1655807 := bstep (se 1 (by rfl) ⟨1241855, by rfl⟩ : syracuseStep 1655807 = 2483711) B2483711
theorem B1656447 : Blo 1655527 1656447 := bstep (se 1 (by rfl) ⟨1242335, by rfl⟩ : syracuseStep 1656447 = 2484671) B2484671
theorem B3729023 : Blo 1655527 3729023 := bstep (se 1 (by rfl) ⟨2796767, by rfl⟩ : syracuseStep 3729023 = 5593535) B5593535
theorem B2484071 : Blo 1655527 2484071 := bstep (se 1 (by rfl) ⟨1863053, by rfl⟩ : syracuseStep 2484071 = 3726107) B3726107
theorem B2795519 : Blo 1655527 2795519 := bstep (se 1 (by rfl) ⟨2096639, by rfl⟩ : syracuseStep 2795519 = 4193279) B4193279
theorem B5589755 : Blo 1655527 5589755 := bstep (se 1 (by rfl) ⟨4192316, by rfl⟩ : syracuseStep 5589755 = 8384633) B8384633
theorem B2796329 : Blo 1655527 2796329 := bstep (se 2 (by rfl) ⟨1048623, by rfl⟩ : syracuseStep 2796329 = 2097247) B2097247
theorem B5591321 : Blo 1655527 5591321 := bstep (se 2 (by rfl) ⟨2096745, by rfl⟩ : syracuseStep 5591321 = 4193491) B4193491
theorem B3145385 : Blo 1655527 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B3145711 : Blo 1655527 3145711 := bstep (se 1 (by rfl) ⟨2359283, by rfl⟩ : syracuseStep 3145711 = 4718567) B4718567
theorem B3727547 : Blo 1655527 3727547 := bstep (se 1 (by rfl) ⟨2795660, by rfl⟩ : syracuseStep 3727547 = 5591321) B5591321
theorem B6292349 : Blo 1655527 6292349 := bstep (se 3 (by rfl) ⟨1179815, by rfl⟩ : syracuseStep 6292349 = 2359631) B2359631
theorem B1656047 : Blo 1655527 1656047 := bstep (se 1 (by rfl) ⟨1242035, by rfl⟩ : syracuseStep 1656047 = 2484071) B2484071
theorem B2486015 : Blo 1655527 2486015 := bstep (se 1 (by rfl) ⟨1864511, by rfl⟩ : syracuseStep 2486015 = 3729023) B3729023
theorem B1863679 : Blo 1655527 1863679 := bstep (se 1 (by rfl) ⟨1397759, by rfl⟩ : syracuseStep 1863679 = 2795519) B2795519
theorem B1864219 : Blo 1655527 1864219 := bstep (se 1 (by rfl) ⟨1398164, by rfl⟩ : syracuseStep 1864219 = 2796329) B2796329
theorem B3726503 : Blo 1655527 3726503 := bstep (se 1 (by rfl) ⟨2794877, by rfl⟩ : syracuseStep 3726503 = 5589755) B5589755
theorem B2096923 : Blo 1655527 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B4194281 : Blo 1655527 4194281 := bstep (se 2 (by rfl) ⟨1572855, by rfl⟩ : syracuseStep 4194281 = 3145711) B3145711
theorem B4194899 : Blo 1655527 4194899 := bstep (se 1 (by rfl) ⟨3146174, by rfl⟩ : syracuseStep 4194899 = 6292349) B6292349
theorem B2484335 : Blo 1655527 2484335 := bstep (se 1 (by rfl) ⟨1863251, by rfl⟩ : syracuseStep 2484335 = 3726503) B3726503
theorem B2795897 : Blo 1655527 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B1657343 : Blo 1655527 1657343 := bstep (se 1 (by rfl) ⟨1243007, by rfl⟩ : syracuseStep 1657343 = 2486015) B2486015
theorem B2796187 : Blo 1655527 2796187 := bstep (se 1 (by rfl) ⟨2097140, by rfl⟩ : syracuseStep 2796187 = 4194281) B4194281
theorem B2484905 : Blo 1655527 2484905 := bstep (se 2 (by rfl) ⟨931839, by rfl⟩ : syracuseStep 2484905 = 1863679) B1863679
theorem B2485031 : Blo 1655527 2485031 := bstep (se 1 (by rfl) ⟨1863773, by rfl⟩ : syracuseStep 2485031 = 3727547) B3727547
theorem B2485625 : Blo 1655527 2485625 := bstep (se 2 (by rfl) ⟨932109, by rfl⟩ : syracuseStep 2485625 = 1864219) B1864219
theorem B3728249 : Blo 1655527 3728249 := bstep (se 2 (by rfl) ⟨1398093, by rfl⟩ : syracuseStep 3728249 = 2796187) B2796187
theorem B1656223 : Blo 1655527 1656223 := bstep (se 1 (by rfl) ⟨1242167, by rfl⟩ : syracuseStep 1656223 = 2484335) B2484335
theorem B1656603 : Blo 1655527 1656603 := bstep (se 1 (by rfl) ⟨1242452, by rfl⟩ : syracuseStep 1656603 = 2484905) B2484905
theorem B1656687 : Blo 1655527 1656687 := bstep (se 1 (by rfl) ⟨1242515, by rfl⟩ : syracuseStep 1656687 = 2485031) B2485031
theorem B1657083 : Blo 1655527 1657083 := bstep (se 1 (by rfl) ⟨1242812, by rfl⟩ : syracuseStep 1657083 = 2485625) B2485625
theorem B2796599 : Blo 1655527 2796599 := bstep (se 1 (by rfl) ⟨2097449, by rfl⟩ : syracuseStep 2796599 = 4194899) B4194899
theorem B1863931 : Blo 1655527 1863931 := bstep (se 1 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 1863931 = 2795897) B2795897
theorem B2485241 : Blo 1655527 2485241 := bstep (se 2 (by rfl) ⟨931965, by rfl⟩ : syracuseStep 2485241 = 1863931) B1863931
theorem B2485499 : Blo 1655527 2485499 := bstep (se 1 (by rfl) ⟨1864124, by rfl⟩ : syracuseStep 2485499 = 3728249) B3728249
theorem B1864399 : Blo 1655527 1864399 := bstep (se 1 (by rfl) ⟨1398299, by rfl⟩ : syracuseStep 1864399 = 2796599) B2796599
theorem B1656827 : Blo 1655527 1656827 := bstep (se 1 (by rfl) ⟨1242620, by rfl⟩ : syracuseStep 1656827 = 2485241) B2485241
theorem B1656999 : Blo 1655527 1656999 := bstep (se 1 (by rfl) ⟨1242749, by rfl⟩ : syracuseStep 1656999 = 2485499) B2485499
theorem B2485865 : Blo 1655527 2485865 := bstep (se 2 (by rfl) ⟨932199, by rfl⟩ : syracuseStep 2485865 = 1864399) B1864399
theorem B1657243 : Blo 1655527 1657243 := bstep (se 1 (by rfl) ⟨1242932, by rfl⟩ : syracuseStep 1657243 = 2485865) B2485865

theorem C0 (j : ℕ) (h1 : 413881 ≤ j) (h2 : j ≤ 414381) : Blo 1655527 (4 * j + 3) := by
  interval_cases j
  · exact B1655527
  · exact B1655531
  · exact B1655535
  · exact B1655539
  · exact B1655543
  · exact B1655547
  · exact B1655551
  · exact B1655555
  · exact B1655559
  · exact B1655563
  · exact B1655567
  · exact B1655571
  · exact B1655575
  · exact B1655579
  · exact B1655583
  · exact B1655587
  · exact B1655591
  · exact B1655595
  · exact B1655599
  · exact B1655603
  · exact B1655607
  · exact B1655611
  · exact B1655615
  · exact B1655619
  · exact B1655623
  · exact B1655627
  · exact B1655631
  · exact B1655635
  · exact B1655639
  · exact B1655643
  · exact B1655647
  · exact B1655651
  · exact B1655655
  · exact B1655659
  · exact B1655663
  · exact B1655667
  · exact B1655671
  · exact B1655675
  · exact B1655679
  · exact B1655683
  · exact B1655687
  · exact B1655691
  · exact B1655695
  · exact B1655699
  · exact B1655703
  · exact B1655707
  · exact B1655711
  · exact B1655715
  · exact B1655719
  · exact B1655723
  · exact B1655727
  · exact B1655731
  · exact B1655735
  · exact B1655739
  · exact B1655743
  · exact B1655747
  · exact B1655751
  · exact B1655755
  · exact B1655759
  · exact B1655763
  · exact B1655767
  · exact B1655771
  · exact B1655775
  · exact B1655779
  · exact B1655783
  · exact B1655787
  · exact B1655791
  · exact B1655795
  · exact B1655799
  · exact B1655803
  · exact B1655807
  · exact B1655811
  · exact B1655815
  · exact B1655819
  · exact B1655823
  · exact B1655827
  · exact B1655831
  · exact B1655835
  · exact B1655839
  · exact B1655843
  · exact B1655847
  · exact B1655851
  · exact B1655855
  · exact B1655859
  · exact B1655863
  · exact B1655867
  · exact B1655871
  · exact B1655875
  · exact B1655879
  · exact B1655883
  · exact B1655887
  · exact B1655891
  · exact B1655895
  · exact B1655899
  · exact B1655903
  · exact B1655907
  · exact B1655911
  · exact B1655915
  · exact B1655919
  · exact B1655923
  · exact B1655927
  · exact B1655931
  · exact B1655935
  · exact B1655939
  · exact B1655943
  · exact B1655947
  · exact B1655951
  · exact B1655955
  · exact B1655959
  · exact B1655963
  · exact B1655967
  · exact B1655971
  · exact B1655975
  · exact B1655979
  · exact B1655983
  · exact B1655987
  · exact B1655991
  · exact B1655995
  · exact B1655999
  · exact B1656003
  · exact B1656007
  · exact B1656011
  · exact B1656015
  · exact B1656019
  · exact B1656023
  · exact B1656027
  · exact B1656031
  · exact B1656035
  · exact B1656039
  · exact B1656043
  · exact B1656047
  · exact B1656051
  · exact B1656055
  · exact B1656059
  · exact B1656063
  · exact B1656067
  · exact B1656071
  · exact B1656075
  · exact B1656079
  · exact B1656083
  · exact B1656087
  · exact B1656091
  · exact B1656095
  · exact B1656099
  · exact B1656103
  · exact B1656107
  · exact B1656111
  · exact B1656115
  · exact B1656119
  · exact B1656123
  · exact B1656127
  · exact B1656131
  · exact B1656135
  · exact B1656139
  · exact B1656143
  · exact B1656147
  · exact B1656151
  · exact B1656155
  · exact B1656159
  · exact B1656163
  · exact B1656167
  · exact B1656171
  · exact B1656175
  · exact B1656179
  · exact B1656183
  · exact B1656187
  · exact B1656191
  · exact B1656195
  · exact B1656199
  · exact B1656203
  · exact B1656207
  · exact B1656211
  · exact B1656215
  · exact B1656219
  · exact B1656223
  · exact B1656227
  · exact B1656231
  · exact B1656235
  · exact B1656239
  · exact B1656243
  · exact B1656247
  · exact B1656251
  · exact B1656255
  · exact B1656259
  · exact B1656263
  · exact B1656267
  · exact B1656271
  · exact B1656275
  · exact B1656279
  · exact B1656283
  · exact B1656287
  · exact B1656291
  · exact B1656295
  · exact B1656299
  · exact B1656303
  · exact B1656307
  · exact B1656311
  · exact B1656315
  · exact B1656319
  · exact B1656323
  · exact B1656327
  · exact B1656331
  · exact B1656335
  · exact B1656339
  · exact B1656343
  · exact B1656347
  · exact B1656351
  · exact B1656355
  · exact B1656359
  · exact B1656363
  · exact B1656367
  · exact B1656371
  · exact B1656375
  · exact B1656379
  · exact B1656383
  · exact B1656387
  · exact B1656391
  · exact B1656395
  · exact B1656399
  · exact B1656403
  · exact B1656407
  · exact B1656411
  · exact B1656415
  · exact B1656419
  · exact B1656423
  · exact B1656427
  · exact B1656431
  · exact B1656435
  · exact B1656439
  · exact B1656443
  · exact B1656447
  · exact B1656451
  · exact B1656455
  · exact B1656459
  · exact B1656463
  · exact B1656467
  · exact B1656471
  · exact B1656475
  · exact B1656479
  · exact B1656483
  · exact B1656487
  · exact B1656491
  · exact B1656495
  · exact B1656499
  · exact B1656503
  · exact B1656507
  · exact B1656511
  · exact B1656515
  · exact B1656519
  · exact B1656523
  · exact B1656527
  · exact B1656531
  · exact B1656535
  · exact B1656539
  · exact B1656543
  · exact B1656547
  · exact B1656551
  · exact B1656555
  · exact B1656559
  · exact B1656563
  · exact B1656567
  · exact B1656571
  · exact B1656575
  · exact B1656579
  · exact B1656583
  · exact B1656587
  · exact B1656591
  · exact B1656595
  · exact B1656599
  · exact B1656603
  · exact B1656607
  · exact B1656611
  · exact B1656615
  · exact B1656619
  · exact B1656623
  · exact B1656627
  · exact B1656631
  · exact B1656635
  · exact B1656639
  · exact B1656643
  · exact B1656647
  · exact B1656651
  · exact B1656655
  · exact B1656659
  · exact B1656663
  · exact B1656667
  · exact B1656671
  · exact B1656675
  · exact B1656679
  · exact B1656683
  · exact B1656687
  · exact B1656691
  · exact B1656695
  · exact B1656699
  · exact B1656703
  · exact B1656707
  · exact B1656711
  · exact B1656715
  · exact B1656719
  · exact B1656723
  · exact B1656727
  · exact B1656731
  · exact B1656735
  · exact B1656739
  · exact B1656743
  · exact B1656747
  · exact B1656751
  · exact B1656755
  · exact B1656759
  · exact B1656763
  · exact B1656767
  · exact B1656771
  · exact B1656775
  · exact B1656779
  · exact B1656783
  · exact B1656787
  · exact B1656791
  · exact B1656795
  · exact B1656799
  · exact B1656803
  · exact B1656807
  · exact B1656811
  · exact B1656815
  · exact B1656819
  · exact B1656823
  · exact B1656827
  · exact B1656831
  · exact B1656835
  · exact B1656839
  · exact B1656843
  · exact B1656847
  · exact B1656851
  · exact B1656855
  · exact B1656859
  · exact B1656863
  · exact B1656867
  · exact B1656871
  · exact B1656875
  · exact B1656879
  · exact B1656883
  · exact B1656887
  · exact B1656891
  · exact B1656895
  · exact B1656899
  · exact B1656903
  · exact B1656907
  · exact B1656911
  · exact B1656915
  · exact B1656919
  · exact B1656923
  · exact B1656927
  · exact B1656931
  · exact B1656935
  · exact B1656939
  · exact B1656943
  · exact B1656947
  · exact B1656951
  · exact B1656955
  · exact B1656959
  · exact B1656963
  · exact B1656967
  · exact B1656971
  · exact B1656975
  · exact B1656979
  · exact B1656983
  · exact B1656987
  · exact B1656991
  · exact B1656995
  · exact B1656999
  · exact B1657003
  · exact B1657007
  · exact B1657011
  · exact B1657015
  · exact B1657019
  · exact B1657023
  · exact B1657027
  · exact B1657031
  · exact B1657035
  · exact B1657039
  · exact B1657043
  · exact B1657047
  · exact B1657051
  · exact B1657055
  · exact B1657059
  · exact B1657063
  · exact B1657067
  · exact B1657071
  · exact B1657075
  · exact B1657079
  · exact B1657083
  · exact B1657087
  · exact B1657091
  · exact B1657095
  · exact B1657099
  · exact B1657103
  · exact B1657107
  · exact B1657111
  · exact B1657115
  · exact B1657119
  · exact B1657123
  · exact B1657127
  · exact B1657131
  · exact B1657135
  · exact B1657139
  · exact B1657143
  · exact B1657147
  · exact B1657151
  · exact B1657155
  · exact B1657159
  · exact B1657163
  · exact B1657167
  · exact B1657171
  · exact B1657175
  · exact B1657179
  · exact B1657183
  · exact B1657187
  · exact B1657191
  · exact B1657195
  · exact B1657199
  · exact B1657203
  · exact B1657207
  · exact B1657211
  · exact B1657215
  · exact B1657219
  · exact B1657223
  · exact B1657227
  · exact B1657231
  · exact B1657235
  · exact B1657239
  · exact B1657243
  · exact B1657247
  · exact B1657251
  · exact B1657255
  · exact B1657259
  · exact B1657263
  · exact B1657267
  · exact B1657271
  · exact B1657275
  · exact B1657279
  · exact B1657283
  · exact B1657287
  · exact B1657291
  · exact B1657295
  · exact B1657299
  · exact B1657303
  · exact B1657307
  · exact B1657311
  · exact B1657315
  · exact B1657319
  · exact B1657323
  · exact B1657327
  · exact B1657331
  · exact B1657335
  · exact B1657339
  · exact B1657343
  · exact B1657347
  · exact B1657351
  · exact B1657355
  · exact B1657359
  · exact B1657363
  · exact B1657367
  · exact B1657371
  · exact B1657375
  · exact B1657379
  · exact B1657383
  · exact B1657387
  · exact B1657391
  · exact B1657395
  · exact B1657399
  · exact B1657403
  · exact B1657407
  · exact B1657411
  · exact B1657415
  · exact B1657419
  · exact B1657423
  · exact B1657427
  · exact B1657431
  · exact B1657435
  · exact B1657439
  · exact B1657443
  · exact B1657447
  · exact B1657451
  · exact B1657455
  · exact B1657459
  · exact B1657463
  · exact B1657467
  · exact B1657471
  · exact B1657475
  · exact B1657479
  · exact B1657483
  · exact B1657487
  · exact B1657491
  · exact B1657495
  · exact B1657499
  · exact B1657503
  · exact B1657507
  · exact B1657511
  · exact B1657515
  · exact B1657519
  · exact B1657523
  · exact B1657527

theorem solution (m : ℕ) (hlo : 1655527 ≤ m) (hhi : m ≤ 1657527) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 413881 ≤ j := by omega
    have hj2 : j ≤ 414381 := by omega
    have hb : Blo 1655527 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
