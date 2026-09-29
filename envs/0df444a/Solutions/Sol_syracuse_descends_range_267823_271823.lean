-- Prove2me | solution 1 for syracuse_descends_range_267823_271823
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:09.714127+00:00
-- url     : https://prove2.me/submissions/8c81c1ee-060b-42ac-a619-4bcc09c68cf1

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


theorem B688445 : Blo 267823 688445 := bbase (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) (by norm_num)
theorem B3277205 : Blo 267823 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B295633 : Blo 267823 295633 := bbase (se 2 (by rfl) ⟨110862, by rfl⟩ : syracuseStep 295633 = 221725) (by norm_num)
theorem B1147765 : Blo 267823 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B2327413 : Blo 267823 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B1737845 : Blo 267823 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B820469 : Blo 267823 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B1377605 : Blo 267823 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B1836533 : Blo 267823 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B984565 : Blo 267823 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B460933 : Blo 267823 460933 := bbase (se 4 (by rfl) ⟨43212, by rfl⟩ : syracuseStep 460933 = 86425) (by norm_num)
theorem B821381 : Blo 267823 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B2033909 : Blo 267823 2033909 := bbase (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) (by norm_num)
theorem B2787605 : Blo 267823 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B1935701 : Blo 267823 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1018277 : Blo 267823 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B1018565 : Blo 267823 1018565 := bbase (se 4 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 1018565 = 190981) (by norm_num)
theorem B428885 : Blo 267823 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B4623317 : Blo 267823 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B1543157 : Blo 267823 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B3083669 : Blo 267823 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B822757 : Blo 267823 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B429797 : Blo 267823 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B1150757 : Blo 267823 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1019749 : Blo 267823 1019749 := bbase (se 4 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 1019749 = 191203) (by norm_num)
theorem B2297717 : Blo 267823 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B1020053 : Blo 267823 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B430733 : Blo 267823 430733 := bbase (se 3 (by rfl) ⟨80762, by rfl⟩ : syracuseStep 430733 = 161525) (by norm_num)
theorem B332429 : Blo 267823 332429 := bbase (se 3 (by rfl) ⟨62330, by rfl⟩ : syracuseStep 332429 = 124661) (by norm_num)
theorem B1151765 : Blo 267823 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B725845 : Blo 267823 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B463909 : Blo 267823 463909 := bbase (se 4 (by rfl) ⟨43491, by rfl⟩ : syracuseStep 463909 = 86983) (by norm_num)
theorem B431381 : Blo 267823 431381 := bbase (se 6 (by rfl) ⟨10110, by rfl⟩ : syracuseStep 431381 = 20221) (by norm_num)
theorem B3446165 : Blo 267823 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B693749 : Blo 267823 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B464717 : Blo 267823 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B3479381 : Blo 267823 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1022165 : Blo 267823 1022165 := bbase (se 7 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 1022165 = 23957) (by norm_num)
theorem B432373 : Blo 267823 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B301333 : Blo 267823 301333 := bbase (se 6 (by rfl) ⟨7062, by rfl⟩ : syracuseStep 301333 = 14125) (by norm_num)
theorem B301369 : Blo 267823 301369 := bbase (se 2 (by rfl) ⟨113013, by rfl⟩ : syracuseStep 301369 = 226027) (by norm_num)
theorem B301405 : Blo 267823 301405 := bbase (se 3 (by rfl) ⟨56513, by rfl⟩ : syracuseStep 301405 = 113027) (by norm_num)
theorem B301441 : Blo 267823 301441 := bbase (se 2 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 301441 = 226081) (by norm_num)
theorem B301477 : Blo 267823 301477 := bbase (se 4 (by rfl) ⟨28263, by rfl⟩ : syracuseStep 301477 = 56527) (by norm_num)
theorem B301513 : Blo 267823 301513 := bbase (se 2 (by rfl) ⟨113067, by rfl⟩ : syracuseStep 301513 = 226135) (by norm_num)
theorem B301549 : Blo 267823 301549 := bbase (se 3 (by rfl) ⟨56540, by rfl⟩ : syracuseStep 301549 = 113081) (by norm_num)
theorem B1022453 : Blo 267823 1022453 := bbase (se 5 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 1022453 = 95855) (by norm_num)
theorem B1153541 : Blo 267823 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B301585 : Blo 267823 301585 := bbase (se 2 (by rfl) ⟨113094, by rfl⟩ : syracuseStep 301585 = 226189) (by norm_num)
theorem B301621 : Blo 267823 301621 := bbase (se 5 (by rfl) ⟨14138, by rfl⟩ : syracuseStep 301621 = 28277) (by norm_num)
theorem B4659797 : Blo 267823 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B301657 : Blo 267823 301657 := bbase (se 2 (by rfl) ⟨113121, by rfl⟩ : syracuseStep 301657 = 226243) (by norm_num)
theorem B301693 : Blo 267823 301693 := bbase (se 3 (by rfl) ⟨56567, by rfl⟩ : syracuseStep 301693 = 113135) (by norm_num)
theorem B367237 : Blo 267823 367237 := bbase (se 4 (by rfl) ⟨34428, by rfl⟩ : syracuseStep 367237 = 68857) (by norm_num)
theorem B301729 : Blo 267823 301729 := bbase (se 2 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 301729 = 226297) (by norm_num)
theorem B432821 : Blo 267823 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B301765 : Blo 267823 301765 := bbase (se 4 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 301765 = 56581) (by norm_num)
theorem B301801 : Blo 267823 301801 := bbase (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) (by norm_num)
theorem B301837 : Blo 267823 301837 := bbase (se 3 (by rfl) ⟨56594, by rfl⟩ : syracuseStep 301837 = 113189) (by norm_num)
theorem B301873 : Blo 267823 301873 := bbase (se 2 (by rfl) ⟨113202, by rfl⟩ : syracuseStep 301873 = 226405) (by norm_num)
theorem B301909 : Blo 267823 301909 := bbase (se 9 (by rfl) ⟨884, by rfl⟩ : syracuseStep 301909 = 1769) (by norm_num)
theorem B301945 : Blo 267823 301945 := bbase (se 2 (by rfl) ⟨113229, by rfl⟩ : syracuseStep 301945 = 226459) (by norm_num)
theorem B433021 : Blo 267823 433021 := bbase (se 3 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 433021 = 162383) (by norm_num)
theorem B301981 : Blo 267823 301981 := bbase (se 3 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 301981 = 113243) (by norm_num)
theorem B302017 : Blo 267823 302017 := bbase (se 2 (by rfl) ⟨113256, by rfl⟩ : syracuseStep 302017 = 226513) (by norm_num)
theorem B302053 : Blo 267823 302053 := bbase (se 4 (by rfl) ⟨28317, by rfl⟩ : syracuseStep 302053 = 56635) (by norm_num)
theorem B302089 : Blo 267823 302089 := bbase (se 2 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 302089 = 226567) (by norm_num)
theorem B302125 : Blo 267823 302125 := bbase (se 3 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 302125 = 113297) (by norm_num)
theorem B695341 : Blo 267823 695341 := bbase (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) (by norm_num)
theorem B302161 : Blo 267823 302161 := bbase (se 2 (by rfl) ⟨113310, by rfl⟩ : syracuseStep 302161 = 226621) (by norm_num)
theorem B826453 : Blo 267823 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B302197 : Blo 267823 302197 := bbase (se 5 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 302197 = 28331) (by norm_num)
theorem B433277 : Blo 267823 433277 := bbase (se 3 (by rfl) ⟨81239, by rfl⟩ : syracuseStep 433277 = 162479) (by norm_num)
theorem B302233 : Blo 267823 302233 := bbase (se 2 (by rfl) ⟨113337, by rfl⟩ : syracuseStep 302233 = 226675) (by norm_num)
theorem B2202805 : Blo 267823 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B302269 : Blo 267823 302269 := bbase (se 3 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 302269 = 113351) (by norm_num)
theorem B302305 : Blo 267823 302305 := bbase (se 2 (by rfl) ⟨113364, by rfl⟩ : syracuseStep 302305 = 226729) (by norm_num)
theorem B302341 : Blo 267823 302341 := bbase (se 4 (by rfl) ⟨28344, by rfl⟩ : syracuseStep 302341 = 56689) (by norm_num)
theorem B302377 : Blo 267823 302377 := bbase (se 2 (by rfl) ⟨113391, by rfl⟩ : syracuseStep 302377 = 226783) (by norm_num)
theorem B302413 : Blo 267823 302413 := bbase (se 3 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 302413 = 113405) (by norm_num)
theorem B302449 : Blo 267823 302449 := bbase (se 2 (by rfl) ⟨113418, by rfl⟩ : syracuseStep 302449 = 226837) (by norm_num)
theorem B302485 : Blo 267823 302485 := bbase (se 6 (by rfl) ⟨7089, by rfl⟩ : syracuseStep 302485 = 14179) (by norm_num)
theorem B302521 : Blo 267823 302521 := bbase (se 2 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 302521 = 226891) (by norm_num)
theorem B990677 : Blo 267823 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B302557 : Blo 267823 302557 := bbase (se 3 (by rfl) ⟨56729, by rfl⟩ : syracuseStep 302557 = 113459) (by norm_num)
theorem B2334197 : Blo 267823 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B302593 : Blo 267823 302593 := bbase (se 2 (by rfl) ⟨113472, by rfl⟩ : syracuseStep 302593 = 226945) (by norm_num)
theorem B302629 : Blo 267823 302629 := bbase (se 4 (by rfl) ⟨28371, by rfl⟩ : syracuseStep 302629 = 56743) (by norm_num)
theorem B302665 : Blo 267823 302665 := bbase (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) (by norm_num)
theorem B302701 : Blo 267823 302701 := bbase (se 3 (by rfl) ⟨56756, by rfl⟩ : syracuseStep 302701 = 113513) (by norm_num)
theorem B302737 : Blo 267823 302737 := bbase (se 2 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 302737 = 227053) (by norm_num)
theorem B1023637 : Blo 267823 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B302773 : Blo 267823 302773 := bbase (se 5 (by rfl) ⟨14192, by rfl⟩ : syracuseStep 302773 = 28385) (by norm_num)
theorem B302809 : Blo 267823 302809 := bbase (se 2 (by rfl) ⟨113553, by rfl⟩ : syracuseStep 302809 = 227107) (by norm_num)
theorem B302845 : Blo 267823 302845 := bbase (se 3 (by rfl) ⟨56783, by rfl⟩ : syracuseStep 302845 = 113567) (by norm_num)
theorem B302881 : Blo 267823 302881 := bbase (se 2 (by rfl) ⟨113580, by rfl⟩ : syracuseStep 302881 = 227161) (by norm_num)
theorem B302917 : Blo 267823 302917 := bbase (se 4 (by rfl) ⟨28398, by rfl⟩ : syracuseStep 302917 = 56797) (by norm_num)
theorem B302953 : Blo 267823 302953 := bbase (se 2 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 302953 = 227215) (by norm_num)
theorem B1056629 : Blo 267823 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B302989 : Blo 267823 302989 := bbase (se 3 (by rfl) ⟨56810, by rfl⟩ : syracuseStep 302989 = 113621) (by norm_num)
theorem B368533 : Blo 267823 368533 := bbase (se 6 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 368533 = 17275) (by norm_num)
theorem B303025 : Blo 267823 303025 := bbase (se 2 (by rfl) ⟨113634, by rfl⟩ : syracuseStep 303025 = 227269) (by norm_num)
theorem B1023941 : Blo 267823 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B303061 : Blo 267823 303061 := bbase (se 7 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 303061 = 7103) (by norm_num)
theorem B303097 : Blo 267823 303097 := bbase (se 2 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 303097 = 227323) (by norm_num)
theorem B696325 : Blo 267823 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B303133 : Blo 267823 303133 := bbase (se 3 (by rfl) ⟨56837, by rfl⟩ : syracuseStep 303133 = 113675) (by norm_num)
theorem B303169 : Blo 267823 303169 := bbase (se 2 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 303169 = 227377) (by norm_num)
theorem B303205 : Blo 267823 303205 := bbase (se 4 (by rfl) ⟨28425, by rfl⟩ : syracuseStep 303205 = 56851) (by norm_num)
theorem B303241 : Blo 267823 303241 := bbase (se 2 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 303241 = 227431) (by norm_num)
theorem B303277 : Blo 267823 303277 := bbase (se 3 (by rfl) ⟨56864, by rfl⟩ : syracuseStep 303277 = 113729) (by norm_num)
theorem B303313 : Blo 267823 303313 := bbase (se 2 (by rfl) ⟨113742, by rfl⟩ : syracuseStep 303313 = 227485) (by norm_num)
theorem B434405 : Blo 267823 434405 := bbase (se 4 (by rfl) ⟨40725, by rfl⟩ : syracuseStep 434405 = 81451) (by norm_num)
theorem B303349 : Blo 267823 303349 := bbase (se 5 (by rfl) ⟨14219, by rfl⟩ : syracuseStep 303349 = 28439) (by norm_num)
theorem B303385 : Blo 267823 303385 := bbase (se 2 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 303385 = 227539) (by norm_num)
theorem B303421 : Blo 267823 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B401741 : Blo 267823 401741 := bbase (se 3 (by rfl) ⟨75326, by rfl⟩ : syracuseStep 401741 = 150653) (by norm_num)
theorem B303457 : Blo 267823 303457 := bbase (se 2 (by rfl) ⟨113796, by rfl⟩ : syracuseStep 303457 = 227593) (by norm_num)
theorem B401765 : Blo 267823 401765 := bbase (se 4 (by rfl) ⟨37665, by rfl⟩ : syracuseStep 401765 = 75331) (by norm_num)
theorem B401789 : Blo 267823 401789 := bbase (se 3 (by rfl) ⟨75335, by rfl⟩ : syracuseStep 401789 = 150671) (by norm_num)
theorem B303493 : Blo 267823 303493 := bbase (se 4 (by rfl) ⟨28452, by rfl⟩ : syracuseStep 303493 = 56905) (by norm_num)
theorem B401813 : Blo 267823 401813 := bbase (se 6 (by rfl) ⟨9417, by rfl⟩ : syracuseStep 401813 = 18835) (by norm_num)
theorem B303529 : Blo 267823 303529 := bbase (se 2 (by rfl) ⟨113823, by rfl⟩ : syracuseStep 303529 = 227647) (by norm_num)
theorem B401837 : Blo 267823 401837 := bbase (se 3 (by rfl) ⟨75344, by rfl⟩ : syracuseStep 401837 = 150689) (by norm_num)
theorem B401861 : Blo 267823 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B303565 : Blo 267823 303565 := bbase (se 3 (by rfl) ⟨56918, by rfl⟩ : syracuseStep 303565 = 113837) (by norm_num)
theorem B401885 : Blo 267823 401885 := bbase (se 3 (by rfl) ⟨75353, by rfl⟩ : syracuseStep 401885 = 150707) (by norm_num)
theorem B860645 : Blo 267823 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B303601 : Blo 267823 303601 := bbase (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) (by norm_num)
theorem B401909 : Blo 267823 401909 := bbase (se 5 (by rfl) ⟨18839, by rfl⟩ : syracuseStep 401909 = 37679) (by norm_num)
theorem B401933 : Blo 267823 401933 := bbase (se 3 (by rfl) ⟨75362, by rfl⟩ : syracuseStep 401933 = 150725) (by norm_num)
theorem B303637 : Blo 267823 303637 := bbase (se 6 (by rfl) ⟨7116, by rfl⟩ : syracuseStep 303637 = 14233) (by norm_num)
theorem B401957 : Blo 267823 401957 := bbase (se 4 (by rfl) ⟨37683, by rfl⟩ : syracuseStep 401957 = 75367) (by norm_num)
theorem B303673 : Blo 267823 303673 := bbase (se 2 (by rfl) ⟨113877, by rfl⟩ : syracuseStep 303673 = 227755) (by norm_num)
theorem B401981 : Blo 267823 401981 := bbase (se 3 (by rfl) ⟨75371, by rfl⟩ : syracuseStep 401981 = 150743) (by norm_num)
theorem B402005 : Blo 267823 402005 := bbase (se 8 (by rfl) ⟨2355, by rfl⟩ : syracuseStep 402005 = 4711) (by norm_num)
theorem B303709 : Blo 267823 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B402029 : Blo 267823 402029 := bbase (se 3 (by rfl) ⟨75380, by rfl⟩ : syracuseStep 402029 = 150761) (by norm_num)
theorem B303745 : Blo 267823 303745 := bbase (se 2 (by rfl) ⟨113904, by rfl⟩ : syracuseStep 303745 = 227809) (by norm_num)
theorem B402053 : Blo 267823 402053 := bbase (se 4 (by rfl) ⟨37692, by rfl⟩ : syracuseStep 402053 = 75385) (by norm_num)
theorem B402077 : Blo 267823 402077 := bbase (se 3 (by rfl) ⟨75389, by rfl⟩ : syracuseStep 402077 = 150779) (by norm_num)
theorem B303781 : Blo 267823 303781 := bbase (se 4 (by rfl) ⟨28479, by rfl⟩ : syracuseStep 303781 = 56959) (by norm_num)
theorem B402101 : Blo 267823 402101 := bbase (se 5 (by rfl) ⟨18848, by rfl⟩ : syracuseStep 402101 = 37697) (by norm_num)
theorem B303817 : Blo 267823 303817 := bbase (se 2 (by rfl) ⟨113931, by rfl⟩ : syracuseStep 303817 = 227863) (by norm_num)
theorem B402125 : Blo 267823 402125 := bbase (se 3 (by rfl) ⟨75398, by rfl⟩ : syracuseStep 402125 = 150797) (by norm_num)
theorem B402149 : Blo 267823 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B434917 : Blo 267823 434917 := bbase (se 4 (by rfl) ⟨40773, by rfl⟩ : syracuseStep 434917 = 81547) (by norm_num)
theorem B303853 : Blo 267823 303853 := bbase (se 3 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 303853 = 113945) (by norm_num)
theorem B402173 : Blo 267823 402173 := bbase (se 3 (by rfl) ⟨75407, by rfl⟩ : syracuseStep 402173 = 150815) (by norm_num)
theorem B303889 : Blo 267823 303889 := bbase (se 2 (by rfl) ⟨113958, by rfl⟩ : syracuseStep 303889 = 227917) (by norm_num)
theorem B402197 : Blo 267823 402197 := bbase (se 6 (by rfl) ⟨9426, by rfl⟩ : syracuseStep 402197 = 18853) (by norm_num)
theorem B402221 : Blo 267823 402221 := bbase (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) (by norm_num)
theorem B303925 : Blo 267823 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B402245 : Blo 267823 402245 := bbase (se 4 (by rfl) ⟨37710, by rfl⟩ : syracuseStep 402245 = 75421) (by norm_num)
theorem B303961 : Blo 267823 303961 := bbase (se 2 (by rfl) ⟨113985, by rfl⟩ : syracuseStep 303961 = 227971) (by norm_num)
theorem B402269 : Blo 267823 402269 := bbase (se 3 (by rfl) ⟨75425, by rfl⟩ : syracuseStep 402269 = 150851) (by norm_num)
theorem B402293 : Blo 267823 402293 := bbase (se 5 (by rfl) ⟨18857, by rfl⟩ : syracuseStep 402293 = 37715) (by norm_num)
theorem B303997 : Blo 267823 303997 := bbase (se 3 (by rfl) ⟨56999, by rfl⟩ : syracuseStep 303997 = 113999) (by norm_num)
theorem B402317 : Blo 267823 402317 := bbase (se 3 (by rfl) ⟨75434, by rfl⟩ : syracuseStep 402317 = 150869) (by norm_num)
theorem B304033 : Blo 267823 304033 := bbase (se 2 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 304033 = 228025) (by norm_num)
theorem B402341 : Blo 267823 402341 := bbase (se 4 (by rfl) ⟨37719, by rfl⟩ : syracuseStep 402341 = 75439) (by norm_num)
theorem B402365 : Blo 267823 402365 := bbase (se 3 (by rfl) ⟨75443, by rfl⟩ : syracuseStep 402365 = 150887) (by norm_num)
theorem B304069 : Blo 267823 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B402389 : Blo 267823 402389 := bbase (se 7 (by rfl) ⟨4715, by rfl⟩ : syracuseStep 402389 = 9431) (by norm_num)
theorem B762853 : Blo 267823 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B304105 : Blo 267823 304105 := bbase (se 2 (by rfl) ⟨114039, by rfl⟩ : syracuseStep 304105 = 228079) (by norm_num)
theorem B402413 : Blo 267823 402413 := bbase (se 3 (by rfl) ⟨75452, by rfl⟩ : syracuseStep 402413 = 150905) (by norm_num)
theorem B402437 : Blo 267823 402437 := bbase (se 4 (by rfl) ⟨37728, by rfl⟩ : syracuseStep 402437 = 75457) (by norm_num)
theorem B304141 : Blo 267823 304141 := bbase (se 3 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 304141 = 114053) (by norm_num)
theorem B402461 : Blo 267823 402461 := bbase (se 3 (by rfl) ⟨75461, by rfl⟩ : syracuseStep 402461 = 150923) (by norm_num)
theorem B304177 : Blo 267823 304177 := bbase (se 2 (by rfl) ⟨114066, by rfl⟩ : syracuseStep 304177 = 228133) (by norm_num)
theorem B402485 : Blo 267823 402485 := bbase (se 5 (by rfl) ⟨18866, by rfl⟩ : syracuseStep 402485 = 37733) (by norm_num)
theorem B402509 : Blo 267823 402509 := bbase (se 3 (by rfl) ⟨75470, by rfl⟩ : syracuseStep 402509 = 150941) (by norm_num)
theorem B304213 : Blo 267823 304213 := bbase (se 8 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 304213 = 3565) (by norm_num)
theorem B402533 : Blo 267823 402533 := bbase (se 4 (by rfl) ⟨37737, by rfl⟩ : syracuseStep 402533 = 75475) (by norm_num)
theorem B304249 : Blo 267823 304249 := bbase (se 2 (by rfl) ⟨114093, by rfl⟩ : syracuseStep 304249 = 228187) (by norm_num)
theorem B402557 : Blo 267823 402557 := bbase (se 3 (by rfl) ⟨75479, by rfl⟩ : syracuseStep 402557 = 150959) (by norm_num)
theorem B763013 : Blo 267823 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B402581 : Blo 267823 402581 := bbase (se 6 (by rfl) ⟨9435, by rfl⟩ : syracuseStep 402581 = 18871) (by norm_num)
theorem B304285 : Blo 267823 304285 := bbase (se 3 (by rfl) ⟨57053, by rfl⟩ : syracuseStep 304285 = 114107) (by norm_num)
theorem B402605 : Blo 267823 402605 := bbase (se 3 (by rfl) ⟨75488, by rfl⟩ : syracuseStep 402605 = 150977) (by norm_num)
theorem B304321 : Blo 267823 304321 := bbase (se 2 (by rfl) ⟨114120, by rfl⟩ : syracuseStep 304321 = 228241) (by norm_num)
theorem B402629 : Blo 267823 402629 := bbase (se 4 (by rfl) ⟨37746, by rfl⟩ : syracuseStep 402629 = 75493) (by norm_num)
theorem B402653 : Blo 267823 402653 := bbase (se 3 (by rfl) ⟨75497, by rfl⟩ : syracuseStep 402653 = 150995) (by norm_num)
theorem B304357 : Blo 267823 304357 := bbase (se 4 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 304357 = 57067) (by norm_num)
theorem B402677 : Blo 267823 402677 := bbase (se 5 (by rfl) ⟨18875, by rfl⟩ : syracuseStep 402677 = 37751) (by norm_num)
theorem B304393 : Blo 267823 304393 := bbase (se 2 (by rfl) ⟨114147, by rfl⟩ : syracuseStep 304393 = 228295) (by norm_num)
theorem B402701 : Blo 267823 402701 := bbase (se 3 (by rfl) ⟨75506, by rfl⟩ : syracuseStep 402701 = 151013) (by norm_num)
theorem B402725 : Blo 267823 402725 := bbase (se 4 (by rfl) ⟨37755, by rfl⟩ : syracuseStep 402725 = 75511) (by norm_num)
theorem B304429 : Blo 267823 304429 := bbase (se 3 (by rfl) ⟨57080, by rfl⟩ : syracuseStep 304429 = 114161) (by norm_num)
theorem B402749 : Blo 267823 402749 := bbase (se 3 (by rfl) ⟨75515, by rfl⟩ : syracuseStep 402749 = 151031) (by norm_num)
theorem B304465 : Blo 267823 304465 := bbase (se 2 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 304465 = 228349) (by norm_num)
theorem B402773 : Blo 267823 402773 := bbase (se 12 (by rfl) ⟨147, by rfl⟩ : syracuseStep 402773 = 295) (by norm_num)
theorem B402797 : Blo 267823 402797 := bbase (se 3 (by rfl) ⟨75524, by rfl⟩ : syracuseStep 402797 = 151049) (by norm_num)
theorem B763253 : Blo 267823 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B304501 : Blo 267823 304501 := bbase (se 5 (by rfl) ⟨14273, by rfl⟩ : syracuseStep 304501 = 28547) (by norm_num)
theorem B402821 : Blo 267823 402821 := bbase (se 4 (by rfl) ⟨37764, by rfl⟩ : syracuseStep 402821 = 75529) (by norm_num)
theorem B304537 : Blo 267823 304537 := bbase (se 2 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 304537 = 228403) (by norm_num)
theorem B402845 : Blo 267823 402845 := bbase (se 3 (by rfl) ⟨75533, by rfl⟩ : syracuseStep 402845 = 151067) (by norm_num)
theorem B402869 : Blo 267823 402869 := bbase (se 5 (by rfl) ⟨18884, by rfl⟩ : syracuseStep 402869 = 37769) (by norm_num)
theorem B304573 : Blo 267823 304573 := bbase (se 3 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 304573 = 114215) (by norm_num)
theorem B402893 : Blo 267823 402893 := bbase (se 3 (by rfl) ⟨75542, by rfl⟩ : syracuseStep 402893 = 151085) (by norm_num)
theorem B304609 : Blo 267823 304609 := bbase (se 2 (by rfl) ⟨114228, by rfl⟩ : syracuseStep 304609 = 228457) (by norm_num)
theorem B402917 : Blo 267823 402917 := bbase (se 4 (by rfl) ⟨37773, by rfl⟩ : syracuseStep 402917 = 75547) (by norm_num)
theorem B402941 : Blo 267823 402941 := bbase (se 3 (by rfl) ⟨75551, by rfl⟩ : syracuseStep 402941 = 151103) (by norm_num)
theorem B304645 : Blo 267823 304645 := bbase (se 4 (by rfl) ⟨28560, by rfl⟩ : syracuseStep 304645 = 57121) (by norm_num)
theorem B402965 : Blo 267823 402965 := bbase (se 6 (by rfl) ⟨9444, by rfl⟩ : syracuseStep 402965 = 18889) (by norm_num)
theorem B304681 : Blo 267823 304681 := bbase (se 2 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 304681 = 228511) (by norm_num)
theorem B402989 : Blo 267823 402989 := bbase (se 3 (by rfl) ⟨75560, by rfl⟩ : syracuseStep 402989 = 151121) (by norm_num)
theorem B763445 : Blo 267823 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B403013 : Blo 267823 403013 := bbase (se 4 (by rfl) ⟨37782, by rfl⟩ : syracuseStep 403013 = 75565) (by norm_num)
theorem B304717 : Blo 267823 304717 := bbase (se 3 (by rfl) ⟨57134, by rfl⟩ : syracuseStep 304717 = 114269) (by norm_num)
theorem B403037 : Blo 267823 403037 := bbase (se 3 (by rfl) ⟨75569, by rfl⟩ : syracuseStep 403037 = 151139) (by norm_num)
theorem B304753 : Blo 267823 304753 := bbase (se 2 (by rfl) ⟨114282, by rfl⟩ : syracuseStep 304753 = 228565) (by norm_num)
theorem B403061 : Blo 267823 403061 := bbase (se 5 (by rfl) ⟨18893, by rfl⟩ : syracuseStep 403061 = 37787) (by norm_num)
theorem B403085 : Blo 267823 403085 := bbase (se 3 (by rfl) ⟨75578, by rfl⟩ : syracuseStep 403085 = 151157) (by norm_num)
theorem B304789 : Blo 267823 304789 := bbase (se 6 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 304789 = 14287) (by norm_num)
theorem B403109 : Blo 267823 403109 := bbase (se 4 (by rfl) ⟨37791, by rfl⟩ : syracuseStep 403109 = 75583) (by norm_num)
theorem B304825 : Blo 267823 304825 := bbase (se 2 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 304825 = 228619) (by norm_num)
theorem B403133 : Blo 267823 403133 := bbase (se 3 (by rfl) ⟨75587, by rfl⟩ : syracuseStep 403133 = 151175) (by norm_num)
theorem B1287893 : Blo 267823 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B403157 : Blo 267823 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B304861 : Blo 267823 304861 := bbase (se 3 (by rfl) ⟨57161, by rfl⟩ : syracuseStep 304861 = 114323) (by norm_num)
theorem B403181 : Blo 267823 403181 := bbase (se 3 (by rfl) ⟨75596, by rfl⟩ : syracuseStep 403181 = 151193) (by norm_num)
theorem B861941 : Blo 267823 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B468725 : Blo 267823 468725 := bbase (se 5 (by rfl) ⟨21971, by rfl⟩ : syracuseStep 468725 = 43943) (by norm_num)
theorem B304897 : Blo 267823 304897 := bbase (se 2 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 304897 = 228673) (by norm_num)
theorem B403205 : Blo 267823 403205 := bbase (se 4 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 403205 = 75601) (by norm_num)
theorem B403229 : Blo 267823 403229 := bbase (se 3 (by rfl) ⟨75605, by rfl⟩ : syracuseStep 403229 = 151211) (by norm_num)
theorem B304933 : Blo 267823 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B403253 : Blo 267823 403253 := bbase (se 5 (by rfl) ⟨18902, by rfl⟩ : syracuseStep 403253 = 37805) (by norm_num)
theorem B304969 : Blo 267823 304969 := bbase (se 2 (by rfl) ⟨114363, by rfl⟩ : syracuseStep 304969 = 228727) (by norm_num)
theorem B403277 : Blo 267823 403277 := bbase (se 3 (by rfl) ⟨75614, by rfl⟩ : syracuseStep 403277 = 151229) (by norm_num)
theorem B2041685 : Blo 267823 2041685 := bbase (se 9 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 2041685 = 11963) (by norm_num)
theorem B403301 : Blo 267823 403301 := bbase (se 4 (by rfl) ⟨37809, by rfl⟩ : syracuseStep 403301 = 75619) (by norm_num)
theorem B305005 : Blo 267823 305005 := bbase (se 3 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 305005 = 114377) (by norm_num)
theorem B403325 : Blo 267823 403325 := bbase (se 3 (by rfl) ⟨75623, by rfl⟩ : syracuseStep 403325 = 151247) (by norm_num)
theorem B272273 : Blo 267823 272273 := bbase (se 2 (by rfl) ⟨102102, by rfl⟩ : syracuseStep 272273 = 204205) (by norm_num)
theorem B305041 : Blo 267823 305041 := bbase (se 2 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 305041 = 228781) (by norm_num)
theorem B403349 : Blo 267823 403349 := bbase (se 6 (by rfl) ⟨9453, by rfl⟩ : syracuseStep 403349 = 18907) (by norm_num)
theorem B403373 : Blo 267823 403373 := bbase (se 3 (by rfl) ⟨75632, by rfl⟩ : syracuseStep 403373 = 151265) (by norm_num)
theorem B305077 : Blo 267823 305077 := bbase (se 5 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 305077 = 28601) (by norm_num)
theorem B403397 : Blo 267823 403397 := bbase (se 4 (by rfl) ⟨37818, by rfl⟩ : syracuseStep 403397 = 75637) (by norm_num)
theorem B305113 : Blo 267823 305113 := bbase (se 2 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 305113 = 228835) (by norm_num)
theorem B403421 : Blo 267823 403421 := bbase (se 3 (by rfl) ⟨75641, by rfl⟩ : syracuseStep 403421 = 151283) (by norm_num)
theorem B403445 : Blo 267823 403445 := bbase (se 5 (by rfl) ⟨18911, by rfl⟩ : syracuseStep 403445 = 37823) (by norm_num)
theorem B305149 : Blo 267823 305149 := bbase (se 3 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 305149 = 114431) (by norm_num)
theorem B1026053 : Blo 267823 1026053 := bbase (se 4 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 1026053 = 192385) (by norm_num)
theorem B403469 : Blo 267823 403469 := bbase (se 3 (by rfl) ⟨75650, by rfl⟩ : syracuseStep 403469 = 151301) (by norm_num)
theorem B305185 : Blo 267823 305185 := bbase (se 2 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 305185 = 228889) (by norm_num)
theorem B403493 : Blo 267823 403493 := bbase (se 4 (by rfl) ⟨37827, by rfl⟩ : syracuseStep 403493 = 75655) (by norm_num)
theorem B403517 : Blo 267823 403517 := bbase (se 3 (by rfl) ⟨75659, by rfl⟩ : syracuseStep 403517 = 151319) (by norm_num)
theorem B305221 : Blo 267823 305221 := bbase (se 4 (by rfl) ⟨28614, by rfl⟩ : syracuseStep 305221 = 57229) (by norm_num)
theorem B403541 : Blo 267823 403541 := bbase (se 8 (by rfl) ⟨2364, by rfl⟩ : syracuseStep 403541 = 4729) (by norm_num)
theorem B305257 : Blo 267823 305257 := bbase (se 2 (by rfl) ⟨114471, by rfl⟩ : syracuseStep 305257 = 228943) (by norm_num)
theorem B403565 : Blo 267823 403565 := bbase (se 3 (by rfl) ⟨75668, by rfl⟩ : syracuseStep 403565 = 151337) (by norm_num)
theorem B403589 : Blo 267823 403589 := bbase (se 4 (by rfl) ⟨37836, by rfl⟩ : syracuseStep 403589 = 75673) (by norm_num)
theorem B305293 : Blo 267823 305293 := bbase (se 3 (by rfl) ⟨57242, by rfl⟩ : syracuseStep 305293 = 114485) (by norm_num)
theorem B403613 : Blo 267823 403613 := bbase (se 3 (by rfl) ⟨75677, by rfl⟩ : syracuseStep 403613 = 151355) (by norm_num)
theorem B469165 : Blo 267823 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B305329 : Blo 267823 305329 := bbase (se 2 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 305329 = 228997) (by norm_num)
theorem B403637 : Blo 267823 403637 := bbase (se 5 (by rfl) ⟨18920, by rfl⟩ : syracuseStep 403637 = 37841) (by norm_num)
theorem B403661 : Blo 267823 403661 := bbase (se 3 (by rfl) ⟨75686, by rfl⟩ : syracuseStep 403661 = 151373) (by norm_num)
theorem B305365 : Blo 267823 305365 := bbase (se 7 (by rfl) ⟨3578, by rfl⟩ : syracuseStep 305365 = 7157) (by norm_num)
theorem B403685 : Blo 267823 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B305401 : Blo 267823 305401 := bbase (se 2 (by rfl) ⟨114525, by rfl⟩ : syracuseStep 305401 = 229051) (by norm_num)
theorem B403709 : Blo 267823 403709 := bbase (se 3 (by rfl) ⟨75695, by rfl⟩ : syracuseStep 403709 = 151391) (by norm_num)
theorem B403733 : Blo 267823 403733 := bbase (se 6 (by rfl) ⟨9462, by rfl⟩ : syracuseStep 403733 = 18925) (by norm_num)
theorem B305437 : Blo 267823 305437 := bbase (se 3 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 305437 = 114539) (by norm_num)
theorem B1026341 : Blo 267823 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B403757 : Blo 267823 403757 := bbase (se 3 (by rfl) ⟨75704, by rfl⟩ : syracuseStep 403757 = 151409) (by norm_num)
theorem B305473 : Blo 267823 305473 := bbase (se 2 (by rfl) ⟨114552, by rfl⟩ : syracuseStep 305473 = 229105) (by norm_num)
theorem B403781 : Blo 267823 403781 := bbase (se 4 (by rfl) ⟨37854, by rfl⟩ : syracuseStep 403781 = 75709) (by norm_num)
theorem B403805 : Blo 267823 403805 := bbase (se 3 (by rfl) ⟨75713, by rfl⟩ : syracuseStep 403805 = 151427) (by norm_num)
theorem B305509 : Blo 267823 305509 := bbase (se 4 (by rfl) ⟨28641, by rfl⟩ : syracuseStep 305509 = 57283) (by norm_num)
theorem B403829 : Blo 267823 403829 := bbase (se 5 (by rfl) ⟨18929, by rfl⟩ : syracuseStep 403829 = 37859) (by norm_num)
theorem B305545 : Blo 267823 305545 := bbase (se 2 (by rfl) ⟨114579, by rfl⟩ : syracuseStep 305545 = 229159) (by norm_num)
theorem B403853 : Blo 267823 403853 := bbase (se 3 (by rfl) ⟨75722, by rfl⟩ : syracuseStep 403853 = 151445) (by norm_num)
theorem B403877 : Blo 267823 403877 := bbase (se 4 (by rfl) ⟨37863, by rfl⟩ : syracuseStep 403877 = 75727) (by norm_num)
theorem B305581 : Blo 267823 305581 := bbase (se 3 (by rfl) ⟨57296, by rfl⟩ : syracuseStep 305581 = 114593) (by norm_num)
theorem B403901 : Blo 267823 403901 := bbase (se 3 (by rfl) ⟨75731, by rfl⟩ : syracuseStep 403901 = 151463) (by norm_num)
theorem B305617 : Blo 267823 305617 := bbase (se 2 (by rfl) ⟨114606, by rfl⟩ : syracuseStep 305617 = 229213) (by norm_num)
theorem B403925 : Blo 267823 403925 := bbase (se 7 (by rfl) ⟨4733, by rfl⟩ : syracuseStep 403925 = 9467) (by norm_num)
theorem B272857 : Blo 267823 272857 := bbase (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) (by norm_num)
theorem B403949 : Blo 267823 403949 := bbase (se 3 (by rfl) ⟨75740, by rfl⟩ : syracuseStep 403949 = 151481) (by norm_num)
theorem B305653 : Blo 267823 305653 := bbase (se 5 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 305653 = 28655) (by norm_num)
theorem B403973 : Blo 267823 403973 := bbase (se 4 (by rfl) ⟨37872, by rfl⟩ : syracuseStep 403973 = 75745) (by norm_num)
theorem B764437 : Blo 267823 764437 := bbase (se 6 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 764437 = 35833) (by norm_num)
theorem B305689 : Blo 267823 305689 := bbase (se 2 (by rfl) ⟨114633, by rfl⟩ : syracuseStep 305689 = 229267) (by norm_num)
theorem B403997 : Blo 267823 403997 := bbase (se 3 (by rfl) ⟨75749, by rfl⟩ : syracuseStep 403997 = 151499) (by norm_num)
theorem B404021 : Blo 267823 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B305725 : Blo 267823 305725 := bbase (se 3 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 305725 = 114647) (by norm_num)
theorem B404045 : Blo 267823 404045 := bbase (se 3 (by rfl) ⟨75758, by rfl⟩ : syracuseStep 404045 = 151517) (by norm_num)
theorem B305761 : Blo 267823 305761 := bbase (se 2 (by rfl) ⟨114660, by rfl⟩ : syracuseStep 305761 = 229321) (by norm_num)
theorem B404069 : Blo 267823 404069 := bbase (se 4 (by rfl) ⟨37881, by rfl⟩ : syracuseStep 404069 = 75763) (by norm_num)
theorem B404093 : Blo 267823 404093 := bbase (se 3 (by rfl) ⟨75767, by rfl⟩ : syracuseStep 404093 = 151535) (by norm_num)
theorem B305797 : Blo 267823 305797 := bbase (se 4 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 305797 = 57337) (by norm_num)
theorem B404117 : Blo 267823 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B404141 : Blo 267823 404141 := bbase (se 3 (by rfl) ⟨75776, by rfl⟩ : syracuseStep 404141 = 151553) (by norm_num)
theorem B1157813 : Blo 267823 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B404165 : Blo 267823 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B404189 : Blo 267823 404189 := bbase (se 3 (by rfl) ⟨75785, by rfl⟩ : syracuseStep 404189 = 151571) (by norm_num)
theorem B404213 : Blo 267823 404213 := bbase (se 5 (by rfl) ⟨18947, by rfl⟩ : syracuseStep 404213 = 37895) (by norm_num)
theorem B404237 : Blo 267823 404237 := bbase (se 3 (by rfl) ⟨75794, by rfl⟩ : syracuseStep 404237 = 151589) (by norm_num)
theorem B404261 : Blo 267823 404261 := bbase (se 4 (by rfl) ⟨37899, by rfl⟩ : syracuseStep 404261 = 75799) (by norm_num)
theorem B404285 : Blo 267823 404285 := bbase (se 3 (by rfl) ⟨75803, by rfl⟩ : syracuseStep 404285 = 151607) (by norm_num)
theorem B2796373 : Blo 267823 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B404309 : Blo 267823 404309 := bbase (se 9 (by rfl) ⟨1184, by rfl⟩ : syracuseStep 404309 = 2369) (by norm_num)
theorem B404333 : Blo 267823 404333 := bbase (se 3 (by rfl) ⟨75812, by rfl⟩ : syracuseStep 404333 = 151625) (by norm_num)
theorem B404357 : Blo 267823 404357 := bbase (se 4 (by rfl) ⟨37908, by rfl⟩ : syracuseStep 404357 = 75817) (by norm_num)
theorem B732053 : Blo 267823 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B404381 : Blo 267823 404381 := bbase (se 3 (by rfl) ⟨75821, by rfl⟩ : syracuseStep 404381 = 151643) (by norm_num)
theorem B404405 : Blo 267823 404405 := bbase (se 5 (by rfl) ⟨18956, by rfl⟩ : syracuseStep 404405 = 37913) (by norm_num)
theorem B404429 : Blo 267823 404429 := bbase (se 3 (by rfl) ⟨75830, by rfl⟩ : syracuseStep 404429 = 151661) (by norm_num)
theorem B404453 : Blo 267823 404453 := bbase (se 4 (by rfl) ⟨37917, by rfl⟩ : syracuseStep 404453 = 75835) (by norm_num)
theorem B404477 : Blo 267823 404477 := bbase (se 3 (by rfl) ⟨75839, by rfl⟩ : syracuseStep 404477 = 151679) (by norm_num)
theorem B1092629 : Blo 267823 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B404501 : Blo 267823 404501 := bbase (se 6 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 404501 = 18961) (by norm_num)
theorem B404525 : Blo 267823 404525 := bbase (se 3 (by rfl) ⟨75848, by rfl⟩ : syracuseStep 404525 = 151697) (by norm_num)
theorem B339005 : Blo 267823 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B404549 : Blo 267823 404549 := bbase (se 4 (by rfl) ⟨37926, by rfl⟩ : syracuseStep 404549 = 75853) (by norm_num)
theorem B404573 : Blo 267823 404573 := bbase (se 3 (by rfl) ⟨75857, by rfl⟩ : syracuseStep 404573 = 151715) (by norm_num)
theorem B339061 : Blo 267823 339061 := bbase (se 5 (by rfl) ⟨15893, by rfl⟩ : syracuseStep 339061 = 31787) (by norm_num)
theorem B404597 : Blo 267823 404597 := bbase (se 5 (by rfl) ⟨18965, by rfl⟩ : syracuseStep 404597 = 37931) (by norm_num)
theorem B404621 : Blo 267823 404621 := bbase (se 3 (by rfl) ⟨75866, by rfl⟩ : syracuseStep 404621 = 151733) (by norm_num)
theorem B404645 : Blo 267823 404645 := bbase (se 4 (by rfl) ⟨37935, by rfl⟩ : syracuseStep 404645 = 75871) (by norm_num)
theorem B404669 : Blo 267823 404669 := bbase (se 3 (by rfl) ⟨75875, by rfl⟩ : syracuseStep 404669 = 151751) (by norm_num)
theorem B339157 : Blo 267823 339157 := bbase (se 7 (by rfl) ⟨3974, by rfl⟩ : syracuseStep 339157 = 7949) (by norm_num)
theorem B404693 : Blo 267823 404693 := bbase (se 7 (by rfl) ⟨4742, by rfl⟩ : syracuseStep 404693 = 9485) (by norm_num)
theorem B404717 : Blo 267823 404717 := bbase (se 3 (by rfl) ⟨75884, by rfl⟩ : syracuseStep 404717 = 151769) (by norm_num)
theorem B404741 : Blo 267823 404741 := bbase (se 4 (by rfl) ⟨37944, by rfl⟩ : syracuseStep 404741 = 75889) (by norm_num)
theorem B404765 : Blo 267823 404765 := bbase (se 3 (by rfl) ⟨75893, by rfl⟩ : syracuseStep 404765 = 151787) (by norm_num)
theorem B404789 : Blo 267823 404789 := bbase (se 5 (by rfl) ⟨18974, by rfl⟩ : syracuseStep 404789 = 37949) (by norm_num)
theorem B404813 : Blo 267823 404813 := bbase (se 3 (by rfl) ⟨75902, by rfl⟩ : syracuseStep 404813 = 151805) (by norm_num)
theorem B5680469 : Blo 267823 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B404837 : Blo 267823 404837 := bbase (se 4 (by rfl) ⟨37953, by rfl⟩ : syracuseStep 404837 = 75907) (by norm_num)
theorem B404861 : Blo 267823 404861 := bbase (se 3 (by rfl) ⟨75911, by rfl⟩ : syracuseStep 404861 = 151823) (by norm_num)
theorem B339329 : Blo 267823 339329 := bbase (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) (by norm_num)
theorem B2174357 : Blo 267823 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B404885 : Blo 267823 404885 := bbase (se 6 (by rfl) ⟨9489, by rfl⟩ : syracuseStep 404885 = 18979) (by norm_num)
theorem B404909 : Blo 267823 404909 := bbase (se 3 (by rfl) ⟨75920, by rfl⟩ : syracuseStep 404909 = 151841) (by norm_num)
theorem B339385 : Blo 267823 339385 := bbase (se 2 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 339385 = 254539) (by norm_num)
theorem B404933 : Blo 267823 404933 := bbase (se 4 (by rfl) ⟨37962, by rfl⟩ : syracuseStep 404933 = 75925) (by norm_num)
theorem B1027525 : Blo 267823 1027525 := bbase (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) (by norm_num)
theorem B404957 : Blo 267823 404957 := bbase (se 3 (by rfl) ⟨75929, by rfl⟩ : syracuseStep 404957 = 151859) (by norm_num)
theorem B404981 : Blo 267823 404981 := bbase (se 5 (by rfl) ⟨18983, by rfl⟩ : syracuseStep 404981 = 37967) (by norm_num)
theorem B405005 : Blo 267823 405005 := bbase (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) (by norm_num)
theorem B339481 : Blo 267823 339481 := bbase (se 2 (by rfl) ⟨127305, by rfl⟩ : syracuseStep 339481 = 254611) (by norm_num)
theorem B405029 : Blo 267823 405029 := bbase (se 4 (by rfl) ⟨37971, by rfl⟩ : syracuseStep 405029 = 75943) (by norm_num)
theorem B863797 : Blo 267823 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B405053 : Blo 267823 405053 := bbase (se 3 (by rfl) ⟨75947, by rfl⟩ : syracuseStep 405053 = 151895) (by norm_num)
theorem B405077 : Blo 267823 405077 := bbase (se 8 (by rfl) ⟨2373, by rfl⟩ : syracuseStep 405077 = 4747) (by norm_num)
theorem B765541 : Blo 267823 765541 := bbase (se 4 (by rfl) ⟨71769, by rfl⟩ : syracuseStep 765541 = 143539) (by norm_num)
theorem B405101 : Blo 267823 405101 := bbase (se 3 (by rfl) ⟨75956, by rfl⟩ : syracuseStep 405101 = 151913) (by norm_num)
theorem B405125 : Blo 267823 405125 := bbase (se 4 (by rfl) ⟨37980, by rfl⟩ : syracuseStep 405125 = 75961) (by norm_num)
theorem B405149 : Blo 267823 405149 := bbase (se 3 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 405149 = 151931) (by norm_num)
theorem B405173 : Blo 267823 405173 := bbase (se 5 (by rfl) ⟨18992, by rfl⟩ : syracuseStep 405173 = 37985) (by norm_num)
theorem B339653 : Blo 267823 339653 := bbase (se 4 (by rfl) ⟨31842, by rfl⟩ : syracuseStep 339653 = 63685) (by norm_num)
theorem B405197 : Blo 267823 405197 := bbase (se 3 (by rfl) ⟨75974, by rfl⟩ : syracuseStep 405197 = 151949) (by norm_num)
theorem B405221 : Blo 267823 405221 := bbase (se 4 (by rfl) ⟨37989, by rfl⟩ : syracuseStep 405221 = 75979) (by norm_num)
theorem B1027829 : Blo 267823 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B339709 : Blo 267823 339709 := bbase (se 3 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 339709 = 127391) (by norm_num)
theorem B405245 : Blo 267823 405245 := bbase (se 3 (by rfl) ⟨75983, by rfl⟩ : syracuseStep 405245 = 151967) (by norm_num)
theorem B405269 : Blo 267823 405269 := bbase (se 6 (by rfl) ⟨9498, by rfl⟩ : syracuseStep 405269 = 18997) (by norm_num)
theorem B438053 : Blo 267823 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B405293 : Blo 267823 405293 := bbase (se 3 (by rfl) ⟨75992, by rfl⟩ : syracuseStep 405293 = 151985) (by norm_num)
theorem B405317 : Blo 267823 405317 := bbase (se 4 (by rfl) ⟨37998, by rfl⟩ : syracuseStep 405317 = 75997) (by norm_num)
theorem B339805 : Blo 267823 339805 := bbase (se 3 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 339805 = 127427) (by norm_num)
theorem B405341 : Blo 267823 405341 := bbase (se 3 (by rfl) ⟨76001, by rfl⟩ : syracuseStep 405341 = 152003) (by norm_num)
theorem B405365 : Blo 267823 405365 := bbase (se 5 (by rfl) ⟨19001, by rfl⟩ : syracuseStep 405365 = 38003) (by norm_num)
theorem B274313 : Blo 267823 274313 := bbase (se 2 (by rfl) ⟨102867, by rfl⟩ : syracuseStep 274313 = 205735) (by norm_num)
theorem B405389 : Blo 267823 405389 := bbase (se 3 (by rfl) ⟨76010, by rfl⟩ : syracuseStep 405389 = 152021) (by norm_num)
theorem B307093 : Blo 267823 307093 := bbase (se 6 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 307093 = 14395) (by norm_num)
theorem B405413 : Blo 267823 405413 := bbase (se 4 (by rfl) ⟨38007, by rfl⟩ : syracuseStep 405413 = 76015) (by norm_num)
theorem B274349 : Blo 267823 274349 := bbase (se 3 (by rfl) ⟨51440, by rfl⟩ : syracuseStep 274349 = 102881) (by norm_num)
theorem B405437 : Blo 267823 405437 := bbase (se 3 (by rfl) ⟨76019, by rfl⟩ : syracuseStep 405437 = 152039) (by norm_num)
theorem B405461 : Blo 267823 405461 := bbase (se 7 (by rfl) ⟨4751, by rfl⟩ : syracuseStep 405461 = 9503) (by norm_num)
theorem B405485 : Blo 267823 405485 := bbase (se 3 (by rfl) ⟨76028, by rfl⟩ : syracuseStep 405485 = 152057) (by norm_num)
theorem B1093621 : Blo 267823 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B405509 : Blo 267823 405509 := bbase (se 4 (by rfl) ⟨38016, by rfl⟩ : syracuseStep 405509 = 76033) (by norm_num)
theorem B339977 : Blo 267823 339977 := bbase (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) (by norm_num)
theorem B405533 : Blo 267823 405533 := bbase (se 3 (by rfl) ⟨76037, by rfl⟩ : syracuseStep 405533 = 152075) (by norm_num)
theorem B405557 : Blo 267823 405557 := bbase (se 5 (by rfl) ⟨19010, by rfl⟩ : syracuseStep 405557 = 38021) (by norm_num)
theorem B340033 : Blo 267823 340033 := bbase (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) (by norm_num)
theorem B405581 : Blo 267823 405581 := bbase (se 3 (by rfl) ⟨76046, by rfl⟩ : syracuseStep 405581 = 152093) (by norm_num)
theorem B405605 : Blo 267823 405605 := bbase (se 4 (by rfl) ⟨38025, by rfl⟩ : syracuseStep 405605 = 76051) (by norm_num)
theorem B405629 : Blo 267823 405629 := bbase (se 3 (by rfl) ⟨76055, by rfl⟩ : syracuseStep 405629 = 152111) (by norm_num)
theorem B405653 : Blo 267823 405653 := bbase (se 6 (by rfl) ⟨9507, by rfl⟩ : syracuseStep 405653 = 19015) (by norm_num)
theorem B340129 : Blo 267823 340129 := bbase (se 2 (by rfl) ⟨127548, by rfl⟩ : syracuseStep 340129 = 255097) (by norm_num)
theorem B405677 : Blo 267823 405677 := bbase (se 3 (by rfl) ⟨76064, by rfl⟩ : syracuseStep 405677 = 152129) (by norm_num)
theorem B405701 : Blo 267823 405701 := bbase (se 4 (by rfl) ⟨38034, by rfl⟩ : syracuseStep 405701 = 76069) (by norm_num)
theorem B405725 : Blo 267823 405725 := bbase (se 3 (by rfl) ⟨76073, by rfl⟩ : syracuseStep 405725 = 152147) (by norm_num)
theorem B405749 : Blo 267823 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B405773 : Blo 267823 405773 := bbase (se 3 (by rfl) ⟨76082, by rfl⟩ : syracuseStep 405773 = 152165) (by norm_num)
theorem B405797 : Blo 267823 405797 := bbase (se 4 (by rfl) ⟨38043, by rfl⟩ : syracuseStep 405797 = 76087) (by norm_num)
theorem B405821 : Blo 267823 405821 := bbase (se 3 (by rfl) ⟨76091, by rfl⟩ : syracuseStep 405821 = 152183) (by norm_num)
theorem B1356101 : Blo 267823 1356101 := bbase (se 4 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 1356101 = 254269) (by norm_num)
theorem B340301 : Blo 267823 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B405845 : Blo 267823 405845 := bbase (se 10 (by rfl) ⟨594, by rfl⟩ : syracuseStep 405845 = 1189) (by norm_num)
theorem B405869 : Blo 267823 405869 := bbase (se 3 (by rfl) ⟨76100, by rfl⟩ : syracuseStep 405869 = 152201) (by norm_num)
theorem B307585 : Blo 267823 307585 := bbase (se 2 (by rfl) ⟨115344, by rfl⟩ : syracuseStep 307585 = 230689) (by norm_num)
theorem B340357 : Blo 267823 340357 := bbase (se 4 (by rfl) ⟨31908, by rfl⟩ : syracuseStep 340357 = 63817) (by norm_num)
theorem B405893 : Blo 267823 405893 := bbase (se 4 (by rfl) ⟨38052, by rfl⟩ : syracuseStep 405893 = 76105) (by norm_num)
theorem B405917 : Blo 267823 405917 := bbase (se 3 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 405917 = 152219) (by norm_num)
theorem B307621 : Blo 267823 307621 := bbase (se 4 (by rfl) ⟨28839, by rfl⟩ : syracuseStep 307621 = 57679) (by norm_num)
theorem B1159589 : Blo 267823 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B405941 : Blo 267823 405941 := bbase (se 5 (by rfl) ⟨19028, by rfl⟩ : syracuseStep 405941 = 38057) (by norm_num)
theorem B405965 : Blo 267823 405965 := bbase (se 3 (by rfl) ⟨76118, by rfl⟩ : syracuseStep 405965 = 152237) (by norm_num)
theorem B340453 : Blo 267823 340453 := bbase (se 4 (by rfl) ⟨31917, by rfl⟩ : syracuseStep 340453 = 63835) (by norm_num)
theorem B405989 : Blo 267823 405989 := bbase (se 4 (by rfl) ⟨38061, by rfl⟩ : syracuseStep 405989 = 76123) (by norm_num)
theorem B602621 : Blo 267823 602621 := bbase (se 3 (by rfl) ⟨112991, by rfl⟩ : syracuseStep 602621 = 225983) (by norm_num)
theorem B406013 : Blo 267823 406013 := bbase (se 3 (by rfl) ⟨76127, by rfl⟩ : syracuseStep 406013 = 152255) (by norm_num)
theorem B406037 : Blo 267823 406037 := bbase (se 6 (by rfl) ⟨9516, by rfl⟩ : syracuseStep 406037 = 19033) (by norm_num)
theorem B406061 : Blo 267823 406061 := bbase (se 3 (by rfl) ⟨76136, by rfl⟩ : syracuseStep 406061 = 152273) (by norm_num)
theorem B602693 : Blo 267823 602693 := bbase (se 4 (by rfl) ⟨56502, by rfl⟩ : syracuseStep 602693 = 113005) (by norm_num)
theorem B406085 : Blo 267823 406085 := bbase (se 4 (by rfl) ⟨38070, by rfl⟩ : syracuseStep 406085 = 76141) (by norm_num)
theorem B406109 : Blo 267823 406109 := bbase (se 3 (by rfl) ⟨76145, by rfl⟩ : syracuseStep 406109 = 152291) (by norm_num)
theorem B406133 : Blo 267823 406133 := bbase (se 5 (by rfl) ⟨19037, by rfl⟩ : syracuseStep 406133 = 38075) (by norm_num)
theorem B602765 : Blo 267823 602765 := bbase (se 3 (by rfl) ⟨113018, by rfl⟩ : syracuseStep 602765 = 226037) (by norm_num)
theorem B406157 : Blo 267823 406157 := bbase (se 3 (by rfl) ⟨76154, by rfl⟩ : syracuseStep 406157 = 152309) (by norm_num)
theorem B340625 : Blo 267823 340625 := bbase (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) (by norm_num)
theorem B1159829 : Blo 267823 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B406181 : Blo 267823 406181 := bbase (se 4 (by rfl) ⟨38079, by rfl⟩ : syracuseStep 406181 = 76159) (by norm_num)
theorem B406205 : Blo 267823 406205 := bbase (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) (by norm_num)
theorem B340681 : Blo 267823 340681 := bbase (se 2 (by rfl) ⟨127755, by rfl⟩ : syracuseStep 340681 = 255511) (by norm_num)
theorem B602837 : Blo 267823 602837 := bbase (se 7 (by rfl) ⟨7064, by rfl⟩ : syracuseStep 602837 = 14129) (by norm_num)
theorem B406229 : Blo 267823 406229 := bbase (se 7 (by rfl) ⟨4760, by rfl⟩ : syracuseStep 406229 = 9521) (by norm_num)
theorem B406253 : Blo 267823 406253 := bbase (se 3 (by rfl) ⟨76172, by rfl⟩ : syracuseStep 406253 = 152345) (by norm_num)
theorem B406277 : Blo 267823 406277 := bbase (se 4 (by rfl) ⟨38088, by rfl⟩ : syracuseStep 406277 = 76177) (by norm_num)
theorem B602909 : Blo 267823 602909 := bbase (se 3 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 602909 = 226091) (by norm_num)
theorem B406301 : Blo 267823 406301 := bbase (se 3 (by rfl) ⟨76181, by rfl⟩ : syracuseStep 406301 = 152363) (by norm_num)
theorem B340777 : Blo 267823 340777 := bbase (se 2 (by rfl) ⟨127791, by rfl⟩ : syracuseStep 340777 = 255583) (by norm_num)
theorem B406325 : Blo 267823 406325 := bbase (se 5 (by rfl) ⟨19046, by rfl⟩ : syracuseStep 406325 = 38093) (by norm_num)
theorem B406349 : Blo 267823 406349 := bbase (se 3 (by rfl) ⟨76190, by rfl⟩ : syracuseStep 406349 = 152381) (by norm_num)
theorem B602981 : Blo 267823 602981 := bbase (se 4 (by rfl) ⟨56529, by rfl⟩ : syracuseStep 602981 = 113059) (by norm_num)
theorem B406373 : Blo 267823 406373 := bbase (se 4 (by rfl) ⟨38097, by rfl⟩ : syracuseStep 406373 = 76195) (by norm_num)
theorem B406397 : Blo 267823 406397 := bbase (se 3 (by rfl) ⟨76199, by rfl⟩ : syracuseStep 406397 = 152399) (by norm_num)
theorem B406421 : Blo 267823 406421 := bbase (se 6 (by rfl) ⟨9525, by rfl⟩ : syracuseStep 406421 = 19051) (by norm_num)
theorem B1160101 : Blo 267823 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B603053 : Blo 267823 603053 := bbase (se 3 (by rfl) ⟨113072, by rfl⟩ : syracuseStep 603053 = 226145) (by norm_num)
theorem B406445 : Blo 267823 406445 := bbase (se 3 (by rfl) ⟨76208, by rfl⟩ : syracuseStep 406445 = 152417) (by norm_num)
theorem B406469 : Blo 267823 406469 := bbase (se 4 (by rfl) ⟨38106, by rfl⟩ : syracuseStep 406469 = 76213) (by norm_num)
theorem B340949 : Blo 267823 340949 := bbase (se 7 (by rfl) ⟨3995, by rfl⟩ : syracuseStep 340949 = 7991) (by norm_num)
theorem B406493 : Blo 267823 406493 := bbase (se 3 (by rfl) ⟨76217, by rfl⟩ : syracuseStep 406493 = 152435) (by norm_num)
theorem B603125 : Blo 267823 603125 := bbase (se 5 (by rfl) ⟨28271, by rfl⟩ : syracuseStep 603125 = 56543) (by norm_num)
theorem B832501 : Blo 267823 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B406517 : Blo 267823 406517 := bbase (se 5 (by rfl) ⟨19055, by rfl⟩ : syracuseStep 406517 = 38111) (by norm_num)
theorem B341005 : Blo 267823 341005 := bbase (se 3 (by rfl) ⟨63938, by rfl⟩ : syracuseStep 341005 = 127877) (by norm_num)
theorem B406541 : Blo 267823 406541 := bbase (se 3 (by rfl) ⟨76226, by rfl⟩ : syracuseStep 406541 = 152453) (by norm_num)
theorem B406565 : Blo 267823 406565 := bbase (se 4 (by rfl) ⟨38115, by rfl⟩ : syracuseStep 406565 = 76231) (by norm_num)
theorem B603197 : Blo 267823 603197 := bbase (se 3 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 603197 = 226199) (by norm_num)
theorem B406589 : Blo 267823 406589 := bbase (se 3 (by rfl) ⟨76235, by rfl⟩ : syracuseStep 406589 = 152471) (by norm_num)
theorem B767045 : Blo 267823 767045 := bbase (se 4 (by rfl) ⟨71910, by rfl⟩ : syracuseStep 767045 = 143821) (by norm_num)
theorem B406613 : Blo 267823 406613 := bbase (se 8 (by rfl) ⟨2382, by rfl⟩ : syracuseStep 406613 = 4765) (by norm_num)
theorem B341101 : Blo 267823 341101 := bbase (se 3 (by rfl) ⟨63956, by rfl⟩ : syracuseStep 341101 = 127913) (by norm_num)
theorem B406637 : Blo 267823 406637 := bbase (se 3 (by rfl) ⟨76244, by rfl⟩ : syracuseStep 406637 = 152489) (by norm_num)
theorem B603269 : Blo 267823 603269 := bbase (se 4 (by rfl) ⟨56556, by rfl⟩ : syracuseStep 603269 = 113113) (by norm_num)
theorem B406661 : Blo 267823 406661 := bbase (se 4 (by rfl) ⟨38124, by rfl⟩ : syracuseStep 406661 = 76249) (by norm_num)
theorem B406685 : Blo 267823 406685 := bbase (se 3 (by rfl) ⟨76253, by rfl⟩ : syracuseStep 406685 = 152507) (by norm_num)
theorem B406709 : Blo 267823 406709 := bbase (se 5 (by rfl) ⟨19064, by rfl⟩ : syracuseStep 406709 = 38129) (by norm_num)
theorem B603341 : Blo 267823 603341 := bbase (se 3 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 603341 = 226253) (by norm_num)
theorem B406733 : Blo 267823 406733 := bbase (se 3 (by rfl) ⟨76262, by rfl⟩ : syracuseStep 406733 = 152525) (by norm_num)
theorem B406757 : Blo 267823 406757 := bbase (se 4 (by rfl) ⟨38133, by rfl⟩ : syracuseStep 406757 = 76267) (by norm_num)
theorem B406781 : Blo 267823 406781 := bbase (se 3 (by rfl) ⟨76271, by rfl⟩ : syracuseStep 406781 = 152543) (by norm_num)
theorem B603413 : Blo 267823 603413 := bbase (se 6 (by rfl) ⟨14142, by rfl⟩ : syracuseStep 603413 = 28285) (by norm_num)
theorem B406805 : Blo 267823 406805 := bbase (se 6 (by rfl) ⟨9534, by rfl⟩ : syracuseStep 406805 = 19069) (by norm_num)
theorem B341273 : Blo 267823 341273 := bbase (se 2 (by rfl) ⟨127977, by rfl⟩ : syracuseStep 341273 = 255955) (by norm_num)
theorem B406829 : Blo 267823 406829 := bbase (se 3 (by rfl) ⟨76280, by rfl⟩ : syracuseStep 406829 = 152561) (by norm_num)
theorem B406853 : Blo 267823 406853 := bbase (se 4 (by rfl) ⟨38142, by rfl⟩ : syracuseStep 406853 = 76285) (by norm_num)
theorem B341329 : Blo 267823 341329 := bbase (se 2 (by rfl) ⟨127998, by rfl⟩ : syracuseStep 341329 = 255997) (by norm_num)
theorem B603485 : Blo 267823 603485 := bbase (se 3 (by rfl) ⟨113153, by rfl⟩ : syracuseStep 603485 = 226307) (by norm_num)
theorem B406877 : Blo 267823 406877 := bbase (se 3 (by rfl) ⟨76289, by rfl⟩ : syracuseStep 406877 = 152579) (by norm_num)
theorem B1291621 : Blo 267823 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B406901 : Blo 267823 406901 := bbase (se 5 (by rfl) ⟨19073, by rfl⟩ : syracuseStep 406901 = 38147) (by norm_num)
theorem B406925 : Blo 267823 406925 := bbase (se 3 (by rfl) ⟨76298, by rfl⟩ : syracuseStep 406925 = 152597) (by norm_num)
theorem B603557 : Blo 267823 603557 := bbase (se 4 (by rfl) ⟨56583, by rfl⟩ : syracuseStep 603557 = 113167) (by norm_num)
theorem B406949 : Blo 267823 406949 := bbase (se 4 (by rfl) ⟨38151, by rfl⟩ : syracuseStep 406949 = 76303) (by norm_num)
theorem B341425 : Blo 267823 341425 := bbase (se 2 (by rfl) ⟨128034, by rfl⟩ : syracuseStep 341425 = 256069) (by norm_num)
theorem B439741 : Blo 267823 439741 := bbase (se 3 (by rfl) ⟨82451, by rfl⟩ : syracuseStep 439741 = 164903) (by norm_num)
theorem B406973 : Blo 267823 406973 := bbase (se 3 (by rfl) ⟨76307, by rfl⟩ : syracuseStep 406973 = 152615) (by norm_num)
theorem B406997 : Blo 267823 406997 := bbase (se 7 (by rfl) ⟨4769, by rfl⟩ : syracuseStep 406997 = 9539) (by norm_num)
theorem B603629 : Blo 267823 603629 := bbase (se 3 (by rfl) ⟨113180, by rfl⟩ : syracuseStep 603629 = 226361) (by norm_num)
theorem B407021 : Blo 267823 407021 := bbase (se 3 (by rfl) ⟨76316, by rfl⟩ : syracuseStep 407021 = 152633) (by norm_num)
theorem B2635253 : Blo 267823 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B407045 : Blo 267823 407045 := bbase (se 4 (by rfl) ⟨38160, by rfl⟩ : syracuseStep 407045 = 76321) (by norm_num)
theorem B407069 : Blo 267823 407069 := bbase (se 3 (by rfl) ⟨76325, by rfl⟩ : syracuseStep 407069 = 152651) (by norm_num)
theorem B603701 : Blo 267823 603701 := bbase (se 5 (by rfl) ⟨28298, by rfl⟩ : syracuseStep 603701 = 56597) (by norm_num)
theorem B407093 : Blo 267823 407093 := bbase (se 5 (by rfl) ⟨19082, by rfl⟩ : syracuseStep 407093 = 38165) (by norm_num)
theorem B407117 : Blo 267823 407117 := bbase (se 3 (by rfl) ⟨76334, by rfl⟩ : syracuseStep 407117 = 152669) (by norm_num)
theorem B1357397 : Blo 267823 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B341597 : Blo 267823 341597 := bbase (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) (by norm_num)
theorem B407141 : Blo 267823 407141 := bbase (se 4 (by rfl) ⟨38169, by rfl⟩ : syracuseStep 407141 = 76339) (by norm_num)
theorem B603773 : Blo 267823 603773 := bbase (se 3 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 603773 = 226415) (by norm_num)
theorem B407165 : Blo 267823 407165 := bbase (se 3 (by rfl) ⟨76343, by rfl⟩ : syracuseStep 407165 = 152687) (by norm_num)
theorem B341653 : Blo 267823 341653 := bbase (se 6 (by rfl) ⟨8007, by rfl⟩ : syracuseStep 341653 = 16015) (by norm_num)
theorem B407189 : Blo 267823 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B407213 : Blo 267823 407213 := bbase (se 3 (by rfl) ⟨76352, by rfl⟩ : syracuseStep 407213 = 152705) (by norm_num)
theorem B308917 : Blo 267823 308917 := bbase (se 5 (by rfl) ⟨14480, by rfl⟩ : syracuseStep 308917 = 28961) (by norm_num)
theorem B603845 : Blo 267823 603845 := bbase (se 4 (by rfl) ⟨56610, by rfl⟩ : syracuseStep 603845 = 113221) (by norm_num)
theorem B407237 : Blo 267823 407237 := bbase (se 4 (by rfl) ⟨38178, by rfl⟩ : syracuseStep 407237 = 76357) (by norm_num)
theorem B407261 : Blo 267823 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B341749 : Blo 267823 341749 := bbase (se 5 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 341749 = 32039) (by norm_num)
theorem B407285 : Blo 267823 407285 := bbase (se 5 (by rfl) ⟨19091, by rfl⟩ : syracuseStep 407285 = 38183) (by norm_num)
theorem B603917 : Blo 267823 603917 := bbase (se 3 (by rfl) ⟨113234, by rfl⟩ : syracuseStep 603917 = 226469) (by norm_num)
theorem B407309 : Blo 267823 407309 := bbase (se 3 (by rfl) ⟨76370, by rfl⟩ : syracuseStep 407309 = 152741) (by norm_num)
theorem B407333 : Blo 267823 407333 := bbase (se 4 (by rfl) ⟨38187, by rfl⟩ : syracuseStep 407333 = 76375) (by norm_num)
theorem B1029941 : Blo 267823 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B407357 : Blo 267823 407357 := bbase (se 3 (by rfl) ⟨76379, by rfl⟩ : syracuseStep 407357 = 152759) (by norm_num)
theorem B603989 : Blo 267823 603989 := bbase (se 9 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 603989 = 3539) (by norm_num)
theorem B407381 : Blo 267823 407381 := bbase (se 9 (by rfl) ⟨1193, by rfl⟩ : syracuseStep 407381 = 2387) (by norm_num)
theorem B407405 : Blo 267823 407405 := bbase (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) (by norm_num)
theorem B2176885 : Blo 267823 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B407429 : Blo 267823 407429 := bbase (se 4 (by rfl) ⟨38196, by rfl⟩ : syracuseStep 407429 = 76393) (by norm_num)
theorem B604061 : Blo 267823 604061 := bbase (se 3 (by rfl) ⟨113261, by rfl⟩ : syracuseStep 604061 = 226523) (by norm_num)
theorem B407453 : Blo 267823 407453 := bbase (se 3 (by rfl) ⟨76397, by rfl⟩ : syracuseStep 407453 = 152795) (by norm_num)
theorem B341921 : Blo 267823 341921 := bbase (se 2 (by rfl) ⟨128220, by rfl⟩ : syracuseStep 341921 = 256441) (by norm_num)
theorem B407477 : Blo 267823 407477 := bbase (se 5 (by rfl) ⟨19100, by rfl⟩ : syracuseStep 407477 = 38201) (by norm_num)
theorem B407501 : Blo 267823 407501 := bbase (se 3 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 407501 = 152813) (by norm_num)
theorem B341977 : Blo 267823 341977 := bbase (se 2 (by rfl) ⟨128241, by rfl⟩ : syracuseStep 341977 = 256483) (by norm_num)
theorem B604133 : Blo 267823 604133 := bbase (se 4 (by rfl) ⟨56637, by rfl⟩ : syracuseStep 604133 = 113275) (by norm_num)
theorem B407525 : Blo 267823 407525 := bbase (se 4 (by rfl) ⟨38205, by rfl⟩ : syracuseStep 407525 = 76411) (by norm_num)
theorem B407549 : Blo 267823 407549 := bbase (se 3 (by rfl) ⟨76415, by rfl⟩ : syracuseStep 407549 = 152831) (by norm_num)
theorem B407573 : Blo 267823 407573 := bbase (se 6 (by rfl) ⟨9552, by rfl⟩ : syracuseStep 407573 = 19105) (by norm_num)
theorem B604205 : Blo 267823 604205 := bbase (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) (by norm_num)
theorem B407597 : Blo 267823 407597 := bbase (se 3 (by rfl) ⟨76424, by rfl⟩ : syracuseStep 407597 = 152849) (by norm_num)
theorem B342073 : Blo 267823 342073 := bbase (se 2 (by rfl) ⟨128277, by rfl⟩ : syracuseStep 342073 = 256555) (by norm_num)
theorem B407621 : Blo 267823 407621 := bbase (se 4 (by rfl) ⟨38214, by rfl⟩ : syracuseStep 407621 = 76429) (by norm_num)
theorem B1030229 : Blo 267823 1030229 := bbase (se 8 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 1030229 = 12073) (by norm_num)
theorem B407645 : Blo 267823 407645 := bbase (se 3 (by rfl) ⟨76433, by rfl⟩ : syracuseStep 407645 = 152867) (by norm_num)
theorem B604277 : Blo 267823 604277 := bbase (se 5 (by rfl) ⟨28325, by rfl⟩ : syracuseStep 604277 = 56651) (by norm_num)
theorem B407669 : Blo 267823 407669 := bbase (se 5 (by rfl) ⟨19109, by rfl⟩ : syracuseStep 407669 = 38219) (by norm_num)
theorem B407693 : Blo 267823 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B407717 : Blo 267823 407717 := bbase (se 4 (by rfl) ⟨38223, by rfl⟩ : syracuseStep 407717 = 76447) (by norm_num)
theorem B604349 : Blo 267823 604349 := bbase (se 3 (by rfl) ⟨113315, by rfl⟩ : syracuseStep 604349 = 226631) (by norm_num)
theorem B342245 : Blo 267823 342245 := bbase (se 4 (by rfl) ⟨32085, by rfl⟩ : syracuseStep 342245 = 64171) (by norm_num)
theorem B604421 : Blo 267823 604421 := bbase (se 4 (by rfl) ⟨56664, by rfl⟩ : syracuseStep 604421 = 113329) (by norm_num)
theorem B309529 : Blo 267823 309529 := bbase (se 2 (by rfl) ⟨116073, by rfl⟩ : syracuseStep 309529 = 232147) (by norm_num)
theorem B342301 : Blo 267823 342301 := bbase (se 3 (by rfl) ⟨64181, by rfl⟩ : syracuseStep 342301 = 128363) (by norm_num)
theorem B604493 : Blo 267823 604493 := bbase (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) (by norm_num)
theorem B1096037 : Blo 267823 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B342397 : Blo 267823 342397 := bbase (se 3 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 342397 = 128399) (by norm_num)
theorem B604565 : Blo 267823 604565 := bbase (se 6 (by rfl) ⟨14169, by rfl⟩ : syracuseStep 604565 = 28339) (by norm_num)
theorem B440749 : Blo 267823 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B604637 : Blo 267823 604637 := bbase (se 3 (by rfl) ⟨113369, by rfl⟩ : syracuseStep 604637 = 226739) (by norm_num)
theorem B604709 : Blo 267823 604709 := bbase (se 4 (by rfl) ⟨56691, by rfl⟩ : syracuseStep 604709 = 113383) (by norm_num)
theorem B1096229 : Blo 267823 1096229 := bbase (se 4 (by rfl) ⟨102771, by rfl⟩ : syracuseStep 1096229 = 205543) (by norm_num)
theorem B342569 : Blo 267823 342569 := bbase (se 2 (by rfl) ⟨128463, by rfl⟩ : syracuseStep 342569 = 256927) (by norm_num)
theorem B342625 : Blo 267823 342625 := bbase (se 2 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 342625 = 256969) (by norm_num)
theorem B604781 : Blo 267823 604781 := bbase (se 3 (by rfl) ⟨113396, by rfl⟩ : syracuseStep 604781 = 226793) (by norm_num)
theorem B768629 : Blo 267823 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B604853 : Blo 267823 604853 := bbase (se 5 (by rfl) ⟨28352, by rfl⟩ : syracuseStep 604853 = 56705) (by norm_num)
theorem B342721 : Blo 267823 342721 := bbase (se 2 (by rfl) ⟨128520, by rfl⟩ : syracuseStep 342721 = 257041) (by norm_num)
theorem B604925 : Blo 267823 604925 := bbase (se 3 (by rfl) ⟨113423, by rfl⟩ : syracuseStep 604925 = 226847) (by norm_num)
theorem B604997 : Blo 267823 604997 := bbase (se 4 (by rfl) ⟨56718, by rfl⟩ : syracuseStep 604997 = 113437) (by norm_num)
theorem B1358693 : Blo 267823 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B342893 : Blo 267823 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B605069 : Blo 267823 605069 := bbase (se 3 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 605069 = 226901) (by norm_num)
theorem B1031077 : Blo 267823 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B342949 : Blo 267823 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B1391525 : Blo 267823 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B277453 : Blo 267823 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B605141 : Blo 267823 605141 := bbase (se 7 (by rfl) ⟨7091, by rfl⟩ : syracuseStep 605141 = 14183) (by norm_num)
theorem B343045 : Blo 267823 343045 := bbase (se 4 (by rfl) ⟨32160, by rfl⟩ : syracuseStep 343045 = 64321) (by norm_num)
theorem B605213 : Blo 267823 605213 := bbase (se 3 (by rfl) ⟨113477, by rfl⟩ : syracuseStep 605213 = 226955) (by norm_num)
theorem B605285 : Blo 267823 605285 := bbase (se 4 (by rfl) ⟨56745, by rfl⟩ : syracuseStep 605285 = 113491) (by norm_num)
theorem B605357 : Blo 267823 605357 := bbase (se 3 (by rfl) ⟨113504, by rfl⟩ : syracuseStep 605357 = 227009) (by norm_num)
theorem B343217 : Blo 267823 343217 := bbase (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) (by norm_num)
theorem B572645 : Blo 267823 572645 := bbase (se 4 (by rfl) ⟨53685, by rfl⟩ : syracuseStep 572645 = 107371) (by norm_num)
theorem B343273 : Blo 267823 343273 := bbase (se 2 (by rfl) ⟨128727, by rfl⟩ : syracuseStep 343273 = 257455) (by norm_num)
theorem B605429 : Blo 267823 605429 := bbase (se 5 (by rfl) ⟨28379, by rfl⟩ : syracuseStep 605429 = 56759) (by norm_num)
theorem B1031413 : Blo 267823 1031413 := bbase (se 5 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 1031413 = 96695) (by norm_num)
theorem B933125 : Blo 267823 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B769301 : Blo 267823 769301 := bbase (se 6 (by rfl) ⟨18030, by rfl⟩ : syracuseStep 769301 = 36061) (by norm_num)
theorem B605501 : Blo 267823 605501 := bbase (se 3 (by rfl) ⟨113531, by rfl⟩ : syracuseStep 605501 = 227063) (by norm_num)
theorem B343369 : Blo 267823 343369 := bbase (se 2 (by rfl) ⟨128763, by rfl⟩ : syracuseStep 343369 = 257527) (by norm_num)
theorem B572789 : Blo 267823 572789 := bbase (se 5 (by rfl) ⟨26849, by rfl⟩ : syracuseStep 572789 = 53699) (by norm_num)
theorem B605573 : Blo 267823 605573 := bbase (se 4 (by rfl) ⟨56772, by rfl⟩ : syracuseStep 605573 = 113545) (by norm_num)
theorem B1719701 : Blo 267823 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B605645 : Blo 267823 605645 := bbase (se 3 (by rfl) ⟨113558, by rfl⟩ : syracuseStep 605645 = 227117) (by norm_num)
theorem B343541 : Blo 267823 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B605717 : Blo 267823 605717 := bbase (se 6 (by rfl) ⟨14196, by rfl⟩ : syracuseStep 605717 = 28393) (by norm_num)
theorem B1031717 : Blo 267823 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B343597 : Blo 267823 343597 := bbase (se 3 (by rfl) ⟨64424, by rfl⟩ : syracuseStep 343597 = 128849) (by norm_num)
theorem B605789 : Blo 267823 605789 := bbase (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) (by norm_num)
theorem B343693 : Blo 267823 343693 := bbase (se 3 (by rfl) ⟨64442, by rfl⟩ : syracuseStep 343693 = 128885) (by norm_num)
theorem B867989 : Blo 267823 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B605861 : Blo 267823 605861 := bbase (se 4 (by rfl) ⟨56799, by rfl⟩ : syracuseStep 605861 = 113599) (by norm_num)
theorem B769733 : Blo 267823 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B573149 : Blo 267823 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B605933 : Blo 267823 605933 := bbase (se 3 (by rfl) ⟨113612, by rfl⟩ : syracuseStep 605933 = 227225) (by norm_num)
theorem B606005 : Blo 267823 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B343865 : Blo 267823 343865 := bbase (se 2 (by rfl) ⟨128949, by rfl⟩ : syracuseStep 343865 = 257899) (by norm_num)
theorem B343921 : Blo 267823 343921 := bbase (se 2 (by rfl) ⟨128970, by rfl⟩ : syracuseStep 343921 = 257941) (by norm_num)
theorem B606077 : Blo 267823 606077 := bbase (se 3 (by rfl) ⟨113639, by rfl⟩ : syracuseStep 606077 = 227279) (by norm_num)
theorem B376741 : Blo 267823 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B606149 : Blo 267823 606149 := bbase (se 4 (by rfl) ⟨56826, by rfl⟩ : syracuseStep 606149 = 113653) (by norm_num)
theorem B344017 : Blo 267823 344017 := bbase (se 2 (by rfl) ⟨129006, by rfl⟩ : syracuseStep 344017 = 258013) (by norm_num)
theorem B966613 : Blo 267823 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B606221 : Blo 267823 606221 := bbase (se 3 (by rfl) ⟨113666, by rfl⟩ : syracuseStep 606221 = 227333) (by norm_num)
theorem B606293 : Blo 267823 606293 := bbase (se 8 (by rfl) ⟨3552, by rfl⟩ : syracuseStep 606293 = 7105) (by norm_num)
theorem B1359989 : Blo 267823 1359989 := bbase (se 5 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 1359989 = 127499) (by norm_num)
theorem B606365 : Blo 267823 606365 := bbase (se 3 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 606365 = 227387) (by norm_num)
theorem B606437 : Blo 267823 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B966917 : Blo 267823 966917 := bbase (se 4 (by rfl) ⟨90648, by rfl⟩ : syracuseStep 966917 = 181297) (by norm_num)
theorem B606509 : Blo 267823 606509 := bbase (se 3 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 606509 = 227441) (by norm_num)
theorem B606581 : Blo 267823 606581 := bbase (se 5 (by rfl) ⟨28433, by rfl⟩ : syracuseStep 606581 = 56867) (by norm_num)
theorem B770485 : Blo 267823 770485 := bbase (se 5 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 770485 = 72233) (by norm_num)
theorem B606653 : Blo 267823 606653 := bbase (se 3 (by rfl) ⟨113747, by rfl⟩ : syracuseStep 606653 = 227495) (by norm_num)
theorem B606725 : Blo 267823 606725 := bbase (se 4 (by rfl) ⟨56880, by rfl⟩ : syracuseStep 606725 = 113761) (by norm_num)
theorem B508493 : Blo 267823 508493 := bbase (se 3 (by rfl) ⟨95342, by rfl⟩ : syracuseStep 508493 = 190685) (by norm_num)
theorem B606797 : Blo 267823 606797 := bbase (se 3 (by rfl) ⟨113774, by rfl⟩ : syracuseStep 606797 = 227549) (by norm_num)
theorem B574037 : Blo 267823 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B606869 : Blo 267823 606869 := bbase (se 6 (by rfl) ⟨14223, by rfl⟩ : syracuseStep 606869 = 28447) (by norm_num)
theorem B606941 : Blo 267823 606941 := bbase (se 3 (by rfl) ⟨113801, by rfl⟩ : syracuseStep 606941 = 227603) (by norm_num)
theorem B607013 : Blo 267823 607013 := bbase (se 4 (by rfl) ⟨56907, by rfl⟩ : syracuseStep 607013 = 113815) (by norm_num)
theorem B574285 : Blo 267823 574285 := bbase (se 3 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 574285 = 215357) (by norm_num)
theorem B508781 : Blo 267823 508781 := bbase (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) (by norm_num)
theorem B607085 : Blo 267823 607085 := bbase (se 3 (by rfl) ⟨113828, by rfl⟩ : syracuseStep 607085 = 227657) (by norm_num)
theorem B1524629 : Blo 267823 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B607157 : Blo 267823 607157 := bbase (se 5 (by rfl) ⟨28460, by rfl⟩ : syracuseStep 607157 = 56921) (by norm_num)
theorem B607229 : Blo 267823 607229 := bbase (se 3 (by rfl) ⟨113855, by rfl⟩ : syracuseStep 607229 = 227711) (by norm_num)
theorem B508933 : Blo 267823 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B967717 : Blo 267823 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B607301 : Blo 267823 607301 := bbase (se 4 (by rfl) ⟨56934, by rfl⟩ : syracuseStep 607301 = 113869) (by norm_num)
theorem B607373 : Blo 267823 607373 := bbase (se 3 (by rfl) ⟨113882, by rfl⟩ : syracuseStep 607373 = 227765) (by norm_num)
theorem B410789 : Blo 267823 410789 := bbase (se 4 (by rfl) ⟨38511, by rfl⟩ : syracuseStep 410789 = 77023) (by norm_num)
theorem B607445 : Blo 267823 607445 := bbase (se 7 (by rfl) ⟨7118, by rfl⟩ : syracuseStep 607445 = 14237) (by norm_num)
theorem B1295621 : Blo 267823 1295621 := bbase (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) (by norm_num)
theorem B607517 : Blo 267823 607517 := bbase (se 3 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 607517 = 227819) (by norm_num)
theorem B509237 : Blo 267823 509237 := bbase (se 5 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 509237 = 47741) (by norm_num)
theorem B574789 : Blo 267823 574789 := bbase (se 4 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 574789 = 107773) (by norm_num)
theorem B607589 : Blo 267823 607589 := bbase (se 4 (by rfl) ⟨56961, by rfl⟩ : syracuseStep 607589 = 113923) (by norm_num)
theorem B1361285 : Blo 267823 1361285 := bbase (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) (by norm_num)
theorem B607661 : Blo 267823 607661 := bbase (se 3 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 607661 = 227873) (by norm_num)
theorem B2049461 : Blo 267823 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B607733 : Blo 267823 607733 := bbase (se 5 (by rfl) ⟨28487, by rfl⟩ : syracuseStep 607733 = 56975) (by norm_num)
theorem B607805 : Blo 267823 607805 := bbase (se 3 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 607805 = 227927) (by norm_num)
theorem B607877 : Blo 267823 607877 := bbase (se 4 (by rfl) ⟨56988, by rfl⟩ : syracuseStep 607877 = 113977) (by norm_num)
theorem B607949 : Blo 267823 607949 := bbase (se 3 (by rfl) ⟨113990, by rfl⟩ : syracuseStep 607949 = 227981) (by norm_num)
theorem B608021 : Blo 267823 608021 := bbase (se 6 (by rfl) ⟨14250, by rfl⟩ : syracuseStep 608021 = 28501) (by norm_num)
theorem B608093 : Blo 267823 608093 := bbase (se 3 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 608093 = 228035) (by norm_num)
theorem B345961 : Blo 267823 345961 := bbase (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) (by norm_num)
theorem B608165 : Blo 267823 608165 := bbase (se 4 (by rfl) ⟨57015, by rfl⟩ : syracuseStep 608165 = 114031) (by norm_num)
theorem B608237 : Blo 267823 608237 := bbase (se 3 (by rfl) ⟨114044, by rfl⟩ : syracuseStep 608237 = 228089) (by norm_num)
theorem B313345 : Blo 267823 313345 := bbase (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) (by norm_num)
theorem B509989 : Blo 267823 509989 := bbase (se 4 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 509989 = 95623) (by norm_num)
theorem B608309 : Blo 267823 608309 := bbase (se 5 (by rfl) ⟨28514, by rfl⟩ : syracuseStep 608309 = 57029) (by norm_num)
theorem B608381 : Blo 267823 608381 := bbase (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) (by norm_num)
theorem B1230997 : Blo 267823 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B510133 : Blo 267823 510133 := bbase (se 5 (by rfl) ⟨23912, by rfl⟩ : syracuseStep 510133 = 47825) (by norm_num)
theorem B575677 : Blo 267823 575677 := bbase (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) (by norm_num)
theorem B608453 : Blo 267823 608453 := bbase (se 4 (by rfl) ⟨57042, by rfl⟩ : syracuseStep 608453 = 114085) (by norm_num)
theorem B542957 : Blo 267823 542957 := bbase (se 3 (by rfl) ⟨101804, by rfl⟩ : syracuseStep 542957 = 203609) (by norm_num)
theorem B346361 : Blo 267823 346361 := bbase (se 2 (by rfl) ⟨129885, by rfl⟩ : syracuseStep 346361 = 259771) (by norm_num)
theorem B608525 : Blo 267823 608525 := bbase (se 3 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 608525 = 228197) (by norm_num)
theorem B510293 : Blo 267823 510293 := bbase (se 10 (by rfl) ⟨747, by rfl⟩ : syracuseStep 510293 = 1495) (by norm_num)
theorem B608597 : Blo 267823 608597 := bbase (se 10 (by rfl) ⟨891, by rfl⟩ : syracuseStep 608597 = 1783) (by norm_num)
theorem B346465 : Blo 267823 346465 := bbase (se 2 (by rfl) ⟨129924, by rfl⟩ : syracuseStep 346465 = 259849) (by norm_num)
theorem B1296773 : Blo 267823 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B608669 : Blo 267823 608669 := bbase (se 3 (by rfl) ⟨114125, by rfl⟩ : syracuseStep 608669 = 228251) (by norm_num)
theorem B870821 : Blo 267823 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B510437 : Blo 267823 510437 := bbase (se 4 (by rfl) ⟨47853, by rfl⟩ : syracuseStep 510437 = 95707) (by norm_num)
theorem B608741 : Blo 267823 608741 := bbase (se 4 (by rfl) ⟨57069, by rfl⟩ : syracuseStep 608741 = 114139) (by norm_num)
theorem B608813 : Blo 267823 608813 := bbase (se 3 (by rfl) ⟨114152, by rfl⟩ : syracuseStep 608813 = 228305) (by norm_num)
theorem B608885 : Blo 267823 608885 := bbase (se 5 (by rfl) ⟨28541, by rfl⟩ : syracuseStep 608885 = 57083) (by norm_num)
theorem B1362581 : Blo 267823 1362581 := bbase (se 6 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 1362581 = 63871) (by norm_num)
theorem B576173 : Blo 267823 576173 := bbase (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) (by norm_num)
theorem B608957 : Blo 267823 608957 := bbase (se 3 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 608957 = 228359) (by norm_num)
theorem B510725 : Blo 267823 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B609029 : Blo 267823 609029 := bbase (se 4 (by rfl) ⟨57096, by rfl⟩ : syracuseStep 609029 = 114193) (by norm_num)
theorem B609101 : Blo 267823 609101 := bbase (se 3 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 609101 = 228413) (by norm_num)
theorem B3263381 : Blo 267823 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B609173 : Blo 267823 609173 := bbase (se 6 (by rfl) ⟨14277, by rfl⟩ : syracuseStep 609173 = 28555) (by norm_num)
theorem B510877 : Blo 267823 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B609245 : Blo 267823 609245 := bbase (se 3 (by rfl) ⟨114233, by rfl⟩ : syracuseStep 609245 = 228467) (by norm_num)
theorem B904229 : Blo 267823 904229 := bbase (se 4 (by rfl) ⟨84771, by rfl⟩ : syracuseStep 904229 = 169543) (by norm_num)
theorem B609317 : Blo 267823 609317 := bbase (se 4 (by rfl) ⟨57123, by rfl⟩ : syracuseStep 609317 = 114247) (by norm_num)
theorem B609389 : Blo 267823 609389 := bbase (se 3 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 609389 = 228521) (by norm_num)
theorem B412789 : Blo 267823 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B1297541 : Blo 267823 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B609461 : Blo 267823 609461 := bbase (se 5 (by rfl) ⟨28568, by rfl⟩ : syracuseStep 609461 = 57137) (by norm_num)
theorem B511181 : Blo 267823 511181 := bbase (se 3 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 511181 = 191693) (by norm_num)
theorem B773333 : Blo 267823 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B609533 : Blo 267823 609533 := bbase (se 3 (by rfl) ⟨114287, by rfl⟩ : syracuseStep 609533 = 228575) (by norm_num)
theorem B609605 : Blo 267823 609605 := bbase (se 4 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 609605 = 114301) (by norm_num)
theorem B544085 : Blo 267823 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B609677 : Blo 267823 609677 := bbase (se 3 (by rfl) ⟨114314, by rfl⟩ : syracuseStep 609677 = 228629) (by norm_num)
theorem B904661 : Blo 267823 904661 := bbase (se 7 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 904661 = 21203) (by norm_num)
theorem B609749 : Blo 267823 609749 := bbase (se 7 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 609749 = 14291) (by norm_num)
theorem B609821 : Blo 267823 609821 := bbase (se 3 (by rfl) ⟨114341, by rfl⟩ : syracuseStep 609821 = 228683) (by norm_num)
theorem B577061 : Blo 267823 577061 := bbase (se 4 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 577061 = 108199) (by norm_num)
theorem B609893 : Blo 267823 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B577181 : Blo 267823 577181 := bbase (se 3 (by rfl) ⟨108221, by rfl⟩ : syracuseStep 577181 = 216443) (by norm_num)
theorem B609965 : Blo 267823 609965 := bbase (se 3 (by rfl) ⟨114368, by rfl⟩ : syracuseStep 609965 = 228737) (by norm_num)
theorem B675533 : Blo 267823 675533 := bbase (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) (by norm_num)
theorem B610037 : Blo 267823 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B610109 : Blo 267823 610109 := bbase (se 3 (by rfl) ⟨114395, by rfl⟩ : syracuseStep 610109 = 228791) (by norm_num)
theorem B905093 : Blo 267823 905093 := bbase (se 4 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 905093 = 169705) (by norm_num)
theorem B610181 : Blo 267823 610181 := bbase (se 4 (by rfl) ⟨57204, by rfl⟩ : syracuseStep 610181 = 114409) (by norm_num)
theorem B1363877 : Blo 267823 1363877 := bbase (se 4 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 1363877 = 255727) (by norm_num)
theorem B511933 : Blo 267823 511933 := bbase (se 3 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 511933 = 191975) (by norm_num)
theorem B610253 : Blo 267823 610253 := bbase (se 3 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 610253 = 228845) (by norm_num)
theorem B610325 : Blo 267823 610325 := bbase (se 6 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 610325 = 28609) (by norm_num)
theorem B512077 : Blo 267823 512077 := bbase (se 3 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 512077 = 192029) (by norm_num)
theorem B1527893 : Blo 267823 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B610397 : Blo 267823 610397 := bbase (se 3 (by rfl) ⟨114449, by rfl⟩ : syracuseStep 610397 = 228899) (by norm_num)
theorem B610469 : Blo 267823 610469 := bbase (se 4 (by rfl) ⟨57231, by rfl⟩ : syracuseStep 610469 = 114463) (by norm_num)
theorem B512237 : Blo 267823 512237 := bbase (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) (by norm_num)
theorem B610541 : Blo 267823 610541 := bbase (se 3 (by rfl) ⟨114476, by rfl⟩ : syracuseStep 610541 = 228953) (by norm_num)
theorem B577813 : Blo 267823 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B905525 : Blo 267823 905525 := bbase (se 5 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 905525 = 84893) (by norm_num)
theorem B610613 : Blo 267823 610613 := bbase (se 5 (by rfl) ⟨28622, by rfl⟩ : syracuseStep 610613 = 57245) (by norm_num)
theorem B512381 : Blo 267823 512381 := bbase (se 3 (by rfl) ⟨96071, by rfl⟩ : syracuseStep 512381 = 192143) (by norm_num)
theorem B610685 : Blo 267823 610685 := bbase (se 3 (by rfl) ⟨114503, by rfl⟩ : syracuseStep 610685 = 229007) (by norm_num)
theorem B610757 : Blo 267823 610757 := bbase (se 4 (by rfl) ⟨57258, by rfl⟩ : syracuseStep 610757 = 114517) (by norm_num)
theorem B610829 : Blo 267823 610829 := bbase (se 3 (by rfl) ⟨114530, by rfl⟩ : syracuseStep 610829 = 229061) (by norm_num)
theorem B610901 : Blo 267823 610901 := bbase (se 8 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 610901 = 7159) (by norm_num)
theorem B1036901 : Blo 267823 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B512669 : Blo 267823 512669 := bbase (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) (by norm_num)
theorem B610973 : Blo 267823 610973 := bbase (se 3 (by rfl) ⟨114557, by rfl⟩ : syracuseStep 610973 = 229115) (by norm_num)
theorem B1233589 : Blo 267823 1233589 := bbase (se 5 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 1233589 = 115649) (by norm_num)
theorem B840389 : Blo 267823 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B905957 : Blo 267823 905957 := bbase (se 4 (by rfl) ⟨84933, by rfl⟩ : syracuseStep 905957 = 169867) (by norm_num)
theorem B611045 : Blo 267823 611045 := bbase (se 4 (by rfl) ⟨57285, by rfl⟩ : syracuseStep 611045 = 114571) (by norm_num)
theorem B381677 : Blo 267823 381677 := bbase (se 3 (by rfl) ⟨71564, by rfl⟩ : syracuseStep 381677 = 143129) (by norm_num)
theorem B611117 : Blo 267823 611117 := bbase (se 3 (by rfl) ⟨114584, by rfl⟩ : syracuseStep 611117 = 229169) (by norm_num)
theorem B512821 : Blo 267823 512821 := bbase (se 5 (by rfl) ⟨24038, by rfl⟩ : syracuseStep 512821 = 48077) (by norm_num)
theorem B611189 : Blo 267823 611189 := bbase (se 5 (by rfl) ⟨28649, by rfl⟩ : syracuseStep 611189 = 57299) (by norm_num)
theorem B611261 : Blo 267823 611261 := bbase (se 3 (by rfl) ⟨114611, by rfl⟩ : syracuseStep 611261 = 229223) (by norm_num)
theorem B1102837 : Blo 267823 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B611333 : Blo 267823 611333 := bbase (se 4 (by rfl) ⟨57312, by rfl⟩ : syracuseStep 611333 = 114625) (by norm_num)
theorem B611365 : Blo 267823 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B611405 : Blo 267823 611405 := bbase (se 3 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 611405 = 229277) (by norm_num)
theorem B513125 : Blo 267823 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B349309 : Blo 267823 349309 := bbase (se 3 (by rfl) ⟨65495, by rfl⟩ : syracuseStep 349309 = 130991) (by norm_num)
theorem B578701 : Blo 267823 578701 := bbase (se 3 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 578701 = 217013) (by norm_num)
theorem B906389 : Blo 267823 906389 := bbase (se 6 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 906389 = 42487) (by norm_num)
theorem B611477 : Blo 267823 611477 := bbase (se 6 (by rfl) ⟨14331, by rfl⟩ : syracuseStep 611477 = 28663) (by norm_num)
theorem B1365173 : Blo 267823 1365173 := bbase (se 5 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 1365173 = 127985) (by norm_num)
theorem B611549 : Blo 267823 611549 := bbase (se 3 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 611549 = 229331) (by norm_num)
theorem B1529077 : Blo 267823 1529077 := bbase (se 5 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 1529077 = 143351) (by norm_num)
theorem B578821 : Blo 267823 578821 := bbase (se 4 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 578821 = 108529) (by norm_num)
theorem B1725749 : Blo 267823 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B382429 : Blo 267823 382429 := bbase (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) (by norm_num)
theorem B579077 : Blo 267823 579077 := bbase (se 4 (by rfl) ⟨54288, by rfl⟩ : syracuseStep 579077 = 108577) (by norm_num)
theorem B906821 : Blo 267823 906821 := bbase (se 4 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 906821 = 170029) (by norm_num)
theorem B644773 : Blo 267823 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B644869 : Blo 267823 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B513877 : Blo 267823 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B1103813 : Blo 267823 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B514021 : Blo 267823 514021 := bbase (se 4 (by rfl) ⟨48189, by rfl⟩ : syracuseStep 514021 = 96379) (by norm_num)
theorem B907253 : Blo 267823 907253 := bbase (se 5 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 907253 = 85055) (by norm_num)
theorem B612461 : Blo 267823 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B514181 : Blo 267823 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B383221 : Blo 267823 383221 := bbase (se 5 (by rfl) ⟨17963, by rfl⟩ : syracuseStep 383221 = 35927) (by norm_num)
theorem B547069 : Blo 267823 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B514325 : Blo 267823 514325 := bbase (se 6 (by rfl) ⟨12054, by rfl⟩ : syracuseStep 514325 = 24109) (by norm_num)
theorem B678253 : Blo 267823 678253 := bbase (se 3 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 678253 = 254345) (by norm_num)
theorem B579965 : Blo 267823 579965 := bbase (se 3 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 579965 = 217487) (by norm_num)
theorem B907685 : Blo 267823 907685 := bbase (se 4 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 907685 = 170191) (by norm_num)
theorem B1366469 : Blo 267823 1366469 := bbase (se 4 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 1366469 = 256213) (by norm_num)
theorem B678365 : Blo 267823 678365 := bbase (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) (by norm_num)
theorem B514613 : Blo 267823 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B383557 : Blo 267823 383557 := bbase (se 4 (by rfl) ⟨35958, by rfl⟩ : syracuseStep 383557 = 71917) (by norm_num)
theorem B580205 : Blo 267823 580205 := bbase (se 3 (by rfl) ⟨108788, by rfl⟩ : syracuseStep 580205 = 217577) (by norm_num)
theorem B678557 : Blo 267823 678557 := bbase (se 3 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 678557 = 254459) (by norm_num)
theorem B514765 : Blo 267823 514765 := bbase (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) (by norm_num)
theorem B383773 : Blo 267823 383773 := bbase (se 3 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 383773 = 143915) (by norm_num)
theorem B645965 : Blo 267823 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B547661 : Blo 267823 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B908117 : Blo 267823 908117 := bbase (se 9 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 908117 = 5321) (by norm_num)
theorem B547741 : Blo 267823 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B678901 : Blo 267823 678901 := bbase (se 5 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 678901 = 63647) (by norm_num)
theorem B515069 : Blo 267823 515069 := bbase (se 3 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 515069 = 193151) (by norm_num)
theorem B679013 : Blo 267823 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B384149 : Blo 267823 384149 := bbase (se 6 (by rfl) ⟨9003, by rfl⟩ : syracuseStep 384149 = 18007) (by norm_num)
theorem B1531061 : Blo 267823 1531061 := bbase (se 5 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 1531061 = 143537) (by norm_num)
theorem B908549 : Blo 267823 908549 := bbase (se 4 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 908549 = 170353) (by norm_num)
theorem B679205 : Blo 267823 679205 := bbase (se 4 (by rfl) ⟨63675, by rfl⟩ : syracuseStep 679205 = 127351) (by norm_num)
theorem B286049 : Blo 267823 286049 := bbase (se 2 (by rfl) ⟨107268, by rfl⟩ : syracuseStep 286049 = 214537) (by norm_num)
theorem B548237 : Blo 267823 548237 := bbase (se 3 (by rfl) ⟨102794, by rfl⟩ : syracuseStep 548237 = 205589) (by norm_num)
theorem B548309 : Blo 267823 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B286301 : Blo 267823 286301 := bbase (se 3 (by rfl) ⟨53681, by rfl⟩ : syracuseStep 286301 = 107363) (by norm_num)
theorem B482917 : Blo 267823 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B679549 : Blo 267823 679549 := bbase (se 3 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 679549 = 254831) (by norm_num)
theorem B908981 : Blo 267823 908981 := bbase (se 5 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 908981 = 85217) (by norm_num)
theorem B1367765 : Blo 267823 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B679661 : Blo 267823 679661 := bbase (se 3 (by rfl) ⟨127436, by rfl⟩ : syracuseStep 679661 = 254873) (by norm_num)
theorem B515821 : Blo 267823 515821 := bbase (se 3 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 515821 = 193433) (by norm_num)
theorem B646925 : Blo 267823 646925 := bbase (se 3 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 646925 = 242597) (by norm_num)
theorem B515965 : Blo 267823 515965 := bbase (se 3 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 515965 = 193487) (by norm_num)
theorem B679853 : Blo 267823 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B483349 : Blo 267823 483349 := bbase (se 6 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 483349 = 22657) (by norm_num)
theorem B286745 : Blo 267823 286745 := bbase (se 2 (by rfl) ⟨107529, by rfl⟩ : syracuseStep 286745 = 215059) (by norm_num)
theorem B548893 : Blo 267823 548893 := bbase (se 3 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 548893 = 205835) (by norm_num)
theorem B909413 : Blo 267823 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B680197 : Blo 267823 680197 := bbase (se 4 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 680197 = 127537) (by norm_num)
theorem B286993 : Blo 267823 286993 := bbase (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) (by norm_num)
theorem B680309 : Blo 267823 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B909845 : Blo 267823 909845 := bbase (se 6 (by rfl) ⟨21324, by rfl⟩ : syracuseStep 909845 = 42649) (by norm_num)
theorem B483869 : Blo 267823 483869 := bbase (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) (by norm_num)
theorem B385573 : Blo 267823 385573 := bbase (se 4 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 385573 = 72295) (by norm_num)
theorem B680501 : Blo 267823 680501 := bbase (se 5 (by rfl) ⟨31898, by rfl⟩ : syracuseStep 680501 = 63797) (by norm_num)
theorem B975493 : Blo 267823 975493 := bbase (se 4 (by rfl) ⟨91452, by rfl⟩ : syracuseStep 975493 = 182905) (by norm_num)
theorem B1237637 : Blo 267823 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B287437 : Blo 267823 287437 := bbase (se 3 (by rfl) ⟨53894, by rfl⟩ : syracuseStep 287437 = 107789) (by norm_num)
theorem B287497 : Blo 267823 287497 := bbase (se 2 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 287497 = 215623) (by norm_num)
theorem B1237781 : Blo 267823 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B484157 : Blo 267823 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B680845 : Blo 267823 680845 := bbase (se 3 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 680845 = 255317) (by norm_num)
theorem B975797 : Blo 267823 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B910277 : Blo 267823 910277 := bbase (se 4 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 910277 = 170677) (by norm_num)
theorem B1369061 : Blo 267823 1369061 := bbase (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) (by norm_num)
theorem B680957 : Blo 267823 680957 := bbase (se 3 (by rfl) ⟨127679, by rfl⟩ : syracuseStep 680957 = 255359) (by norm_num)
theorem B2057237 : Blo 267823 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B287813 : Blo 267823 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B386165 : Blo 267823 386165 := bbase (se 5 (by rfl) ⟨18101, by rfl⟩ : syracuseStep 386165 = 36203) (by norm_num)
theorem B681149 : Blo 267823 681149 := bbase (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) (by norm_num)
theorem B386245 : Blo 267823 386245 := bbase (se 4 (by rfl) ⟨36210, by rfl⟩ : syracuseStep 386245 = 72421) (by norm_num)
theorem B484589 : Blo 267823 484589 := bbase (se 3 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 484589 = 181721) (by norm_num)
theorem B386365 : Blo 267823 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B1402181 : Blo 267823 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1533269 : Blo 267823 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B910709 : Blo 267823 910709 := bbase (se 5 (by rfl) ⟨42689, by rfl⟩ : syracuseStep 910709 = 85379) (by norm_num)
theorem B484733 : Blo 267823 484733 := bbase (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) (by norm_num)
theorem B451973 : Blo 267823 451973 := bbase (se 4 (by rfl) ⟨42372, by rfl⟩ : syracuseStep 451973 = 84745) (by norm_num)
theorem B386461 : Blo 267823 386461 := bbase (se 3 (by rfl) ⟨72461, by rfl⟩ : syracuseStep 386461 = 144923) (by norm_num)
theorem B517565 : Blo 267823 517565 := bbase (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) (by norm_num)
theorem B648685 : Blo 267823 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B288257 : Blo 267823 288257 := bbase (se 2 (by rfl) ⟨108096, by rfl⟩ : syracuseStep 288257 = 216193) (by norm_num)
theorem B452101 : Blo 267823 452101 := bbase (se 4 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 452101 = 84769) (by norm_num)
theorem B681493 : Blo 267823 681493 := bbase (se 6 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 681493 = 31945) (by norm_num)
theorem B288317 : Blo 267823 288317 := bbase (se 3 (by rfl) ⟨54059, by rfl⟩ : syracuseStep 288317 = 108119) (by norm_num)
theorem B452189 : Blo 267823 452189 := bbase (se 3 (by rfl) ⟨84785, by rfl⟩ : syracuseStep 452189 = 169571) (by norm_num)
theorem B681605 : Blo 267823 681605 := bbase (se 4 (by rfl) ⟨63900, by rfl⟩ : syracuseStep 681605 = 127801) (by norm_num)
theorem B288445 : Blo 267823 288445 := bbase (se 3 (by rfl) ⟨54083, by rfl⟩ : syracuseStep 288445 = 108167) (by norm_num)
theorem B550597 : Blo 267823 550597 := bbase (se 4 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 550597 = 103237) (by norm_num)
theorem B648917 : Blo 267823 648917 := bbase (se 7 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 648917 = 15209) (by norm_num)
theorem B452317 : Blo 267823 452317 := bbase (se 3 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 452317 = 169619) (by norm_num)
theorem B911141 : Blo 267823 911141 := bbase (se 4 (by rfl) ⟨85419, by rfl⟩ : syracuseStep 911141 = 170839) (by norm_num)
theorem B452405 : Blo 267823 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B681797 : Blo 267823 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B386957 : Blo 267823 386957 := bbase (se 3 (by rfl) ⟨72554, by rfl⟩ : syracuseStep 386957 = 145109) (by norm_num)
theorem B452533 : Blo 267823 452533 := bbase (se 5 (by rfl) ⟨21212, by rfl⟩ : syracuseStep 452533 = 42425) (by norm_num)
theorem B354233 : Blo 267823 354233 := bbase (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) (by norm_num)
theorem B452621 : Blo 267823 452621 := bbase (se 3 (by rfl) ⟨84866, by rfl⟩ : syracuseStep 452621 = 169733) (by norm_num)
theorem B3467285 : Blo 267823 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B1173541 : Blo 267823 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B4384853 : Blo 267823 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B649309 : Blo 267823 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B288889 : Blo 267823 288889 := bbase (se 2 (by rfl) ⟨108333, by rfl⟩ : syracuseStep 288889 = 216667) (by norm_num)
theorem B452749 : Blo 267823 452749 := bbase (se 3 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 452749 = 169781) (by norm_num)
theorem B682141 : Blo 267823 682141 := bbase (se 3 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 682141 = 255803) (by norm_num)
theorem B911573 : Blo 267823 911573 := bbase (se 7 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 911573 = 21365) (by norm_num)
theorem B452837 : Blo 267823 452837 := bbase (se 4 (by rfl) ⟨42453, by rfl⟩ : syracuseStep 452837 = 84907) (by norm_num)
theorem B289009 : Blo 267823 289009 := bbase (se 2 (by rfl) ⟨108378, by rfl⟩ : syracuseStep 289009 = 216757) (by norm_num)
theorem B1370357 : Blo 267823 1370357 := bbase (se 5 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 1370357 = 128471) (by norm_num)
theorem B682253 : Blo 267823 682253 := bbase (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) (by norm_num)
theorem B452965 : Blo 267823 452965 := bbase (se 4 (by rfl) ⟨42465, by rfl⟩ : syracuseStep 452965 = 84931) (by norm_num)
theorem B321925 : Blo 267823 321925 := bbase (se 4 (by rfl) ⟨30180, by rfl⟩ : syracuseStep 321925 = 60361) (by norm_num)
theorem B485765 : Blo 267823 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B518557 : Blo 267823 518557 := bbase (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) (by norm_num)
theorem B1173941 : Blo 267823 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B453053 : Blo 267823 453053 := bbase (se 3 (by rfl) ⟨84947, by rfl⟩ : syracuseStep 453053 = 169895) (by norm_num)
theorem B682445 : Blo 267823 682445 := bbase (se 3 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 682445 = 255917) (by norm_num)
theorem B289261 : Blo 267823 289261 := bbase (se 3 (by rfl) ⟨54236, by rfl⟩ : syracuseStep 289261 = 108473) (by norm_num)
theorem B289265 : Blo 267823 289265 := bbase (se 2 (by rfl) ⟨108474, by rfl⟩ : syracuseStep 289265 = 216949) (by norm_num)
theorem B453181 : Blo 267823 453181 := bbase (se 3 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 453181 = 169943) (by norm_num)
theorem B912005 : Blo 267823 912005 := bbase (se 4 (by rfl) ⟨85500, by rfl⟩ : syracuseStep 912005 = 171001) (by norm_num)
theorem B453269 : Blo 267823 453269 := bbase (se 6 (by rfl) ⟨10623, by rfl⟩ : syracuseStep 453269 = 21247) (by norm_num)
theorem B453397 : Blo 267823 453397 := bbase (se 6 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 453397 = 21253) (by norm_num)
theorem B682789 : Blo 267823 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B453485 : Blo 267823 453485 := bbase (se 3 (by rfl) ⟨85028, by rfl⟩ : syracuseStep 453485 = 170057) (by norm_num)
theorem B1043333 : Blo 267823 1043333 := bbase (se 4 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 1043333 = 195625) (by norm_num)
theorem B682901 : Blo 267823 682901 := bbase (se 6 (by rfl) ⟨16005, by rfl⟩ : syracuseStep 682901 = 32011) (by norm_num)
theorem B3959765 : Blo 267823 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B453613 : Blo 267823 453613 := bbase (se 3 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 453613 = 170105) (by norm_num)
theorem B289829 : Blo 267823 289829 := bbase (se 4 (by rfl) ⟨27171, by rfl⟩ : syracuseStep 289829 = 54343) (by norm_num)
theorem B912437 : Blo 267823 912437 := bbase (se 5 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 912437 = 85541) (by norm_num)
theorem B453701 : Blo 267823 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B683093 : Blo 267823 683093 := bbase (se 8 (by rfl) ⟨4002, by rfl⟩ : syracuseStep 683093 = 8005) (by norm_num)
theorem B650405 : Blo 267823 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B453829 : Blo 267823 453829 := bbase (se 4 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 453829 = 85093) (by norm_num)
theorem B290017 : Blo 267823 290017 := bbase (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) (by norm_num)
theorem B322805 : Blo 267823 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B1305845 : Blo 267823 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B453917 : Blo 267823 453917 := bbase (se 3 (by rfl) ⟨85109, by rfl⟩ : syracuseStep 453917 = 170219) (by norm_num)
theorem B290129 : Blo 267823 290129 := bbase (se 2 (by rfl) ⟨108798, by rfl⟩ : syracuseStep 290129 = 217597) (by norm_num)
theorem B454045 : Blo 267823 454045 := bbase (se 3 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 454045 = 170267) (by norm_num)
theorem B683437 : Blo 267823 683437 := bbase (se 3 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 683437 = 256289) (by norm_num)
theorem B650693 : Blo 267823 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B912869 : Blo 267823 912869 := bbase (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) (by norm_num)
theorem B454133 : Blo 267823 454133 := bbase (se 5 (by rfl) ⟨21287, by rfl⟩ : syracuseStep 454133 = 42575) (by norm_num)
theorem B1371653 : Blo 267823 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B683549 : Blo 267823 683549 := bbase (se 3 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 683549 = 256331) (by norm_num)
theorem B454261 : Blo 267823 454261 := bbase (se 5 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 454261 = 42587) (by norm_num)
theorem B454349 : Blo 267823 454349 := bbase (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) (by norm_num)
theorem B683741 : Blo 267823 683741 := bbase (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) (by norm_num)
theorem B323309 : Blo 267823 323309 := bbase (se 3 (by rfl) ⟨60620, by rfl⟩ : syracuseStep 323309 = 121241) (by norm_num)
theorem B323357 : Blo 267823 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B454477 : Blo 267823 454477 := bbase (se 3 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 454477 = 170429) (by norm_num)
theorem B913301 : Blo 267823 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B454565 : Blo 267823 454565 := bbase (se 4 (by rfl) ⟨42615, by rfl⟩ : syracuseStep 454565 = 85231) (by norm_num)
theorem B2289653 : Blo 267823 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B323617 : Blo 267823 323617 := bbase (se 2 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 323617 = 242713) (by norm_num)
theorem B454693 : Blo 267823 454693 := bbase (se 4 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 454693 = 85255) (by norm_num)
theorem B684085 : Blo 267823 684085 := bbase (se 5 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 684085 = 64133) (by norm_num)
theorem B454781 : Blo 267823 454781 := bbase (se 3 (by rfl) ⟨85271, by rfl⟩ : syracuseStep 454781 = 170543) (by norm_num)
theorem B684197 : Blo 267823 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B454909 : Blo 267823 454909 := bbase (se 3 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 454909 = 170591) (by norm_num)
theorem B323881 : Blo 267823 323881 := bbase (se 2 (by rfl) ⟨121455, by rfl⟩ : syracuseStep 323881 = 242911) (by norm_num)
theorem B913733 : Blo 267823 913733 := bbase (se 4 (by rfl) ⟨85662, by rfl⟩ : syracuseStep 913733 = 171325) (by norm_num)
theorem B454997 : Blo 267823 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B684389 : Blo 267823 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B324001 : Blo 267823 324001 := bbase (se 2 (by rfl) ⟨121500, by rfl⟩ : syracuseStep 324001 = 243001) (by norm_num)
theorem B455125 : Blo 267823 455125 := bbase (se 7 (by rfl) ⟨5333, by rfl⟩ : syracuseStep 455125 = 10667) (by norm_num)
theorem B618965 : Blo 267823 618965 := bbase (se 7 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 618965 = 14507) (by norm_num)
theorem B455213 : Blo 267823 455213 := bbase (se 3 (by rfl) ⟨85352, by rfl⟩ : syracuseStep 455213 = 170705) (by norm_num)
theorem B291481 : Blo 267823 291481 := bbase (se 2 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 291481 = 218611) (by norm_num)
theorem B455341 : Blo 267823 455341 := bbase (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) (by norm_num)
theorem B684733 : Blo 267823 684733 := bbase (se 3 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 684733 = 256775) (by norm_num)
theorem B914165 : Blo 267823 914165 := bbase (se 5 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 914165 = 85703) (by norm_num)
theorem B455429 : Blo 267823 455429 := bbase (se 4 (by rfl) ⟨42696, by rfl⟩ : syracuseStep 455429 = 85393) (by norm_num)
theorem B1372949 : Blo 267823 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B684845 : Blo 267823 684845 := bbase (se 3 (by rfl) ⟨128408, by rfl⟩ : syracuseStep 684845 = 256817) (by norm_num)
theorem B2749301 : Blo 267823 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B455557 : Blo 267823 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B455645 : Blo 267823 455645 := bbase (se 3 (by rfl) ⟨85433, by rfl⟩ : syracuseStep 455645 = 170867) (by norm_num)
theorem B685037 : Blo 267823 685037 := bbase (se 3 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 685037 = 256889) (by norm_num)
theorem B488533 : Blo 267823 488533 := bbase (se 8 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 488533 = 5725) (by norm_num)
theorem B455773 : Blo 267823 455773 := bbase (se 3 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 455773 = 170915) (by norm_num)
theorem B914597 : Blo 267823 914597 := bbase (se 4 (by rfl) ⟨85743, by rfl⟩ : syracuseStep 914597 = 171487) (by norm_num)
theorem B455861 : Blo 267823 455861 := bbase (se 5 (by rfl) ⟨21368, by rfl⟩ : syracuseStep 455861 = 42737) (by norm_num)
theorem B292069 : Blo 267823 292069 := bbase (se 4 (by rfl) ⟨27381, by rfl⟩ : syracuseStep 292069 = 54763) (by norm_num)
theorem B324857 : Blo 267823 324857 := bbase (se 2 (by rfl) ⟨121821, by rfl⟩ : syracuseStep 324857 = 243643) (by norm_num)
theorem B455989 : Blo 267823 455989 := bbase (se 5 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 455989 = 42749) (by norm_num)
theorem B685381 : Blo 267823 685381 := bbase (se 4 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 685381 = 128509) (by norm_num)
theorem B456077 : Blo 267823 456077 := bbase (se 3 (by rfl) ⟨85514, by rfl⟩ : syracuseStep 456077 = 171029) (by norm_num)
theorem B685493 : Blo 267823 685493 := bbase (se 5 (by rfl) ⟨32132, by rfl⟩ : syracuseStep 685493 = 64265) (by norm_num)
theorem B652789 : Blo 267823 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B456205 : Blo 267823 456205 := bbase (se 3 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 456205 = 171077) (by norm_num)
theorem B915029 : Blo 267823 915029 := bbase (se 8 (by rfl) ⟨5361, by rfl⟩ : syracuseStep 915029 = 10723) (by norm_num)
theorem B456293 : Blo 267823 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B685685 : Blo 267823 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B1144469 : Blo 267823 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B456421 : Blo 267823 456421 := bbase (se 4 (by rfl) ⟨42789, by rfl⟩ : syracuseStep 456421 = 85579) (by norm_num)
theorem B456509 : Blo 267823 456509 := bbase (se 3 (by rfl) ⟨85595, by rfl⟩ : syracuseStep 456509 = 171191) (by norm_num)
theorem B292745 : Blo 267823 292745 := bbase (se 2 (by rfl) ⟨109779, by rfl⟩ : syracuseStep 292745 = 219559) (by norm_num)
theorem B456637 : Blo 267823 456637 := bbase (se 3 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 456637 = 171239) (by norm_num)
theorem B325577 : Blo 267823 325577 := bbase (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) (by norm_num)
theorem B686029 : Blo 267823 686029 := bbase (se 3 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 686029 = 257261) (by norm_num)
theorem B489461 : Blo 267823 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B915461 : Blo 267823 915461 := bbase (se 4 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 915461 = 171649) (by norm_num)
theorem B456725 : Blo 267823 456725 := bbase (se 6 (by rfl) ⟨10704, by rfl⟩ : syracuseStep 456725 = 21409) (by norm_num)
theorem B1374245 : Blo 267823 1374245 := bbase (se 4 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 1374245 = 257671) (by norm_num)
theorem B686141 : Blo 267823 686141 := bbase (se 3 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 686141 = 257303) (by norm_num)
theorem B2193493 : Blo 267823 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B456853 : Blo 267823 456853 := bbase (se 6 (by rfl) ⟨10707, by rfl⟩ : syracuseStep 456853 = 21415) (by norm_num)
theorem B456941 : Blo 267823 456941 := bbase (se 3 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 456941 = 171353) (by norm_num)
theorem B686333 : Blo 267823 686333 := bbase (se 3 (by rfl) ⟨128687, by rfl⟩ : syracuseStep 686333 = 257375) (by norm_num)
theorem B325885 : Blo 267823 325885 := bbase (se 3 (by rfl) ⟨61103, by rfl⟩ : syracuseStep 325885 = 122207) (by norm_num)
theorem B1603925 : Blo 267823 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B325981 : Blo 267823 325981 := bbase (se 3 (by rfl) ⟨61121, by rfl⟩ : syracuseStep 325981 = 122243) (by norm_num)
theorem B457069 : Blo 267823 457069 := bbase (se 3 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 457069 = 171401) (by norm_num)
theorem B915893 : Blo 267823 915893 := bbase (se 5 (by rfl) ⟨42932, by rfl⟩ : syracuseStep 915893 = 85865) (by norm_num)
theorem B457157 : Blo 267823 457157 := bbase (se 4 (by rfl) ⟨42858, by rfl⟩ : syracuseStep 457157 = 85717) (by norm_num)
theorem B326125 : Blo 267823 326125 := bbase (se 3 (by rfl) ⟨61148, by rfl⟩ : syracuseStep 326125 = 122297) (by norm_num)
theorem B4946453 : Blo 267823 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B457285 : Blo 267823 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B686677 : Blo 267823 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B1342037 : Blo 267823 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B457373 : Blo 267823 457373 := bbase (se 3 (by rfl) ⟨85757, by rfl⟩ : syracuseStep 457373 = 171515) (by norm_num)
theorem B686789 : Blo 267823 686789 := bbase (se 4 (by rfl) ⟨64386, by rfl⟩ : syracuseStep 686789 = 128773) (by norm_num)
theorem B1178389 : Blo 267823 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B457501 : Blo 267823 457501 := bbase (se 3 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 457501 = 171563) (by norm_num)
theorem B916325 : Blo 267823 916325 := bbase (se 4 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 916325 = 171811) (by norm_num)
theorem B457589 : Blo 267823 457589 := bbase (se 5 (by rfl) ⟨21449, by rfl⟩ : syracuseStep 457589 = 42899) (by norm_num)
theorem B686981 : Blo 267823 686981 := bbase (se 4 (by rfl) ⟨64404, by rfl⟩ : syracuseStep 686981 = 128809) (by norm_num)
theorem B457717 : Blo 267823 457717 := bbase (se 5 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 457717 = 42911) (by norm_num)
theorem B326669 : Blo 267823 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B457805 : Blo 267823 457805 := bbase (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) (by norm_num)
theorem B457933 : Blo 267823 457933 := bbase (se 3 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 457933 = 171725) (by norm_num)
theorem B687325 : Blo 267823 687325 := bbase (se 3 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 687325 = 257747) (by norm_num)
theorem B916757 : Blo 267823 916757 := bbase (se 6 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 916757 = 42973) (by norm_num)
theorem B458021 : Blo 267823 458021 := bbase (se 4 (by rfl) ⟨42939, by rfl⟩ : syracuseStep 458021 = 85879) (by norm_num)
theorem B1375541 : Blo 267823 1375541 := bbase (se 5 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 1375541 = 128957) (by norm_num)
theorem B687437 : Blo 267823 687437 := bbase (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) (by norm_num)
theorem B458149 : Blo 267823 458149 := bbase (se 4 (by rfl) ⟨42951, by rfl⟩ : syracuseStep 458149 = 85903) (by norm_num)
theorem B458237 : Blo 267823 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B687629 : Blo 267823 687629 := bbase (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) (by norm_num)
theorem B1932821 : Blo 267823 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B458365 : Blo 267823 458365 := bbase (se 3 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 458365 = 171887) (by norm_num)
theorem B917189 : Blo 267823 917189 := bbase (se 4 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 917189 = 171973) (by norm_num)
theorem B458453 : Blo 267823 458453 := bbase (se 7 (by rfl) ⟨5372, by rfl⟩ : syracuseStep 458453 = 10745) (by norm_num)
theorem B1310453 : Blo 267823 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B458581 : Blo 267823 458581 := bbase (se 9 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 458581 = 2687) (by norm_num)
theorem B687973 : Blo 267823 687973 := bbase (se 4 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 687973 = 128995) (by norm_num)
theorem B491437 : Blo 267823 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B458669 : Blo 267823 458669 := bbase (se 3 (by rfl) ⟨86000, by rfl⟩ : syracuseStep 458669 = 172001) (by norm_num)
theorem B327677 : Blo 267823 327677 := bbase (se 3 (by rfl) ⟨61439, by rfl⟩ : syracuseStep 327677 = 122879) (by norm_num)
theorem B458963 : Blo 267823 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B1540741 : Blo 267823 1540741 := bstep (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) B288889
theorem B2458309 : Blo 267823 2458309 := bstep (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) B460933
theorem B394177 : Blo 267823 394177 := bstep (se 2 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 394177 = 295633) B295633
theorem B2295053 : Blo 267823 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B1017137 : Blo 267823 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B886477 : Blo 267823 886477 := bstep (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) B332429
theorem B1017805 : Blo 267823 1017805 := bstep (se 3 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 1017805 = 381677) B381677
theorem B3082211 : Blo 267823 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B1312753 : Blo 267823 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B362723 : Blo 267823 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B4065677 : Blo 267823 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B1542725 : Blo 267823 1542725 := bstep (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) B289261
theorem B1739333 : Blo 267823 1739333 := bstep (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) B326125
theorem B1018595 : Blo 267823 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1641329 : Blo 267823 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B625553 : Blo 267823 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B691267 : Blo 267823 691267 := bstep (se 1 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 691267 = 1036901) B1036901
theorem B461953 : Blo 267823 461953 := bstep (se 2 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 461953 = 346465) B346465
theorem B429233 : Blo 267823 429233 := bstep (se 2 (by rfl) ⟨160962, by rfl⟩ : syracuseStep 429233 = 321925) B321925
theorem B691409 : Blo 267823 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B363809 : Blo 267823 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B1019249 : Blo 267823 1019249 := bstep (se 2 (by rfl) ⟨382218, by rfl⟩ : syracuseStep 1019249 = 764437) B764437
theorem B3673613 : Blo 267823 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1150499 : Blo 267823 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B2297443 : Blo 267823 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B2035853 : Blo 267823 2035853 := bstep (se 3 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 2035853 = 763445) B763445
theorem B14913989 : Blo 267823 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B430643 : Blo 267823 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B1249933 : Blo 267823 1249933 := bstep (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) B468725
theorem B1151729 : Blo 267823 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1020707 : Blo 267823 1020707 := bstep (se 1 (by rfl) ⟨765530, by rfl⟩ : syracuseStep 1020707 = 1531061) B1531061
theorem B1020721 : Blo 267823 1020721 := bstep (se 2 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 1020721 = 765541) B765541
theorem B2921285 : Blo 267823 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B365491 : Blo 267823 365491 := bstep (se 1 (by rfl) ⟨274118, by rfl⟩ : syracuseStep 365491 = 548237) B548237
theorem B431489 : Blo 267823 431489 := bstep (se 2 (by rfl) ⟨161808, by rfl⟩ : syracuseStep 431489 = 323617) B323617
theorem B267827 : Blo 267823 267827 := bstep (se 1 (by rfl) ⟨200870, by rfl⟩ : syracuseStep 267827 = 401741) B401741
theorem B267843 : Blo 267823 267843 := bstep (se 1 (by rfl) ⟨200882, by rfl⟩ : syracuseStep 267843 = 401765) B401765
theorem B267859 : Blo 267823 267859 := bstep (se 1 (by rfl) ⟨200894, by rfl⟩ : syracuseStep 267859 = 401789) B401789
theorem B267875 : Blo 267823 267875 := bstep (se 1 (by rfl) ⟨200906, by rfl⟩ : syracuseStep 267875 = 401813) B401813
theorem B267891 : Blo 267823 267891 := bstep (se 1 (by rfl) ⟨200918, by rfl⟩ : syracuseStep 267891 = 401837) B401837
theorem B267907 : Blo 267823 267907 := bstep (se 1 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 267907 = 401861) B401861
theorem B267923 : Blo 267823 267923 := bstep (se 1 (by rfl) ⟨200942, by rfl⟩ : syracuseStep 267923 = 401885) B401885
theorem B267939 : Blo 267823 267939 := bstep (se 1 (by rfl) ⟨200954, by rfl⟩ : syracuseStep 267939 = 401909) B401909
theorem B267955 : Blo 267823 267955 := bstep (se 1 (by rfl) ⟨200966, by rfl⟩ : syracuseStep 267955 = 401933) B401933
theorem B267971 : Blo 267823 267971 := bstep (se 1 (by rfl) ⟨200978, by rfl⟩ : syracuseStep 267971 = 401957) B401957
theorem B267987 : Blo 267823 267987 := bstep (se 1 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 267987 = 401981) B401981
theorem B268003 : Blo 267823 268003 := bstep (se 1 (by rfl) ⟨201002, by rfl⟩ : syracuseStep 268003 = 402005) B402005
theorem B268019 : Blo 267823 268019 := bstep (se 1 (by rfl) ⟨201014, by rfl⟩ : syracuseStep 268019 = 402029) B402029
theorem B268035 : Blo 267823 268035 := bstep (se 1 (by rfl) ⟨201026, by rfl⟩ : syracuseStep 268035 = 402053) B402053
theorem B268051 : Blo 267823 268051 := bstep (se 1 (by rfl) ⟨201038, by rfl⟩ : syracuseStep 268051 = 402077) B402077
theorem B268067 : Blo 267823 268067 := bstep (se 1 (by rfl) ⟨201050, by rfl⟩ : syracuseStep 268067 = 402101) B402101
theorem B268083 : Blo 267823 268083 := bstep (se 1 (by rfl) ⟨201062, by rfl⟩ : syracuseStep 268083 = 402125) B402125
theorem B268099 : Blo 267823 268099 := bstep (se 1 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 268099 = 402149) B402149
theorem B268115 : Blo 267823 268115 := bstep (se 1 (by rfl) ⟨201086, by rfl⟩ : syracuseStep 268115 = 402173) B402173
theorem B268131 : Blo 267823 268131 := bstep (se 1 (by rfl) ⟨201098, by rfl⟩ : syracuseStep 268131 = 402197) B402197
theorem B268147 : Blo 267823 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B432001 : Blo 267823 432001 := bstep (se 2 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 432001 = 324001) B324001
theorem B268163 : Blo 267823 268163 := bstep (se 1 (by rfl) ⟨201122, by rfl⟩ : syracuseStep 268163 = 402245) B402245
theorem B268179 : Blo 267823 268179 := bstep (se 1 (by rfl) ⟨201134, by rfl⟩ : syracuseStep 268179 = 402269) B402269
theorem B268195 : Blo 267823 268195 := bstep (se 1 (by rfl) ⟨201146, by rfl⟩ : syracuseStep 268195 = 402293) B402293
theorem B268211 : Blo 267823 268211 := bstep (se 1 (by rfl) ⟨201158, by rfl⟩ : syracuseStep 268211 = 402317) B402317
theorem B268227 : Blo 267823 268227 := bstep (se 1 (by rfl) ⟨201170, by rfl⟩ : syracuseStep 268227 = 402341) B402341
theorem B1447885 : Blo 267823 1447885 := bstep (se 3 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 1447885 = 542957) B542957
theorem B268243 : Blo 267823 268243 := bstep (se 1 (by rfl) ⟨201182, by rfl⟩ : syracuseStep 268243 = 402365) B402365
theorem B268259 : Blo 267823 268259 := bstep (se 1 (by rfl) ⟨201194, by rfl⟩ : syracuseStep 268259 = 402389) B402389
theorem B268275 : Blo 267823 268275 := bstep (se 1 (by rfl) ⟨201206, by rfl⟩ : syracuseStep 268275 = 402413) B402413
theorem B268291 : Blo 267823 268291 := bstep (se 1 (by rfl) ⟨201218, by rfl⟩ : syracuseStep 268291 = 402437) B402437
theorem B268307 : Blo 267823 268307 := bstep (se 1 (by rfl) ⟨201230, by rfl⟩ : syracuseStep 268307 = 402461) B402461
theorem B268323 : Blo 267823 268323 := bstep (se 1 (by rfl) ⟨201242, by rfl⟩ : syracuseStep 268323 = 402485) B402485
theorem B268339 : Blo 267823 268339 := bstep (se 1 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 268339 = 402509) B402509
theorem B268355 : Blo 267823 268355 := bstep (se 1 (by rfl) ⟨201266, by rfl⟩ : syracuseStep 268355 = 402533) B402533
theorem B268371 : Blo 267823 268371 := bstep (se 1 (by rfl) ⟨201278, by rfl⟩ : syracuseStep 268371 = 402557) B402557
theorem B268387 : Blo 267823 268387 := bstep (se 1 (by rfl) ⟨201290, by rfl⟩ : syracuseStep 268387 = 402581) B402581
theorem B268403 : Blo 267823 268403 := bstep (se 1 (by rfl) ⟨201302, by rfl⟩ : syracuseStep 268403 = 402605) B402605
theorem B268419 : Blo 267823 268419 := bstep (se 1 (by rfl) ⟨201314, by rfl⟩ : syracuseStep 268419 = 402629) B402629
theorem B268435 : Blo 267823 268435 := bstep (se 1 (by rfl) ⟨201326, by rfl⟩ : syracuseStep 268435 = 402653) B402653
theorem B268451 : Blo 267823 268451 := bstep (se 1 (by rfl) ⟨201338, by rfl⟩ : syracuseStep 268451 = 402677) B402677
theorem B268467 : Blo 267823 268467 := bstep (se 1 (by rfl) ⟨201350, by rfl⟩ : syracuseStep 268467 = 402701) B402701
theorem B268483 : Blo 267823 268483 := bstep (se 1 (by rfl) ⟨201362, by rfl⟩ : syracuseStep 268483 = 402725) B402725
theorem B268499 : Blo 267823 268499 := bstep (se 1 (by rfl) ⟨201374, by rfl⟩ : syracuseStep 268499 = 402749) B402749
theorem B268515 : Blo 267823 268515 := bstep (se 1 (by rfl) ⟨201386, by rfl⟩ : syracuseStep 268515 = 402773) B402773
theorem B1022179 : Blo 267823 1022179 := bstep (se 1 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 1022179 = 1533269) B1533269
theorem B1644785 : Blo 267823 1644785 := bstep (se 2 (by rfl) ⟨616794, by rfl⟩ : syracuseStep 1644785 = 1233589) B1233589
theorem B268531 : Blo 267823 268531 := bstep (se 1 (by rfl) ⟨201398, by rfl⟩ : syracuseStep 268531 = 402797) B402797
theorem B301315 : Blo 267823 301315 := bstep (se 1 (by rfl) ⟨225986, by rfl⟩ : syracuseStep 301315 = 451973) B451973
theorem B268547 : Blo 267823 268547 := bstep (se 1 (by rfl) ⟨201410, by rfl⟩ : syracuseStep 268547 = 402821) B402821
theorem B268563 : Blo 267823 268563 := bstep (se 1 (by rfl) ⟨201422, by rfl⟩ : syracuseStep 268563 = 402845) B402845
theorem B268579 : Blo 267823 268579 := bstep (se 1 (by rfl) ⟨201434, by rfl⟩ : syracuseStep 268579 = 402869) B402869
theorem B268595 : Blo 267823 268595 := bstep (se 1 (by rfl) ⟨201446, by rfl⟩ : syracuseStep 268595 = 402893) B402893
theorem B268611 : Blo 267823 268611 := bstep (se 1 (by rfl) ⟨201458, by rfl⟩ : syracuseStep 268611 = 402917) B402917
theorem B1546573 : Blo 267823 1546573 := bstep (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) B579965
theorem B268627 : Blo 267823 268627 := bstep (se 1 (by rfl) ⟨201470, by rfl⟩ : syracuseStep 268627 = 402941) B402941
theorem B268643 : Blo 267823 268643 := bstep (se 1 (by rfl) ⟨201482, by rfl⟩ : syracuseStep 268643 = 402965) B402965
theorem B268659 : Blo 267823 268659 := bstep (se 1 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 268659 = 402989) B402989
theorem B268675 : Blo 267823 268675 := bstep (se 1 (by rfl) ⟨201506, by rfl⟩ : syracuseStep 268675 = 403013) B403013
theorem B301459 : Blo 267823 301459 := bstep (se 1 (by rfl) ⟨226094, by rfl⟩ : syracuseStep 301459 = 452189) B452189
theorem B268691 : Blo 267823 268691 := bstep (se 1 (by rfl) ⟨201518, by rfl⟩ : syracuseStep 268691 = 403037) B403037
theorem B268707 : Blo 267823 268707 := bstep (se 1 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 268707 = 403061) B403061
theorem B268723 : Blo 267823 268723 := bstep (se 1 (by rfl) ⟨201542, by rfl⟩ : syracuseStep 268723 = 403085) B403085
theorem B268739 : Blo 267823 268739 := bstep (se 1 (by rfl) ⟨201554, by rfl⟩ : syracuseStep 268739 = 403109) B403109
theorem B268755 : Blo 267823 268755 := bstep (se 1 (by rfl) ⟨201566, by rfl⟩ : syracuseStep 268755 = 403133) B403133
theorem B858595 : Blo 267823 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B268771 : Blo 267823 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B432611 : Blo 267823 432611 := bstep (se 1 (by rfl) ⟨324458, by rfl⟩ : syracuseStep 432611 = 648917) B648917
theorem B268787 : Blo 267823 268787 := bstep (se 1 (by rfl) ⟨201590, by rfl⟩ : syracuseStep 268787 = 403181) B403181
theorem B268803 : Blo 267823 268803 := bstep (se 1 (by rfl) ⟨201602, by rfl⟩ : syracuseStep 268803 = 403205) B403205
theorem B268819 : Blo 267823 268819 := bstep (se 1 (by rfl) ⟨201614, by rfl⟩ : syracuseStep 268819 = 403229) B403229
theorem B301603 : Blo 267823 301603 := bstep (se 1 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 301603 = 452405) B452405
theorem B268835 : Blo 267823 268835 := bstep (se 1 (by rfl) ⟨201626, by rfl⟩ : syracuseStep 268835 = 403253) B403253
theorem B268851 : Blo 267823 268851 := bstep (se 1 (by rfl) ⟨201638, by rfl⟩ : syracuseStep 268851 = 403277) B403277
theorem B268867 : Blo 267823 268867 := bstep (se 1 (by rfl) ⟨201650, by rfl⟩ : syracuseStep 268867 = 403301) B403301
theorem B268883 : Blo 267823 268883 := bstep (se 1 (by rfl) ⟨201662, by rfl⟩ : syracuseStep 268883 = 403325) B403325
theorem B268899 : Blo 267823 268899 := bstep (se 1 (by rfl) ⟨201674, by rfl⟩ : syracuseStep 268899 = 403349) B403349
theorem B268915 : Blo 267823 268915 := bstep (se 1 (by rfl) ⟨201686, by rfl⟩ : syracuseStep 268915 = 403373) B403373
theorem B268931 : Blo 267823 268931 := bstep (se 1 (by rfl) ⟨201698, by rfl⟩ : syracuseStep 268931 = 403397) B403397
theorem B268947 : Blo 267823 268947 := bstep (se 1 (by rfl) ⟨201710, by rfl⟩ : syracuseStep 268947 = 403421) B403421
theorem B268963 : Blo 267823 268963 := bstep (se 1 (by rfl) ⟨201722, by rfl⟩ : syracuseStep 268963 = 403445) B403445
theorem B301747 : Blo 267823 301747 := bstep (se 1 (by rfl) ⟨226310, by rfl⟩ : syracuseStep 301747 = 452621) B452621
theorem B268979 : Blo 267823 268979 := bstep (se 1 (by rfl) ⟨201734, by rfl⟩ : syracuseStep 268979 = 403469) B403469
theorem B268995 : Blo 267823 268995 := bstep (se 1 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 268995 = 403493) B403493
theorem B269011 : Blo 267823 269011 := bstep (se 1 (by rfl) ⟨201758, by rfl⟩ : syracuseStep 269011 = 403517) B403517
theorem B269027 : Blo 267823 269027 := bstep (se 1 (by rfl) ⟨201770, by rfl⟩ : syracuseStep 269027 = 403541) B403541
theorem B2923235 : Blo 267823 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B269043 : Blo 267823 269043 := bstep (se 1 (by rfl) ⟨201782, by rfl⟩ : syracuseStep 269043 = 403565) B403565
theorem B269059 : Blo 267823 269059 := bstep (se 1 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 269059 = 403589) B403589
theorem B269075 : Blo 267823 269075 := bstep (se 1 (by rfl) ⟨201806, by rfl⟩ : syracuseStep 269075 = 403613) B403613
theorem B269091 : Blo 267823 269091 := bstep (se 1 (by rfl) ⟨201818, by rfl⟩ : syracuseStep 269091 = 403637) B403637
theorem B269107 : Blo 267823 269107 := bstep (se 1 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 269107 = 403661) B403661
theorem B301891 : Blo 267823 301891 := bstep (se 1 (by rfl) ⟨226418, by rfl⟩ : syracuseStep 301891 = 452837) B452837
theorem B269123 : Blo 267823 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B465745 : Blo 267823 465745 := bstep (se 2 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 465745 = 349309) B349309
theorem B269139 : Blo 267823 269139 := bstep (se 1 (by rfl) ⟨201854, by rfl⟩ : syracuseStep 269139 = 403709) B403709
theorem B269155 : Blo 267823 269155 := bstep (se 1 (by rfl) ⟨201866, by rfl⟩ : syracuseStep 269155 = 403733) B403733
theorem B269171 : Blo 267823 269171 := bstep (se 1 (by rfl) ⟨201878, by rfl⟩ : syracuseStep 269171 = 403757) B403757
theorem B269187 : Blo 267823 269187 := bstep (se 1 (by rfl) ⟨201890, by rfl⟩ : syracuseStep 269187 = 403781) B403781
theorem B269203 : Blo 267823 269203 := bstep (se 1 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 269203 = 403805) B403805
theorem B269219 : Blo 267823 269219 := bstep (se 1 (by rfl) ⟨201914, by rfl⟩ : syracuseStep 269219 = 403829) B403829
theorem B269235 : Blo 267823 269235 := bstep (se 1 (by rfl) ⟨201926, by rfl⟩ : syracuseStep 269235 = 403853) B403853
theorem B269251 : Blo 267823 269251 := bstep (se 1 (by rfl) ⟨201938, by rfl⟩ : syracuseStep 269251 = 403877) B403877
theorem B302035 : Blo 267823 302035 := bstep (se 1 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 302035 = 453053) B453053
theorem B269267 : Blo 267823 269267 := bstep (se 1 (by rfl) ⟨201950, by rfl⟩ : syracuseStep 269267 = 403901) B403901
theorem B269283 : Blo 267823 269283 := bstep (se 1 (by rfl) ⟨201962, by rfl⟩ : syracuseStep 269283 = 403925) B403925
theorem B2038769 : Blo 267823 2038769 := bstep (se 2 (by rfl) ⟨764538, by rfl⟩ : syracuseStep 2038769 = 1529077) B1529077
theorem B269299 : Blo 267823 269299 := bstep (se 1 (by rfl) ⟨201974, by rfl⟩ : syracuseStep 269299 = 403949) B403949
theorem B269315 : Blo 267823 269315 := bstep (se 1 (by rfl) ⟨201986, by rfl⟩ : syracuseStep 269315 = 403973) B403973
theorem B269331 : Blo 267823 269331 := bstep (se 1 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 269331 = 403997) B403997
theorem B269347 : Blo 267823 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B269363 : Blo 267823 269363 := bstep (se 1 (by rfl) ⟨202022, by rfl⟩ : syracuseStep 269363 = 404045) B404045
theorem B269379 : Blo 267823 269379 := bstep (se 1 (by rfl) ⟨202034, by rfl⟩ : syracuseStep 269379 = 404069) B404069
theorem B269395 : Blo 267823 269395 := bstep (se 1 (by rfl) ⟨202046, by rfl⟩ : syracuseStep 269395 = 404093) B404093
theorem B302179 : Blo 267823 302179 := bstep (se 1 (by rfl) ⟨226634, by rfl⟩ : syracuseStep 302179 = 453269) B453269
theorem B269411 : Blo 267823 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B269427 : Blo 267823 269427 := bstep (se 1 (by rfl) ⟨202070, by rfl⟩ : syracuseStep 269427 = 404141) B404141
theorem B269443 : Blo 267823 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B1154189 : Blo 267823 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B269459 : Blo 267823 269459 := bstep (se 1 (by rfl) ⟨202094, by rfl⟩ : syracuseStep 269459 = 404189) B404189
theorem B269475 : Blo 267823 269475 := bstep (se 1 (by rfl) ⟨202106, by rfl⟩ : syracuseStep 269475 = 404213) B404213
theorem B269491 : Blo 267823 269491 := bstep (se 1 (by rfl) ⟨202118, by rfl⟩ : syracuseStep 269491 = 404237) B404237
theorem B269507 : Blo 267823 269507 := bstep (se 1 (by rfl) ⟨202130, by rfl⟩ : syracuseStep 269507 = 404261) B404261
theorem B269523 : Blo 267823 269523 := bstep (se 1 (by rfl) ⟨202142, by rfl⟩ : syracuseStep 269523 = 404285) B404285
theorem B269539 : Blo 267823 269539 := bstep (se 1 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 269539 = 404309) B404309
theorem B302323 : Blo 267823 302323 := bstep (se 1 (by rfl) ⟨226742, by rfl⟩ : syracuseStep 302323 = 453485) B453485
theorem B269555 : Blo 267823 269555 := bstep (se 1 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 269555 = 404333) B404333
theorem B269571 : Blo 267823 269571 := bstep (se 1 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 269571 = 404357) B404357
theorem B695555 : Blo 267823 695555 := bstep (se 1 (by rfl) ⟨521666, by rfl⟩ : syracuseStep 695555 = 1043333) B1043333
theorem B269587 : Blo 267823 269587 := bstep (se 1 (by rfl) ⟨202190, by rfl⟩ : syracuseStep 269587 = 404381) B404381
theorem B269603 : Blo 267823 269603 := bstep (se 1 (by rfl) ⟨202202, by rfl⟩ : syracuseStep 269603 = 404405) B404405
theorem B269619 : Blo 267823 269619 := bstep (se 1 (by rfl) ⟨202214, by rfl⟩ : syracuseStep 269619 = 404429) B404429
theorem B269635 : Blo 267823 269635 := bstep (se 1 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 269635 = 404453) B404453
theorem B269651 : Blo 267823 269651 := bstep (se 1 (by rfl) ⟨202238, by rfl⟩ : syracuseStep 269651 = 404477) B404477
theorem B269667 : Blo 267823 269667 := bstep (se 1 (by rfl) ⟨202250, by rfl⟩ : syracuseStep 269667 = 404501) B404501
theorem B269683 : Blo 267823 269683 := bstep (se 1 (by rfl) ⟨202262, by rfl⟩ : syracuseStep 269683 = 404525) B404525
theorem B302467 : Blo 267823 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B269699 : Blo 267823 269699 := bstep (se 1 (by rfl) ⟨202274, by rfl⟩ : syracuseStep 269699 = 404549) B404549
theorem B269715 : Blo 267823 269715 := bstep (se 1 (by rfl) ⟨202286, by rfl⟩ : syracuseStep 269715 = 404573) B404573
theorem B269731 : Blo 267823 269731 := bstep (se 1 (by rfl) ⟨202298, by rfl⟩ : syracuseStep 269731 = 404597) B404597
theorem B269747 : Blo 267823 269747 := bstep (se 1 (by rfl) ⟨202310, by rfl⟩ : syracuseStep 269747 = 404621) B404621
theorem B269763 : Blo 267823 269763 := bstep (se 1 (by rfl) ⟨202322, by rfl⟩ : syracuseStep 269763 = 404645) B404645
theorem B433603 : Blo 267823 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B269779 : Blo 267823 269779 := bstep (se 1 (by rfl) ⟨202334, by rfl⟩ : syracuseStep 269779 = 404669) B404669
theorem B269795 : Blo 267823 269795 := bstep (se 1 (by rfl) ⟨202346, by rfl⟩ : syracuseStep 269795 = 404693) B404693
theorem B269811 : Blo 267823 269811 := bstep (se 1 (by rfl) ⟨202358, by rfl⟩ : syracuseStep 269811 = 404717) B404717
theorem B269827 : Blo 267823 269827 := bstep (se 1 (by rfl) ⟨202370, by rfl⟩ : syracuseStep 269827 = 404741) B404741
theorem B302611 : Blo 267823 302611 := bstep (se 1 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 302611 = 453917) B453917
theorem B269843 : Blo 267823 269843 := bstep (se 1 (by rfl) ⟨202382, by rfl⟩ : syracuseStep 269843 = 404765) B404765
theorem B269859 : Blo 267823 269859 := bstep (se 1 (by rfl) ⟨202394, by rfl⟩ : syracuseStep 269859 = 404789) B404789
theorem B859697 : Blo 267823 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B269875 : Blo 267823 269875 := bstep (se 1 (by rfl) ⟨202406, by rfl⟩ : syracuseStep 269875 = 404813) B404813
theorem B269891 : Blo 267823 269891 := bstep (se 1 (by rfl) ⟨202418, by rfl⟩ : syracuseStep 269891 = 404837) B404837
theorem B269907 : Blo 267823 269907 := bstep (se 1 (by rfl) ⟨202430, by rfl⟩ : syracuseStep 269907 = 404861) B404861
theorem B1449571 : Blo 267823 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B269923 : Blo 267823 269923 := bstep (se 1 (by rfl) ⟨202442, by rfl⟩ : syracuseStep 269923 = 404885) B404885
theorem B269939 : Blo 267823 269939 := bstep (se 1 (by rfl) ⟨202454, by rfl⟩ : syracuseStep 269939 = 404909) B404909
theorem B269955 : Blo 267823 269955 := bstep (se 1 (by rfl) ⟨202466, by rfl⟩ : syracuseStep 269955 = 404933) B404933
theorem B269971 : Blo 267823 269971 := bstep (se 1 (by rfl) ⟨202478, by rfl⟩ : syracuseStep 269971 = 404957) B404957
theorem B302755 : Blo 267823 302755 := bstep (se 1 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 302755 = 454133) B454133
theorem B269987 : Blo 267823 269987 := bstep (se 1 (by rfl) ⟨202490, by rfl⟩ : syracuseStep 269987 = 404981) B404981
theorem B859825 : Blo 267823 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B270003 : Blo 267823 270003 := bstep (se 1 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 270003 = 405005) B405005
theorem B270019 : Blo 267823 270019 := bstep (se 1 (by rfl) ⟨202514, by rfl⟩ : syracuseStep 270019 = 405029) B405029
theorem B270035 : Blo 267823 270035 := bstep (se 1 (by rfl) ⟨202526, by rfl⟩ : syracuseStep 270035 = 405053) B405053
theorem B270051 : Blo 267823 270051 := bstep (se 1 (by rfl) ⟨202538, by rfl⟩ : syracuseStep 270051 = 405077) B405077
theorem B270067 : Blo 267823 270067 := bstep (se 1 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 270067 = 405101) B405101
theorem B270083 : Blo 267823 270083 := bstep (se 1 (by rfl) ⟨202562, by rfl⟩ : syracuseStep 270083 = 405125) B405125
theorem B270099 : Blo 267823 270099 := bstep (se 1 (by rfl) ⟨202574, by rfl⟩ : syracuseStep 270099 = 405149) B405149
theorem B270115 : Blo 267823 270115 := bstep (se 1 (by rfl) ⟨202586, by rfl⟩ : syracuseStep 270115 = 405173) B405173
theorem B302899 : Blo 267823 302899 := bstep (se 1 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 302899 = 454349) B454349
theorem B270131 : Blo 267823 270131 := bstep (se 1 (by rfl) ⟨202598, by rfl⟩ : syracuseStep 270131 = 405197) B405197
theorem B270147 : Blo 267823 270147 := bstep (se 1 (by rfl) ⟨202610, by rfl⟩ : syracuseStep 270147 = 405221) B405221
theorem B270163 : Blo 267823 270163 := bstep (se 1 (by rfl) ⟨202622, by rfl⟩ : syracuseStep 270163 = 405245) B405245
theorem B270179 : Blo 267823 270179 := bstep (se 1 (by rfl) ⟨202634, by rfl⟩ : syracuseStep 270179 = 405269) B405269
theorem B270195 : Blo 267823 270195 := bstep (se 1 (by rfl) ⟨202646, by rfl⟩ : syracuseStep 270195 = 405293) B405293
theorem B270211 : Blo 267823 270211 := bstep (se 1 (by rfl) ⟨202658, by rfl⟩ : syracuseStep 270211 = 405317) B405317
theorem B270227 : Blo 267823 270227 := bstep (se 1 (by rfl) ⟨202670, by rfl⟩ : syracuseStep 270227 = 405341) B405341
theorem B270243 : Blo 267823 270243 := bstep (se 1 (by rfl) ⟨202682, by rfl⟩ : syracuseStep 270243 = 405365) B405365
theorem B270259 : Blo 267823 270259 := bstep (se 1 (by rfl) ⟨202694, by rfl⟩ : syracuseStep 270259 = 405389) B405389
theorem B303043 : Blo 267823 303043 := bstep (se 1 (by rfl) ⟨227282, by rfl⟩ : syracuseStep 303043 = 454565) B454565
theorem B270275 : Blo 267823 270275 := bstep (se 1 (by rfl) ⟨202706, by rfl⟩ : syracuseStep 270275 = 405413) B405413
theorem B270291 : Blo 267823 270291 := bstep (se 1 (by rfl) ⟨202718, by rfl⟩ : syracuseStep 270291 = 405437) B405437
theorem B270307 : Blo 267823 270307 := bstep (se 1 (by rfl) ⟨202730, by rfl⟩ : syracuseStep 270307 = 405461) B405461
theorem B270323 : Blo 267823 270323 := bstep (se 1 (by rfl) ⟨202742, by rfl⟩ : syracuseStep 270323 = 405485) B405485
theorem B270339 : Blo 267823 270339 := bstep (se 1 (by rfl) ⟨202754, by rfl⟩ : syracuseStep 270339 = 405509) B405509
theorem B270355 : Blo 267823 270355 := bstep (se 1 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 270355 = 405533) B405533
theorem B270371 : Blo 267823 270371 := bstep (se 1 (by rfl) ⟨202778, by rfl⟩ : syracuseStep 270371 = 405557) B405557
theorem B270387 : Blo 267823 270387 := bstep (se 1 (by rfl) ⟨202790, by rfl⟩ : syracuseStep 270387 = 405581) B405581
theorem B270403 : Blo 267823 270403 := bstep (se 1 (by rfl) ⟨202802, by rfl⟩ : syracuseStep 270403 = 405605) B405605
theorem B303187 : Blo 267823 303187 := bstep (se 1 (by rfl) ⟨227390, by rfl⟩ : syracuseStep 303187 = 454781) B454781
theorem B270419 : Blo 267823 270419 := bstep (se 1 (by rfl) ⟨202814, by rfl⟩ : syracuseStep 270419 = 405629) B405629
theorem B270435 : Blo 267823 270435 := bstep (se 1 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 270435 = 405653) B405653
theorem B2924657 : Blo 267823 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B270451 : Blo 267823 270451 := bstep (se 1 (by rfl) ⟨202838, by rfl⟩ : syracuseStep 270451 = 405677) B405677
theorem B270467 : Blo 267823 270467 := bstep (se 1 (by rfl) ⟨202850, by rfl⟩ : syracuseStep 270467 = 405701) B405701
theorem B270483 : Blo 267823 270483 := bstep (se 1 (by rfl) ⟨202862, by rfl⟩ : syracuseStep 270483 = 405725) B405725
theorem B270499 : Blo 267823 270499 := bstep (se 1 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 270499 = 405749) B405749
theorem B270515 : Blo 267823 270515 := bstep (se 1 (by rfl) ⟨202886, by rfl⟩ : syracuseStep 270515 = 405773) B405773
theorem B270531 : Blo 267823 270531 := bstep (se 1 (by rfl) ⟨202898, by rfl⟩ : syracuseStep 270531 = 405797) B405797
theorem B270547 : Blo 267823 270547 := bstep (se 1 (by rfl) ⟨202910, by rfl⟩ : syracuseStep 270547 = 405821) B405821
theorem B303331 : Blo 267823 303331 := bstep (se 1 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 303331 = 454997) B454997
theorem B270563 : Blo 267823 270563 := bstep (se 1 (by rfl) ⟨202922, by rfl⟩ : syracuseStep 270563 = 405845) B405845
theorem B270579 : Blo 267823 270579 := bstep (se 1 (by rfl) ⟨202934, by rfl⟩ : syracuseStep 270579 = 405869) B405869
theorem B270595 : Blo 267823 270595 := bstep (se 1 (by rfl) ⟨202946, by rfl⟩ : syracuseStep 270595 = 405893) B405893
theorem B270611 : Blo 267823 270611 := bstep (se 1 (by rfl) ⟨202958, by rfl⟩ : syracuseStep 270611 = 405917) B405917
theorem B270627 : Blo 267823 270627 := bstep (se 1 (by rfl) ⟨202970, by rfl⟩ : syracuseStep 270627 = 405941) B405941
theorem B270643 : Blo 267823 270643 := bstep (se 1 (by rfl) ⟨202982, by rfl⟩ : syracuseStep 270643 = 405965) B405965
theorem B3449141 : Blo 267823 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B270659 : Blo 267823 270659 := bstep (se 1 (by rfl) ⟨202994, by rfl⟩ : syracuseStep 270659 = 405989) B405989
theorem B729425 : Blo 267823 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B401747 : Blo 267823 401747 := bstep (se 1 (by rfl) ⟨301310, by rfl⟩ : syracuseStep 401747 = 602621) B602621
theorem B270675 : Blo 267823 270675 := bstep (se 1 (by rfl) ⟨203006, by rfl⟩ : syracuseStep 270675 = 406013) B406013
theorem B434513 : Blo 267823 434513 := bstep (se 2 (by rfl) ⟨162942, by rfl⟩ : syracuseStep 434513 = 325885) B325885
theorem B270691 : Blo 267823 270691 := bstep (se 1 (by rfl) ⟨203018, by rfl⟩ : syracuseStep 270691 = 406037) B406037
theorem B401777 : Blo 267823 401777 := bstep (se 2 (by rfl) ⟨150666, by rfl⟩ : syracuseStep 401777 = 301333) B301333
theorem B303475 : Blo 267823 303475 := bstep (se 1 (by rfl) ⟨227606, by rfl⟩ : syracuseStep 303475 = 455213) B455213
theorem B270707 : Blo 267823 270707 := bstep (se 1 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 270707 = 406061) B406061
theorem B401795 : Blo 267823 401795 := bstep (se 1 (by rfl) ⟨301346, by rfl⟩ : syracuseStep 401795 = 602693) B602693
theorem B270723 : Blo 267823 270723 := bstep (se 1 (by rfl) ⟨203042, by rfl⟩ : syracuseStep 270723 = 406085) B406085
theorem B1024397 : Blo 267823 1024397 := bstep (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) B384149
theorem B270739 : Blo 267823 270739 := bstep (se 1 (by rfl) ⟨203054, by rfl⟩ : syracuseStep 270739 = 406109) B406109
theorem B401825 : Blo 267823 401825 := bstep (se 2 (by rfl) ⟨150684, by rfl⟩ : syracuseStep 401825 = 301369) B301369
theorem B270755 : Blo 267823 270755 := bstep (se 1 (by rfl) ⟨203066, by rfl⟩ : syracuseStep 270755 = 406133) B406133
theorem B401843 : Blo 267823 401843 := bstep (se 1 (by rfl) ⟨301382, by rfl⟩ : syracuseStep 401843 = 602765) B602765
theorem B270771 : Blo 267823 270771 := bstep (se 1 (by rfl) ⟨203078, by rfl⟩ : syracuseStep 270771 = 406157) B406157
theorem B270787 : Blo 267823 270787 := bstep (se 1 (by rfl) ⟨203090, by rfl⟩ : syracuseStep 270787 = 406181) B406181
theorem B401873 : Blo 267823 401873 := bstep (se 2 (by rfl) ⟨150702, by rfl⟩ : syracuseStep 401873 = 301405) B301405
theorem B434641 : Blo 267823 434641 := bstep (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) B325981
theorem B270803 : Blo 267823 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B401891 : Blo 267823 401891 := bstep (se 1 (by rfl) ⟨301418, by rfl⟩ : syracuseStep 401891 = 602837) B602837
theorem B270819 : Blo 267823 270819 := bstep (se 1 (by rfl) ⟨203114, by rfl⟩ : syracuseStep 270819 = 406229) B406229
theorem B270835 : Blo 267823 270835 := bstep (se 1 (by rfl) ⟨203126, by rfl⟩ : syracuseStep 270835 = 406253) B406253
theorem B401921 : Blo 267823 401921 := bstep (se 2 (by rfl) ⟨150720, by rfl⟩ : syracuseStep 401921 = 301441) B301441
theorem B303619 : Blo 267823 303619 := bstep (se 1 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 303619 = 455429) B455429
theorem B270851 : Blo 267823 270851 := bstep (se 1 (by rfl) ⟨203138, by rfl⟩ : syracuseStep 270851 = 406277) B406277
theorem B401939 : Blo 267823 401939 := bstep (se 1 (by rfl) ⟨301454, by rfl⟩ : syracuseStep 401939 = 602909) B602909
theorem B270867 : Blo 267823 270867 := bstep (se 1 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 270867 = 406301) B406301
theorem B270883 : Blo 267823 270883 := bstep (se 1 (by rfl) ⟨203162, by rfl⟩ : syracuseStep 270883 = 406325) B406325
theorem B401969 : Blo 267823 401969 := bstep (se 2 (by rfl) ⟨150738, by rfl⟩ : syracuseStep 401969 = 301477) B301477
theorem B270899 : Blo 267823 270899 := bstep (se 1 (by rfl) ⟨203174, by rfl⟩ : syracuseStep 270899 = 406349) B406349
theorem B401987 : Blo 267823 401987 := bstep (se 1 (by rfl) ⟨301490, by rfl⟩ : syracuseStep 401987 = 602981) B602981
theorem B270915 : Blo 267823 270915 := bstep (se 1 (by rfl) ⟨203186, by rfl⟩ : syracuseStep 270915 = 406373) B406373
theorem B270931 : Blo 267823 270931 := bstep (se 1 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 270931 = 406397) B406397
theorem B402017 : Blo 267823 402017 := bstep (se 2 (by rfl) ⟨150756, by rfl⟩ : syracuseStep 402017 = 301513) B301513
theorem B270947 : Blo 267823 270947 := bstep (se 1 (by rfl) ⟨203210, by rfl⟩ : syracuseStep 270947 = 406421) B406421
theorem B402035 : Blo 267823 402035 := bstep (se 1 (by rfl) ⟨301526, by rfl⟩ : syracuseStep 402035 = 603053) B603053
theorem B270963 : Blo 267823 270963 := bstep (se 1 (by rfl) ⟨203222, by rfl⟩ : syracuseStep 270963 = 406445) B406445
theorem B270979 : Blo 267823 270979 := bstep (se 1 (by rfl) ⟨203234, by rfl⟩ : syracuseStep 270979 = 406469) B406469
theorem B860813 : Blo 267823 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B402065 : Blo 267823 402065 := bstep (se 2 (by rfl) ⟨150774, by rfl⟩ : syracuseStep 402065 = 301549) B301549
theorem B303763 : Blo 267823 303763 := bstep (se 1 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 303763 = 455645) B455645
theorem B270995 : Blo 267823 270995 := bstep (se 1 (by rfl) ⟨203246, by rfl⟩ : syracuseStep 270995 = 406493) B406493
theorem B402083 : Blo 267823 402083 := bstep (se 1 (by rfl) ⟨301562, by rfl⟩ : syracuseStep 402083 = 603125) B603125
theorem B271011 : Blo 267823 271011 := bstep (se 1 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 271011 = 406517) B406517
theorem B271027 : Blo 267823 271027 := bstep (se 1 (by rfl) ⟨203270, by rfl⟩ : syracuseStep 271027 = 406541) B406541
theorem B402113 : Blo 267823 402113 := bstep (se 2 (by rfl) ⟨150792, by rfl⟩ : syracuseStep 402113 = 301585) B301585
theorem B271043 : Blo 267823 271043 := bstep (se 1 (by rfl) ⟨203282, by rfl⟩ : syracuseStep 271043 = 406565) B406565
theorem B402131 : Blo 267823 402131 := bstep (se 1 (by rfl) ⟨301598, by rfl⟩ : syracuseStep 402131 = 603197) B603197
theorem B271059 : Blo 267823 271059 := bstep (se 1 (by rfl) ⟨203294, by rfl⟩ : syracuseStep 271059 = 406589) B406589
theorem B271075 : Blo 267823 271075 := bstep (se 1 (by rfl) ⟨203306, by rfl⟩ : syracuseStep 271075 = 406613) B406613
theorem B402161 : Blo 267823 402161 := bstep (se 2 (by rfl) ⟨150810, by rfl⟩ : syracuseStep 402161 = 301621) B301621
theorem B271091 : Blo 267823 271091 := bstep (se 1 (by rfl) ⟨203318, by rfl⟩ : syracuseStep 271091 = 406637) B406637
theorem B402179 : Blo 267823 402179 := bstep (se 1 (by rfl) ⟨301634, by rfl⟩ : syracuseStep 402179 = 603269) B603269
theorem B271107 : Blo 267823 271107 := bstep (se 1 (by rfl) ⟨203330, by rfl⟩ : syracuseStep 271107 = 406661) B406661
theorem B271123 : Blo 267823 271123 := bstep (se 1 (by rfl) ⟨203342, by rfl⟩ : syracuseStep 271123 = 406685) B406685
theorem B402209 : Blo 267823 402209 := bstep (se 2 (by rfl) ⟨150828, by rfl⟩ : syracuseStep 402209 = 301657) B301657
theorem B303907 : Blo 267823 303907 := bstep (se 1 (by rfl) ⟨227930, by rfl⟩ : syracuseStep 303907 = 455861) B455861
theorem B271139 : Blo 267823 271139 := bstep (se 1 (by rfl) ⟨203354, by rfl⟩ : syracuseStep 271139 = 406709) B406709
theorem B402227 : Blo 267823 402227 := bstep (se 1 (by rfl) ⟨301670, by rfl⟩ : syracuseStep 402227 = 603341) B603341
theorem B271155 : Blo 267823 271155 := bstep (se 1 (by rfl) ⟨203366, by rfl⟩ : syracuseStep 271155 = 406733) B406733
theorem B271171 : Blo 267823 271171 := bstep (se 1 (by rfl) ⟨203378, by rfl⟩ : syracuseStep 271171 = 406757) B406757
theorem B402257 : Blo 267823 402257 := bstep (se 2 (by rfl) ⟨150846, by rfl⟩ : syracuseStep 402257 = 301693) B301693
theorem B271187 : Blo 267823 271187 := bstep (se 1 (by rfl) ⟨203390, by rfl⟩ : syracuseStep 271187 = 406781) B406781
theorem B402275 : Blo 267823 402275 := bstep (se 1 (by rfl) ⟨301706, by rfl⟩ : syracuseStep 402275 = 603413) B603413
theorem B271203 : Blo 267823 271203 := bstep (se 1 (by rfl) ⟨203402, by rfl⟩ : syracuseStep 271203 = 406805) B406805
theorem B271219 : Blo 267823 271219 := bstep (se 1 (by rfl) ⟨203414, by rfl⟩ : syracuseStep 271219 = 406829) B406829
theorem B402305 : Blo 267823 402305 := bstep (se 2 (by rfl) ⟨150864, by rfl⟩ : syracuseStep 402305 = 301729) B301729
theorem B271235 : Blo 267823 271235 := bstep (se 1 (by rfl) ⟨203426, by rfl⟩ : syracuseStep 271235 = 406853) B406853
theorem B402323 : Blo 267823 402323 := bstep (se 1 (by rfl) ⟨301742, by rfl⟩ : syracuseStep 402323 = 603485) B603485
theorem B271251 : Blo 267823 271251 := bstep (se 1 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 271251 = 406877) B406877
theorem B271267 : Blo 267823 271267 := bstep (se 1 (by rfl) ⟨203450, by rfl⟩ : syracuseStep 271267 = 406901) B406901
theorem B762797 : Blo 267823 762797 := bstep (se 3 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 762797 = 286049) B286049
theorem B402353 : Blo 267823 402353 := bstep (se 2 (by rfl) ⟨150882, by rfl⟩ : syracuseStep 402353 = 301765) B301765
theorem B304051 : Blo 267823 304051 := bstep (se 1 (by rfl) ⟨228038, by rfl⟩ : syracuseStep 304051 = 456077) B456077
theorem B271283 : Blo 267823 271283 := bstep (se 1 (by rfl) ⟨203462, by rfl⟩ : syracuseStep 271283 = 406925) B406925
theorem B402371 : Blo 267823 402371 := bstep (se 1 (by rfl) ⟨301778, by rfl⟩ : syracuseStep 402371 = 603557) B603557
theorem B271299 : Blo 267823 271299 := bstep (se 1 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 271299 = 406949) B406949
theorem B271315 : Blo 267823 271315 := bstep (se 1 (by rfl) ⟨203486, by rfl⟩ : syracuseStep 271315 = 406973) B406973
theorem B402401 : Blo 267823 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B271331 : Blo 267823 271331 := bstep (se 1 (by rfl) ⟨203498, by rfl⟩ : syracuseStep 271331 = 406997) B406997
theorem B402419 : Blo 267823 402419 := bstep (se 1 (by rfl) ⟨301814, by rfl⟩ : syracuseStep 402419 = 603629) B603629
theorem B271347 : Blo 267823 271347 := bstep (se 1 (by rfl) ⟨203510, by rfl⟩ : syracuseStep 271347 = 407021) B407021
theorem B271363 : Blo 267823 271363 := bstep (se 1 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 271363 = 407045) B407045
theorem B402449 : Blo 267823 402449 := bstep (se 2 (by rfl) ⟨150918, by rfl⟩ : syracuseStep 402449 = 301837) B301837
theorem B271379 : Blo 267823 271379 := bstep (se 1 (by rfl) ⟨203534, by rfl⟩ : syracuseStep 271379 = 407069) B407069
theorem B402467 : Blo 267823 402467 := bstep (se 1 (by rfl) ⟨301850, by rfl⟩ : syracuseStep 402467 = 603701) B603701
theorem B271395 : Blo 267823 271395 := bstep (se 1 (by rfl) ⟨203546, by rfl⟩ : syracuseStep 271395 = 407093) B407093
theorem B271411 : Blo 267823 271411 := bstep (se 1 (by rfl) ⟨203558, by rfl⟩ : syracuseStep 271411 = 407117) B407117
theorem B402497 : Blo 267823 402497 := bstep (se 2 (by rfl) ⟨150936, by rfl⟩ : syracuseStep 402497 = 301873) B301873
theorem B304195 : Blo 267823 304195 := bstep (se 1 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 304195 = 456293) B456293
theorem B271427 : Blo 267823 271427 := bstep (se 1 (by rfl) ⟨203570, by rfl⟩ : syracuseStep 271427 = 407141) B407141
theorem B402515 : Blo 267823 402515 := bstep (se 1 (by rfl) ⟨301886, by rfl⟩ : syracuseStep 402515 = 603773) B603773
theorem B271443 : Blo 267823 271443 := bstep (se 1 (by rfl) ⟨203582, by rfl⟩ : syracuseStep 271443 = 407165) B407165
theorem B762979 : Blo 267823 762979 := bstep (se 1 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 762979 = 1144469) B1144469
theorem B271459 : Blo 267823 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B402545 : Blo 267823 402545 := bstep (se 2 (by rfl) ⟨150954, by rfl⟩ : syracuseStep 402545 = 301909) B301909
theorem B271475 : Blo 267823 271475 := bstep (se 1 (by rfl) ⟨203606, by rfl⟩ : syracuseStep 271475 = 407213) B407213
theorem B402563 : Blo 267823 402563 := bstep (se 1 (by rfl) ⟨301922, by rfl⟩ : syracuseStep 402563 = 603845) B603845
theorem B271491 : Blo 267823 271491 := bstep (se 1 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 271491 = 407237) B407237
theorem B271507 : Blo 267823 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B402593 : Blo 267823 402593 := bstep (se 2 (by rfl) ⟨150972, by rfl⟩ : syracuseStep 402593 = 301945) B301945
theorem B271523 : Blo 267823 271523 := bstep (se 1 (by rfl) ⟨203642, by rfl⟩ : syracuseStep 271523 = 407285) B407285
theorem B402611 : Blo 267823 402611 := bstep (se 1 (by rfl) ⟨301958, by rfl⟩ : syracuseStep 402611 = 603917) B603917
theorem B271539 : Blo 267823 271539 := bstep (se 1 (by rfl) ⟨203654, by rfl⟩ : syracuseStep 271539 = 407309) B407309
theorem B271555 : Blo 267823 271555 := bstep (se 1 (by rfl) ⟨203666, by rfl⟩ : syracuseStep 271555 = 407333) B407333
theorem B402641 : Blo 267823 402641 := bstep (se 2 (by rfl) ⟨150990, by rfl⟩ : syracuseStep 402641 = 301981) B301981
theorem B304339 : Blo 267823 304339 := bstep (se 1 (by rfl) ⟨228254, by rfl⟩ : syracuseStep 304339 = 456509) B456509
theorem B271571 : Blo 267823 271571 := bstep (se 1 (by rfl) ⟨203678, by rfl⟩ : syracuseStep 271571 = 407357) B407357
theorem B402659 : Blo 267823 402659 := bstep (se 1 (by rfl) ⟨301994, by rfl⟩ : syracuseStep 402659 = 603989) B603989
theorem B271587 : Blo 267823 271587 := bstep (se 1 (by rfl) ⟨203690, by rfl⟩ : syracuseStep 271587 = 407381) B407381
theorem B271603 : Blo 267823 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B402689 : Blo 267823 402689 := bstep (se 2 (by rfl) ⟨151008, by rfl⟩ : syracuseStep 402689 = 302017) B302017
theorem B271619 : Blo 267823 271619 := bstep (se 1 (by rfl) ⟨203714, by rfl⟩ : syracuseStep 271619 = 407429) B407429
theorem B369937 : Blo 267823 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B402707 : Blo 267823 402707 := bstep (se 1 (by rfl) ⟨302030, by rfl⟩ : syracuseStep 402707 = 604061) B604061
theorem B271635 : Blo 267823 271635 := bstep (se 1 (by rfl) ⟨203726, by rfl⟩ : syracuseStep 271635 = 407453) B407453
theorem B271651 : Blo 267823 271651 := bstep (se 1 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 271651 = 407477) B407477
theorem B402737 : Blo 267823 402737 := bstep (se 2 (by rfl) ⟨151026, by rfl⟩ : syracuseStep 402737 = 302053) B302053
theorem B271667 : Blo 267823 271667 := bstep (se 1 (by rfl) ⟨203750, by rfl⟩ : syracuseStep 271667 = 407501) B407501
theorem B402755 : Blo 267823 402755 := bstep (se 1 (by rfl) ⟨302066, by rfl⟩ : syracuseStep 402755 = 604133) B604133
theorem B271683 : Blo 267823 271683 := bstep (se 1 (by rfl) ⟨203762, by rfl⟩ : syracuseStep 271683 = 407525) B407525
theorem B271699 : Blo 267823 271699 := bstep (se 1 (by rfl) ⟨203774, by rfl⟩ : syracuseStep 271699 = 407549) B407549
theorem B402785 : Blo 267823 402785 := bstep (se 2 (by rfl) ⟨151044, by rfl⟩ : syracuseStep 402785 = 302089) B302089
theorem B304483 : Blo 267823 304483 := bstep (se 1 (by rfl) ⟨228362, by rfl⟩ : syracuseStep 304483 = 456725) B456725
theorem B271715 : Blo 267823 271715 := bstep (se 1 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 271715 = 407573) B407573
theorem B402803 : Blo 267823 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B271731 : Blo 267823 271731 := bstep (se 1 (by rfl) ⟨203798, by rfl⟩ : syracuseStep 271731 = 407597) B407597
theorem B271747 : Blo 267823 271747 := bstep (se 1 (by rfl) ⟨203810, by rfl⟩ : syracuseStep 271747 = 407621) B407621
theorem B402833 : Blo 267823 402833 := bstep (se 2 (by rfl) ⟨151062, by rfl⟩ : syracuseStep 402833 = 302125) B302125
theorem B927121 : Blo 267823 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B271763 : Blo 267823 271763 := bstep (se 1 (by rfl) ⟨203822, by rfl⟩ : syracuseStep 271763 = 407645) B407645
theorem B402851 : Blo 267823 402851 := bstep (se 1 (by rfl) ⟨302138, by rfl⟩ : syracuseStep 402851 = 604277) B604277
theorem B271779 : Blo 267823 271779 := bstep (se 1 (by rfl) ⟨203834, by rfl⟩ : syracuseStep 271779 = 407669) B407669
theorem B271795 : Blo 267823 271795 := bstep (se 1 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 271795 = 407693) B407693
theorem B402881 : Blo 267823 402881 := bstep (se 2 (by rfl) ⟨151080, by rfl⟩ : syracuseStep 402881 = 302161) B302161
theorem B271811 : Blo 267823 271811 := bstep (se 1 (by rfl) ⟨203858, by rfl⟩ : syracuseStep 271811 = 407717) B407717
theorem B402899 : Blo 267823 402899 := bstep (se 1 (by rfl) ⟨302174, by rfl⟩ : syracuseStep 402899 = 604349) B604349
theorem B402929 : Blo 267823 402929 := bstep (se 2 (by rfl) ⟨151098, by rfl⟩ : syracuseStep 402929 = 302197) B302197
theorem B304627 : Blo 267823 304627 := bstep (se 1 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 304627 = 456941) B456941
theorem B402947 : Blo 267823 402947 := bstep (se 1 (by rfl) ⟨302210, by rfl⟩ : syracuseStep 402947 = 604421) B604421
theorem B402977 : Blo 267823 402977 := bstep (se 2 (by rfl) ⟨151116, by rfl⟩ : syracuseStep 402977 = 302233) B302233
theorem B402995 : Blo 267823 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B730691 : Blo 267823 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B763469 : Blo 267823 763469 := bstep (se 3 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 763469 = 286301) B286301
theorem B403025 : Blo 267823 403025 := bstep (se 2 (by rfl) ⟨151134, by rfl⟩ : syracuseStep 403025 = 302269) B302269
theorem B403043 : Blo 267823 403043 := bstep (se 1 (by rfl) ⟨302282, by rfl⟩ : syracuseStep 403043 = 604565) B604565
theorem B403073 : Blo 267823 403073 := bstep (se 2 (by rfl) ⟨151152, by rfl⟩ : syracuseStep 403073 = 302305) B302305
theorem B304771 : Blo 267823 304771 := bstep (se 1 (by rfl) ⟨228578, by rfl⟩ : syracuseStep 304771 = 457157) B457157
theorem B403091 : Blo 267823 403091 := bstep (se 1 (by rfl) ⟨302318, by rfl⟩ : syracuseStep 403091 = 604637) B604637
theorem B403121 : Blo 267823 403121 := bstep (se 2 (by rfl) ⟨151170, by rfl⟩ : syracuseStep 403121 = 302341) B302341
theorem B403139 : Blo 267823 403139 := bstep (se 1 (by rfl) ⟨302354, by rfl⟩ : syracuseStep 403139 = 604709) B604709
theorem B730819 : Blo 267823 730819 := bstep (se 1 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 730819 = 1096229) B1096229
theorem B403169 : Blo 267823 403169 := bstep (se 2 (by rfl) ⟨151188, by rfl⟩ : syracuseStep 403169 = 302377) B302377
theorem B894691 : Blo 267823 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B403187 : Blo 267823 403187 := bstep (se 1 (by rfl) ⟨302390, by rfl⟩ : syracuseStep 403187 = 604781) B604781
theorem B403217 : Blo 267823 403217 := bstep (se 2 (by rfl) ⟨151206, by rfl⟩ : syracuseStep 403217 = 302413) B302413
theorem B304915 : Blo 267823 304915 := bstep (se 1 (by rfl) ⟨228686, by rfl⟩ : syracuseStep 304915 = 457373) B457373
theorem B403235 : Blo 267823 403235 := bstep (se 1 (by rfl) ⟨302426, by rfl⟩ : syracuseStep 403235 = 604853) B604853
theorem B403265 : Blo 267823 403265 := bstep (se 2 (by rfl) ⟨151224, by rfl⟩ : syracuseStep 403265 = 302449) B302449
theorem B403283 : Blo 267823 403283 := bstep (se 1 (by rfl) ⟨302462, by rfl⟩ : syracuseStep 403283 = 604925) B604925
theorem B403313 : Blo 267823 403313 := bstep (se 2 (by rfl) ⟨151242, by rfl⟩ : syracuseStep 403313 = 302485) B302485
theorem B403331 : Blo 267823 403331 := bstep (se 1 (by rfl) ⟨302498, by rfl⟩ : syracuseStep 403331 = 604997) B604997
theorem B1845125 : Blo 267823 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B403361 : Blo 267823 403361 := bstep (se 2 (by rfl) ⟨151260, by rfl⟩ : syracuseStep 403361 = 302521) B302521
theorem B305059 : Blo 267823 305059 := bstep (se 1 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 305059 = 457589) B457589
theorem B403379 : Blo 267823 403379 := bstep (se 1 (by rfl) ⟨302534, by rfl⟩ : syracuseStep 403379 = 605069) B605069
theorem B927683 : Blo 267823 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B11610053 : Blo 267823 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B862157 : Blo 267823 862157 := bstep (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) B323309
theorem B403409 : Blo 267823 403409 := bstep (se 2 (by rfl) ⟨151278, by rfl⟩ : syracuseStep 403409 = 302557) B302557
theorem B403427 : Blo 267823 403427 := bstep (se 1 (by rfl) ⟨302570, by rfl⟩ : syracuseStep 403427 = 605141) B605141
theorem B403457 : Blo 267823 403457 := bstep (se 2 (by rfl) ⟨151296, by rfl⟩ : syracuseStep 403457 = 302593) B302593
theorem B403475 : Blo 267823 403475 := bstep (se 1 (by rfl) ⟨302606, by rfl⟩ : syracuseStep 403475 = 605213) B605213
theorem B403505 : Blo 267823 403505 := bstep (se 2 (by rfl) ⟨151314, by rfl⟩ : syracuseStep 403505 = 302629) B302629
theorem B305203 : Blo 267823 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B403523 : Blo 267823 403523 := bstep (se 1 (by rfl) ⟨302642, by rfl⟩ : syracuseStep 403523 = 605285) B605285
theorem B403553 : Blo 267823 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B403571 : Blo 267823 403571 := bstep (se 1 (by rfl) ⟨302678, by rfl⟩ : syracuseStep 403571 = 605357) B605357
theorem B403601 : Blo 267823 403601 := bstep (se 2 (by rfl) ⟨151350, by rfl⟩ : syracuseStep 403601 = 302701) B302701
theorem B403619 : Blo 267823 403619 := bstep (se 1 (by rfl) ⟨302714, by rfl⟩ : syracuseStep 403619 = 605429) B605429
theorem B403649 : Blo 267823 403649 := bstep (se 2 (by rfl) ⟨151368, by rfl⟩ : syracuseStep 403649 = 302737) B302737
theorem B305347 : Blo 267823 305347 := bstep (se 1 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 305347 = 458021) B458021
theorem B2009285 : Blo 267823 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B403667 : Blo 267823 403667 := bstep (se 1 (by rfl) ⟨302750, by rfl⟩ : syracuseStep 403667 = 605501) B605501
theorem B403697 : Blo 267823 403697 := bstep (se 2 (by rfl) ⟨151386, by rfl⟩ : syracuseStep 403697 = 302773) B302773
theorem B403715 : Blo 267823 403715 := bstep (se 1 (by rfl) ⟨302786, by rfl⟩ : syracuseStep 403715 = 605573) B605573
theorem B403745 : Blo 267823 403745 := bstep (se 2 (by rfl) ⟨151404, by rfl⟩ : syracuseStep 403745 = 302809) B302809
theorem B403763 : Blo 267823 403763 := bstep (se 1 (by rfl) ⟨302822, by rfl⟩ : syracuseStep 403763 = 605645) B605645
theorem B403793 : Blo 267823 403793 := bstep (se 2 (by rfl) ⟨151422, by rfl⟩ : syracuseStep 403793 = 302845) B302845
theorem B305491 : Blo 267823 305491 := bstep (se 1 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 305491 = 458237) B458237
theorem B1288547 : Blo 267823 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B403811 : Blo 267823 403811 := bstep (se 1 (by rfl) ⟨302858, by rfl⟩ : syracuseStep 403811 = 605717) B605717
theorem B731501 : Blo 267823 731501 := bstep (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) B274313
theorem B403841 : Blo 267823 403841 := bstep (se 2 (by rfl) ⟨151440, by rfl⟩ : syracuseStep 403841 = 302881) B302881
theorem B403859 : Blo 267823 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B403889 : Blo 267823 403889 := bstep (se 2 (by rfl) ⟨151458, by rfl⟩ : syracuseStep 403889 = 302917) B302917
theorem B403907 : Blo 267823 403907 := bstep (se 1 (by rfl) ⟨302930, by rfl⟩ : syracuseStep 403907 = 605861) B605861
theorem B731597 : Blo 267823 731597 := bstep (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) B274349
theorem B403937 : Blo 267823 403937 := bstep (se 2 (by rfl) ⟨151476, by rfl⟩ : syracuseStep 403937 = 302953) B302953
theorem B305635 : Blo 267823 305635 := bstep (se 1 (by rfl) ⟨229226, by rfl⟩ : syracuseStep 305635 = 458453) B458453
theorem B403955 : Blo 267823 403955 := bstep (se 1 (by rfl) ⟨302966, by rfl⟩ : syracuseStep 403955 = 605933) B605933
theorem B403985 : Blo 267823 403985 := bstep (se 2 (by rfl) ⟨151494, by rfl⟩ : syracuseStep 403985 = 302989) B302989
theorem B404003 : Blo 267823 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B404033 : Blo 267823 404033 := bstep (se 2 (by rfl) ⟨151512, by rfl⟩ : syracuseStep 404033 = 303025) B303025
theorem B404051 : Blo 267823 404051 := bstep (se 1 (by rfl) ⟨303038, by rfl⟩ : syracuseStep 404051 = 606077) B606077
theorem B1288817 : Blo 267823 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B404081 : Blo 267823 404081 := bstep (se 2 (by rfl) ⟨151530, by rfl⟩ : syracuseStep 404081 = 303061) B303061
theorem B305779 : Blo 267823 305779 := bstep (se 1 (by rfl) ⟨229334, by rfl⟩ : syracuseStep 305779 = 458669) B458669
theorem B404099 : Blo 267823 404099 := bstep (se 1 (by rfl) ⟨303074, by rfl⟩ : syracuseStep 404099 = 606149) B606149
theorem B404129 : Blo 267823 404129 := bstep (se 2 (by rfl) ⟨151548, by rfl⟩ : syracuseStep 404129 = 303097) B303097
theorem B928433 : Blo 267823 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B404147 : Blo 267823 404147 := bstep (se 1 (by rfl) ⟨303110, by rfl⟩ : syracuseStep 404147 = 606221) B606221
theorem B404177 : Blo 267823 404177 := bstep (se 2 (by rfl) ⟨151566, by rfl⟩ : syracuseStep 404177 = 303133) B303133
theorem B731857 : Blo 267823 731857 := bstep (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) B548893
theorem B404195 : Blo 267823 404195 := bstep (se 1 (by rfl) ⟨303146, by rfl⟩ : syracuseStep 404195 = 606293) B606293
theorem B764653 : Blo 267823 764653 := bstep (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) B286745
theorem B404225 : Blo 267823 404225 := bstep (se 2 (by rfl) ⟨151584, by rfl⟩ : syracuseStep 404225 = 303169) B303169
theorem B404243 : Blo 267823 404243 := bstep (se 1 (by rfl) ⟨303182, by rfl⟩ : syracuseStep 404243 = 606365) B606365
theorem B404273 : Blo 267823 404273 := bstep (se 2 (by rfl) ⟨151602, by rfl⟩ : syracuseStep 404273 = 303205) B303205
theorem B404291 : Blo 267823 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B404321 : Blo 267823 404321 := bstep (se 2 (by rfl) ⟨151620, by rfl⟩ : syracuseStep 404321 = 303241) B303241
theorem B404339 : Blo 267823 404339 := bstep (se 1 (by rfl) ⟨303254, by rfl⟩ : syracuseStep 404339 = 606509) B606509
theorem B404369 : Blo 267823 404369 := bstep (se 2 (by rfl) ⟨151638, by rfl⟩ : syracuseStep 404369 = 303277) B303277
theorem B404387 : Blo 267823 404387 := bstep (se 1 (by rfl) ⟨303290, by rfl⟩ : syracuseStep 404387 = 606581) B606581
theorem B404417 : Blo 267823 404417 := bstep (se 2 (by rfl) ⟨151656, by rfl⟩ : syracuseStep 404417 = 303313) B303313
theorem B404435 : Blo 267823 404435 := bstep (se 1 (by rfl) ⟨303326, by rfl⟩ : syracuseStep 404435 = 606653) B606653
theorem B404465 : Blo 267823 404465 := bstep (se 2 (by rfl) ⟨151674, by rfl⟩ : syracuseStep 404465 = 303349) B303349
theorem B404483 : Blo 267823 404483 := bstep (se 1 (by rfl) ⟨303362, by rfl⟩ : syracuseStep 404483 = 606725) B606725
theorem B404513 : Blo 267823 404513 := bstep (se 2 (by rfl) ⟨151692, by rfl⟩ : syracuseStep 404513 = 303385) B303385
theorem B338995 : Blo 267823 338995 := bstep (se 1 (by rfl) ⟨254246, by rfl⟩ : syracuseStep 338995 = 508493) B508493
theorem B404531 : Blo 267823 404531 := bstep (se 1 (by rfl) ⟨303398, by rfl⟩ : syracuseStep 404531 = 606797) B606797
theorem B404561 : Blo 267823 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B404579 : Blo 267823 404579 := bstep (se 1 (by rfl) ⟨303434, by rfl⟩ : syracuseStep 404579 = 606869) B606869
theorem B404609 : Blo 267823 404609 := bstep (se 2 (by rfl) ⟨151728, by rfl⟩ : syracuseStep 404609 = 303457) B303457
theorem B404627 : Blo 267823 404627 := bstep (se 1 (by rfl) ⟨303470, by rfl⟩ : syracuseStep 404627 = 606941) B606941
theorem B404657 : Blo 267823 404657 := bstep (se 2 (by rfl) ⟨151746, by rfl⟩ : syracuseStep 404657 = 303493) B303493
theorem B404675 : Blo 267823 404675 := bstep (se 1 (by rfl) ⟨303506, by rfl⟩ : syracuseStep 404675 = 607013) B607013
theorem B404705 : Blo 267823 404705 := bstep (se 2 (by rfl) ⟨151764, by rfl⟩ : syracuseStep 404705 = 303529) B303529
theorem B1027313 : Blo 267823 1027313 := bstep (se 2 (by rfl) ⟨385242, by rfl⟩ : syracuseStep 1027313 = 770485) B770485
theorem B404723 : Blo 267823 404723 := bstep (se 1 (by rfl) ⟨303542, by rfl⟩ : syracuseStep 404723 = 607085) B607085
theorem B404753 : Blo 267823 404753 := bstep (se 2 (by rfl) ⟨151782, by rfl⟩ : syracuseStep 404753 = 303565) B303565
theorem B404771 : Blo 267823 404771 := bstep (se 1 (by rfl) ⟨303578, by rfl⟩ : syracuseStep 404771 = 607157) B607157
theorem B404801 : Blo 267823 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B404819 : Blo 267823 404819 := bstep (se 1 (by rfl) ⟨303614, by rfl⟩ : syracuseStep 404819 = 607229) B607229
theorem B404849 : Blo 267823 404849 := bstep (se 2 (by rfl) ⟨151818, by rfl⟩ : syracuseStep 404849 = 303637) B303637
theorem B404867 : Blo 267823 404867 := bstep (se 1 (by rfl) ⟨303650, by rfl⟩ : syracuseStep 404867 = 607301) B607301
theorem B404897 : Blo 267823 404897 := bstep (se 2 (by rfl) ⟨151836, by rfl⟩ : syracuseStep 404897 = 303673) B303673
theorem B1158563 : Blo 267823 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B404915 : Blo 267823 404915 := bstep (se 1 (by rfl) ⟨303686, by rfl⟩ : syracuseStep 404915 = 607373) B607373
theorem B404945 : Blo 267823 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B404963 : Blo 267823 404963 := bstep (se 1 (by rfl) ⟨303722, by rfl⟩ : syracuseStep 404963 = 607445) B607445
theorem B404993 : Blo 267823 404993 := bstep (se 2 (by rfl) ⟨151872, by rfl⟩ : syracuseStep 404993 = 303745) B303745
theorem B863747 : Blo 267823 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B405011 : Blo 267823 405011 := bstep (se 1 (by rfl) ⟨303758, by rfl⟩ : syracuseStep 405011 = 607517) B607517
theorem B339491 : Blo 267823 339491 := bstep (se 1 (by rfl) ⟨254618, by rfl⟩ : syracuseStep 339491 = 509237) B509237
theorem B405041 : Blo 267823 405041 := bstep (se 2 (by rfl) ⟨151890, by rfl⟩ : syracuseStep 405041 = 303781) B303781
theorem B405059 : Blo 267823 405059 := bstep (se 1 (by rfl) ⟨303794, by rfl⟩ : syracuseStep 405059 = 607589) B607589
theorem B405089 : Blo 267823 405089 := bstep (se 2 (by rfl) ⟨151908, by rfl⟩ : syracuseStep 405089 = 303817) B303817
theorem B405107 : Blo 267823 405107 := bstep (se 1 (by rfl) ⟨303830, by rfl⟩ : syracuseStep 405107 = 607661) B607661
theorem B405137 : Blo 267823 405137 := bstep (se 2 (by rfl) ⟨151926, by rfl⟩ : syracuseStep 405137 = 303853) B303853
theorem B1224355 : Blo 267823 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B405155 : Blo 267823 405155 := bstep (se 1 (by rfl) ⟨303866, by rfl⟩ : syracuseStep 405155 = 607733) B607733
theorem B405185 : Blo 267823 405185 := bstep (se 2 (by rfl) ⟨151944, by rfl⟩ : syracuseStep 405185 = 303889) B303889
theorem B405203 : Blo 267823 405203 := bstep (se 1 (by rfl) ⟨303902, by rfl⟩ : syracuseStep 405203 = 607805) B607805
theorem B405233 : Blo 267823 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B405251 : Blo 267823 405251 := bstep (se 1 (by rfl) ⟨303938, by rfl⟩ : syracuseStep 405251 = 607877) B607877
theorem B765713 : Blo 267823 765713 := bstep (se 2 (by rfl) ⟨287142, by rfl⟩ : syracuseStep 765713 = 574285) B574285
theorem B405281 : Blo 267823 405281 := bstep (se 2 (by rfl) ⟨151980, by rfl⟩ : syracuseStep 405281 = 303961) B303961
theorem B405299 : Blo 267823 405299 := bstep (se 1 (by rfl) ⟨303974, by rfl⟩ : syracuseStep 405299 = 607949) B607949
theorem B405329 : Blo 267823 405329 := bstep (se 2 (by rfl) ⟨151998, by rfl⟩ : syracuseStep 405329 = 303997) B303997
theorem B405347 : Blo 267823 405347 := bstep (se 1 (by rfl) ⟨304010, by rfl⟩ : syracuseStep 405347 = 608021) B608021
theorem B405377 : Blo 267823 405377 := bstep (se 2 (by rfl) ⟨152016, by rfl⟩ : syracuseStep 405377 = 304033) B304033
theorem B405395 : Blo 267823 405395 := bstep (se 1 (by rfl) ⟨304046, by rfl⟩ : syracuseStep 405395 = 608093) B608093
theorem B405425 : Blo 267823 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B405443 : Blo 267823 405443 := bstep (se 1 (by rfl) ⟨304082, by rfl⟩ : syracuseStep 405443 = 608165) B608165
theorem B405473 : Blo 267823 405473 := bstep (se 2 (by rfl) ⟨152052, by rfl⟩ : syracuseStep 405473 = 304105) B304105
theorem B405491 : Blo 267823 405491 := bstep (se 1 (by rfl) ⟨304118, by rfl⟩ : syracuseStep 405491 = 608237) B608237
theorem B405521 : Blo 267823 405521 := bstep (se 2 (by rfl) ⟨152070, by rfl⟩ : syracuseStep 405521 = 304141) B304141
theorem B405539 : Blo 267823 405539 := bstep (se 1 (by rfl) ⟨304154, by rfl⟩ : syracuseStep 405539 = 608309) B608309
theorem B1290289 : Blo 267823 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B405569 : Blo 267823 405569 := bstep (se 2 (by rfl) ⟨152088, by rfl⟩ : syracuseStep 405569 = 304177) B304177
theorem B405587 : Blo 267823 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B405617 : Blo 267823 405617 := bstep (se 2 (by rfl) ⟨152106, by rfl⟩ : syracuseStep 405617 = 304213) B304213
theorem B405635 : Blo 267823 405635 := bstep (se 1 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 405635 = 608453) B608453
theorem B405665 : Blo 267823 405665 := bstep (se 2 (by rfl) ⟨152124, by rfl⟩ : syracuseStep 405665 = 304249) B304249
theorem B1355939 : Blo 267823 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B405683 : Blo 267823 405683 := bstep (se 1 (by rfl) ⟨304262, by rfl⟩ : syracuseStep 405683 = 608525) B608525
theorem B405713 : Blo 267823 405713 := bstep (se 2 (by rfl) ⟨152142, by rfl⟩ : syracuseStep 405713 = 304285) B304285
theorem B1290467 : Blo 267823 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B340195 : Blo 267823 340195 := bstep (se 1 (by rfl) ⟨255146, by rfl⟩ : syracuseStep 340195 = 510293) B510293
theorem B405731 : Blo 267823 405731 := bstep (se 1 (by rfl) ⟨304298, by rfl⟩ : syracuseStep 405731 = 608597) B608597
theorem B405761 : Blo 267823 405761 := bstep (se 2 (by rfl) ⟨152160, by rfl⟩ : syracuseStep 405761 = 304321) B304321
theorem B864515 : Blo 267823 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B405779 : Blo 267823 405779 := bstep (se 1 (by rfl) ⟨304334, by rfl⟩ : syracuseStep 405779 = 608669) B608669
theorem B405809 : Blo 267823 405809 := bstep (se 2 (by rfl) ⟨152178, by rfl⟩ : syracuseStep 405809 = 304357) B304357
theorem B340291 : Blo 267823 340291 := bstep (se 1 (by rfl) ⟨255218, by rfl⟩ : syracuseStep 340291 = 510437) B510437
theorem B405827 : Blo 267823 405827 := bstep (se 1 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 405827 = 608741) B608741
theorem B405857 : Blo 267823 405857 := bstep (se 2 (by rfl) ⟨152196, by rfl⟩ : syracuseStep 405857 = 304393) B304393
theorem B405875 : Blo 267823 405875 := bstep (se 1 (by rfl) ⟨304406, by rfl⟩ : syracuseStep 405875 = 608813) B608813
theorem B405905 : Blo 267823 405905 := bstep (se 2 (by rfl) ⟨152214, by rfl⟩ : syracuseStep 405905 = 304429) B304429
theorem B405923 : Blo 267823 405923 := bstep (se 1 (by rfl) ⟨304442, by rfl⟩ : syracuseStep 405923 = 608885) B608885
theorem B766385 : Blo 267823 766385 := bstep (se 2 (by rfl) ⟨287394, by rfl⟩ : syracuseStep 766385 = 574789) B574789
theorem B405953 : Blo 267823 405953 := bstep (se 2 (by rfl) ⟨152232, by rfl⟩ : syracuseStep 405953 = 304465) B304465
theorem B405971 : Blo 267823 405971 := bstep (se 1 (by rfl) ⟨304478, by rfl⟩ : syracuseStep 405971 = 608957) B608957
theorem B406001 : Blo 267823 406001 := bstep (se 2 (by rfl) ⟨152250, by rfl⟩ : syracuseStep 406001 = 304501) B304501
theorem B406019 : Blo 267823 406019 := bstep (se 1 (by rfl) ⟨304514, by rfl⟩ : syracuseStep 406019 = 609029) B609029
theorem B2241037 : Blo 267823 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B406049 : Blo 267823 406049 := bstep (se 2 (by rfl) ⟨152268, by rfl⟩ : syracuseStep 406049 = 304537) B304537
theorem B406067 : Blo 267823 406067 := bstep (se 1 (by rfl) ⟨304550, by rfl⟩ : syracuseStep 406067 = 609101) B609101
theorem B406097 : Blo 267823 406097 := bstep (se 2 (by rfl) ⟨152286, by rfl⟩ : syracuseStep 406097 = 304573) B304573
theorem B2175587 : Blo 267823 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B406115 : Blo 267823 406115 := bstep (se 1 (by rfl) ⟨304586, by rfl⟩ : syracuseStep 406115 = 609173) B609173
theorem B406145 : Blo 267823 406145 := bstep (se 2 (by rfl) ⟨152304, by rfl⟩ : syracuseStep 406145 = 304609) B304609
theorem B864913 : Blo 267823 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B406163 : Blo 267823 406163 := bstep (se 1 (by rfl) ⟨304622, by rfl⟩ : syracuseStep 406163 = 609245) B609245
theorem B1028771 : Blo 267823 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B602801 : Blo 267823 602801 := bstep (se 2 (by rfl) ⟨226050, by rfl⟩ : syracuseStep 602801 = 452101) B452101
theorem B406193 : Blo 267823 406193 := bstep (se 2 (by rfl) ⟨152322, by rfl⟩ : syracuseStep 406193 = 304645) B304645
theorem B602819 : Blo 267823 602819 := bstep (se 1 (by rfl) ⟨452114, by rfl⟩ : syracuseStep 602819 = 904229) B904229
theorem B406211 : Blo 267823 406211 := bstep (se 1 (by rfl) ⟨304658, by rfl⟩ : syracuseStep 406211 = 609317) B609317
theorem B406241 : Blo 267823 406241 := bstep (se 2 (by rfl) ⟨152340, by rfl⟩ : syracuseStep 406241 = 304681) B304681
theorem B406259 : Blo 267823 406259 := bstep (se 1 (by rfl) ⟨304694, by rfl⟩ : syracuseStep 406259 = 609389) B609389
theorem B865027 : Blo 267823 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B406289 : Blo 267823 406289 := bstep (se 2 (by rfl) ⟨152358, by rfl⟩ : syracuseStep 406289 = 304717) B304717
theorem B406307 : Blo 267823 406307 := bstep (se 1 (by rfl) ⟨304730, by rfl⟩ : syracuseStep 406307 = 609461) B609461
theorem B340787 : Blo 267823 340787 := bstep (se 1 (by rfl) ⟨255590, by rfl⟩ : syracuseStep 340787 = 511181) B511181
theorem B406337 : Blo 267823 406337 := bstep (se 2 (by rfl) ⟨152376, by rfl⟩ : syracuseStep 406337 = 304753) B304753
theorem B406355 : Blo 267823 406355 := bstep (se 1 (by rfl) ⟨304766, by rfl⟩ : syracuseStep 406355 = 609533) B609533
theorem B406385 : Blo 267823 406385 := bstep (se 2 (by rfl) ⟨152394, by rfl⟩ : syracuseStep 406385 = 304789) B304789
theorem B406403 : Blo 267823 406403 := bstep (se 1 (by rfl) ⟨304802, by rfl⟩ : syracuseStep 406403 = 609605) B609605
theorem B406433 : Blo 267823 406433 := bstep (se 2 (by rfl) ⟨152412, by rfl⟩ : syracuseStep 406433 = 304825) B304825
theorem B734129 : Blo 267823 734129 := bstep (se 2 (by rfl) ⟨275298, by rfl⟩ : syracuseStep 734129 = 550597) B550597
theorem B406451 : Blo 267823 406451 := bstep (se 1 (by rfl) ⟨304838, by rfl⟩ : syracuseStep 406451 = 609677) B609677
theorem B1356749 : Blo 267823 1356749 := bstep (se 3 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 1356749 = 508781) B508781
theorem B603089 : Blo 267823 603089 := bstep (se 2 (by rfl) ⟨226158, by rfl⟩ : syracuseStep 603089 = 452317) B452317
theorem B406481 : Blo 267823 406481 := bstep (se 2 (by rfl) ⟨152430, by rfl⟩ : syracuseStep 406481 = 304861) B304861
theorem B603107 : Blo 267823 603107 := bstep (se 1 (by rfl) ⟨452330, by rfl⟩ : syracuseStep 603107 = 904661) B904661
theorem B406499 : Blo 267823 406499 := bstep (se 1 (by rfl) ⟨304874, by rfl⟩ : syracuseStep 406499 = 609749) B609749
theorem B406529 : Blo 267823 406529 := bstep (se 2 (by rfl) ⟨152448, by rfl⟩ : syracuseStep 406529 = 304897) B304897
theorem B406547 : Blo 267823 406547 := bstep (se 1 (by rfl) ⟨304910, by rfl⟩ : syracuseStep 406547 = 609821) B609821
theorem B406577 : Blo 267823 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B406595 : Blo 267823 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B406625 : Blo 267823 406625 := bstep (se 2 (by rfl) ⟨152484, by rfl⟩ : syracuseStep 406625 = 304969) B304969
theorem B406643 : Blo 267823 406643 := bstep (se 1 (by rfl) ⟨304982, by rfl⟩ : syracuseStep 406643 = 609965) B609965
theorem B406673 : Blo 267823 406673 := bstep (se 2 (by rfl) ⟨152502, by rfl⟩ : syracuseStep 406673 = 305005) B305005
theorem B406691 : Blo 267823 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B406721 : Blo 267823 406721 := bstep (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) B305041
theorem B767171 : Blo 267823 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B406739 : Blo 267823 406739 := bstep (se 1 (by rfl) ⟨305054, by rfl⟩ : syracuseStep 406739 = 610109) B610109
theorem B603377 : Blo 267823 603377 := bstep (se 2 (by rfl) ⟨226266, by rfl⟩ : syracuseStep 603377 = 452533) B452533
theorem B406769 : Blo 267823 406769 := bstep (se 2 (by rfl) ⟨152538, by rfl⟩ : syracuseStep 406769 = 305077) B305077
theorem B603395 : Blo 267823 603395 := bstep (se 1 (by rfl) ⟨452546, by rfl⟩ : syracuseStep 603395 = 905093) B905093
theorem B406787 : Blo 267823 406787 := bstep (se 1 (by rfl) ⟨305090, by rfl⟩ : syracuseStep 406787 = 610181) B610181
theorem B406817 : Blo 267823 406817 := bstep (se 2 (by rfl) ⟨152556, by rfl⟩ : syracuseStep 406817 = 305113) B305113
theorem B406835 : Blo 267823 406835 := bstep (se 1 (by rfl) ⟨305126, by rfl⟩ : syracuseStep 406835 = 610253) B610253
theorem B406865 : Blo 267823 406865 := bstep (se 2 (by rfl) ⟨152574, by rfl⟩ : syracuseStep 406865 = 305149) B305149
theorem B406883 : Blo 267823 406883 := bstep (se 1 (by rfl) ⟨305162, by rfl⟩ : syracuseStep 406883 = 610325) B610325
theorem B406913 : Blo 267823 406913 := bstep (se 2 (by rfl) ⟨152592, by rfl⟩ : syracuseStep 406913 = 305185) B305185
theorem B406931 : Blo 267823 406931 := bstep (se 1 (by rfl) ⟨305198, by rfl⟩ : syracuseStep 406931 = 610397) B610397
theorem B406961 : Blo 267823 406961 := bstep (se 2 (by rfl) ⟨152610, by rfl⟩ : syracuseStep 406961 = 305221) B305221
theorem B406979 : Blo 267823 406979 := bstep (se 1 (by rfl) ⟨305234, by rfl⟩ : syracuseStep 406979 = 610469) B610469
theorem B865745 : Blo 267823 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B407009 : Blo 267823 407009 := bstep (se 2 (by rfl) ⟨152628, by rfl⟩ : syracuseStep 407009 = 305257) B305257
theorem B341491 : Blo 267823 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B407027 : Blo 267823 407027 := bstep (se 1 (by rfl) ⟨305270, by rfl⟩ : syracuseStep 407027 = 610541) B610541
theorem B767501 : Blo 267823 767501 := bstep (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) B287813
theorem B603665 : Blo 267823 603665 := bstep (se 2 (by rfl) ⟨226374, by rfl⟩ : syracuseStep 603665 = 452749) B452749
theorem B407057 : Blo 267823 407057 := bstep (se 2 (by rfl) ⟨152646, by rfl⟩ : syracuseStep 407057 = 305293) B305293
theorem B603683 : Blo 267823 603683 := bstep (se 1 (by rfl) ⟨452762, by rfl⟩ : syracuseStep 603683 = 905525) B905525
theorem B407075 : Blo 267823 407075 := bstep (se 1 (by rfl) ⟨305306, by rfl⟩ : syracuseStep 407075 = 610613) B610613
theorem B407105 : Blo 267823 407105 := bstep (se 2 (by rfl) ⟨152664, by rfl⟩ : syracuseStep 407105 = 305329) B305329
theorem B767569 : Blo 267823 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B341587 : Blo 267823 341587 := bstep (se 1 (by rfl) ⟨256190, by rfl⟩ : syracuseStep 341587 = 512381) B512381
theorem B407123 : Blo 267823 407123 := bstep (se 1 (by rfl) ⟨305342, by rfl⟩ : syracuseStep 407123 = 610685) B610685
theorem B407153 : Blo 267823 407153 := bstep (se 2 (by rfl) ⟨152682, by rfl⟩ : syracuseStep 407153 = 305365) B305365
theorem B407171 : Blo 267823 407171 := bstep (se 1 (by rfl) ⟨305378, by rfl⟩ : syracuseStep 407171 = 610757) B610757
theorem B1029773 : Blo 267823 1029773 := bstep (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) B386165
theorem B407201 : Blo 267823 407201 := bstep (se 2 (by rfl) ⟨152700, by rfl⟩ : syracuseStep 407201 = 305401) B305401
theorem B407219 : Blo 267823 407219 := bstep (se 1 (by rfl) ⟨305414, by rfl⟩ : syracuseStep 407219 = 610829) B610829
theorem B407249 : Blo 267823 407249 := bstep (se 2 (by rfl) ⟨152718, by rfl⟩ : syracuseStep 407249 = 305437) B305437
theorem B407267 : Blo 267823 407267 := bstep (se 1 (by rfl) ⟨305450, by rfl⟩ : syracuseStep 407267 = 610901) B610901
theorem B407297 : Blo 267823 407297 := bstep (se 2 (by rfl) ⟨152736, by rfl⟩ : syracuseStep 407297 = 305473) B305473
theorem B1095437 : Blo 267823 1095437 := bstep (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) B410789
theorem B407315 : Blo 267823 407315 := bstep (se 1 (by rfl) ⟨305486, by rfl⟩ : syracuseStep 407315 = 610973) B610973
theorem B603953 : Blo 267823 603953 := bstep (se 2 (by rfl) ⟨226482, by rfl⟩ : syracuseStep 603953 = 452965) B452965
theorem B407345 : Blo 267823 407345 := bstep (se 2 (by rfl) ⟨152754, by rfl⟩ : syracuseStep 407345 = 305509) B305509
theorem B603971 : Blo 267823 603971 := bstep (se 1 (by rfl) ⟨452978, by rfl⟩ : syracuseStep 603971 = 905957) B905957
theorem B407363 : Blo 267823 407363 := bstep (se 1 (by rfl) ⟨305522, by rfl⟩ : syracuseStep 407363 = 611045) B611045
theorem B407393 : Blo 267823 407393 := bstep (se 2 (by rfl) ⟨152772, by rfl⟩ : syracuseStep 407393 = 305545) B305545
theorem B767843 : Blo 267823 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B407411 : Blo 267823 407411 := bstep (se 1 (by rfl) ⟨305558, by rfl⟩ : syracuseStep 407411 = 611117) B611117
theorem B407441 : Blo 267823 407441 := bstep (se 2 (by rfl) ⟨152790, by rfl⟩ : syracuseStep 407441 = 305581) B305581
theorem B407459 : Blo 267823 407459 := bstep (se 1 (by rfl) ⟨305594, by rfl⟩ : syracuseStep 407459 = 611189) B611189
theorem B407489 : Blo 267823 407489 := bstep (se 2 (by rfl) ⟨152808, by rfl⟩ : syracuseStep 407489 = 305617) B305617
theorem B1292237 : Blo 267823 1292237 := bstep (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) B484589
theorem B407507 : Blo 267823 407507 := bstep (se 1 (by rfl) ⟨305630, by rfl⟩ : syracuseStep 407507 = 611261) B611261
theorem B866285 : Blo 267823 866285 := bstep (se 3 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 866285 = 324857) B324857
theorem B407537 : Blo 267823 407537 := bstep (se 2 (by rfl) ⟨152826, by rfl⟩ : syracuseStep 407537 = 305653) B305653
theorem B407555 : Blo 267823 407555 := bstep (se 1 (by rfl) ⟨305666, by rfl⟩ : syracuseStep 407555 = 611333) B611333
theorem B407585 : Blo 267823 407585 := bstep (se 2 (by rfl) ⟨152844, by rfl⟩ : syracuseStep 407585 = 305689) B305689
theorem B407603 : Blo 267823 407603 := bstep (se 1 (by rfl) ⟨305702, by rfl⟩ : syracuseStep 407603 = 611405) B611405
theorem B14956597 : Blo 267823 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B342083 : Blo 267823 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B604241 : Blo 267823 604241 := bstep (se 2 (by rfl) ⟨226590, by rfl⟩ : syracuseStep 604241 = 453181) B453181
theorem B407633 : Blo 267823 407633 := bstep (se 2 (by rfl) ⟨152862, by rfl⟩ : syracuseStep 407633 = 305725) B305725
theorem B604259 : Blo 267823 604259 := bstep (se 1 (by rfl) ⟨453194, by rfl⟩ : syracuseStep 604259 = 906389) B906389
theorem B407651 : Blo 267823 407651 := bstep (se 1 (by rfl) ⟨305738, by rfl⟩ : syracuseStep 407651 = 611477) B611477
theorem B407681 : Blo 267823 407681 := bstep (se 2 (by rfl) ⟨152880, by rfl⟩ : syracuseStep 407681 = 305761) B305761
theorem B1554565 : Blo 267823 1554565 := bstep (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) B291481
theorem B407699 : Blo 267823 407699 := bstep (se 1 (by rfl) ⟨305774, by rfl⟩ : syracuseStep 407699 = 611549) B611549
theorem B407729 : Blo 267823 407729 := bstep (se 2 (by rfl) ⟨152898, by rfl⟩ : syracuseStep 407729 = 305797) B305797
theorem B604529 : Blo 267823 604529 := bstep (se 2 (by rfl) ⟨226698, by rfl⟩ : syracuseStep 604529 = 453397) B453397
theorem B604547 : Blo 267823 604547 := bstep (se 1 (by rfl) ⟨453410, by rfl⟩ : syracuseStep 604547 = 906821) B906821
theorem B735875 : Blo 267823 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B1849997 : Blo 267823 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B604817 : Blo 267823 604817 := bstep (se 2 (by rfl) ⟨226806, by rfl⟩ : syracuseStep 604817 = 453613) B453613
theorem B604835 : Blo 267823 604835 := bstep (se 1 (by rfl) ⟨453626, by rfl⟩ : syracuseStep 604835 = 907253) B907253
theorem B768685 : Blo 267823 768685 := bstep (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) B288257
theorem B342787 : Blo 267823 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B768845 : Blo 267823 768845 := bstep (se 3 (by rfl) ⟨144158, by rfl⟩ : syracuseStep 768845 = 288317) B288317
theorem B342883 : Blo 267823 342883 := bstep (se 1 (by rfl) ⟨257162, by rfl⟩ : syracuseStep 342883 = 514325) B514325
theorem B605105 : Blo 267823 605105 := bstep (se 2 (by rfl) ⟨226914, by rfl⟩ : syracuseStep 605105 = 453829) B453829
theorem B605123 : Blo 267823 605123 := bstep (se 1 (by rfl) ⟨453842, by rfl⟩ : syracuseStep 605123 = 907685) B907685
theorem B769027 : Blo 267823 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B605393 : Blo 267823 605393 := bstep (se 2 (by rfl) ⟨227022, by rfl⟩ : syracuseStep 605393 = 454045) B454045
theorem B605411 : Blo 267823 605411 := bstep (se 1 (by rfl) ⟨454058, by rfl⟩ : syracuseStep 605411 = 908117) B908117
theorem B1097009 : Blo 267823 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B343379 : Blo 267823 343379 := bstep (se 1 (by rfl) ⟨257534, by rfl⟩ : syracuseStep 343379 = 515069) B515069
theorem B605681 : Blo 267823 605681 := bstep (se 2 (by rfl) ⟨227130, by rfl⟩ : syracuseStep 605681 = 454261) B454261
theorem B605699 : Blo 267823 605699 := bstep (se 1 (by rfl) ⟨454274, by rfl⟩ : syracuseStep 605699 = 908549) B908549
theorem B1556131 : Blo 267823 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B1031885 : Blo 267823 1031885 := bstep (se 3 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 1031885 = 386957) B386957
theorem B605969 : Blo 267823 605969 := bstep (se 2 (by rfl) ⟨227238, by rfl⟩ : syracuseStep 605969 = 454477) B454477
theorem B605987 : Blo 267823 605987 := bstep (se 1 (by rfl) ⟨454490, by rfl⟩ : syracuseStep 605987 = 908981) B908981
theorem B1359665 : Blo 267823 1359665 := bstep (se 2 (by rfl) ⟨509874, by rfl⟩ : syracuseStep 1359665 = 1019749) B1019749
theorem B868205 : Blo 267823 868205 := bstep (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) B325577
theorem B409457 : Blo 267823 409457 := bstep (se 2 (by rfl) ⟨153546, by rfl⟩ : syracuseStep 409457 = 307093) B307093
theorem B4440005 : Blo 267823 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B1458161 : Blo 267823 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B606257 : Blo 267823 606257 := bstep (se 2 (by rfl) ⟨227346, by rfl⟩ : syracuseStep 606257 = 454693) B454693
theorem B606275 : Blo 267823 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B606545 : Blo 267823 606545 := bstep (se 2 (by rfl) ⟨227454, by rfl⟩ : syracuseStep 606545 = 454909) B454909
theorem B606563 : Blo 267823 606563 := bstep (se 1 (by rfl) ⟨454922, by rfl⟩ : syracuseStep 606563 = 909845) B909845
theorem B770417 : Blo 267823 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B410113 : Blo 267823 410113 := bstep (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) B307585
theorem B410161 : Blo 267823 410161 := bstep (se 2 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 410161 = 307621) B307621
theorem B606833 : Blo 267823 606833 := bstep (se 2 (by rfl) ⟨227562, by rfl⟩ : syracuseStep 606833 = 455125) B455125
theorem B606851 : Blo 267823 606851 := bstep (se 1 (by rfl) ⟨455138, by rfl⟩ : syracuseStep 606851 = 910277) B910277
theorem B508675 : Blo 267823 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B607121 : Blo 267823 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B508835 : Blo 267823 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B607139 : Blo 267823 607139 := bstep (se 1 (by rfl) ⟨455354, by rfl⟩ : syracuseStep 607139 = 910709) B910709
theorem B345043 : Blo 267823 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B967793 : Blo 267823 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B574627 : Blo 267823 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B607409 : Blo 267823 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B607427 : Blo 267823 607427 := bstep (se 1 (by rfl) ⟨455570, by rfl⟩ : syracuseStep 607427 = 911141) B911141
theorem B1557701 : Blo 267823 1557701 := bstep (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) B292069
theorem B1361123 : Blo 267823 1361123 := bstep (se 1 (by rfl) ⟨1020842, by rfl⟩ : syracuseStep 1361123 = 2041685) B2041685
theorem B771373 : Blo 267823 771373 := bstep (se 3 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 771373 = 289265) B289265
theorem B2311523 : Blo 267823 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B607697 : Blo 267823 607697 := bstep (se 2 (by rfl) ⟨227886, by rfl⟩ : syracuseStep 607697 = 455773) B455773
theorem B607715 : Blo 267823 607715 := bstep (se 1 (by rfl) ⟨455786, by rfl⟩ : syracuseStep 607715 = 911573) B911573
theorem B771601 : Blo 267823 771601 := bstep (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) B578701
theorem B771761 : Blo 267823 771761 := bstep (se 2 (by rfl) ⟨289410, by rfl⟩ : syracuseStep 771761 = 578821) B578821
theorem B607985 : Blo 267823 607985 := bstep (se 2 (by rfl) ⟨227994, by rfl⟩ : syracuseStep 607985 = 455989) B455989
theorem B608003 : Blo 267823 608003 := bstep (se 1 (by rfl) ⟨456002, by rfl⟩ : syracuseStep 608003 = 912005) B912005
theorem B771875 : Blo 267823 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B1722161 : Blo 267823 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B509905 : Blo 267823 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B2639843 : Blo 267823 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B870385 : Blo 267823 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B1361933 : Blo 267823 1361933 := bstep (se 3 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 1361933 = 510725) B510725
theorem B608273 : Blo 267823 608273 := bstep (se 2 (by rfl) ⟨228102, by rfl⟩ : syracuseStep 608273 = 456205) B456205
theorem B608291 : Blo 267823 608291 := bstep (se 1 (by rfl) ⟨456218, by rfl⟩ : syracuseStep 608291 = 912437) B912437
theorem B870563 : Blo 267823 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B1460429 : Blo 267823 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B3786979 : Blo 267823 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B411889 : Blo 267823 411889 := bstep (se 2 (by rfl) ⟨154458, by rfl⟩ : syracuseStep 411889 = 308917) B308917
theorem B608561 : Blo 267823 608561 := bstep (se 2 (by rfl) ⟨228210, by rfl⟩ : syracuseStep 608561 = 456421) B456421
theorem B608579 : Blo 267823 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B608849 : Blo 267823 608849 := bstep (se 2 (by rfl) ⟨228318, by rfl⟩ : syracuseStep 608849 = 456637) B456637
theorem B608867 : Blo 267823 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B1526435 : Blo 267823 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B871117 : Blo 267823 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B772877 : Blo 267823 772877 := bstep (se 3 (by rfl) ⟨144914, by rfl⟩ : syracuseStep 772877 = 289829) B289829
theorem B904013 : Blo 267823 904013 := bstep (se 3 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 904013 = 339005) B339005
theorem B609137 : Blo 267823 609137 := bstep (se 2 (by rfl) ⟨228426, by rfl⟩ : syracuseStep 609137 = 456853) B456853
theorem B904067 : Blo 267823 904067 := bstep (se 1 (by rfl) ⟨678050, by rfl⟩ : syracuseStep 904067 = 1356101) B1356101
theorem B609155 : Blo 267823 609155 := bstep (se 1 (by rfl) ⟨456866, by rfl⟩ : syracuseStep 609155 = 913733) B913733
theorem B773059 : Blo 267823 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B412643 : Blo 267823 412643 := bstep (se 1 (by rfl) ⟨309482, by rfl⟩ : syracuseStep 412643 = 618965) B618965
theorem B510961 : Blo 267823 510961 := bstep (se 2 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 510961 = 383221) B383221
theorem B576497 : Blo 267823 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B412705 : Blo 267823 412705 := bstep (se 2 (by rfl) ⟨154764, by rfl⟩ : syracuseStep 412705 = 309529) B309529
theorem B773219 : Blo 267823 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B904337 : Blo 267823 904337 := bstep (se 2 (by rfl) ⟨339126, by rfl⟩ : syracuseStep 904337 = 678253) B678253
theorem B609425 : Blo 267823 609425 := bstep (se 2 (by rfl) ⟨228534, by rfl⟩ : syracuseStep 609425 = 457069) B457069
theorem B609443 : Blo 267823 609443 := bstep (se 1 (by rfl) ⟨457082, by rfl⟩ : syracuseStep 609443 = 914165) B914165
theorem B511363 : Blo 267823 511363 := bstep (se 1 (by rfl) ⟨383522, by rfl⟩ : syracuseStep 511363 = 767045) B767045
theorem B511409 : Blo 267823 511409 := bstep (se 2 (by rfl) ⟨191778, by rfl⟩ : syracuseStep 511409 = 383557) B383557
theorem B609713 : Blo 267823 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B609731 : Blo 267823 609731 := bstep (se 1 (by rfl) ⟨457298, by rfl⟩ : syracuseStep 609731 = 914597) B914597
theorem B773677 : Blo 267823 773677 := bstep (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) B290129
theorem B4574773 : Blo 267823 4574773 := bstep (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) B428885
theorem B1527437 : Blo 267823 1527437 := bstep (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) B572789
theorem B1756835 : Blo 267823 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B904877 : Blo 267823 904877 := bstep (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) B339329
theorem B511697 : Blo 267823 511697 := bstep (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) B383773
theorem B610001 : Blo 267823 610001 := bstep (se 2 (by rfl) ⟨228750, by rfl⟩ : syracuseStep 610001 = 457501) B457501
theorem B904931 : Blo 267823 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B610019 : Blo 267823 610019 := bstep (se 1 (by rfl) ⟨457514, by rfl⟩ : syracuseStep 610019 = 915029) B915029
theorem B577361 : Blo 267823 577361 := bstep (se 2 (by rfl) ⟨216510, by rfl⟩ : syracuseStep 577361 = 433021) B433021
theorem B1462157 : Blo 267823 1462157 := bstep (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) B548309
theorem B2641805 : Blo 267823 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B905201 : Blo 267823 905201 := bstep (se 2 (by rfl) ⟨339450, by rfl⟩ : syracuseStep 905201 = 678901) B678901
theorem B610289 : Blo 267823 610289 := bstep (se 2 (by rfl) ⟨228858, by rfl⟩ : syracuseStep 610289 = 457717) B457717
theorem B610307 : Blo 267823 610307 := bstep (se 1 (by rfl) ⟨457730, by rfl⟩ : syracuseStep 610307 = 915461) B915461
theorem B1101937 : Blo 267823 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B2904245 : Blo 267823 2904245 := bstep (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) B272273
theorem B1069283 : Blo 267823 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B2937073 : Blo 267823 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B610577 : Blo 267823 610577 := bstep (se 2 (by rfl) ⟨228966, by rfl⟩ : syracuseStep 610577 = 457933) B457933
theorem B610595 : Blo 267823 610595 := bstep (se 1 (by rfl) ⟨457946, by rfl⟩ : syracuseStep 610595 = 915893) B915893
theorem B3297635 : Blo 267823 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B512419 : Blo 267823 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B905741 : Blo 267823 905741 := bstep (se 3 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 905741 = 339653) B339653
theorem B610865 : Blo 267823 610865 := bstep (se 2 (by rfl) ⟨229074, by rfl⟩ : syracuseStep 610865 = 458149) B458149
theorem B905795 : Blo 267823 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B610883 : Blo 267823 610883 := bstep (se 1 (by rfl) ⟨458162, by rfl⟩ : syracuseStep 610883 = 916325) B916325
theorem B1725133 : Blo 267823 1725133 := bstep (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) B646925
theorem B1168141 : Blo 267823 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B643889 : Blo 267823 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B381763 : Blo 267823 381763 := bstep (se 1 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 381763 = 572645) B572645
theorem B906065 : Blo 267823 906065 := bstep (se 2 (by rfl) ⟨339774, by rfl⟩ : syracuseStep 906065 = 679549) B679549
theorem B611153 : Blo 267823 611153 := bstep (se 2 (by rfl) ⟨229182, by rfl⟩ : syracuseStep 611153 = 458365) B458365
theorem B512867 : Blo 267823 512867 := bstep (se 1 (by rfl) ⟨384650, by rfl⟩ : syracuseStep 512867 = 769301) B769301
theorem B611171 : Blo 267823 611171 := bstep (se 1 (by rfl) ⟨458378, by rfl⟩ : syracuseStep 611171 = 916757) B916757
theorem B1364849 : Blo 267823 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B578659 : Blo 267823 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B611441 : Blo 267823 611441 := bstep (se 2 (by rfl) ⟨229290, by rfl⟩ : syracuseStep 611441 = 458581) B458581
theorem B513155 : Blo 267823 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B611459 : Blo 267823 611459 := bstep (se 1 (by rfl) ⟨458594, by rfl⟩ : syracuseStep 611459 = 917189) B917189
theorem B382099 : Blo 267823 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B873635 : Blo 267823 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B3495221 : Blo 267823 3495221 := bstep (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) B327677
theorem B906605 : Blo 267823 906605 := bstep (se 3 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 906605 = 339977) B339977
theorem B644465 : Blo 267823 644465 := bstep (se 2 (by rfl) ⟨241674, by rfl⟩ : syracuseStep 644465 = 483349) B483349
theorem B906659 : Blo 267823 906659 := bstep (se 1 (by rfl) ⟨679994, by rfl⟩ : syracuseStep 906659 = 1359989) B1359989
theorem B644611 : Blo 267823 644611 := bstep (se 1 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 644611 = 966917) B966917
theorem B2184803 : Blo 267823 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B906929 : Blo 267823 906929 := bstep (se 2 (by rfl) ⟨340098, by rfl⟩ : syracuseStep 906929 = 680197) B680197
theorem B382657 : Blo 267823 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B382691 : Blo 267823 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B514097 : Blo 267823 514097 := bstep (se 2 (by rfl) ⟨192786, by rfl⟩ : syracuseStep 514097 = 385573) B385573
theorem B1300657 : Blo 267823 1300657 := bstep (se 2 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 1300657 = 975493) B975493
theorem B907469 : Blo 267823 907469 := bstep (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) B340301
theorem B907523 : Blo 267823 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B383249 : Blo 267823 383249 := bstep (se 2 (by rfl) ⟨143718, by rfl⟩ : syracuseStep 383249 = 287437) B287437
theorem B1366307 : Blo 267823 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B579889 : Blo 267823 579889 := bstep (se 2 (by rfl) ⟨217458, by rfl⟩ : syracuseStep 579889 = 434917) B434917
theorem B383329 : Blo 267823 383329 := bstep (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) B287497
theorem B1530353 : Blo 267823 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B3103217 : Blo 267823 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B907793 : Blo 267823 907793 := bstep (se 2 (by rfl) ⟨340422, by rfl⟩ : syracuseStep 907793 = 680845) B680845
theorem B678577 : Blo 267823 678577 := bstep (se 2 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 678577 = 508933) B508933
theorem B1858403 : Blo 267823 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B1727365 : Blo 267823 1727365 := bstep (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) B323881
theorem B514993 : Blo 267823 514993 := bstep (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) B386245
theorem B678851 : Blo 267823 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B580547 : Blo 267823 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B3300365 : Blo 267823 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B908333 : Blo 267823 908333 := bstep (se 3 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 908333 = 340625) B340625
theorem B1367117 : Blo 267823 1367117 := bstep (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) B512669
theorem B515153 : Blo 267823 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B908387 : Blo 267823 908387 := bstep (se 1 (by rfl) ⟨681290, by rfl⟩ : syracuseStep 908387 = 1362581) B1362581
theorem B384115 : Blo 267823 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B679043 : Blo 267823 679043 := bstep (se 1 (by rfl) ⟨509282, by rfl⟩ : syracuseStep 679043 = 1018565) B1018565
theorem B908657 : Blo 267823 908657 := bstep (se 2 (by rfl) ⟨340746, by rfl⟩ : syracuseStep 908657 = 681493) B681493
theorem B3300749 : Blo 267823 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B515555 : Blo 267823 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B384593 : Blo 267823 384593 := bstep (se 2 (by rfl) ⟨144222, by rfl⟩ : syracuseStep 384593 = 288445) B288445
theorem B2055779 : Blo 267823 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B384707 : Blo 267823 384707 := bstep (se 1 (by rfl) ⟨288530, by rfl⟩ : syracuseStep 384707 = 577061) B577061
theorem B384787 : Blo 267823 384787 := bstep (se 1 (by rfl) ⟨288590, by rfl⟩ : syracuseStep 384787 = 577181) B577181
theorem B450355 : Blo 267823 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B909197 : Blo 267823 909197 := bstep (se 3 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 909197 = 340949) B340949
theorem B1531811 : Blo 267823 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B3694517 : Blo 267823 3694517 := bstep (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) B346361
theorem B909251 : Blo 267823 909251 := bstep (se 1 (by rfl) ⟨681938, by rfl⟩ : syracuseStep 909251 = 1363877) B1363877
theorem B417793 : Blo 267823 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B679985 : Blo 267823 679985 := bstep (se 2 (by rfl) ⟨254994, by rfl⟩ : syracuseStep 679985 = 509989) B509989
theorem B1564721 : Blo 267823 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B680035 : Blo 267823 680035 := bstep (se 1 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 680035 = 1020053) B1020053
theorem B909521 : Blo 267823 909521 := bstep (se 2 (by rfl) ⟨341070, by rfl⟩ : syracuseStep 909521 = 682141) B682141
theorem B680177 : Blo 267823 680177 := bstep (se 2 (by rfl) ⟨255066, by rfl⟩ : syracuseStep 680177 = 510133) B510133
theorem B385345 : Blo 267823 385345 := bstep (se 2 (by rfl) ⟨144504, by rfl⟩ : syracuseStep 385345 = 289009) B289009
theorem B287155 : Blo 267823 287155 := bstep (se 1 (by rfl) ⟨215366, by rfl⟩ : syracuseStep 287155 = 430733) B430733
theorem B2187917 : Blo 267823 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B910061 : Blo 267823 910061 := bstep (se 3 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 910061 = 341273) B341273
theorem B910115 : Blo 267823 910115 := bstep (se 1 (by rfl) ⟨682586, by rfl⟩ : syracuseStep 910115 = 1365173) B1365173
theorem B287587 : Blo 267823 287587 := bstep (se 1 (by rfl) ⟨215690, by rfl⟩ : syracuseStep 287587 = 431381) B431381
theorem B386051 : Blo 267823 386051 := bstep (se 1 (by rfl) ⟨289538, by rfl⟩ : syracuseStep 386051 = 579077) B579077
theorem B910385 : Blo 267823 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B681169 : Blo 267823 681169 := bstep (se 2 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 681169 = 510877) B510877
theorem B2319587 : Blo 267823 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B681443 : Blo 267823 681443 := bstep (se 1 (by rfl) ⟨511082, by rfl⟩ : syracuseStep 681443 = 1022165) B1022165
theorem B452081 : Blo 267823 452081 := bstep (se 2 (by rfl) ⟨169530, by rfl⟩ : syracuseStep 452081 = 339061) B339061
theorem B550385 : Blo 267823 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B910925 : Blo 267823 910925 := bstep (se 3 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 910925 = 341597) B341597
theorem B452209 : Blo 267823 452209 := bstep (se 2 (by rfl) ⟨169578, by rfl⟩ : syracuseStep 452209 = 339157) B339157
theorem B386689 : Blo 267823 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B910979 : Blo 267823 910979 := bstep (se 1 (by rfl) ⟨683234, by rfl⟩ : syracuseStep 910979 = 1366469) B1366469
theorem B452243 : Blo 267823 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B681635 : Blo 267823 681635 := bstep (se 1 (by rfl) ⟨511226, by rfl⟩ : syracuseStep 681635 = 1022453) B1022453
theorem B3106531 : Blo 267823 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B386803 : Blo 267823 386803 := bstep (se 1 (by rfl) ⟨290102, by rfl⟩ : syracuseStep 386803 = 580205) B580205
theorem B452371 : Blo 267823 452371 := bstep (se 1 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 452371 = 678557) B678557
theorem B911249 : Blo 267823 911249 := bstep (se 2 (by rfl) ⟨341718, by rfl⟩ : syracuseStep 911249 = 683437) B683437
theorem B452513 : Blo 267823 452513 := bstep (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) B339385
theorem B1370033 : Blo 267823 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B452641 : Blo 267823 452641 := bstep (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) B339481
theorem B452675 : Blo 267823 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B288851 : Blo 267823 288851 := bstep (se 1 (by rfl) ⟨216638, by rfl⟩ : syracuseStep 288851 = 433277) B433277
theorem B452803 : Blo 267823 452803 := bstep (se 1 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 452803 = 679205) B679205
theorem B6187205 : Blo 267823 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1239245 : Blo 267823 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B452945 : Blo 267823 452945 := bstep (se 2 (by rfl) ⟨169854, by rfl⟩ : syracuseStep 452945 = 339709) B339709
theorem B780653 : Blo 267823 780653 := bstep (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) B292745
theorem B911789 : Blo 267823 911789 := bstep (se 3 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 911789 = 341921) B341921
theorem B453073 : Blo 267823 453073 := bstep (se 2 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 453073 = 339805) B339805
theorem B911843 : Blo 267823 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B944621 : Blo 267823 944621 := bstep (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) B354233
theorem B453107 : Blo 267823 453107 := bstep (se 1 (by rfl) ⟨339830, by rfl⟩ : syracuseStep 453107 = 679661) B679661
theorem B682577 : Blo 267823 682577 := bstep (se 2 (by rfl) ⟨255966, by rfl⟩ : syracuseStep 682577 = 511933) B511933
theorem B453235 : Blo 267823 453235 := bstep (se 1 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 453235 = 679853) B679853
theorem B682627 : Blo 267823 682627 := bstep (se 1 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 682627 = 1023941) B1023941
theorem B1305229 : Blo 267823 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B912113 : Blo 267823 912113 := bstep (se 2 (by rfl) ⟨342042, by rfl⟩ : syracuseStep 912113 = 684085) B684085
theorem B453377 : Blo 267823 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B682769 : Blo 267823 682769 := bstep (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) B512077
theorem B289603 : Blo 267823 289603 := bstep (se 1 (by rfl) ⟨217202, by rfl⟩ : syracuseStep 289603 = 434405) B434405
theorem B453505 : Blo 267823 453505 := bstep (se 2 (by rfl) ⟨170064, by rfl⟩ : syracuseStep 453505 = 340129) B340129
theorem B453539 : Blo 267823 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B1633229 : Blo 267823 1633229 := bstep (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) B612461
theorem B2190349 : Blo 267823 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B322579 : Blo 267823 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B453667 : Blo 267823 453667 := bstep (se 1 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 453667 = 680501) B680501
theorem B453809 : Blo 267823 453809 := bstep (se 2 (by rfl) ⟨170178, by rfl⟩ : syracuseStep 453809 = 340357) B340357
theorem B322771 : Blo 267823 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B912653 : Blo 267823 912653 := bstep (se 3 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 912653 = 342245) B342245
theorem B650531 : Blo 267823 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B453937 : Blo 267823 453937 := bstep (se 2 (by rfl) ⟨170226, by rfl⟩ : syracuseStep 453937 = 340453) B340453
theorem B912707 : Blo 267823 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B453971 : Blo 267823 453971 := bstep (se 1 (by rfl) ⟨340478, by rfl⟩ : syracuseStep 453971 = 680957) B680957
theorem B1371491 : Blo 267823 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B454099 : Blo 267823 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B912977 : Blo 267823 912977 := bstep (se 2 (by rfl) ⟨342366, by rfl⟩ : syracuseStep 912977 = 684733) B684733
theorem B323155 : Blo 267823 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B454241 : Blo 267823 454241 := bstep (se 2 (by rfl) ⟨170340, by rfl⟩ : syracuseStep 454241 = 340681) B340681
theorem B454369 : Blo 267823 454369 := bstep (se 2 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 454369 = 340777) B340777
theorem B683761 : Blo 267823 683761 := bstep (se 2 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 683761 = 512821) B512821
theorem B454403 : Blo 267823 454403 := bstep (se 1 (by rfl) ⟨340802, by rfl⟩ : syracuseStep 454403 = 681605) B681605
theorem B454531 : Blo 267823 454531 := bstep (se 1 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 454531 = 681797) B681797
theorem B1470449 : Blo 267823 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B684035 : Blo 267823 684035 := bstep (se 1 (by rfl) ⟨513026, by rfl⟩ : syracuseStep 684035 = 1026053) B1026053
theorem B454673 : Blo 267823 454673 := bstep (se 2 (by rfl) ⟨170502, by rfl⟩ : syracuseStep 454673 = 341005) B341005
theorem B815153 : Blo 267823 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B618545 : Blo 267823 618545 := bstep (se 2 (by rfl) ⟨231954, by rfl⟩ : syracuseStep 618545 = 463909) B463909
theorem B913517 : Blo 267823 913517 := bstep (se 3 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 913517 = 342569) B342569
theorem B651377 : Blo 267823 651377 := bstep (se 2 (by rfl) ⟨244266, by rfl⟩ : syracuseStep 651377 = 488533) B488533
theorem B1372301 : Blo 267823 1372301 := bstep (se 3 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 1372301 = 514613) B514613
theorem B454801 : Blo 267823 454801 := bstep (se 2 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 454801 = 341101) B341101
theorem B913571 : Blo 267823 913571 := bstep (se 1 (by rfl) ⟨685178, by rfl⟩ : syracuseStep 913571 = 1370357) B1370357
theorem B454835 : Blo 267823 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B684227 : Blo 267823 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B323843 : Blo 267823 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B782627 : Blo 267823 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B454963 : Blo 267823 454963 := bstep (se 1 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 454963 = 682445) B682445
theorem B913841 : Blo 267823 913841 := bstep (se 2 (by rfl) ⟨342690, by rfl⟩ : syracuseStep 913841 = 685381) B685381
theorem B455105 : Blo 267823 455105 := bstep (se 2 (by rfl) ⟨170664, by rfl⟩ : syracuseStep 455105 = 341329) B341329
theorem B455233 : Blo 267823 455233 := bstep (se 2 (by rfl) ⟨170712, by rfl⟩ : syracuseStep 455233 = 341425) B341425
theorem B586321 : Blo 267823 586321 := bstep (se 2 (by rfl) ⟨219870, by rfl⟩ : syracuseStep 586321 = 439741) B439741
theorem B455267 : Blo 267823 455267 := bstep (se 1 (by rfl) ⟨341450, by rfl⟩ : syracuseStep 455267 = 682901) B682901
theorem B488035 : Blo 267823 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B455395 : Blo 267823 455395 := bstep (se 1 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 455395 = 683093) B683093
theorem B2061125 : Blo 267823 2061125 := bstep (se 4 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 2061125 = 386461) B386461
theorem B455537 : Blo 267823 455537 := bstep (se 2 (by rfl) ⟨170826, by rfl⟩ : syracuseStep 455537 = 341653) B341653
theorem B914381 : Blo 267823 914381 := bstep (se 3 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 914381 = 342893) B342893
theorem B455665 : Blo 267823 455665 := bstep (se 2 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 455665 = 341749) B341749
theorem B914435 : Blo 267823 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B455699 : Blo 267823 455699 := bstep (se 1 (by rfl) ⟨341774, by rfl⟩ : syracuseStep 455699 = 683549) B683549
theorem B685169 : Blo 267823 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B455827 : Blo 267823 455827 := bstep (se 1 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 455827 = 683741) B683741
theorem B685219 : Blo 267823 685219 := bstep (se 1 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 685219 = 1027829) B1027829
theorem B914705 : Blo 267823 914705 := bstep (se 2 (by rfl) ⟨343014, by rfl⟩ : syracuseStep 914705 = 686029) B686029
theorem B455969 : Blo 267823 455969 := bstep (se 2 (by rfl) ⟨170988, by rfl⟩ : syracuseStep 455969 = 341977) B341977
theorem B685361 : Blo 267823 685361 := bstep (se 2 (by rfl) ⟨257010, by rfl⟩ : syracuseStep 685361 = 514021) B514021
theorem B2913677 : Blo 267823 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B456097 : Blo 267823 456097 := bstep (se 2 (by rfl) ⟨171036, by rfl⟩ : syracuseStep 456097 = 342073) B342073
theorem B456131 : Blo 267823 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B456259 : Blo 267823 456259 := bstep (se 1 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 456259 = 684389) B684389
theorem B456401 : Blo 267823 456401 := bstep (se 2 (by rfl) ⟨171150, by rfl⟩ : syracuseStep 456401 = 342301) B342301
theorem B915245 : Blo 267823 915245 := bstep (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) B343217
theorem B456529 : Blo 267823 456529 := bstep (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) B342397
theorem B915299 : Blo 267823 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B456563 : Blo 267823 456563 := bstep (se 1 (by rfl) ⟨342422, by rfl⟩ : syracuseStep 456563 = 684845) B684845
theorem B587665 : Blo 267823 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B1832867 : Blo 267823 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B456691 : Blo 267823 456691 := bstep (se 1 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 456691 = 685037) B685037
theorem B2488333 : Blo 267823 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B915569 : Blo 267823 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B456833 : Blo 267823 456833 := bstep (se 2 (by rfl) ⟨171312, by rfl⟩ : syracuseStep 456833 = 342625) B342625
theorem B489649 : Blo 267823 489649 := bstep (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) B367237
theorem B456961 : Blo 267823 456961 := bstep (se 2 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 456961 = 342721) B342721
theorem B686353 : Blo 267823 686353 := bstep (se 2 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 686353 = 514765) B514765
theorem B456995 : Blo 267823 456995 := bstep (se 1 (by rfl) ⟨342746, by rfl⟩ : syracuseStep 456995 = 685493) B685493
theorem B1571185 : Blo 267823 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B457123 : Blo 267823 457123 := bstep (se 1 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 457123 = 685685) B685685
theorem B1735181 : Blo 267823 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B686627 : Blo 267823 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B1374769 : Blo 267823 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B457265 : Blo 267823 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B916109 : Blo 267823 916109 := bstep (se 3 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 916109 = 343541) B343541
theorem B457393 : Blo 267823 457393 := bstep (se 2 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 457393 = 343045) B343045
theorem B916163 : Blo 267823 916163 := bstep (se 1 (by rfl) ⟨687122, by rfl⟩ : syracuseStep 916163 = 1374245) B1374245
theorem B457427 : Blo 267823 457427 := bstep (se 1 (by rfl) ⟨343070, by rfl⟩ : syracuseStep 457427 = 686141) B686141
theorem B686819 : Blo 267823 686819 := bstep (se 1 (by rfl) ⟨515114, by rfl⟩ : syracuseStep 686819 = 1030229) B1030229
theorem B457555 : Blo 267823 457555 := bstep (se 1 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 457555 = 686333) B686333
theorem B916433 : Blo 267823 916433 := bstep (se 2 (by rfl) ⟨343662, by rfl⟩ : syracuseStep 916433 = 687325) B687325
theorem B457697 : Blo 267823 457697 := bstep (se 2 (by rfl) ⟨171636, by rfl⟩ : syracuseStep 457697 = 343273) B343273
theorem B1375217 : Blo 267823 1375217 := bstep (se 2 (by rfl) ⟨515706, by rfl⟩ : syracuseStep 1375217 = 1031413) B1031413
theorem B457825 : Blo 267823 457825 := bstep (se 2 (by rfl) ⟨171684, by rfl⟩ : syracuseStep 457825 = 343369) B343369
theorem B457859 : Blo 267823 457859 := bstep (se 1 (by rfl) ⟨343394, by rfl⟩ : syracuseStep 457859 = 686789) B686789
theorem B457987 : Blo 267823 457987 := bstep (se 1 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 457987 = 686981) B686981
theorem B1146125 : Blo 267823 1146125 := bstep (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) B429797
theorem B458129 : Blo 267823 458129 := bstep (se 2 (by rfl) ⟨171798, by rfl⟩ : syracuseStep 458129 = 343597) B343597
theorem B916973 : Blo 267823 916973 := bstep (se 3 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 916973 = 343865) B343865
theorem B458257 : Blo 267823 458257 := bstep (se 2 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 458257 = 343693) B343693
theorem B917027 : Blo 267823 917027 := bstep (se 1 (by rfl) ⟨687770, by rfl⟩ : syracuseStep 917027 = 1375541) B1375541
theorem B458291 : Blo 267823 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B2620997 : Blo 267823 2620997 := bstep (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) B491437
theorem B1146467 : Blo 267823 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B2817677 : Blo 267823 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B687761 : Blo 267823 687761 := bstep (se 2 (by rfl) ⟨257910, by rfl⟩ : syracuseStep 687761 = 515821) B515821
theorem B458419 : Blo 267823 458419 := bstep (se 1 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 458419 = 687629) B687629
theorem B687811 : Blo 267823 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B917297 : Blo 267823 917297 := bstep (se 2 (by rfl) ⟨343986, by rfl⟩ : syracuseStep 917297 = 687973) B687973
theorem B458561 : Blo 267823 458561 := bstep (se 2 (by rfl) ⟨171960, by rfl⟩ : syracuseStep 458561 = 343921) B343921
theorem B687953 : Blo 267823 687953 := bstep (se 2 (by rfl) ⟨257982, by rfl⟩ : syracuseStep 687953 = 515965) B515965
theorem B491377 : Blo 267823 491377 := bstep (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) B368533
theorem B458689 : Blo 267823 458689 := bstep (se 2 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 458689 = 344017) B344017
theorem B557057 : Blo 267823 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B2851421 : Blo 267823 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1541015 : Blo 267823 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B3277745 : Blo 267823 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B1148107 : Blo 267823 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B525569 : Blo 267823 525569 := bstep (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) B394177
theorem B1017305 : Blo 267823 1017305 := bstep (se 2 (by rfl) ⟨381489, by rfl⟩ : syracuseStep 1017305 = 762979) B762979
theorem B1148381 : Blo 267823 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B493249 : Blo 267823 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B1017623 : Blo 267823 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B460939 : Blo 267823 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B1181969 : Blo 267823 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B3869045 : Blo 267823 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B1018291 : Blo 267823 1018291 := bstep (se 1 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 1018291 = 1527437) B1527437
theorem B1936163 : Blo 267823 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B2198423 : Blo 267823 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B5049305 : Blo 267823 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1740305 : Blo 267823 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B2330147 : Blo 267823 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B429643 : Blo 267823 429643 := bstep (se 1 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 429643 = 644465) B644465
theorem B1019537 : Blo 267823 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B2920465 : Blo 267823 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B430105 : Blo 267823 430105 := bstep (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) B322579
theorem B921689 : Blo 267823 921689 := bstep (se 2 (by rfl) ⟨345633, by rfl⟩ : syracuseStep 921689 = 691267) B691267
theorem B18583829 : Blo 267823 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B430361 : Blo 267823 430361 := bstep (se 2 (by rfl) ⟨161385, by rfl⟩ : syracuseStep 430361 = 322771) B322771
theorem B1020235 : Blo 267823 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B2068811 : Blo 267823 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1020509 : Blo 267823 1020509 := bstep (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) B382691
theorem B2200243 : Blo 267823 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B6099697 : Blo 267823 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B463703 : Blo 267823 463703 := bstep (se 1 (by rfl) ⟨347777, by rfl⟩ : syracuseStep 463703 = 695555) B695555
theorem B2200499 : Blo 267823 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B1840229 : Blo 267823 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B1021207 : Blo 267823 1021207 := bstep (se 1 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 1021207 = 1531811) B1531811
theorem B2463011 : Blo 267823 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B2201093 : Blo 267823 2201093 := bstep (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) B412705
theorem B2299427 : Blo 267823 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B267831 : Blo 267823 267831 := bstep (se 1 (by rfl) ⟨200873, by rfl⟩ : syracuseStep 267831 = 401747) B401747
theorem B267851 : Blo 267823 267851 := bstep (se 1 (by rfl) ⟨200888, by rfl⟩ : syracuseStep 267851 = 401777) B401777
theorem B267863 : Blo 267823 267863 := bstep (se 1 (by rfl) ⟨200897, by rfl⟩ : syracuseStep 267863 = 401795) B401795
theorem B267883 : Blo 267823 267883 := bstep (se 1 (by rfl) ⟨200912, by rfl⟩ : syracuseStep 267883 = 401825) B401825
theorem B267895 : Blo 267823 267895 := bstep (se 1 (by rfl) ⟨200921, by rfl⟩ : syracuseStep 267895 = 401843) B401843
theorem B267915 : Blo 267823 267915 := bstep (se 1 (by rfl) ⟨200936, by rfl⟩ : syracuseStep 267915 = 401873) B401873
theorem B267927 : Blo 267823 267927 := bstep (se 1 (by rfl) ⟨200945, by rfl⟩ : syracuseStep 267927 = 401891) B401891
theorem B267947 : Blo 267823 267947 := bstep (se 1 (by rfl) ⟨200960, by rfl⟩ : syracuseStep 267947 = 401921) B401921
theorem B267959 : Blo 267823 267959 := bstep (se 1 (by rfl) ⟨200969, by rfl⟩ : syracuseStep 267959 = 401939) B401939
theorem B267979 : Blo 267823 267979 := bstep (se 1 (by rfl) ⟨200984, by rfl⟩ : syracuseStep 267979 = 401969) B401969
theorem B267991 : Blo 267823 267991 := bstep (se 1 (by rfl) ⟨200993, by rfl⟩ : syracuseStep 267991 = 401987) B401987
theorem B268011 : Blo 267823 268011 := bstep (se 1 (by rfl) ⟨201008, by rfl⟩ : syracuseStep 268011 = 402017) B402017
theorem B268023 : Blo 267823 268023 := bstep (se 1 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 268023 = 402035) B402035
theorem B268043 : Blo 267823 268043 := bstep (se 1 (by rfl) ⟨201032, by rfl⟩ : syracuseStep 268043 = 402065) B402065
theorem B268055 : Blo 267823 268055 := bstep (se 1 (by rfl) ⟨201041, by rfl⟩ : syracuseStep 268055 = 402083) B402083
theorem B268075 : Blo 267823 268075 := bstep (se 1 (by rfl) ⟨201056, by rfl⟩ : syracuseStep 268075 = 402113) B402113
theorem B268087 : Blo 267823 268087 := bstep (se 1 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 268087 = 402131) B402131
theorem B268107 : Blo 267823 268107 := bstep (se 1 (by rfl) ⟨201080, by rfl⟩ : syracuseStep 268107 = 402161) B402161
theorem B268119 : Blo 267823 268119 := bstep (se 1 (by rfl) ⟨201089, by rfl⟩ : syracuseStep 268119 = 402179) B402179
theorem B268139 : Blo 267823 268139 := bstep (se 1 (by rfl) ⟨201104, by rfl⟩ : syracuseStep 268139 = 402209) B402209
theorem B268151 : Blo 267823 268151 := bstep (se 1 (by rfl) ⟨201113, by rfl⟩ : syracuseStep 268151 = 402227) B402227
theorem B268171 : Blo 267823 268171 := bstep (se 1 (by rfl) ⟨201128, by rfl⟩ : syracuseStep 268171 = 402257) B402257
theorem B268183 : Blo 267823 268183 := bstep (se 1 (by rfl) ⟨201137, by rfl⟩ : syracuseStep 268183 = 402275) B402275
theorem B268203 : Blo 267823 268203 := bstep (se 1 (by rfl) ⟨201152, by rfl⟩ : syracuseStep 268203 = 402305) B402305
theorem B268215 : Blo 267823 268215 := bstep (se 1 (by rfl) ⟨201161, by rfl⟩ : syracuseStep 268215 = 402323) B402323
theorem B268235 : Blo 267823 268235 := bstep (se 1 (by rfl) ⟨201176, by rfl⟩ : syracuseStep 268235 = 402353) B402353
theorem B268247 : Blo 267823 268247 := bstep (se 1 (by rfl) ⟨201185, by rfl⟩ : syracuseStep 268247 = 402371) B402371
theorem B268267 : Blo 267823 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B268279 : Blo 267823 268279 := bstep (se 1 (by rfl) ⟨201209, by rfl⟩ : syracuseStep 268279 = 402419) B402419
theorem B268299 : Blo 267823 268299 := bstep (se 1 (by rfl) ⟨201224, by rfl⟩ : syracuseStep 268299 = 402449) B402449
theorem B268311 : Blo 267823 268311 := bstep (se 1 (by rfl) ⟨201233, by rfl⟩ : syracuseStep 268311 = 402467) B402467
theorem B268331 : Blo 267823 268331 := bstep (se 1 (by rfl) ⟨201248, by rfl⟩ : syracuseStep 268331 = 402497) B402497
theorem B1021997 : Blo 267823 1021997 := bstep (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) B383249
theorem B268343 : Blo 267823 268343 := bstep (se 1 (by rfl) ⟨201257, by rfl⟩ : syracuseStep 268343 = 402515) B402515
theorem B268363 : Blo 267823 268363 := bstep (se 1 (by rfl) ⟨201272, by rfl⟩ : syracuseStep 268363 = 402545) B402545
theorem B268375 : Blo 267823 268375 := bstep (se 1 (by rfl) ⟨201281, by rfl⟩ : syracuseStep 268375 = 402563) B402563
theorem B268395 : Blo 267823 268395 := bstep (se 1 (by rfl) ⟨201296, by rfl⟩ : syracuseStep 268395 = 402593) B402593
theorem B268407 : Blo 267823 268407 := bstep (se 1 (by rfl) ⟨201305, by rfl⟩ : syracuseStep 268407 = 402611) B402611
theorem B268427 : Blo 267823 268427 := bstep (se 1 (by rfl) ⟨201320, by rfl⟩ : syracuseStep 268427 = 402641) B402641
theorem B268439 : Blo 267823 268439 := bstep (se 1 (by rfl) ⟨201329, by rfl⟩ : syracuseStep 268439 = 402659) B402659
theorem B1546391 : Blo 267823 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B268459 : Blo 267823 268459 := bstep (se 1 (by rfl) ⟨201344, by rfl⟩ : syracuseStep 268459 = 402689) B402689
theorem B268471 : Blo 267823 268471 := bstep (se 1 (by rfl) ⟨201353, by rfl⟩ : syracuseStep 268471 = 402707) B402707
theorem B1153217 : Blo 267823 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B268491 : Blo 267823 268491 := bstep (se 1 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 268491 = 402737) B402737
theorem B268503 : Blo 267823 268503 := bstep (se 1 (by rfl) ⟨201377, by rfl⟩ : syracuseStep 268503 = 402755) B402755
theorem B268523 : Blo 267823 268523 := bstep (se 1 (by rfl) ⟨201392, by rfl⟩ : syracuseStep 268523 = 402785) B402785
theorem B268535 : Blo 267823 268535 := bstep (se 1 (by rfl) ⟨201401, by rfl⟩ : syracuseStep 268535 = 402803) B402803
theorem B268555 : Blo 267823 268555 := bstep (se 1 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 268555 = 402833) B402833
theorem B2300177 : Blo 267823 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B268567 : Blo 267823 268567 := bstep (se 1 (by rfl) ⟨201425, by rfl⟩ : syracuseStep 268567 = 402851) B402851
theorem B268587 : Blo 267823 268587 := bstep (se 1 (by rfl) ⟨201440, by rfl⟩ : syracuseStep 268587 = 402881) B402881
theorem B268599 : Blo 267823 268599 := bstep (se 1 (by rfl) ⟨201449, by rfl⟩ : syracuseStep 268599 = 402899) B402899
theorem B301387 : Blo 267823 301387 := bstep (se 1 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 301387 = 452081) B452081
theorem B268619 : Blo 267823 268619 := bstep (se 1 (by rfl) ⟨201464, by rfl⟩ : syracuseStep 268619 = 402929) B402929
theorem B366923 : Blo 267823 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B268631 : Blo 267823 268631 := bstep (se 1 (by rfl) ⟨201473, by rfl⟩ : syracuseStep 268631 = 402947) B402947
theorem B1153369 : Blo 267823 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B268651 : Blo 267823 268651 := bstep (se 1 (by rfl) ⟨201488, by rfl⟩ : syracuseStep 268651 = 402977) B402977
theorem B268663 : Blo 267823 268663 := bstep (se 1 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 268663 = 402995) B402995
theorem B268683 : Blo 267823 268683 := bstep (se 1 (by rfl) ⟨201512, by rfl⟩ : syracuseStep 268683 = 403025) B403025
theorem B268695 : Blo 267823 268695 := bstep (se 1 (by rfl) ⟨201521, by rfl⟩ : syracuseStep 268695 = 403043) B403043
theorem B268715 : Blo 267823 268715 := bstep (se 1 (by rfl) ⟨201536, by rfl⟩ : syracuseStep 268715 = 403073) B403073
theorem B301495 : Blo 267823 301495 := bstep (se 1 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 301495 = 452243) B452243
theorem B268727 : Blo 267823 268727 := bstep (se 1 (by rfl) ⟨201545, by rfl⟩ : syracuseStep 268727 = 403091) B403091
theorem B268747 : Blo 267823 268747 := bstep (se 1 (by rfl) ⟨201560, by rfl⟩ : syracuseStep 268747 = 403121) B403121
theorem B268759 : Blo 267823 268759 := bstep (se 1 (by rfl) ⟨201569, by rfl⟩ : syracuseStep 268759 = 403139) B403139
theorem B268779 : Blo 267823 268779 := bstep (se 1 (by rfl) ⟨201584, by rfl⟩ : syracuseStep 268779 = 403169) B403169
theorem B268791 : Blo 267823 268791 := bstep (se 1 (by rfl) ⟨201593, by rfl⟩ : syracuseStep 268791 = 403187) B403187
theorem B268811 : Blo 267823 268811 := bstep (se 1 (by rfl) ⟨201608, by rfl⟩ : syracuseStep 268811 = 403217) B403217
theorem B268823 : Blo 267823 268823 := bstep (se 1 (by rfl) ⟨201617, by rfl⟩ : syracuseStep 268823 = 403235) B403235
theorem B268843 : Blo 267823 268843 := bstep (se 1 (by rfl) ⟨201632, by rfl⟩ : syracuseStep 268843 = 403265) B403265
theorem B268855 : Blo 267823 268855 := bstep (se 1 (by rfl) ⟨201641, by rfl⟩ : syracuseStep 268855 = 403283) B403283
theorem B268875 : Blo 267823 268875 := bstep (se 1 (by rfl) ⟨201656, by rfl⟩ : syracuseStep 268875 = 403313) B403313
theorem B268887 : Blo 267823 268887 := bstep (se 1 (by rfl) ⟨201665, by rfl⟩ : syracuseStep 268887 = 403331) B403331
theorem B301675 : Blo 267823 301675 := bstep (se 1 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 301675 = 452513) B452513
theorem B268907 : Blo 267823 268907 := bstep (se 1 (by rfl) ⟨201680, by rfl⟩ : syracuseStep 268907 = 403361) B403361
theorem B268919 : Blo 267823 268919 := bstep (se 1 (by rfl) ⟨201689, by rfl⟩ : syracuseStep 268919 = 403379) B403379
theorem B7740035 : Blo 267823 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B268939 : Blo 267823 268939 := bstep (se 1 (by rfl) ⟨201704, by rfl⟩ : syracuseStep 268939 = 403409) B403409
theorem B268951 : Blo 267823 268951 := bstep (se 1 (by rfl) ⟨201713, by rfl⟩ : syracuseStep 268951 = 403427) B403427
theorem B268971 : Blo 267823 268971 := bstep (se 1 (by rfl) ⟨201728, by rfl⟩ : syracuseStep 268971 = 403457) B403457
theorem B268983 : Blo 267823 268983 := bstep (se 1 (by rfl) ⟨201737, by rfl⟩ : syracuseStep 268983 = 403475) B403475
theorem B269003 : Blo 267823 269003 := bstep (se 1 (by rfl) ⟨201752, by rfl⟩ : syracuseStep 269003 = 403505) B403505
theorem B301783 : Blo 267823 301783 := bstep (se 1 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 301783 = 452675) B452675
theorem B269015 : Blo 267823 269015 := bstep (se 1 (by rfl) ⟨201761, by rfl⟩ : syracuseStep 269015 = 403523) B403523
theorem B269035 : Blo 267823 269035 := bstep (se 1 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 269035 = 403553) B403553
theorem B269047 : Blo 267823 269047 := bstep (se 1 (by rfl) ⟨201785, by rfl⟩ : syracuseStep 269047 = 403571) B403571
theorem B269067 : Blo 267823 269067 := bstep (se 1 (by rfl) ⟨201800, by rfl⟩ : syracuseStep 269067 = 403601) B403601
theorem B269079 : Blo 267823 269079 := bstep (se 1 (by rfl) ⟨201809, by rfl⟩ : syracuseStep 269079 = 403619) B403619
theorem B269099 : Blo 267823 269099 := bstep (se 1 (by rfl) ⟨201824, by rfl⟩ : syracuseStep 269099 = 403649) B403649
theorem B826163 : Blo 267823 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B269111 : Blo 267823 269111 := bstep (se 1 (by rfl) ⟨201833, by rfl⟩ : syracuseStep 269111 = 403667) B403667
theorem B269131 : Blo 267823 269131 := bstep (se 1 (by rfl) ⟨201848, by rfl⟩ : syracuseStep 269131 = 403697) B403697
theorem B269143 : Blo 267823 269143 := bstep (se 1 (by rfl) ⟨201857, by rfl⟩ : syracuseStep 269143 = 403715) B403715
theorem B269163 : Blo 267823 269163 := bstep (se 1 (by rfl) ⟨201872, by rfl⟩ : syracuseStep 269163 = 403745) B403745
theorem B269175 : Blo 267823 269175 := bstep (se 1 (by rfl) ⟨201881, by rfl⟩ : syracuseStep 269175 = 403763) B403763
theorem B301963 : Blo 267823 301963 := bstep (se 1 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 301963 = 452945) B452945
theorem B269195 : Blo 267823 269195 := bstep (se 1 (by rfl) ⟨201896, by rfl⟩ : syracuseStep 269195 = 403793) B403793
theorem B859031 : Blo 267823 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B269207 : Blo 267823 269207 := bstep (se 1 (by rfl) ⟨201905, by rfl⟩ : syracuseStep 269207 = 403811) B403811
theorem B269227 : Blo 267823 269227 := bstep (se 1 (by rfl) ⟨201920, by rfl⟩ : syracuseStep 269227 = 403841) B403841
theorem B269239 : Blo 267823 269239 := bstep (se 1 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 269239 = 403859) B403859
theorem B269259 : Blo 267823 269259 := bstep (se 1 (by rfl) ⟨201944, by rfl⟩ : syracuseStep 269259 = 403889) B403889
theorem B269271 : Blo 267823 269271 := bstep (se 1 (by rfl) ⟨201953, by rfl⟩ : syracuseStep 269271 = 403907) B403907
theorem B269291 : Blo 267823 269291 := bstep (se 1 (by rfl) ⟨201968, by rfl⟩ : syracuseStep 269291 = 403937) B403937
theorem B629747 : Blo 267823 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B302071 : Blo 267823 302071 := bstep (se 1 (by rfl) ⟨226553, by rfl⟩ : syracuseStep 302071 = 453107) B453107
theorem B269303 : Blo 267823 269303 := bstep (se 1 (by rfl) ⟨201977, by rfl⟩ : syracuseStep 269303 = 403955) B403955
theorem B269323 : Blo 267823 269323 := bstep (se 1 (by rfl) ⟨201992, by rfl⟩ : syracuseStep 269323 = 403985) B403985
theorem B269335 : Blo 267823 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B269355 : Blo 267823 269355 := bstep (se 1 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 269355 = 404033) B404033
theorem B269367 : Blo 267823 269367 := bstep (se 1 (by rfl) ⟨202025, by rfl⟩ : syracuseStep 269367 = 404051) B404051
theorem B859211 : Blo 267823 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B269387 : Blo 267823 269387 := bstep (se 1 (by rfl) ⟨202040, by rfl⟩ : syracuseStep 269387 = 404081) B404081
theorem B269399 : Blo 267823 269399 := bstep (se 1 (by rfl) ⟨202049, by rfl⟩ : syracuseStep 269399 = 404099) B404099
theorem B269419 : Blo 267823 269419 := bstep (se 1 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 269419 = 404129) B404129
theorem B269431 : Blo 267823 269431 := bstep (se 1 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 269431 = 404147) B404147
theorem B269451 : Blo 267823 269451 := bstep (se 1 (by rfl) ⟨202088, by rfl⟩ : syracuseStep 269451 = 404177) B404177
theorem B269463 : Blo 267823 269463 := bstep (se 1 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 269463 = 404195) B404195
theorem B302251 : Blo 267823 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B269483 : Blo 267823 269483 := bstep (se 1 (by rfl) ⟨202112, by rfl⟩ : syracuseStep 269483 = 404225) B404225
theorem B269495 : Blo 267823 269495 := bstep (se 1 (by rfl) ⟨202121, by rfl⟩ : syracuseStep 269495 = 404243) B404243
theorem B269515 : Blo 267823 269515 := bstep (se 1 (by rfl) ⟨202136, by rfl⟩ : syracuseStep 269515 = 404273) B404273
theorem B269527 : Blo 267823 269527 := bstep (se 1 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 269527 = 404291) B404291
theorem B269547 : Blo 267823 269547 := bstep (se 1 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 269547 = 404321) B404321
theorem B269559 : Blo 267823 269559 := bstep (se 1 (by rfl) ⟨202169, by rfl⟩ : syracuseStep 269559 = 404339) B404339
theorem B269579 : Blo 267823 269579 := bstep (se 1 (by rfl) ⟨202184, by rfl⟩ : syracuseStep 269579 = 404369) B404369
theorem B302359 : Blo 267823 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B269591 : Blo 267823 269591 := bstep (se 1 (by rfl) ⟨202193, by rfl⟩ : syracuseStep 269591 = 404387) B404387
theorem B269611 : Blo 267823 269611 := bstep (se 1 (by rfl) ⟨202208, by rfl⟩ : syracuseStep 269611 = 404417) B404417
theorem B1088819 : Blo 267823 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B269623 : Blo 267823 269623 := bstep (se 1 (by rfl) ⟨202217, by rfl⟩ : syracuseStep 269623 = 404435) B404435
theorem B269643 : Blo 267823 269643 := bstep (se 1 (by rfl) ⟨202232, by rfl⟩ : syracuseStep 269643 = 404465) B404465
theorem B269655 : Blo 267823 269655 := bstep (se 1 (by rfl) ⟨202241, by rfl⟩ : syracuseStep 269655 = 404483) B404483
theorem B859481 : Blo 267823 859481 := bstep (se 2 (by rfl) ⟨322305, by rfl⟩ : syracuseStep 859481 = 644611) B644611
theorem B269675 : Blo 267823 269675 := bstep (se 1 (by rfl) ⟨202256, by rfl⟩ : syracuseStep 269675 = 404513) B404513
theorem B269687 : Blo 267823 269687 := bstep (se 1 (by rfl) ⟨202265, by rfl⟩ : syracuseStep 269687 = 404531) B404531
theorem B269707 : Blo 267823 269707 := bstep (se 1 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 269707 = 404561) B404561
theorem B269719 : Blo 267823 269719 := bstep (se 1 (by rfl) ⟨202289, by rfl⟩ : syracuseStep 269719 = 404579) B404579
theorem B269739 : Blo 267823 269739 := bstep (se 1 (by rfl) ⟨202304, by rfl⟩ : syracuseStep 269739 = 404609) B404609
theorem B269751 : Blo 267823 269751 := bstep (se 1 (by rfl) ⟨202313, by rfl⟩ : syracuseStep 269751 = 404627) B404627
theorem B1023425 : Blo 267823 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B302539 : Blo 267823 302539 := bstep (se 1 (by rfl) ⟨226904, by rfl⟩ : syracuseStep 302539 = 453809) B453809
theorem B269771 : Blo 267823 269771 := bstep (se 1 (by rfl) ⟨202328, by rfl⟩ : syracuseStep 269771 = 404657) B404657
theorem B269783 : Blo 267823 269783 := bstep (se 1 (by rfl) ⟨202337, by rfl⟩ : syracuseStep 269783 = 404675) B404675
theorem B269803 : Blo 267823 269803 := bstep (se 1 (by rfl) ⟨202352, by rfl⟩ : syracuseStep 269803 = 404705) B404705
theorem B269815 : Blo 267823 269815 := bstep (se 1 (by rfl) ⟨202361, by rfl⟩ : syracuseStep 269815 = 404723) B404723
theorem B269835 : Blo 267823 269835 := bstep (se 1 (by rfl) ⟨202376, by rfl⟩ : syracuseStep 269835 = 404753) B404753
theorem B269847 : Blo 267823 269847 := bstep (se 1 (by rfl) ⟨202385, by rfl⟩ : syracuseStep 269847 = 404771) B404771
theorem B433687 : Blo 267823 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B269867 : Blo 267823 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B302647 : Blo 267823 302647 := bstep (se 1 (by rfl) ⟨226985, by rfl⟩ : syracuseStep 302647 = 453971) B453971
theorem B269879 : Blo 267823 269879 := bstep (se 1 (by rfl) ⟨202409, by rfl⟩ : syracuseStep 269879 = 404819) B404819
theorem B269899 : Blo 267823 269899 := bstep (se 1 (by rfl) ⟨202424, by rfl⟩ : syracuseStep 269899 = 404849) B404849
theorem B269911 : Blo 267823 269911 := bstep (se 1 (by rfl) ⟨202433, by rfl⟩ : syracuseStep 269911 = 404867) B404867
theorem B4955741 : Blo 267823 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B269931 : Blo 267823 269931 := bstep (se 1 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 269931 = 404897) B404897
theorem B269943 : Blo 267823 269943 := bstep (se 1 (by rfl) ⟨202457, by rfl⟩ : syracuseStep 269943 = 404915) B404915
theorem B269963 : Blo 267823 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B269975 : Blo 267823 269975 := bstep (se 1 (by rfl) ⟨202481, by rfl⟩ : syracuseStep 269975 = 404963) B404963
theorem B269995 : Blo 267823 269995 := bstep (se 1 (by rfl) ⟨202496, by rfl⟩ : syracuseStep 269995 = 404993) B404993
theorem B270007 : Blo 267823 270007 := bstep (se 1 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 270007 = 405011) B405011
theorem B270027 : Blo 267823 270027 := bstep (se 1 (by rfl) ⟨202520, by rfl⟩ : syracuseStep 270027 = 405041) B405041
theorem B270039 : Blo 267823 270039 := bstep (se 1 (by rfl) ⟨202529, by rfl⟩ : syracuseStep 270039 = 405059) B405059
theorem B302827 : Blo 267823 302827 := bstep (se 1 (by rfl) ⟨227120, by rfl⟩ : syracuseStep 302827 = 454241) B454241
theorem B270059 : Blo 267823 270059 := bstep (se 1 (by rfl) ⟨202544, by rfl⟩ : syracuseStep 270059 = 405089) B405089
theorem B270071 : Blo 267823 270071 := bstep (se 1 (by rfl) ⟨202553, by rfl⟩ : syracuseStep 270071 = 405107) B405107
theorem B270091 : Blo 267823 270091 := bstep (se 1 (by rfl) ⟨202568, by rfl⟩ : syracuseStep 270091 = 405137) B405137
theorem B270103 : Blo 267823 270103 := bstep (se 1 (by rfl) ⟨202577, by rfl⟩ : syracuseStep 270103 = 405155) B405155
theorem B270123 : Blo 267823 270123 := bstep (se 1 (by rfl) ⟨202592, by rfl⟩ : syracuseStep 270123 = 405185) B405185
theorem B270135 : Blo 267823 270135 := bstep (se 1 (by rfl) ⟨202601, by rfl⟩ : syracuseStep 270135 = 405203) B405203
theorem B270155 : Blo 267823 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B302935 : Blo 267823 302935 := bstep (se 1 (by rfl) ⟨227201, by rfl⟩ : syracuseStep 302935 = 454403) B454403
theorem B270167 : Blo 267823 270167 := bstep (se 1 (by rfl) ⟨202625, by rfl⟩ : syracuseStep 270167 = 405251) B405251
theorem B270187 : Blo 267823 270187 := bstep (se 1 (by rfl) ⟨202640, by rfl⟩ : syracuseStep 270187 = 405281) B405281
theorem B270199 : Blo 267823 270199 := bstep (se 1 (by rfl) ⟨202649, by rfl⟩ : syracuseStep 270199 = 405299) B405299
theorem B270219 : Blo 267823 270219 := bstep (se 1 (by rfl) ⟨202664, by rfl⟩ : syracuseStep 270219 = 405329) B405329
theorem B270231 : Blo 267823 270231 := bstep (se 1 (by rfl) ⟨202673, by rfl⟩ : syracuseStep 270231 = 405347) B405347
theorem B270251 : Blo 267823 270251 := bstep (se 1 (by rfl) ⟨202688, by rfl⟩ : syracuseStep 270251 = 405377) B405377
theorem B270263 : Blo 267823 270263 := bstep (se 1 (by rfl) ⟨202697, by rfl⟩ : syracuseStep 270263 = 405395) B405395
theorem B270283 : Blo 267823 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B270295 : Blo 267823 270295 := bstep (se 1 (by rfl) ⟨202721, by rfl⟩ : syracuseStep 270295 = 405443) B405443
theorem B270315 : Blo 267823 270315 := bstep (se 1 (by rfl) ⟨202736, by rfl⟩ : syracuseStep 270315 = 405473) B405473
theorem B270327 : Blo 267823 270327 := bstep (se 1 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 270327 = 405491) B405491
theorem B303115 : Blo 267823 303115 := bstep (se 1 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 303115 = 454673) B454673
theorem B270347 : Blo 267823 270347 := bstep (se 1 (by rfl) ⟨202760, by rfl⟩ : syracuseStep 270347 = 405521) B405521
theorem B3317777 : Blo 267823 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B270359 : Blo 267823 270359 := bstep (se 1 (by rfl) ⟨202769, by rfl⟩ : syracuseStep 270359 = 405539) B405539
theorem B270379 : Blo 267823 270379 := bstep (se 1 (by rfl) ⟨202784, by rfl⟩ : syracuseStep 270379 = 405569) B405569
theorem B270391 : Blo 267823 270391 := bstep (se 1 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 270391 = 405587) B405587
theorem B270411 : Blo 267823 270411 := bstep (se 1 (by rfl) ⟨202808, by rfl⟩ : syracuseStep 270411 = 405617) B405617
theorem B434251 : Blo 267823 434251 := bstep (se 1 (by rfl) ⟨325688, by rfl⟩ : syracuseStep 434251 = 651377) B651377
theorem B270423 : Blo 267823 270423 := bstep (se 1 (by rfl) ⟨202817, by rfl⟩ : syracuseStep 270423 = 405635) B405635
theorem B270443 : Blo 267823 270443 := bstep (se 1 (by rfl) ⟨202832, by rfl⟩ : syracuseStep 270443 = 405665) B405665
theorem B303223 : Blo 267823 303223 := bstep (se 1 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 303223 = 454835) B454835
theorem B270455 : Blo 267823 270455 := bstep (se 1 (by rfl) ⟨202841, by rfl⟩ : syracuseStep 270455 = 405683) B405683
theorem B270475 : Blo 267823 270475 := bstep (se 1 (by rfl) ⟨202856, by rfl⟩ : syracuseStep 270475 = 405713) B405713
theorem B860311 : Blo 267823 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B270487 : Blo 267823 270487 := bstep (se 1 (by rfl) ⟨202865, by rfl⟩ : syracuseStep 270487 = 405731) B405731
theorem B270507 : Blo 267823 270507 := bstep (se 1 (by rfl) ⟨202880, by rfl⟩ : syracuseStep 270507 = 405761) B405761
theorem B2072753 : Blo 267823 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B270519 : Blo 267823 270519 := bstep (se 1 (by rfl) ⟨202889, by rfl⟩ : syracuseStep 270519 = 405779) B405779
theorem B270539 : Blo 267823 270539 := bstep (se 1 (by rfl) ⟨202904, by rfl⟩ : syracuseStep 270539 = 405809) B405809
theorem B270551 : Blo 267823 270551 := bstep (se 1 (by rfl) ⟨202913, by rfl⟩ : syracuseStep 270551 = 405827) B405827
theorem B270571 : Blo 267823 270571 := bstep (se 1 (by rfl) ⟨202928, by rfl⟩ : syracuseStep 270571 = 405857) B405857
theorem B270583 : Blo 267823 270583 := bstep (se 1 (by rfl) ⟨202937, by rfl⟩ : syracuseStep 270583 = 405875) B405875
theorem B270603 : Blo 267823 270603 := bstep (se 1 (by rfl) ⟨202952, by rfl⟩ : syracuseStep 270603 = 405905) B405905
theorem B270615 : Blo 267823 270615 := bstep (se 1 (by rfl) ⟨202961, by rfl⟩ : syracuseStep 270615 = 405923) B405923
theorem B303403 : Blo 267823 303403 := bstep (se 1 (by rfl) ⟨227552, by rfl⟩ : syracuseStep 303403 = 455105) B455105
theorem B270635 : Blo 267823 270635 := bstep (se 1 (by rfl) ⟨202976, by rfl⟩ : syracuseStep 270635 = 405953) B405953
theorem B270647 : Blo 267823 270647 := bstep (se 1 (by rfl) ⟨202985, by rfl⟩ : syracuseStep 270647 = 405971) B405971
theorem B270667 : Blo 267823 270667 := bstep (se 1 (by rfl) ⟨203000, by rfl⟩ : syracuseStep 270667 = 406001) B406001
theorem B270679 : Blo 267823 270679 := bstep (se 1 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 270679 = 406019) B406019
theorem B401753 : Blo 267823 401753 := bstep (se 2 (by rfl) ⟨150657, by rfl⟩ : syracuseStep 401753 = 301315) B301315
theorem B270699 : Blo 267823 270699 := bstep (se 1 (by rfl) ⟨203024, by rfl⟩ : syracuseStep 270699 = 406049) B406049
theorem B270711 : Blo 267823 270711 := bstep (se 1 (by rfl) ⟨203033, by rfl⟩ : syracuseStep 270711 = 406067) B406067
theorem B270731 : Blo 267823 270731 := bstep (se 1 (by rfl) ⟨203048, by rfl⟩ : syracuseStep 270731 = 406097) B406097
theorem B1450391 : Blo 267823 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B303511 : Blo 267823 303511 := bstep (se 1 (by rfl) ⟨227633, by rfl⟩ : syracuseStep 303511 = 455267) B455267
theorem B270743 : Blo 267823 270743 := bstep (se 1 (by rfl) ⟨203057, by rfl⟩ : syracuseStep 270743 = 406115) B406115
theorem B270763 : Blo 267823 270763 := bstep (se 1 (by rfl) ⟨203072, by rfl⟩ : syracuseStep 270763 = 406145) B406145
theorem B270775 : Blo 267823 270775 := bstep (se 1 (by rfl) ⟨203081, by rfl⟩ : syracuseStep 270775 = 406163) B406163
theorem B401867 : Blo 267823 401867 := bstep (se 1 (by rfl) ⟨301400, by rfl⟩ : syracuseStep 401867 = 602801) B602801
theorem B270795 : Blo 267823 270795 := bstep (se 1 (by rfl) ⟨203096, by rfl⟩ : syracuseStep 270795 = 406193) B406193
theorem B401879 : Blo 267823 401879 := bstep (se 1 (by rfl) ⟨301409, by rfl⟩ : syracuseStep 401879 = 602819) B602819
theorem B270807 : Blo 267823 270807 := bstep (se 1 (by rfl) ⟨203105, by rfl⟩ : syracuseStep 270807 = 406211) B406211
theorem B270827 : Blo 267823 270827 := bstep (se 1 (by rfl) ⟨203120, by rfl⟩ : syracuseStep 270827 = 406241) B406241
theorem B270839 : Blo 267823 270839 := bstep (se 1 (by rfl) ⟨203129, by rfl⟩ : syracuseStep 270839 = 406259) B406259
theorem B270859 : Blo 267823 270859 := bstep (se 1 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 270859 = 406289) B406289
theorem B270871 : Blo 267823 270871 := bstep (se 1 (by rfl) ⟨203153, by rfl⟩ : syracuseStep 270871 = 406307) B406307
theorem B401945 : Blo 267823 401945 := bstep (se 2 (by rfl) ⟨150729, by rfl⟩ : syracuseStep 401945 = 301459) B301459
theorem B270891 : Blo 267823 270891 := bstep (se 1 (by rfl) ⟨203168, by rfl⟩ : syracuseStep 270891 = 406337) B406337
theorem B270903 : Blo 267823 270903 := bstep (se 1 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 270903 = 406355) B406355
theorem B303691 : Blo 267823 303691 := bstep (se 1 (by rfl) ⟨227768, by rfl⟩ : syracuseStep 303691 = 455537) B455537
theorem B270923 : Blo 267823 270923 := bstep (se 1 (by rfl) ⟨203192, by rfl⟩ : syracuseStep 270923 = 406385) B406385
theorem B270935 : Blo 267823 270935 := bstep (se 1 (by rfl) ⟨203201, by rfl⟩ : syracuseStep 270935 = 406403) B406403
theorem B270955 : Blo 267823 270955 := bstep (se 1 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 270955 = 406433) B406433
theorem B270967 : Blo 267823 270967 := bstep (se 1 (by rfl) ⟨203225, by rfl⟩ : syracuseStep 270967 = 406451) B406451
theorem B402059 : Blo 267823 402059 := bstep (se 1 (by rfl) ⟨301544, by rfl⟩ : syracuseStep 402059 = 603089) B603089
theorem B270987 : Blo 267823 270987 := bstep (se 1 (by rfl) ⟨203240, by rfl⟩ : syracuseStep 270987 = 406481) B406481
theorem B402071 : Blo 267823 402071 := bstep (se 1 (by rfl) ⟨301553, by rfl⟩ : syracuseStep 402071 = 603107) B603107
theorem B270999 : Blo 267823 270999 := bstep (se 1 (by rfl) ⟨203249, by rfl⟩ : syracuseStep 270999 = 406499) B406499
theorem B271019 : Blo 267823 271019 := bstep (se 1 (by rfl) ⟨203264, by rfl⟩ : syracuseStep 271019 = 406529) B406529
theorem B303799 : Blo 267823 303799 := bstep (se 1 (by rfl) ⟨227849, by rfl⟩ : syracuseStep 303799 = 455699) B455699
theorem B271031 : Blo 267823 271031 := bstep (se 1 (by rfl) ⟨203273, by rfl⟩ : syracuseStep 271031 = 406547) B406547
theorem B271051 : Blo 267823 271051 := bstep (se 1 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 271051 = 406577) B406577
theorem B271063 : Blo 267823 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B402137 : Blo 267823 402137 := bstep (se 2 (by rfl) ⟨150801, by rfl⟩ : syracuseStep 402137 = 301603) B301603
theorem B271083 : Blo 267823 271083 := bstep (se 1 (by rfl) ⟨203312, by rfl⟩ : syracuseStep 271083 = 406625) B406625
theorem B271095 : Blo 267823 271095 := bstep (se 1 (by rfl) ⟨203321, by rfl⟩ : syracuseStep 271095 = 406643) B406643
theorem B271115 : Blo 267823 271115 := bstep (se 1 (by rfl) ⟨203336, by rfl⟩ : syracuseStep 271115 = 406673) B406673
theorem B271127 : Blo 267823 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B271147 : Blo 267823 271147 := bstep (se 1 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 271147 = 406721) B406721
theorem B271159 : Blo 267823 271159 := bstep (se 1 (by rfl) ⟨203369, by rfl⟩ : syracuseStep 271159 = 406739) B406739
theorem B402251 : Blo 267823 402251 := bstep (se 1 (by rfl) ⟨301688, by rfl⟩ : syracuseStep 402251 = 603377) B603377
theorem B271179 : Blo 267823 271179 := bstep (se 1 (by rfl) ⟨203384, by rfl⟩ : syracuseStep 271179 = 406769) B406769
theorem B402263 : Blo 267823 402263 := bstep (se 1 (by rfl) ⟨301697, by rfl⟩ : syracuseStep 402263 = 603395) B603395
theorem B271191 : Blo 267823 271191 := bstep (se 1 (by rfl) ⟨203393, by rfl⟩ : syracuseStep 271191 = 406787) B406787
theorem B303979 : Blo 267823 303979 := bstep (se 1 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 303979 = 455969) B455969
theorem B271211 : Blo 267823 271211 := bstep (se 1 (by rfl) ⟨203408, by rfl⟩ : syracuseStep 271211 = 406817) B406817
theorem B271223 : Blo 267823 271223 := bstep (se 1 (by rfl) ⟨203417, by rfl⟩ : syracuseStep 271223 = 406835) B406835
theorem B271243 : Blo 267823 271243 := bstep (se 1 (by rfl) ⟨203432, by rfl⟩ : syracuseStep 271243 = 406865) B406865
theorem B1024913 : Blo 267823 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B271255 : Blo 267823 271255 := bstep (se 1 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 271255 = 406883) B406883
theorem B402329 : Blo 267823 402329 := bstep (se 2 (by rfl) ⟨150873, by rfl⟩ : syracuseStep 402329 = 301747) B301747
theorem B271275 : Blo 267823 271275 := bstep (se 1 (by rfl) ⟨203456, by rfl⟩ : syracuseStep 271275 = 406913) B406913
theorem B1942451 : Blo 267823 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B271287 : Blo 267823 271287 := bstep (se 1 (by rfl) ⟨203465, by rfl⟩ : syracuseStep 271287 = 406931) B406931
theorem B271307 : Blo 267823 271307 := bstep (se 1 (by rfl) ⟨203480, by rfl⟩ : syracuseStep 271307 = 406961) B406961
theorem B304087 : Blo 267823 304087 := bstep (se 1 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 304087 = 456131) B456131
theorem B271319 : Blo 267823 271319 := bstep (se 1 (by rfl) ⟨203489, by rfl⟩ : syracuseStep 271319 = 406979) B406979
theorem B271339 : Blo 267823 271339 := bstep (se 1 (by rfl) ⟨203504, by rfl⟩ : syracuseStep 271339 = 407009) B407009
theorem B271351 : Blo 267823 271351 := bstep (se 1 (by rfl) ⟨203513, by rfl⟩ : syracuseStep 271351 = 407027) B407027
theorem B402443 : Blo 267823 402443 := bstep (se 1 (by rfl) ⟨301832, by rfl⟩ : syracuseStep 402443 = 603665) B603665
theorem B271371 : Blo 267823 271371 := bstep (se 1 (by rfl) ⟨203528, by rfl⟩ : syracuseStep 271371 = 407057) B407057
theorem B402455 : Blo 267823 402455 := bstep (se 1 (by rfl) ⟨301841, by rfl⟩ : syracuseStep 402455 = 603683) B603683
theorem B271383 : Blo 267823 271383 := bstep (se 1 (by rfl) ⟨203537, by rfl⟩ : syracuseStep 271383 = 407075) B407075
theorem B271403 : Blo 267823 271403 := bstep (se 1 (by rfl) ⟨203552, by rfl⟩ : syracuseStep 271403 = 407105) B407105
theorem B271415 : Blo 267823 271415 := bstep (se 1 (by rfl) ⟨203561, by rfl⟩ : syracuseStep 271415 = 407123) B407123
theorem B271435 : Blo 267823 271435 := bstep (se 1 (by rfl) ⟨203576, by rfl⟩ : syracuseStep 271435 = 407153) B407153
theorem B271447 : Blo 267823 271447 := bstep (se 1 (by rfl) ⟨203585, by rfl⟩ : syracuseStep 271447 = 407171) B407171
theorem B402521 : Blo 267823 402521 := bstep (se 2 (by rfl) ⟨150945, by rfl⟩ : syracuseStep 402521 = 301891) B301891
theorem B3089501 : Blo 267823 3089501 := bstep (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) B1158563
theorem B271467 : Blo 267823 271467 := bstep (se 1 (by rfl) ⟨203600, by rfl⟩ : syracuseStep 271467 = 407201) B407201
theorem B271479 : Blo 267823 271479 := bstep (se 1 (by rfl) ⟨203609, by rfl⟩ : syracuseStep 271479 = 407219) B407219
theorem B304267 : Blo 267823 304267 := bstep (se 1 (by rfl) ⟨228200, by rfl⟩ : syracuseStep 304267 = 456401) B456401
theorem B271499 : Blo 267823 271499 := bstep (se 1 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 271499 = 407249) B407249
theorem B271511 : Blo 267823 271511 := bstep (se 1 (by rfl) ⟨203633, by rfl⟩ : syracuseStep 271511 = 407267) B407267
theorem B271531 : Blo 267823 271531 := bstep (se 1 (by rfl) ⟨203648, by rfl⟩ : syracuseStep 271531 = 407297) B407297
theorem B2303153 : Blo 267823 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B730291 : Blo 267823 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B271543 : Blo 267823 271543 := bstep (se 1 (by rfl) ⟨203657, by rfl⟩ : syracuseStep 271543 = 407315) B407315
theorem B402635 : Blo 267823 402635 := bstep (se 1 (by rfl) ⟨301976, by rfl⟩ : syracuseStep 402635 = 603953) B603953
theorem B271563 : Blo 267823 271563 := bstep (se 1 (by rfl) ⟨203672, by rfl⟩ : syracuseStep 271563 = 407345) B407345
theorem B402647 : Blo 267823 402647 := bstep (se 1 (by rfl) ⟨301985, by rfl⟩ : syracuseStep 402647 = 603971) B603971
theorem B271575 : Blo 267823 271575 := bstep (se 1 (by rfl) ⟨203681, by rfl⟩ : syracuseStep 271575 = 407363) B407363
theorem B271595 : Blo 267823 271595 := bstep (se 1 (by rfl) ⟨203696, by rfl⟩ : syracuseStep 271595 = 407393) B407393
theorem B304375 : Blo 267823 304375 := bstep (se 1 (by rfl) ⟨228281, by rfl⟩ : syracuseStep 304375 = 456563) B456563
theorem B271607 : Blo 267823 271607 := bstep (se 1 (by rfl) ⟨203705, by rfl⟩ : syracuseStep 271607 = 407411) B407411
theorem B271627 : Blo 267823 271627 := bstep (se 1 (by rfl) ⟨203720, by rfl⟩ : syracuseStep 271627 = 407441) B407441
theorem B1221911 : Blo 267823 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B271639 : Blo 267823 271639 := bstep (se 1 (by rfl) ⟨203729, by rfl⟩ : syracuseStep 271639 = 407459) B407459
theorem B402713 : Blo 267823 402713 := bstep (se 2 (by rfl) ⟨151017, by rfl⟩ : syracuseStep 402713 = 302035) B302035
theorem B271659 : Blo 267823 271659 := bstep (se 1 (by rfl) ⟨203744, by rfl⟩ : syracuseStep 271659 = 407489) B407489
theorem B861491 : Blo 267823 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B271671 : Blo 267823 271671 := bstep (se 1 (by rfl) ⟨203753, by rfl⟩ : syracuseStep 271671 = 407507) B407507
theorem B271691 : Blo 267823 271691 := bstep (se 1 (by rfl) ⟨203768, by rfl⟩ : syracuseStep 271691 = 407537) B407537
theorem B271703 : Blo 267823 271703 := bstep (se 1 (by rfl) ⟨203777, by rfl⟩ : syracuseStep 271703 = 407555) B407555
theorem B1025369 : Blo 267823 1025369 := bstep (se 2 (by rfl) ⟨384513, by rfl⟩ : syracuseStep 1025369 = 769027) B769027
theorem B271723 : Blo 267823 271723 := bstep (se 1 (by rfl) ⟨203792, by rfl⟩ : syracuseStep 271723 = 407585) B407585
theorem B271735 : Blo 267823 271735 := bstep (se 1 (by rfl) ⟨203801, by rfl⟩ : syracuseStep 271735 = 407603) B407603
theorem B402827 : Blo 267823 402827 := bstep (se 1 (by rfl) ⟨302120, by rfl⟩ : syracuseStep 402827 = 604241) B604241
theorem B271755 : Blo 267823 271755 := bstep (se 1 (by rfl) ⟨203816, by rfl⟩ : syracuseStep 271755 = 407633) B407633
theorem B402839 : Blo 267823 402839 := bstep (se 1 (by rfl) ⟨302129, by rfl⟩ : syracuseStep 402839 = 604259) B604259
theorem B271767 : Blo 267823 271767 := bstep (se 1 (by rfl) ⟨203825, by rfl⟩ : syracuseStep 271767 = 407651) B407651
theorem B304555 : Blo 267823 304555 := bstep (se 1 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 304555 = 456833) B456833
theorem B271787 : Blo 267823 271787 := bstep (se 1 (by rfl) ⟨203840, by rfl⟩ : syracuseStep 271787 = 407681) B407681
theorem B271799 : Blo 267823 271799 := bstep (se 1 (by rfl) ⟨203849, by rfl⟩ : syracuseStep 271799 = 407699) B407699
theorem B271819 : Blo 267823 271819 := bstep (se 1 (by rfl) ⟨203864, by rfl⟩ : syracuseStep 271819 = 407729) B407729
theorem B402905 : Blo 267823 402905 := bstep (se 2 (by rfl) ⟨151089, by rfl⟩ : syracuseStep 402905 = 302179) B302179
theorem B304663 : Blo 267823 304663 := bstep (se 1 (by rfl) ⟨228497, by rfl⟩ : syracuseStep 304663 = 456995) B456995
theorem B1025581 : Blo 267823 1025581 := bstep (se 3 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 1025581 = 384593) B384593
theorem B403019 : Blo 267823 403019 := bstep (se 1 (by rfl) ⟨302264, by rfl⟩ : syracuseStep 403019 = 604529) B604529
theorem B403031 : Blo 267823 403031 := bstep (se 1 (by rfl) ⟨302273, by rfl⟩ : syracuseStep 403031 = 604547) B604547
theorem B403097 : Blo 267823 403097 := bstep (se 2 (by rfl) ⟨151161, by rfl⟩ : syracuseStep 403097 = 302323) B302323
theorem B1156787 : Blo 267823 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B304843 : Blo 267823 304843 := bstep (se 1 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 304843 = 457265) B457265
theorem B7513805 : Blo 267823 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B403211 : Blo 267823 403211 := bstep (se 1 (by rfl) ⟨302408, by rfl⟩ : syracuseStep 403211 = 604817) B604817
theorem B403223 : Blo 267823 403223 := bstep (se 1 (by rfl) ⟨302417, by rfl⟩ : syracuseStep 403223 = 604835) B604835
theorem B304951 : Blo 267823 304951 := bstep (se 1 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 304951 = 457427) B457427
theorem B403289 : Blo 267823 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B1025885 : Blo 267823 1025885 := bstep (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) B384707
theorem B403403 : Blo 267823 403403 := bstep (se 1 (by rfl) ⟨302552, by rfl⟩ : syracuseStep 403403 = 605105) B605105
theorem B403415 : Blo 267823 403415 := bstep (se 1 (by rfl) ⟨302561, by rfl⟩ : syracuseStep 403415 = 605123) B605123
theorem B305131 : Blo 267823 305131 := bstep (se 1 (by rfl) ⟨228848, by rfl⟩ : syracuseStep 305131 = 457697) B457697
theorem B403481 : Blo 267823 403481 := bstep (se 2 (by rfl) ⟨151305, by rfl⟩ : syracuseStep 403481 = 302611) B302611
theorem B305239 : Blo 267823 305239 := bstep (se 1 (by rfl) ⟨228929, by rfl⟩ : syracuseStep 305239 = 457859) B457859
theorem B403595 : Blo 267823 403595 := bstep (se 1 (by rfl) ⟨302696, by rfl⟩ : syracuseStep 403595 = 605393) B605393
theorem B403607 : Blo 267823 403607 := bstep (se 1 (by rfl) ⟨302705, by rfl⟩ : syracuseStep 403607 = 605411) B605411
theorem B764083 : Blo 267823 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B731339 : Blo 267823 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B403673 : Blo 267823 403673 := bstep (se 2 (by rfl) ⟨151377, by rfl⟩ : syracuseStep 403673 = 302755) B302755
theorem B2074841 : Blo 267823 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B305419 : Blo 267823 305419 := bstep (se 1 (by rfl) ⟨229064, by rfl⟩ : syracuseStep 305419 = 458129) B458129
theorem B403787 : Blo 267823 403787 := bstep (se 1 (by rfl) ⟨302840, by rfl⟩ : syracuseStep 403787 = 605681) B605681
theorem B403799 : Blo 267823 403799 := bstep (se 1 (by rfl) ⟨302849, by rfl⟩ : syracuseStep 403799 = 605699) B605699
theorem B305527 : Blo 267823 305527 := bstep (se 1 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 305527 = 458291) B458291
theorem B1747331 : Blo 267823 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B764311 : Blo 267823 764311 := bstep (se 1 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 764311 = 1146467) B1146467
theorem B403865 : Blo 267823 403865 := bstep (se 2 (by rfl) ⟨151449, by rfl⟩ : syracuseStep 403865 = 302899) B302899
theorem B600473 : Blo 267823 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B403979 : Blo 267823 403979 := bstep (se 1 (by rfl) ⟨302984, by rfl⟩ : syracuseStep 403979 = 605969) B605969
theorem B403991 : Blo 267823 403991 := bstep (se 1 (by rfl) ⟨302993, by rfl⟩ : syracuseStep 403991 = 605987) B605987
theorem B305707 : Blo 267823 305707 := bstep (se 1 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 305707 = 458561) B458561
theorem B272971 : Blo 267823 272971 := bstep (se 1 (by rfl) ⟨204728, by rfl⟩ : syracuseStep 272971 = 409457) B409457
theorem B404057 : Blo 267823 404057 := bstep (se 2 (by rfl) ⟨151521, by rfl⟩ : syracuseStep 404057 = 303043) B303043
theorem B2960003 : Blo 267823 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B404171 : Blo 267823 404171 := bstep (se 1 (by rfl) ⟨303128, by rfl⟩ : syracuseStep 404171 = 606257) B606257
theorem B404183 : Blo 267823 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B404249 : Blo 267823 404249 := bstep (se 2 (by rfl) ⟨151593, by rfl⟩ : syracuseStep 404249 = 303187) B303187
theorem B305975 : Blo 267823 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B404363 : Blo 267823 404363 := bstep (se 1 (by rfl) ⟨303272, by rfl⟩ : syracuseStep 404363 = 606545) B606545
theorem B404375 : Blo 267823 404375 := bstep (se 1 (by rfl) ⟨303281, by rfl⟩ : syracuseStep 404375 = 606563) B606563
theorem B404441 : Blo 267823 404441 := bstep (se 2 (by rfl) ⟨151665, by rfl⟩ : syracuseStep 404441 = 303331) B303331
theorem B404555 : Blo 267823 404555 := bstep (se 1 (by rfl) ⟨303416, by rfl⟩ : syracuseStep 404555 = 606833) B606833
theorem B404567 : Blo 267823 404567 := bstep (se 1 (by rfl) ⟨303425, by rfl⟩ : syracuseStep 404567 = 606851) B606851
theorem B404633 : Blo 267823 404633 := bstep (se 2 (by rfl) ⟨151737, by rfl⟩ : syracuseStep 404633 = 303475) B303475
theorem B8694965 : Blo 267823 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B404747 : Blo 267823 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B339223 : Blo 267823 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B404759 : Blo 267823 404759 := bstep (se 1 (by rfl) ⟨303569, by rfl⟩ : syracuseStep 404759 = 607139) B607139
theorem B404825 : Blo 267823 404825 := bstep (se 2 (by rfl) ⟨151809, by rfl⟩ : syracuseStep 404825 = 303619) B303619
theorem B863581 : Blo 267823 863581 := bstep (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) B323843
theorem B404939 : Blo 267823 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B404951 : Blo 267823 404951 := bstep (se 1 (by rfl) ⟨303713, by rfl⟩ : syracuseStep 404951 = 607427) B607427
theorem B405017 : Blo 267823 405017 := bstep (se 2 (by rfl) ⟨151881, by rfl⟩ : syracuseStep 405017 = 303763) B303763
theorem B1945133 : Blo 267823 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B405131 : Blo 267823 405131 := bstep (se 1 (by rfl) ⟨303848, by rfl⟩ : syracuseStep 405131 = 607697) B607697
theorem B405143 : Blo 267823 405143 := bstep (se 1 (by rfl) ⟨303857, by rfl⟩ : syracuseStep 405143 = 607715) B607715
theorem B405209 : Blo 267823 405209 := bstep (se 2 (by rfl) ⟨151953, by rfl⟩ : syracuseStep 405209 = 303907) B303907
theorem B405323 : Blo 267823 405323 := bstep (se 1 (by rfl) ⟨303992, by rfl⟩ : syracuseStep 405323 = 607985) B607985
theorem B405335 : Blo 267823 405335 := bstep (se 1 (by rfl) ⟨304001, by rfl⟩ : syracuseStep 405335 = 608003) B608003
theorem B405401 : Blo 267823 405401 := bstep (se 2 (by rfl) ⟨152025, by rfl⟩ : syracuseStep 405401 = 304051) B304051
theorem B405515 : Blo 267823 405515 := bstep (se 1 (by rfl) ⟨304136, by rfl⟩ : syracuseStep 405515 = 608273) B608273
theorem B405527 : Blo 267823 405527 := bstep (se 1 (by rfl) ⟨304145, by rfl⟩ : syracuseStep 405527 = 608291) B608291
theorem B405593 : Blo 267823 405593 := bstep (se 2 (by rfl) ⟨152097, by rfl⟩ : syracuseStep 405593 = 304195) B304195
theorem B405707 : Blo 267823 405707 := bstep (se 1 (by rfl) ⟨304280, by rfl⟩ : syracuseStep 405707 = 608561) B608561
theorem B405719 : Blo 267823 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B766169 : Blo 267823 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B405785 : Blo 267823 405785 := bstep (se 2 (by rfl) ⟨152169, by rfl⟩ : syracuseStep 405785 = 304339) B304339
theorem B9318773 : Blo 267823 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B1028483 : Blo 267823 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B1159555 : Blo 267823 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B405899 : Blo 267823 405899 := bstep (se 1 (by rfl) ⟨304424, by rfl⟩ : syracuseStep 405899 = 608849) B608849
theorem B1028497 : Blo 267823 1028497 := bstep (se 2 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 1028497 = 771373) B771373
theorem B405911 : Blo 267823 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B405977 : Blo 267823 405977 := bstep (se 2 (by rfl) ⟨152241, by rfl⟩ : syracuseStep 405977 = 304483) B304483
theorem B602675 : Blo 267823 602675 := bstep (se 1 (by rfl) ⟨452006, by rfl⟩ : syracuseStep 602675 = 904013) B904013
theorem B1094219 : Blo 267823 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B406091 : Blo 267823 406091 := bstep (se 1 (by rfl) ⟨304568, by rfl⟩ : syracuseStep 406091 = 609137) B609137
theorem B602711 : Blo 267823 602711 := bstep (se 1 (by rfl) ⟨452033, by rfl⟩ : syracuseStep 602711 = 904067) B904067
theorem B406103 : Blo 267823 406103 := bstep (se 1 (by rfl) ⟨304577, by rfl⟩ : syracuseStep 406103 = 609155) B609155
theorem B275095 : Blo 267823 275095 := bstep (se 1 (by rfl) ⟨206321, by rfl⟩ : syracuseStep 275095 = 412643) B412643
theorem B406169 : Blo 267823 406169 := bstep (se 2 (by rfl) ⟨152313, by rfl⟩ : syracuseStep 406169 = 304627) B304627
theorem B1028801 : Blo 267823 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B602891 : Blo 267823 602891 := bstep (se 1 (by rfl) ⟨452168, by rfl⟩ : syracuseStep 602891 = 904337) B904337
theorem B406283 : Blo 267823 406283 := bstep (se 1 (by rfl) ⟨304712, by rfl⟩ : syracuseStep 406283 = 609425) B609425
theorem B406295 : Blo 267823 406295 := bstep (se 1 (by rfl) ⟨304721, by rfl⟩ : syracuseStep 406295 = 609443) B609443
theorem B1717037 : Blo 267823 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B602945 : Blo 267823 602945 := bstep (se 2 (by rfl) ⟨226104, by rfl⟩ : syracuseStep 602945 = 452209) B452209
theorem B406361 : Blo 267823 406361 := bstep (se 2 (by rfl) ⟨152385, by rfl⟩ : syracuseStep 406361 = 304771) B304771
theorem B340939 : Blo 267823 340939 := bstep (se 1 (by rfl) ⟨255704, by rfl⟩ : syracuseStep 340939 = 511409) B511409
theorem B406475 : Blo 267823 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B406487 : Blo 267823 406487 := bstep (se 1 (by rfl) ⟨304865, by rfl⟩ : syracuseStep 406487 = 609731) B609731
theorem B766999 : Blo 267823 766999 := bstep (se 1 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 766999 = 1150499) B1150499
theorem B603161 : Blo 267823 603161 := bstep (se 2 (by rfl) ⟨226185, by rfl⟩ : syracuseStep 603161 = 452371) B452371
theorem B406553 : Blo 267823 406553 := bstep (se 2 (by rfl) ⟨152457, by rfl⟩ : syracuseStep 406553 = 304915) B304915
theorem B603251 : Blo 267823 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B406667 : Blo 267823 406667 := bstep (se 1 (by rfl) ⟨305000, by rfl⟩ : syracuseStep 406667 = 610001) B610001
theorem B603287 : Blo 267823 603287 := bstep (se 1 (by rfl) ⟨452465, by rfl⟩ : syracuseStep 603287 = 904931) B904931
theorem B406679 : Blo 267823 406679 := bstep (se 1 (by rfl) ⟨305009, by rfl⟩ : syracuseStep 406679 = 610019) B610019
theorem B406745 : Blo 267823 406745 := bstep (se 2 (by rfl) ⟨152529, by rfl⟩ : syracuseStep 406745 = 305059) B305059
theorem B1357073 : Blo 267823 1357073 := bstep (se 2 (by rfl) ⟨508902, by rfl⟩ : syracuseStep 1357073 = 1017805) B1017805
theorem B1750337 : Blo 267823 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B1160513 : Blo 267823 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B603467 : Blo 267823 603467 := bstep (se 1 (by rfl) ⟨452600, by rfl⟩ : syracuseStep 603467 = 905201) B905201
theorem B406859 : Blo 267823 406859 := bstep (se 1 (by rfl) ⟨305144, by rfl⟩ : syracuseStep 406859 = 610289) B610289
theorem B406871 : Blo 267823 406871 := bstep (se 1 (by rfl) ⟨305153, by rfl⟩ : syracuseStep 406871 = 610307) B610307
theorem B1029469 : Blo 267823 1029469 := bstep (se 3 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 1029469 = 386051) B386051
theorem B603521 : Blo 267823 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B406937 : Blo 267823 406937 := bstep (se 2 (by rfl) ⟨152601, by rfl⟩ : syracuseStep 406937 = 305203) B305203
theorem B1357235 : Blo 267823 1357235 := bstep (se 1 (by rfl) ⟨1017926, by rfl⟩ : syracuseStep 1357235 = 2035853) B2035853
theorem B407051 : Blo 267823 407051 := bstep (se 1 (by rfl) ⟨305288, by rfl⟩ : syracuseStep 407051 = 610577) B610577
theorem B407063 : Blo 267823 407063 := bstep (se 1 (by rfl) ⟨305297, by rfl⟩ : syracuseStep 407063 = 610595) B610595
theorem B603737 : Blo 267823 603737 := bstep (se 2 (by rfl) ⟨226401, by rfl⟩ : syracuseStep 603737 = 452803) B452803
theorem B407129 : Blo 267823 407129 := bstep (se 2 (by rfl) ⟨152673, by rfl⟩ : syracuseStep 407129 = 305347) B305347
theorem B9942659 : Blo 267823 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B603827 : Blo 267823 603827 := bstep (se 1 (by rfl) ⟨452870, by rfl⟩ : syracuseStep 603827 = 905741) B905741
theorem B407243 : Blo 267823 407243 := bstep (se 1 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 407243 = 610865) B610865
theorem B603863 : Blo 267823 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B407255 : Blo 267823 407255 := bstep (se 1 (by rfl) ⟨305441, by rfl⟩ : syracuseStep 407255 = 610883) B610883
theorem B3127045 : Blo 267823 3127045 := bstep (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) B586321
theorem B407321 : Blo 267823 407321 := bstep (se 2 (by rfl) ⟨152745, by rfl⟩ : syracuseStep 407321 = 305491) B305491
theorem B767819 : Blo 267823 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B604043 : Blo 267823 604043 := bstep (se 1 (by rfl) ⟨453032, by rfl⟩ : syracuseStep 604043 = 906065) B906065
theorem B407435 : Blo 267823 407435 := bstep (se 1 (by rfl) ⟨305576, by rfl⟩ : syracuseStep 407435 = 611153) B611153
theorem B341911 : Blo 267823 341911 := bstep (se 1 (by rfl) ⟨256433, by rfl⟩ : syracuseStep 341911 = 512867) B512867
theorem B407447 : Blo 267823 407447 := bstep (se 1 (by rfl) ⟨305585, by rfl⟩ : syracuseStep 407447 = 611171) B611171
theorem B604097 : Blo 267823 604097 := bstep (se 2 (by rfl) ⟨226536, by rfl⟩ : syracuseStep 604097 = 453073) B453073
theorem B407513 : Blo 267823 407513 := bstep (se 2 (by rfl) ⟨152817, by rfl⟩ : syracuseStep 407513 = 305635) B305635
theorem B407627 : Blo 267823 407627 := bstep (se 1 (by rfl) ⟨305720, by rfl⟩ : syracuseStep 407627 = 611441) B611441
theorem B407639 : Blo 267823 407639 := bstep (se 1 (by rfl) ⟨305729, by rfl⟩ : syracuseStep 407639 = 611459) B611459
theorem B604313 : Blo 267823 604313 := bstep (se 2 (by rfl) ⟨226617, by rfl⟩ : syracuseStep 604313 = 453235) B453235
theorem B407705 : Blo 267823 407705 := bstep (se 2 (by rfl) ⟨152889, by rfl⟩ : syracuseStep 407705 = 305779) B305779
theorem B604403 : Blo 267823 604403 := bstep (se 1 (by rfl) ⟨453302, by rfl⟩ : syracuseStep 604403 = 906605) B906605
theorem B604439 : Blo 267823 604439 := bstep (se 1 (by rfl) ⟨453329, by rfl⟩ : syracuseStep 604439 = 906659) B906659
theorem B1456535 : Blo 267823 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B604619 : Blo 267823 604619 := bstep (se 1 (by rfl) ⟨453464, by rfl⟩ : syracuseStep 604619 = 906929) B906929
theorem B604673 : Blo 267823 604673 := bstep (se 2 (by rfl) ⟨226752, by rfl⟩ : syracuseStep 604673 = 453505) B453505
theorem B1030745 : Blo 267823 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B342731 : Blo 267823 342731 := bstep (se 1 (by rfl) ⟨257048, by rfl⟩ : syracuseStep 342731 = 514097) B514097
theorem B604889 : Blo 267823 604889 := bstep (se 2 (by rfl) ⟨226833, by rfl⟩ : syracuseStep 604889 = 453667) B453667
theorem B604979 : Blo 267823 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B1096523 : Blo 267823 1096523 := bstep (se 1 (by rfl) ⟨822392, by rfl⟩ : syracuseStep 1096523 = 1644785) B1644785
theorem B605015 : Blo 267823 605015 := bstep (se 1 (by rfl) ⟨453761, by rfl⟩ : syracuseStep 605015 = 907523) B907523
theorem B605195 : Blo 267823 605195 := bstep (se 1 (by rfl) ⟨453896, by rfl⟩ : syracuseStep 605195 = 907793) B907793
theorem B605249 : Blo 267823 605249 := bstep (se 2 (by rfl) ⟨226968, by rfl⟩ : syracuseStep 605249 = 453937) B453937
theorem B1948823 : Blo 267823 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B605465 : Blo 267823 605465 := bstep (se 2 (by rfl) ⟨227049, by rfl⟩ : syracuseStep 605465 = 454099) B454099
theorem B1359179 : Blo 267823 1359179 := bstep (se 1 (by rfl) ⟨1019384, by rfl⟩ : syracuseStep 1359179 = 2038769) B2038769
theorem B605555 : Blo 267823 605555 := bstep (se 1 (by rfl) ⟨454166, by rfl⟩ : syracuseStep 605555 = 908333) B908333
theorem B343435 : Blo 267823 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B605591 : Blo 267823 605591 := bstep (se 1 (by rfl) ⟨454193, by rfl⟩ : syracuseStep 605591 = 908387) B908387
theorem B3063257 : Blo 267823 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B605771 : Blo 267823 605771 := bstep (se 1 (by rfl) ⟨454328, by rfl⟩ : syracuseStep 605771 = 908657) B908657
theorem B1949285 : Blo 267823 1949285 := bstep (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) B365491
theorem B605825 : Blo 267823 605825 := bstep (se 2 (by rfl) ⟨227184, by rfl⟩ : syracuseStep 605825 = 454369) B454369
theorem B343703 : Blo 267823 343703 := bstep (se 1 (by rfl) ⟨257777, by rfl⟩ : syracuseStep 343703 = 515555) B515555
theorem B573131 : Blo 267823 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B606041 : Blo 267823 606041 := bstep (se 2 (by rfl) ⟨227265, by rfl⟩ : syracuseStep 606041 = 454531) B454531
theorem B606131 : Blo 267823 606131 := bstep (se 1 (by rfl) ⟨454598, by rfl⟩ : syracuseStep 606131 = 909197) B909197
theorem B606167 : Blo 267823 606167 := bstep (se 1 (by rfl) ⟨454625, by rfl⟩ : syracuseStep 606167 = 909251) B909251
theorem B1720385 : Blo 267823 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1949771 : Blo 267823 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B606347 : Blo 267823 606347 := bstep (se 1 (by rfl) ⟨454760, by rfl⟩ : syracuseStep 606347 = 909521) B909521
theorem B606401 : Blo 267823 606401 := bstep (se 2 (by rfl) ⟨227400, by rfl⟩ : syracuseStep 606401 = 454801) B454801
theorem B770269 : Blo 267823 770269 := bstep (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) B288851
theorem B3916097 : Blo 267823 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B606617 : Blo 267823 606617 := bstep (se 2 (by rfl) ⟨227481, by rfl⟩ : syracuseStep 606617 = 454963) B454963
theorem B573875 : Blo 267823 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B1458611 : Blo 267823 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B606707 : Blo 267823 606707 := bstep (se 1 (by rfl) ⟨455030, by rfl⟩ : syracuseStep 606707 = 910061) B910061
theorem B606743 : Blo 267823 606743 := bstep (se 1 (by rfl) ⟨455057, by rfl⟩ : syracuseStep 606743 = 910115) B910115
theorem B508531 : Blo 267823 508531 := bstep (se 1 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 508531 = 762797) B762797
theorem B606923 : Blo 267823 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B606977 : Blo 267823 606977 := bstep (se 2 (by rfl) ⟨227616, by rfl⟩ : syracuseStep 606977 = 455233) B455233
theorem B607193 : Blo 267823 607193 := bstep (se 2 (by rfl) ⟨227697, by rfl⟩ : syracuseStep 607193 = 455395) B455395
theorem B1557521 : Blo 267823 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B508979 : Blo 267823 508979 := bstep (se 1 (by rfl) ⟨381734, by rfl⟩ : syracuseStep 508979 = 763469) B763469
theorem B607283 : Blo 267823 607283 := bstep (se 1 (by rfl) ⟨455462, by rfl⟩ : syracuseStep 607283 = 910925) B910925
theorem B1360961 : Blo 267823 1360961 := bstep (se 2 (by rfl) ⟨510360, by rfl⟩ : syracuseStep 1360961 = 1020721) B1020721
theorem B607319 : Blo 267823 607319 := bstep (se 1 (by rfl) ⟨455489, by rfl⟩ : syracuseStep 607319 = 910979) B910979
theorem B509017 : Blo 267823 509017 := bstep (se 2 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 509017 = 381763) B381763
theorem B1950925 : Blo 267823 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B1230083 : Blo 267823 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B607499 : Blo 267823 607499 := bstep (se 1 (by rfl) ⟨455624, by rfl⟩ : syracuseStep 607499 = 911249) B911249
theorem B574771 : Blo 267823 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B607553 : Blo 267823 607553 := bstep (se 2 (by rfl) ⟨227832, by rfl⟩ : syracuseStep 607553 = 455665) B455665
theorem B771545 : Blo 267823 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B509465 : Blo 267823 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B607769 : Blo 267823 607769 := bstep (se 2 (by rfl) ⟨227913, by rfl⟩ : syracuseStep 607769 = 455827) B455827
theorem B607859 : Blo 267823 607859 := bstep (se 1 (by rfl) ⟨455894, by rfl⟩ : syracuseStep 607859 = 911789) B911789
theorem B607895 : Blo 267823 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B4933325 : Blo 267823 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B2475821 : Blo 267823 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B608075 : Blo 267823 608075 := bstep (se 1 (by rfl) ⟨456056, by rfl⟩ : syracuseStep 608075 = 912113) B912113
theorem B608129 : Blo 267823 608129 := bstep (se 2 (by rfl) ⟨228048, by rfl⟩ : syracuseStep 608129 = 456097) B456097
theorem B608345 : Blo 267823 608345 := bstep (se 2 (by rfl) ⟨228129, by rfl⟩ : syracuseStep 608345 = 456259) B456259
theorem B608435 : Blo 267823 608435 := bstep (se 1 (by rfl) ⟨456326, by rfl⟩ : syracuseStep 608435 = 912653) B912653
theorem B608471 : Blo 267823 608471 := bstep (se 1 (by rfl) ⟨456353, by rfl⟩ : syracuseStep 608471 = 912707) B912707
theorem B510209 : Blo 267823 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B575831 : Blo 267823 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B2312549 : Blo 267823 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B608651 : Blo 267823 608651 := bstep (se 1 (by rfl) ⟨456488, by rfl⟩ : syracuseStep 608651 = 912977) B912977
theorem B608705 : Blo 267823 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B576001 : Blo 267823 576001 := bstep (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) B432001
theorem B510475 : Blo 267823 510475 := bstep (se 1 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 510475 = 765713) B765713
theorem B608921 : Blo 267823 608921 := bstep (se 2 (by rfl) ⟨228345, by rfl⟩ : syracuseStep 608921 = 456691) B456691
theorem B412363 : Blo 267823 412363 := bstep (se 1 (by rfl) ⟨309272, by rfl⟩ : syracuseStep 412363 = 618545) B618545
theorem B19942129 : Blo 267823 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B609011 : Blo 267823 609011 := bstep (se 1 (by rfl) ⟨456758, by rfl⟩ : syracuseStep 609011 = 913517) B913517
theorem B903959 : Blo 267823 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B609047 : Blo 267823 609047 := bstep (se 1 (by rfl) ⟨456785, by rfl⟩ : syracuseStep 609047 = 913571) B913571
theorem B576343 : Blo 267823 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B510923 : Blo 267823 510923 := bstep (se 1 (by rfl) ⟨383192, by rfl⟩ : syracuseStep 510923 = 766385) B766385
theorem B609227 : Blo 267823 609227 := bstep (se 1 (by rfl) ⟨456920, by rfl⟩ : syracuseStep 609227 = 913841) B913841
theorem B1362905 : Blo 267823 1362905 := bstep (se 2 (by rfl) ⟨511089, by rfl⟩ : syracuseStep 1362905 = 1022179) B1022179
theorem B609281 : Blo 267823 609281 := bstep (se 2 (by rfl) ⟨228480, by rfl⟩ : syracuseStep 609281 = 456961) B456961
theorem B773185 : Blo 267823 773185 := bstep (se 2 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 773185 = 579889) B579889
theorem B1723493 : Blo 267823 1723493 := bstep (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) B323155
theorem B511105 : Blo 267823 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B609497 : Blo 267823 609497 := bstep (se 2 (by rfl) ⟨228561, by rfl⟩ : syracuseStep 609497 = 457123) B457123
theorem B904499 : Blo 267823 904499 := bstep (se 1 (by rfl) ⟨678374, by rfl⟩ : syracuseStep 904499 = 1356749) B1356749
theorem B609587 : Blo 267823 609587 := bstep (se 1 (by rfl) ⟨457190, by rfl⟩ : syracuseStep 609587 = 914381) B914381
theorem B609623 : Blo 267823 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B970157 : Blo 267823 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B511447 : Blo 267823 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B609803 : Blo 267823 609803 := bstep (se 1 (by rfl) ⟨457352, by rfl⟩ : syracuseStep 609803 = 914705) B914705
theorem B904769 : Blo 267823 904769 := bstep (se 2 (by rfl) ⟨339288, by rfl⟩ : syracuseStep 904769 = 678577) B678577
theorem B609857 : Blo 267823 609857 := bstep (se 2 (by rfl) ⟨228696, by rfl⟩ : syracuseStep 609857 = 457393) B457393
theorem B577163 : Blo 267823 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B511667 : Blo 267823 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B610073 : Blo 267823 610073 := bstep (se 2 (by rfl) ⟨228777, by rfl⟩ : syracuseStep 610073 = 457555) B457555
theorem B16568165 : Blo 267823 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B4771685 : Blo 267823 4771685 := bstep (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) B894691
theorem B610163 : Blo 267823 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B511895 : Blo 267823 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B610199 : Blo 267823 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B577523 : Blo 267823 577523 := bstep (se 1 (by rfl) ⟨433142, by rfl⟩ : syracuseStep 577523 = 866285) B866285
theorem B610379 : Blo 267823 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B905309 : Blo 267823 905309 := bstep (se 3 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 905309 = 339491) B339491
theorem B610433 : Blo 267823 610433 := bstep (se 2 (by rfl) ⟨228912, by rfl⟩ : syracuseStep 610433 = 457825) B457825
theorem B512153 : Blo 267823 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B610649 : Blo 267823 610649 := bstep (se 2 (by rfl) ⟨228993, by rfl⟩ : syracuseStep 610649 = 457987) B457987
theorem B610739 : Blo 267823 610739 := bstep (se 1 (by rfl) ⟨458054, by rfl⟩ : syracuseStep 610739 = 916109) B916109
theorem B610775 : Blo 267823 610775 := bstep (se 1 (by rfl) ⟨458081, by rfl⟩ : syracuseStep 610775 = 916163) B916163
theorem B1364525 : Blo 267823 1364525 := bstep (se 3 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 1364525 = 511697) B511697
theorem B512563 : Blo 267823 512563 := bstep (se 1 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 512563 = 768845) B768845
theorem B610955 : Blo 267823 610955 := bstep (se 1 (by rfl) ⟨458216, by rfl⟩ : syracuseStep 610955 = 916433) B916433
theorem B611009 : Blo 267823 611009 := bstep (se 2 (by rfl) ⟨229128, by rfl⟩ : syracuseStep 611009 = 458257) B458257
theorem B3134213 : Blo 267823 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B611225 : Blo 267823 611225 := bstep (se 2 (by rfl) ⟨229209, by rfl⟩ : syracuseStep 611225 = 458419) B458419
theorem B2315213 : Blo 267823 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B611315 : Blo 267823 611315 := bstep (se 1 (by rfl) ⟨458486, by rfl⟩ : syracuseStep 611315 = 916973) B916973
theorem B611351 : Blo 267823 611351 := bstep (se 1 (by rfl) ⟨458513, by rfl⟩ : syracuseStep 611351 = 917027) B917027
theorem B513049 : Blo 267823 513049 := bstep (se 2 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 513049 = 384787) B384787
theorem B906443 : Blo 267823 906443 := bstep (se 1 (by rfl) ⟨679832, by rfl⟩ : syracuseStep 906443 = 1359665) B1359665
theorem B611531 : Blo 267823 611531 := bstep (se 1 (by rfl) ⟨458648, by rfl⟩ : syracuseStep 611531 = 917297) B917297
theorem B611585 : Blo 267823 611585 := bstep (se 2 (by rfl) ⟨229344, by rfl⟩ : syracuseStep 611585 = 458689) B458689
theorem B972107 : Blo 267823 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B906713 : Blo 267823 906713 := bstep (se 2 (by rfl) ⟨340017, by rfl⟩ : syracuseStep 906713 = 680035) B680035
theorem B513611 : Blo 267823 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B513793 : Blo 267823 513793 := bstep (se 2 (by rfl) ⟨192672, by rfl⟩ : syracuseStep 513793 = 385345) B385345
theorem B579521 : Blo 267823 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B546817 : Blo 267823 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B546881 : Blo 267823 546881 := bstep (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) B410161
theorem B1038467 : Blo 267823 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B907415 : Blo 267823 907415 := bstep (se 1 (by rfl) ⟨680561, by rfl⟩ : syracuseStep 907415 = 1361123) B1361123
theorem B2054321 : Blo 267823 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B1530035 : Blo 267823 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B678091 : Blo 267823 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B678233 : Blo 267823 678233 := bstep (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) B508675
theorem B514507 : Blo 267823 514507 := bstep (se 1 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 514507 = 771761) B771761
theorem B383449 : Blo 267823 383449 := bstep (se 2 (by rfl) ⟨143793, by rfl⟩ : syracuseStep 383449 = 287587) B287587
theorem B514583 : Blo 267823 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B2054807 : Blo 267823 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B1759895 : Blo 267823 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B907955 : Blo 267823 907955 := bstep (se 1 (by rfl) ⟨680966, by rfl⟩ : syracuseStep 907955 = 1361933) B1361933
theorem B580375 : Blo 267823 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B973619 : Blo 267823 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B2710451 : Blo 267823 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B908225 : Blo 267823 908225 := bstep (se 2 (by rfl) ⟨340584, by rfl⟩ : syracuseStep 908225 = 681169) B681169
theorem B679063 : Blo 267823 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B515251 : Blo 267823 515251 := bstep (se 1 (by rfl) ⟨386438, by rfl⟩ : syracuseStep 515251 = 772877) B772877
theorem B1236161 : Blo 267823 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B417035 : Blo 267823 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B515479 : Blo 267823 515479 := bstep (se 1 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 515479 = 773219) B773219
theorem B908765 : Blo 267823 908765 := bstep (se 3 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 908765 = 340787) B340787
theorem B515585 : Blo 267823 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B7790093 : Blo 267823 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B679499 : Blo 267823 679499 := bstep (se 1 (by rfl) ⟨509624, by rfl⟩ : syracuseStep 679499 = 1019249) B1019249
theorem B974425 : Blo 267823 974425 := bstep (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) B730819
theorem B1531493 : Blo 267823 1531493 := bstep (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) B287155
theorem B515737 : Blo 267823 515737 := bstep (se 2 (by rfl) ⟨193401, by rfl⟩ : syracuseStep 515737 = 386803) B386803
theorem B2449075 : Blo 267823 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B1171223 : Blo 267823 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B384907 : Blo 267823 384907 := bstep (se 1 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 384907 = 577361) B577361
theorem B974771 : Blo 267823 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B1761203 : Blo 267823 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B679873 : Blo 267823 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B11952197 : Blo 267823 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B26665237 : Blo 267823 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B2580781 : Blo 267823 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B549185 : Blo 267823 549185 := bstep (se 2 (by rfl) ⟨205944, by rfl⟩ : syracuseStep 549185 = 411889) B411889
theorem B1368413 : Blo 267823 1368413 := bstep (se 3 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 1368413 = 513155) B513155
theorem B8348021 : Blo 267823 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B680471 : Blo 267823 680471 := bstep (se 1 (by rfl) ⟨510353, by rfl⟩ : syracuseStep 680471 = 1020707) B1020707
theorem B909899 : Blo 267823 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B910169 : Blo 267823 910169 := bstep (se 2 (by rfl) ⟨341313, by rfl⟩ : syracuseStep 910169 = 682627) B682627
theorem B287659 : Blo 267823 287659 := bstep (se 1 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 287659 = 431489) B431489
theorem B975809 : Blo 267823 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B386137 : Blo 267823 386137 := bstep (se 2 (by rfl) ⟨144801, by rfl⟩ : syracuseStep 386137 = 289603) B289603
theorem B681281 : Blo 267823 681281 := bstep (se 2 (by rfl) ⟨255480, by rfl⟩ : syracuseStep 681281 = 510961) B510961
theorem B451993 : Blo 267823 451993 := bstep (se 2 (by rfl) ⟨169497, by rfl⟩ : syracuseStep 451993 = 338995) B338995
theorem B615937 : Blo 267823 615937 := bstep (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) B461953
theorem B910871 : Blo 267823 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B288407 : Blo 267823 288407 := bstep (se 1 (by rfl) ⟨216305, by rfl⟩ : syracuseStep 288407 = 432611) B432611
theorem B681817 : Blo 267823 681817 := bstep (se 2 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 681817 = 511363) B511363
theorem B452567 : Blo 267823 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B387031 : Blo 267823 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B911411 : Blo 267823 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B452695 : Blo 267823 452695 := bstep (se 1 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 452695 = 679043) B679043
theorem B1632473 : Blo 267823 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B911681 : Blo 267823 911681 := bstep (se 2 (by rfl) ⟨341880, by rfl⟩ : syracuseStep 911681 = 683761) B683761
theorem B1370519 : Blo 267823 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B453323 : Blo 267823 453323 := bstep (se 1 (by rfl) ⟨339992, by rfl⟩ : syracuseStep 453323 = 679985) B679985
theorem B1043147 : Blo 267823 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B1469249 : Blo 267823 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B453451 : Blo 267823 453451 := bstep (se 1 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 453451 = 680177) B680177
theorem B912221 : Blo 267823 912221 := bstep (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) B342083
theorem B289675 : Blo 267823 289675 := bstep (se 1 (by rfl) ⟨217256, by rfl⟩ : syracuseStep 289675 = 434513) B434513
theorem B682931 : Blo 267823 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B453593 : Blo 267823 453593 := bstep (se 2 (by rfl) ⟨170097, by rfl⟩ : syracuseStep 453593 = 340195) B340195
theorem B453721 : Blo 267823 453721 := bstep (se 2 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 453721 = 340291) B340291
theorem B683225 : Blo 267823 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B650713 : Blo 267823 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B454295 : Blo 267823 454295 := bstep (se 1 (by rfl) ⟨340721, by rfl⟩ : syracuseStep 454295 = 681443) B681443
theorem B487127 : Blo 267823 487127 := bstep (se 1 (by rfl) ⟨365345, by rfl⟩ : syracuseStep 487127 = 730691) B730691
theorem B454423 : Blo 267823 454423 := bstep (se 1 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 454423 = 681635) B681635
theorem B913355 : Blo 267823 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B618455 : Blo 267823 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B4124803 : Blo 267823 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B1339523 : Blo 267823 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B913625 : Blo 267823 913625 := bstep (se 2 (by rfl) ⟨342609, by rfl⟩ : syracuseStep 913625 = 685219) B685219
theorem B520435 : Blo 267823 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B487667 : Blo 267823 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B455051 : Blo 267823 455051 := bstep (se 1 (by rfl) ⟨341288, by rfl⟩ : syracuseStep 455051 = 682577) B682577
theorem B455179 : Blo 267823 455179 := bstep (se 1 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 455179 = 682769) B682769
theorem B455321 : Blo 267823 455321 := bstep (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) B341491
theorem B455449 : Blo 267823 455449 := bstep (se 2 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 455449 = 341587) B341587
theorem B684875 : Blo 267823 684875 := bstep (se 1 (by rfl) ⟨513656, by rfl⟩ : syracuseStep 684875 = 1027313) B1027313
theorem B914327 : Blo 267823 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B1930513 : Blo 267823 1930513 := bstep (se 2 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 1930513 = 1447885) B1447885
theorem B1537325 : Blo 267823 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B980299 : Blo 267823 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B456023 : Blo 267823 456023 := bstep (se 1 (by rfl) ⟨342017, by rfl⟩ : syracuseStep 456023 = 684035) B684035
theorem B914867 : Blo 267823 914867 := bstep (se 1 (by rfl) ⟨686150, by rfl⟩ : syracuseStep 914867 = 1372301) B1372301
theorem B456151 : Blo 267823 456151 := bstep (se 1 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 456151 = 684227) B684227
theorem B1734209 : Blo 267823 1734209 := bstep (se 2 (by rfl) ⟨650328, by rfl⟩ : syracuseStep 1734209 = 1300657) B1300657
theorem B652865 : Blo 267823 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B4126277 : Blo 267823 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B915137 : Blo 267823 915137 := bstep (se 2 (by rfl) ⟨343176, by rfl⟩ : syracuseStep 915137 = 686353) B686353
theorem B3077837 : Blo 267823 3077837 := bstep (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) B1154189
theorem B2062097 : Blo 267823 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B685847 : Blo 267823 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B1144621 : Blo 267823 1144621 := bstep (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) B429233
theorem B2094913 : Blo 267823 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1374083 : Blo 267823 1374083 := bstep (se 1 (by rfl) ⟨1030562, by rfl⟩ : syracuseStep 1374083 = 2061125) B2061125
theorem B489419 : Blo 267823 489419 := bstep (se 1 (by rfl) ⟨367064, by rfl⟩ : syracuseStep 489419 = 734129) B734129
theorem B1144793 : Blo 267823 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B1833025 : Blo 267823 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B456779 : Blo 267823 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B456907 : Blo 267823 456907 := bstep (se 1 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 456907 = 685361) B685361
theorem B915677 : Blo 267823 915677 := bstep (se 3 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 915677 = 343379) B343379
theorem B457049 : Blo 267823 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B686515 : Blo 267823 686515 := bstep (se 1 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 686515 = 1029773) B1029773
theorem B620993 : Blo 267823 620993 := bstep (se 2 (by rfl) ⟨232872, by rfl⟩ : syracuseStep 620993 = 465745) B465745
theorem B457177 : Blo 267823 457177 := bstep (se 2 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 457177 = 342883) B342883
theorem B686657 : Blo 267823 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B457751 : Blo 267823 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B490583 : Blo 267823 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B457879 : Blo 267823 457879 := bstep (se 1 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 457879 = 686819) B686819
theorem B916811 : Blo 267823 916811 := bstep (se 1 (by rfl) ⟨687608, by rfl⟩ : syracuseStep 916811 = 1375217) B1375217
theorem B1932761 : Blo 267823 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146433 : Blo 267823 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B917081 : Blo 267823 917081 := bstep (se 2 (by rfl) ⟨343905, by rfl⟩ : syracuseStep 917081 = 687811) B687811
theorem B458507 : Blo 267823 458507 := bstep (se 1 (by rfl) ⟨343880, by rfl⟩ : syracuseStep 458507 = 687761) B687761
theorem B687923 : Blo 267823 687923 := bstep (se 1 (by rfl) ⟨515942, by rfl⟩ : syracuseStep 687923 = 1031885) B1031885
theorem B655169 : Blo 267823 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B458635 : Blo 267823 458635 := bstep (se 1 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 458635 = 687953) B687953
theorem B1146923 : Blo 267823 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B35553649 : Blo 267823 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B3441041 : Blo 267823 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B5833397 : Blo 267823 5833397 := bstep (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) B546881
theorem B4588325 : Blo 267823 4588325 := bstep (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) B860311
theorem B820055 : Blo 267823 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B787979 : Blo 267823 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B1541699 : Blo 267823 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B7603789 : Blo 267823 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B821249 : Blo 267823 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B1148995 : Blo 267823 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B657665 : Blo 267823 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B11045443 : Blo 267823 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B3181123 : Blo 267823 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B12389219 : Blo 267823 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1379207 : Blo 267823 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B1018777 : Blo 267823 1018777 := bstep (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) B764083
theorem B1019081 : Blo 267823 1019081 := bstep (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) B764311
theorem B1543475 : Blo 267823 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B363961 : Blo 267823 363961 := bstep (se 2 (by rfl) ⟨136485, by rfl⟩ : syracuseStep 363961 = 272971) B272971
theorem B1642007 : Blo 267823 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B692311 : Blo 267823 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B1020023 : Blo 267823 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B1740973 : Blo 267823 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B15470837 : Blo 267823 15470837 := bstep (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) B1450391
theorem B1151441 : Blo 267823 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B1806967 : Blo 267823 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B1544933 : Blo 267823 1544933 := bstep (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) B289675
theorem B824107 : Blo 267823 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B725879 : Blo 267823 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B1020995 : Blo 267823 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B1545389 : Blo 267823 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B7968131 : Blo 267823 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1381835 : Blo 267823 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B267835 : Blo 267823 267835 := bstep (se 1 (by rfl) ⟨200876, by rfl⟩ : syracuseStep 267835 = 401753) B401753
theorem B267911 : Blo 267823 267911 := bstep (se 1 (by rfl) ⟨200933, by rfl⟩ : syracuseStep 267911 = 401867) B401867
theorem B267919 : Blo 267823 267919 := bstep (se 1 (by rfl) ⟨200939, by rfl⟩ : syracuseStep 267919 = 401879) B401879
theorem B267963 : Blo 267823 267963 := bstep (se 1 (by rfl) ⟨200972, by rfl⟩ : syracuseStep 267963 = 401945) B401945
theorem B268039 : Blo 267823 268039 := bstep (se 1 (by rfl) ⟨201029, by rfl⟩ : syracuseStep 268039 = 402059) B402059
theorem B268047 : Blo 267823 268047 := bstep (se 1 (by rfl) ⟨201035, by rfl⟩ : syracuseStep 268047 = 402071) B402071
theorem B268091 : Blo 267823 268091 := bstep (se 1 (by rfl) ⟨201068, by rfl⟩ : syracuseStep 268091 = 402137) B402137
theorem B1546073 : Blo 267823 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B268167 : Blo 267823 268167 := bstep (se 1 (by rfl) ⟨201125, by rfl⟩ : syracuseStep 268167 = 402251) B402251
theorem B268175 : Blo 267823 268175 := bstep (se 1 (by rfl) ⟨201131, by rfl⟩ : syracuseStep 268175 = 402263) B402263
theorem B268219 : Blo 267823 268219 := bstep (se 1 (by rfl) ⟨201164, by rfl⟩ : syracuseStep 268219 = 402329) B402329
theorem B268295 : Blo 267823 268295 := bstep (se 1 (by rfl) ⟨201221, by rfl⟩ : syracuseStep 268295 = 402443) B402443
theorem B268303 : Blo 267823 268303 := bstep (se 1 (by rfl) ⟨201227, by rfl⟩ : syracuseStep 268303 = 402455) B402455
theorem B268347 : Blo 267823 268347 := bstep (se 1 (by rfl) ⟨201260, by rfl⟩ : syracuseStep 268347 = 402521) B402521
theorem B268423 : Blo 267823 268423 := bstep (se 1 (by rfl) ⟨201317, by rfl⟩ : syracuseStep 268423 = 402635) B402635
theorem B268431 : Blo 267823 268431 := bstep (se 1 (by rfl) ⟨201323, by rfl⟩ : syracuseStep 268431 = 402647) B402647
theorem B268475 : Blo 267823 268475 := bstep (se 1 (by rfl) ⟨201356, by rfl⟩ : syracuseStep 268475 = 402713) B402713
theorem B268551 : Blo 267823 268551 := bstep (se 1 (by rfl) ⟨201413, by rfl⟩ : syracuseStep 268551 = 402827) B402827
theorem B268559 : Blo 267823 268559 := bstep (se 1 (by rfl) ⟨201419, by rfl⟩ : syracuseStep 268559 = 402839) B402839
theorem B268603 : Blo 267823 268603 := bstep (se 1 (by rfl) ⟨201452, by rfl⟩ : syracuseStep 268603 = 402905) B402905
theorem B268679 : Blo 267823 268679 := bstep (se 1 (by rfl) ⟨201509, by rfl⟩ : syracuseStep 268679 = 403019) B403019
theorem B268687 : Blo 267823 268687 := bstep (se 1 (by rfl) ⟨201515, by rfl⟩ : syracuseStep 268687 = 403031) B403031
theorem B268731 : Blo 267823 268731 := bstep (se 1 (by rfl) ⟨201548, by rfl⟩ : syracuseStep 268731 = 403097) B403097
theorem B268807 : Blo 267823 268807 := bstep (se 1 (by rfl) ⟨201605, by rfl⟩ : syracuseStep 268807 = 403211) B403211
theorem B268815 : Blo 267823 268815 := bstep (se 1 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 268815 = 403223) B403223
theorem B268859 : Blo 267823 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B268935 : Blo 267823 268935 := bstep (se 1 (by rfl) ⟨201701, by rfl⟩ : syracuseStep 268935 = 403403) B403403
theorem B301711 : Blo 267823 301711 := bstep (se 1 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 301711 = 452567) B452567
theorem B268943 : Blo 267823 268943 := bstep (se 1 (by rfl) ⟨201707, by rfl⟩ : syracuseStep 268943 = 403415) B403415
theorem B268987 : Blo 267823 268987 := bstep (se 1 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 268987 = 403481) B403481
theorem B1022665 : Blo 267823 1022665 := bstep (se 2 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 1022665 = 766999) B766999
theorem B269063 : Blo 267823 269063 := bstep (se 1 (by rfl) ⟨201797, by rfl⟩ : syracuseStep 269063 = 403595) B403595
theorem B269071 : Blo 267823 269071 := bstep (se 1 (by rfl) ⟨201803, by rfl⟩ : syracuseStep 269071 = 403607) B403607
theorem B1088315 : Blo 267823 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B269115 : Blo 267823 269115 := bstep (se 1 (by rfl) ⟨201836, by rfl⟩ : syracuseStep 269115 = 403673) B403673
theorem B1383227 : Blo 267823 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B269191 : Blo 267823 269191 := bstep (se 1 (by rfl) ⟨201893, by rfl⟩ : syracuseStep 269191 = 403787) B403787
theorem B269199 : Blo 267823 269199 := bstep (se 1 (by rfl) ⟨201899, by rfl⟩ : syracuseStep 269199 = 403799) B403799
theorem B269243 : Blo 267823 269243 := bstep (se 1 (by rfl) ⟨201932, by rfl⟩ : syracuseStep 269243 = 403865) B403865
theorem B400315 : Blo 267823 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B269319 : Blo 267823 269319 := bstep (se 1 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 269319 = 403979) B403979
theorem B269327 : Blo 267823 269327 := bstep (se 1 (by rfl) ⟨201995, by rfl⟩ : syracuseStep 269327 = 403991) B403991
theorem B269371 : Blo 267823 269371 := bstep (se 1 (by rfl) ⟨202028, by rfl⟩ : syracuseStep 269371 = 404057) B404057
theorem B1973335 : Blo 267823 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B302215 : Blo 267823 302215 := bstep (se 1 (by rfl) ⟨226661, by rfl⟩ : syracuseStep 302215 = 453323) B453323
theorem B269447 : Blo 267823 269447 := bstep (se 1 (by rfl) ⟨202085, by rfl⟩ : syracuseStep 269447 = 404171) B404171
theorem B695431 : Blo 267823 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B269455 : Blo 267823 269455 := bstep (se 1 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 269455 = 404183) B404183
theorem B269499 : Blo 267823 269499 := bstep (se 1 (by rfl) ⟨202124, by rfl⟩ : syracuseStep 269499 = 404249) B404249
theorem B269575 : Blo 267823 269575 := bstep (se 1 (by rfl) ⟨202181, by rfl⟩ : syracuseStep 269575 = 404363) B404363
theorem B269583 : Blo 267823 269583 := bstep (se 1 (by rfl) ⟨202187, by rfl⟩ : syracuseStep 269583 = 404375) B404375
theorem B302395 : Blo 267823 302395 := bstep (se 1 (by rfl) ⟨226796, by rfl⟩ : syracuseStep 302395 = 453593) B453593
theorem B269627 : Blo 267823 269627 := bstep (se 1 (by rfl) ⟨202220, by rfl⟩ : syracuseStep 269627 = 404441) B404441
theorem B269703 : Blo 267823 269703 := bstep (se 1 (by rfl) ⟨202277, by rfl⟩ : syracuseStep 269703 = 404555) B404555
theorem B269711 : Blo 267823 269711 := bstep (se 1 (by rfl) ⟨202283, by rfl⟩ : syracuseStep 269711 = 404567) B404567
theorem B269755 : Blo 267823 269755 := bstep (se 1 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 269755 = 404633) B404633
theorem B269831 : Blo 267823 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B269839 : Blo 267823 269839 := bstep (se 1 (by rfl) ⟨202379, by rfl⟩ : syracuseStep 269839 = 404759) B404759
theorem B269883 : Blo 267823 269883 := bstep (se 1 (by rfl) ⟨202412, by rfl⟩ : syracuseStep 269883 = 404825) B404825
theorem B269959 : Blo 267823 269959 := bstep (se 1 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 269959 = 404939) B404939
theorem B269967 : Blo 267823 269967 := bstep (se 1 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 269967 = 404951) B404951
theorem B4169393 : Blo 267823 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B270011 : Blo 267823 270011 := bstep (se 1 (by rfl) ⟨202508, by rfl⟩ : syracuseStep 270011 = 405017) B405017
theorem B1449701 : Blo 267823 1449701 := bstep (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) B271819
theorem B2793217 : Blo 267823 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B270087 : Blo 267823 270087 := bstep (se 1 (by rfl) ⟨202565, by rfl⟩ : syracuseStep 270087 = 405131) B405131
theorem B302863 : Blo 267823 302863 := bstep (se 1 (by rfl) ⟨227147, by rfl⟩ : syracuseStep 302863 = 454295) B454295
theorem B270095 : Blo 267823 270095 := bstep (se 1 (by rfl) ⟨202571, by rfl⟩ : syracuseStep 270095 = 405143) B405143
theorem B270139 : Blo 267823 270139 := bstep (se 1 (by rfl) ⟨202604, by rfl⟩ : syracuseStep 270139 = 405209) B405209
theorem B270215 : Blo 267823 270215 := bstep (se 1 (by rfl) ⟨202661, by rfl⟩ : syracuseStep 270215 = 405323) B405323
theorem B270223 : Blo 267823 270223 := bstep (se 1 (by rfl) ⟨202667, by rfl⟩ : syracuseStep 270223 = 405335) B405335
theorem B270267 : Blo 267823 270267 := bstep (se 1 (by rfl) ⟨202700, by rfl⟩ : syracuseStep 270267 = 405401) B405401
theorem B729089 : Blo 267823 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B270343 : Blo 267823 270343 := bstep (se 1 (by rfl) ⟨202757, by rfl⟩ : syracuseStep 270343 = 405515) B405515
theorem B270351 : Blo 267823 270351 := bstep (se 1 (by rfl) ⟨202763, by rfl⟩ : syracuseStep 270351 = 405527) B405527
theorem B270395 : Blo 267823 270395 := bstep (se 1 (by rfl) ⟨202796, by rfl⟩ : syracuseStep 270395 = 405593) B405593
theorem B893015 : Blo 267823 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B270471 : Blo 267823 270471 := bstep (se 1 (by rfl) ⟨202853, by rfl⟩ : syracuseStep 270471 = 405707) B405707
theorem B270479 : Blo 267823 270479 := bstep (se 1 (by rfl) ⟨202859, by rfl⟩ : syracuseStep 270479 = 405719) B405719
theorem B270523 : Blo 267823 270523 := bstep (se 1 (by rfl) ⟨202892, by rfl⟩ : syracuseStep 270523 = 405785) B405785
theorem B303367 : Blo 267823 303367 := bstep (se 1 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 303367 = 455051) B455051
theorem B270599 : Blo 267823 270599 := bstep (se 1 (by rfl) ⟨202949, by rfl⟩ : syracuseStep 270599 = 405899) B405899
theorem B270607 : Blo 267823 270607 := bstep (se 1 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 270607 = 405911) B405911
theorem B270651 : Blo 267823 270651 := bstep (se 1 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 270651 = 405977) B405977
theorem B401783 : Blo 267823 401783 := bstep (se 1 (by rfl) ⟨301337, by rfl⟩ : syracuseStep 401783 = 602675) B602675
theorem B729479 : Blo 267823 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B270727 : Blo 267823 270727 := bstep (se 1 (by rfl) ⟨203045, by rfl⟩ : syracuseStep 270727 = 406091) B406091
theorem B401807 : Blo 267823 401807 := bstep (se 1 (by rfl) ⟨301355, by rfl⟩ : syracuseStep 401807 = 602711) B602711
theorem B270735 : Blo 267823 270735 := bstep (se 1 (by rfl) ⟨203051, by rfl⟩ : syracuseStep 270735 = 406103) B406103
theorem B401849 : Blo 267823 401849 := bstep (se 2 (by rfl) ⟨150693, by rfl⟩ : syracuseStep 401849 = 301387) B301387
theorem B303547 : Blo 267823 303547 := bstep (se 1 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 303547 = 455321) B455321
theorem B270779 : Blo 267823 270779 := bstep (se 1 (by rfl) ⟨203084, by rfl⟩ : syracuseStep 270779 = 406169) B406169
theorem B401927 : Blo 267823 401927 := bstep (se 1 (by rfl) ⟨301445, by rfl⟩ : syracuseStep 401927 = 602891) B602891
theorem B270855 : Blo 267823 270855 := bstep (se 1 (by rfl) ⟨203141, by rfl⟩ : syracuseStep 270855 = 406283) B406283
theorem B270863 : Blo 267823 270863 := bstep (se 1 (by rfl) ⟨203147, by rfl⟩ : syracuseStep 270863 = 406295) B406295
theorem B401963 : Blo 267823 401963 := bstep (se 1 (by rfl) ⟨301472, by rfl⟩ : syracuseStep 401963 = 602945) B602945
theorem B270907 : Blo 267823 270907 := bstep (se 1 (by rfl) ⟨203180, by rfl⟩ : syracuseStep 270907 = 406361) B406361
theorem B401993 : Blo 267823 401993 := bstep (se 2 (by rfl) ⟨150747, by rfl⟩ : syracuseStep 401993 = 301495) B301495
theorem B270983 : Blo 267823 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B270991 : Blo 267823 270991 := bstep (se 1 (by rfl) ⟨203243, by rfl⟩ : syracuseStep 270991 = 406487) B406487
theorem B402107 : Blo 267823 402107 := bstep (se 1 (by rfl) ⟨301580, by rfl⟩ : syracuseStep 402107 = 603161) B603161
theorem B271035 : Blo 267823 271035 := bstep (se 1 (by rfl) ⟨203276, by rfl⟩ : syracuseStep 271035 = 406553) B406553
theorem B402167 : Blo 267823 402167 := bstep (se 1 (by rfl) ⟨301625, by rfl⟩ : syracuseStep 402167 = 603251) B603251
theorem B271111 : Blo 267823 271111 := bstep (se 1 (by rfl) ⟨203333, by rfl⟩ : syracuseStep 271111 = 406667) B406667
theorem B402191 : Blo 267823 402191 := bstep (se 1 (by rfl) ⟨301643, by rfl⟩ : syracuseStep 402191 = 603287) B603287
theorem B271119 : Blo 267823 271119 := bstep (se 1 (by rfl) ⟨203339, by rfl⟩ : syracuseStep 271119 = 406679) B406679
theorem B402233 : Blo 267823 402233 := bstep (se 2 (by rfl) ⟨150837, by rfl⟩ : syracuseStep 402233 = 301675) B301675
theorem B271163 : Blo 267823 271163 := bstep (se 1 (by rfl) ⟨203372, by rfl⟩ : syracuseStep 271163 = 406745) B406745
theorem B1024883 : Blo 267823 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B402311 : Blo 267823 402311 := bstep (se 1 (by rfl) ⟨301733, by rfl⟩ : syracuseStep 402311 = 603467) B603467
theorem B271239 : Blo 267823 271239 := bstep (se 1 (by rfl) ⟨203429, by rfl⟩ : syracuseStep 271239 = 406859) B406859
theorem B304015 : Blo 267823 304015 := bstep (se 1 (by rfl) ⟨228011, by rfl⟩ : syracuseStep 304015 = 456023) B456023
theorem B271247 : Blo 267823 271247 := bstep (se 1 (by rfl) ⟨203435, by rfl⟩ : syracuseStep 271247 = 406871) B406871
theorem B402347 : Blo 267823 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B271291 : Blo 267823 271291 := bstep (se 1 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 271291 = 406937) B406937
theorem B402377 : Blo 267823 402377 := bstep (se 2 (by rfl) ⟨150891, by rfl⟩ : syracuseStep 402377 = 301783) B301783
theorem B271367 : Blo 267823 271367 := bstep (se 1 (by rfl) ⟨203525, by rfl⟩ : syracuseStep 271367 = 407051) B407051
theorem B271375 : Blo 267823 271375 := bstep (se 1 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 271375 = 407063) B407063
theorem B1156139 : Blo 267823 1156139 := bstep (se 1 (by rfl) ⟨867104, by rfl⟩ : syracuseStep 1156139 = 1734209) B1734209
theorem B402491 : Blo 267823 402491 := bstep (se 1 (by rfl) ⟨301868, by rfl⟩ : syracuseStep 402491 = 603737) B603737
theorem B271419 : Blo 267823 271419 := bstep (se 1 (by rfl) ⟨203564, by rfl⟩ : syracuseStep 271419 = 407129) B407129
theorem B6628439 : Blo 267823 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B402551 : Blo 267823 402551 := bstep (se 1 (by rfl) ⟨301913, by rfl⟩ : syracuseStep 402551 = 603827) B603827
theorem B271495 : Blo 267823 271495 := bstep (se 1 (by rfl) ⟨203621, by rfl⟩ : syracuseStep 271495 = 407243) B407243
theorem B402575 : Blo 267823 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B271503 : Blo 267823 271503 := bstep (se 1 (by rfl) ⟨203627, by rfl⟩ : syracuseStep 271503 = 407255) B407255
theorem B402617 : Blo 267823 402617 := bstep (se 2 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 402617 = 301963) B301963
theorem B271547 : Blo 267823 271547 := bstep (se 1 (by rfl) ⟨203660, by rfl⟩ : syracuseStep 271547 = 407321) B407321
theorem B5154029 : Blo 267823 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B402695 : Blo 267823 402695 := bstep (se 1 (by rfl) ⟨302021, by rfl⟩ : syracuseStep 402695 = 604043) B604043
theorem B271623 : Blo 267823 271623 := bstep (se 1 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 271623 = 407435) B407435
theorem B271631 : Blo 267823 271631 := bstep (se 1 (by rfl) ⟨203723, by rfl⟩ : syracuseStep 271631 = 407447) B407447
theorem B402731 : Blo 267823 402731 := bstep (se 1 (by rfl) ⟨302048, by rfl⟩ : syracuseStep 402731 = 604097) B604097
theorem B763195 : Blo 267823 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B271675 : Blo 267823 271675 := bstep (se 1 (by rfl) ⟨203756, by rfl⟩ : syracuseStep 271675 = 407513) B407513
theorem B402761 : Blo 267823 402761 := bstep (se 2 (by rfl) ⟨151035, by rfl⟩ : syracuseStep 402761 = 302071) B302071
theorem B304519 : Blo 267823 304519 := bstep (se 1 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 304519 = 456779) B456779
theorem B271751 : Blo 267823 271751 := bstep (se 1 (by rfl) ⟨203813, by rfl⟩ : syracuseStep 271751 = 407627) B407627
theorem B271759 : Blo 267823 271759 := bstep (se 1 (by rfl) ⟨203819, by rfl⟩ : syracuseStep 271759 = 407639) B407639
theorem B402875 : Blo 267823 402875 := bstep (se 1 (by rfl) ⟨302156, by rfl⟩ : syracuseStep 402875 = 604313) B604313
theorem B271803 : Blo 267823 271803 := bstep (se 1 (by rfl) ⟨203852, by rfl⟩ : syracuseStep 271803 = 407705) B407705
theorem B402935 : Blo 267823 402935 := bstep (se 1 (by rfl) ⟨302201, by rfl⟩ : syracuseStep 402935 = 604403) B604403
theorem B402959 : Blo 267823 402959 := bstep (se 1 (by rfl) ⟨302219, by rfl⟩ : syracuseStep 402959 = 604439) B604439
theorem B403001 : Blo 267823 403001 := bstep (se 2 (by rfl) ⟨151125, by rfl⟩ : syracuseStep 403001 = 302251) B302251
theorem B304699 : Blo 267823 304699 := bstep (se 1 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 304699 = 457049) B457049
theorem B403079 : Blo 267823 403079 := bstep (se 1 (by rfl) ⟨302309, by rfl⟩ : syracuseStep 403079 = 604619) B604619
theorem B403115 : Blo 267823 403115 := bstep (se 1 (by rfl) ⟨302336, by rfl⟩ : syracuseStep 403115 = 604673) B604673
theorem B403145 : Blo 267823 403145 := bstep (se 2 (by rfl) ⟨151179, by rfl⟩ : syracuseStep 403145 = 302359) B302359
theorem B403259 : Blo 267823 403259 := bstep (se 1 (by rfl) ⟨302444, by rfl⟩ : syracuseStep 403259 = 604889) B604889
theorem B403319 : Blo 267823 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B731015 : Blo 267823 731015 := bstep (se 1 (by rfl) ⟨548261, by rfl⟩ : syracuseStep 731015 = 1096523) B1096523
theorem B403343 : Blo 267823 403343 := bstep (se 1 (by rfl) ⟨302507, by rfl⟩ : syracuseStep 403343 = 605015) B605015
theorem B403385 : Blo 267823 403385 := bstep (se 2 (by rfl) ⟨151269, by rfl⟩ : syracuseStep 403385 = 302539) B302539
theorem B403463 : Blo 267823 403463 := bstep (se 1 (by rfl) ⟨302597, by rfl⟩ : syracuseStep 403463 = 605195) B605195
theorem B305167 : Blo 267823 305167 := bstep (se 1 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 305167 = 457751) B457751
theorem B403499 : Blo 267823 403499 := bstep (se 1 (by rfl) ⟨302624, by rfl⟩ : syracuseStep 403499 = 605249) B605249
theorem B403529 : Blo 267823 403529 := bstep (se 2 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 403529 = 302647) B302647
theorem B1747117 : Blo 267823 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B403643 : Blo 267823 403643 := bstep (se 1 (by rfl) ⟨302732, by rfl⟩ : syracuseStep 403643 = 605465) B605465
theorem B403703 : Blo 267823 403703 := bstep (se 1 (by rfl) ⟨302777, by rfl⟩ : syracuseStep 403703 = 605555) B605555
theorem B403727 : Blo 267823 403727 := bstep (se 1 (by rfl) ⟨302795, by rfl⟩ : syracuseStep 403727 = 605591) B605591
theorem B403769 : Blo 267823 403769 := bstep (se 2 (by rfl) ⟨151413, by rfl⟩ : syracuseStep 403769 = 302827) B302827
theorem B2042171 : Blo 267823 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B403847 : Blo 267823 403847 := bstep (se 1 (by rfl) ⟨302885, by rfl⟩ : syracuseStep 403847 = 605771) B605771
theorem B403883 : Blo 267823 403883 := bstep (se 1 (by rfl) ⟨302912, by rfl⟩ : syracuseStep 403883 = 605825) B605825
theorem B403913 : Blo 267823 403913 := bstep (se 2 (by rfl) ⟨151467, by rfl⟩ : syracuseStep 403913 = 302935) B302935
theorem B305671 : Blo 267823 305671 := bstep (se 1 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 305671 = 458507) B458507
theorem B404027 : Blo 267823 404027 := bstep (se 1 (by rfl) ⟨303020, by rfl⟩ : syracuseStep 404027 = 606041) B606041
theorem B404087 : Blo 267823 404087 := bstep (se 1 (by rfl) ⟨303065, by rfl⟩ : syracuseStep 404087 = 606131) B606131
theorem B404111 : Blo 267823 404111 := bstep (se 1 (by rfl) ⟨303083, by rfl⟩ : syracuseStep 404111 = 606167) B606167
theorem B1485485 : Blo 267823 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B404153 : Blo 267823 404153 := bstep (se 2 (by rfl) ⟨151557, by rfl⟩ : syracuseStep 404153 = 303115) B303115
theorem B404231 : Blo 267823 404231 := bstep (se 1 (by rfl) ⟨303173, by rfl⟩ : syracuseStep 404231 = 606347) B606347
theorem B404267 : Blo 267823 404267 := bstep (se 1 (by rfl) ⟨303200, by rfl⟩ : syracuseStep 404267 = 606401) B606401
theorem B404297 : Blo 267823 404297 := bstep (se 2 (by rfl) ⟨151611, by rfl⟩ : syracuseStep 404297 = 303223) B303223
theorem B404411 : Blo 267823 404411 := bstep (se 1 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 404411 = 606617) B606617
theorem B1027025 : Blo 267823 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B404471 : Blo 267823 404471 := bstep (se 1 (by rfl) ⟨303353, by rfl⟩ : syracuseStep 404471 = 606707) B606707
theorem B404495 : Blo 267823 404495 := bstep (se 1 (by rfl) ⟨303371, by rfl⟩ : syracuseStep 404495 = 606743) B606743
theorem B404537 : Blo 267823 404537 := bstep (se 2 (by rfl) ⟨151701, by rfl⟩ : syracuseStep 404537 = 303403) B303403
theorem B404615 : Blo 267823 404615 := bstep (se 1 (by rfl) ⟨303461, by rfl⟩ : syracuseStep 404615 = 606923) B606923
theorem B404651 : Blo 267823 404651 := bstep (se 1 (by rfl) ⟨303488, by rfl⟩ : syracuseStep 404651 = 606977) B606977
theorem B404681 : Blo 267823 404681 := bstep (se 2 (by rfl) ⟨151755, by rfl⟩ : syracuseStep 404681 = 303511) B303511
theorem B1027343 : Blo 267823 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B404795 : Blo 267823 404795 := bstep (se 1 (by rfl) ⟨303596, by rfl⟩ : syracuseStep 404795 = 607193) B607193
theorem B339319 : Blo 267823 339319 := bstep (se 1 (by rfl) ⟨254489, by rfl⟩ : syracuseStep 339319 = 508979) B508979
theorem B404855 : Blo 267823 404855 := bstep (se 1 (by rfl) ⟨303641, by rfl⟩ : syracuseStep 404855 = 607283) B607283
theorem B404879 : Blo 267823 404879 := bstep (se 1 (by rfl) ⟨303659, by rfl⟩ : syracuseStep 404879 = 607319) B607319
theorem B404921 : Blo 267823 404921 := bstep (se 2 (by rfl) ⟨151845, by rfl⟩ : syracuseStep 404921 = 303691) B303691
theorem B404999 : Blo 267823 404999 := bstep (se 1 (by rfl) ⟨303749, by rfl⟩ : syracuseStep 404999 = 607499) B607499
theorem B405035 : Blo 267823 405035 := bstep (se 1 (by rfl) ⟨303776, by rfl⟩ : syracuseStep 405035 = 607553) B607553
theorem B405065 : Blo 267823 405065 := bstep (se 2 (by rfl) ⟨151899, by rfl⟩ : syracuseStep 405065 = 303799) B303799
theorem B24850061 : Blo 267823 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B765587 : Blo 267823 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B339643 : Blo 267823 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B405179 : Blo 267823 405179 := bstep (se 1 (by rfl) ⟨303884, by rfl⟩ : syracuseStep 405179 = 607769) B607769
theorem B405239 : Blo 267823 405239 := bstep (se 1 (by rfl) ⟨303929, by rfl⟩ : syracuseStep 405239 = 607859) B607859
theorem B405263 : Blo 267823 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B3288883 : Blo 267823 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B405305 : Blo 267823 405305 := bstep (se 2 (by rfl) ⟨151989, by rfl⟩ : syracuseStep 405305 = 303979) B303979
theorem B1650547 : Blo 267823 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B405383 : Blo 267823 405383 := bstep (se 1 (by rfl) ⟨304037, by rfl⟩ : syracuseStep 405383 = 608075) B608075
theorem B405419 : Blo 267823 405419 := bstep (se 1 (by rfl) ⟨304064, by rfl⟩ : syracuseStep 405419 = 608129) B608129
theorem B405449 : Blo 267823 405449 := bstep (se 2 (by rfl) ⟨152043, by rfl⟩ : syracuseStep 405449 = 304087) B304087
theorem B405563 : Blo 267823 405563 := bstep (se 1 (by rfl) ⟨304172, by rfl⟩ : syracuseStep 405563 = 608345) B608345
theorem B405623 : Blo 267823 405623 := bstep (se 1 (by rfl) ⟨304217, by rfl⟩ : syracuseStep 405623 = 608435) B608435
theorem B405647 : Blo 267823 405647 := bstep (se 1 (by rfl) ⟨304235, by rfl⟩ : syracuseStep 405647 = 608471) B608471
theorem B340139 : Blo 267823 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B405689 : Blo 267823 405689 := bstep (se 2 (by rfl) ⟨152133, by rfl⟩ : syracuseStep 405689 = 304267) B304267
theorem B405767 : Blo 267823 405767 := bstep (se 1 (by rfl) ⟨304325, by rfl⟩ : syracuseStep 405767 = 608651) B608651
theorem B2601233 : Blo 267823 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B405803 : Blo 267823 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B405833 : Blo 267823 405833 := bstep (se 2 (by rfl) ⟨152187, by rfl⟩ : syracuseStep 405833 = 304375) B304375
theorem B766361 : Blo 267823 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B405947 : Blo 267823 405947 := bstep (se 1 (by rfl) ⟨304460, by rfl⟩ : syracuseStep 405947 = 608921) B608921
theorem B406007 : Blo 267823 406007 := bstep (se 1 (by rfl) ⟨304505, by rfl⟩ : syracuseStep 406007 = 609011) B609011
theorem B602639 : Blo 267823 602639 := bstep (se 1 (by rfl) ⟨451979, by rfl⟩ : syracuseStep 602639 = 903959) B903959
theorem B406031 : Blo 267823 406031 := bstep (se 1 (by rfl) ⟨304523, by rfl⟩ : syracuseStep 406031 = 609047) B609047
theorem B1290775 : Blo 267823 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B602657 : Blo 267823 602657 := bstep (se 2 (by rfl) ⟨225996, by rfl⟩ : syracuseStep 602657 = 451993) B451993
theorem B406073 : Blo 267823 406073 := bstep (se 2 (by rfl) ⟨152277, by rfl⟩ : syracuseStep 406073 = 304555) B304555
theorem B340615 : Blo 267823 340615 := bstep (se 1 (by rfl) ⟨255461, by rfl⟩ : syracuseStep 340615 = 510923) B510923
theorem B406151 : Blo 267823 406151 := bstep (se 1 (by rfl) ⟨304613, by rfl⟩ : syracuseStep 406151 = 609227) B609227
theorem B406187 : Blo 267823 406187 := bstep (se 1 (by rfl) ⟨304640, by rfl⟩ : syracuseStep 406187 = 609281) B609281
theorem B406217 : Blo 267823 406217 := bstep (se 2 (by rfl) ⟨152331, by rfl⟩ : syracuseStep 406217 = 304663) B304663
theorem B406331 : Blo 267823 406331 := bstep (se 1 (by rfl) ⟨304748, by rfl⟩ : syracuseStep 406331 = 609497) B609497
theorem B602999 : Blo 267823 602999 := bstep (se 1 (by rfl) ⟨452249, by rfl⟩ : syracuseStep 602999 = 904499) B904499
theorem B406391 : Blo 267823 406391 := bstep (se 1 (by rfl) ⟨304793, by rfl⟩ : syracuseStep 406391 = 609587) B609587
theorem B406415 : Blo 267823 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B406457 : Blo 267823 406457 := bstep (se 2 (by rfl) ⟨152421, by rfl⟩ : syracuseStep 406457 = 304843) B304843
theorem B406535 : Blo 267823 406535 := bstep (se 1 (by rfl) ⟨304901, by rfl⟩ : syracuseStep 406535 = 609803) B609803
theorem B1553431 : Blo 267823 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B603179 : Blo 267823 603179 := bstep (se 1 (by rfl) ⟨452384, by rfl⟩ : syracuseStep 603179 = 904769) B904769
theorem B406571 : Blo 267823 406571 := bstep (se 1 (by rfl) ⟨304928, by rfl⟩ : syracuseStep 406571 = 609857) B609857
theorem B406601 : Blo 267823 406601 := bstep (se 2 (by rfl) ⟨152475, by rfl⟩ : syracuseStep 406601 = 304951) B304951
theorem B341111 : Blo 267823 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B406715 : Blo 267823 406715 := bstep (se 1 (by rfl) ⟨305036, by rfl⟩ : syracuseStep 406715 = 610073) B610073
theorem B406775 : Blo 267823 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B341263 : Blo 267823 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B406799 : Blo 267823 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B406841 : Blo 267823 406841 := bstep (se 2 (by rfl) ⟨152565, by rfl⟩ : syracuseStep 406841 = 305131) B305131
theorem B406919 : Blo 267823 406919 := bstep (se 1 (by rfl) ⟨305189, by rfl⟩ : syracuseStep 406919 = 610379) B610379
theorem B603539 : Blo 267823 603539 := bstep (se 1 (by rfl) ⟨452654, by rfl⟩ : syracuseStep 603539 = 905309) B905309
theorem B406955 : Blo 267823 406955 := bstep (se 1 (by rfl) ⟨305216, by rfl⟩ : syracuseStep 406955 = 610433) B610433
theorem B341435 : Blo 267823 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B603593 : Blo 267823 603593 := bstep (se 2 (by rfl) ⟨226347, by rfl⟩ : syracuseStep 603593 = 452695) B452695
theorem B406985 : Blo 267823 406985 := bstep (se 2 (by rfl) ⟨152619, by rfl⟩ : syracuseStep 406985 = 305239) B305239
theorem B407099 : Blo 267823 407099 := bstep (se 1 (by rfl) ⟨305324, by rfl⟩ : syracuseStep 407099 = 610649) B610649
theorem B407159 : Blo 267823 407159 := bstep (se 1 (by rfl) ⟨305369, by rfl⟩ : syracuseStep 407159 = 610739) B610739
theorem B407183 : Blo 267823 407183 := bstep (se 1 (by rfl) ⟨305387, by rfl⟩ : syracuseStep 407183 = 610775) B610775
theorem B407225 : Blo 267823 407225 := bstep (se 2 (by rfl) ⟨152709, by rfl⟩ : syracuseStep 407225 = 305419) B305419
theorem B407303 : Blo 267823 407303 := bstep (se 1 (by rfl) ⟨305477, by rfl⟩ : syracuseStep 407303 = 610955) B610955
theorem B407339 : Blo 267823 407339 := bstep (se 1 (by rfl) ⟨305504, by rfl⟩ : syracuseStep 407339 = 611009) B611009
theorem B407369 : Blo 267823 407369 := bstep (se 2 (by rfl) ⟨152763, by rfl⟩ : syracuseStep 407369 = 305527) B305527
theorem B1357721 : Blo 267823 1357721 := bstep (se 2 (by rfl) ⟨509145, by rfl⟩ : syracuseStep 1357721 = 1018291) B1018291
theorem B407483 : Blo 267823 407483 := bstep (se 1 (by rfl) ⟨305612, by rfl⟩ : syracuseStep 407483 = 611225) B611225
theorem B407543 : Blo 267823 407543 := bstep (se 1 (by rfl) ⟨305657, by rfl⟩ : syracuseStep 407543 = 611315) B611315
theorem B407567 : Blo 267823 407567 := bstep (se 1 (by rfl) ⟨305675, by rfl⟩ : syracuseStep 407567 = 611351) B611351
theorem B407609 : Blo 267823 407609 := bstep (se 2 (by rfl) ⟨152853, by rfl⟩ : syracuseStep 407609 = 305707) B305707
theorem B1226819 : Blo 267823 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B604295 : Blo 267823 604295 := bstep (se 1 (by rfl) ⟨453221, by rfl⟩ : syracuseStep 604295 = 906443) B906443
theorem B407687 : Blo 267823 407687 := bstep (se 1 (by rfl) ⟨305765, by rfl⟩ : syracuseStep 407687 = 611531) B611531
theorem B407723 : Blo 267823 407723 := bstep (se 1 (by rfl) ⟨305792, by rfl⟩ : syracuseStep 407723 = 611585) B611585
theorem B604475 : Blo 267823 604475 := bstep (se 1 (by rfl) ⟨453356, by rfl⟩ : syracuseStep 604475 = 906713) B906713
theorem B26589505 : Blo 267823 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B342407 : Blo 267823 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B604601 : Blo 267823 604601 := bstep (se 2 (by rfl) ⟨226725, by rfl⟩ : syracuseStep 604601 = 453451) B453451
theorem B768457 : Blo 267823 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B1030913 : Blo 267823 1030913 := bstep (se 2 (by rfl) ⟨386592, by rfl⟩ : syracuseStep 1030913 = 773185) B773185
theorem B604943 : Blo 267823 604943 := bstep (se 1 (by rfl) ⟨453707, by rfl⟩ : syracuseStep 604943 = 907415) B907415
theorem B1030927 : Blo 267823 1030927 := bstep (se 1 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 1030927 = 1546391) B1546391
theorem B604961 : Blo 267823 604961 := bstep (se 2 (by rfl) ⟨226860, by rfl⟩ : syracuseStep 604961 = 453721) B453721
theorem B3095333 : Blo 267823 3095333 := bstep (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) B580375
theorem B768811 : Blo 267823 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B343055 : Blo 267823 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B769085 : Blo 267823 769085 := bstep (se 3 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 769085 = 288407) B288407
theorem B5160023 : Blo 267823 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B605303 : Blo 267823 605303 := bstep (se 1 (by rfl) ⟨453977, by rfl⟩ : syracuseStep 605303 = 907955) B907955
theorem B572687 : Blo 267823 572687 := bstep (se 1 (by rfl) ⟨429515, by rfl⟩ : syracuseStep 572687 = 859031) B859031
theorem B867617 : Blo 267823 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B605483 : Blo 267823 605483 := bstep (se 1 (by rfl) ⟨454112, by rfl⟩ : syracuseStep 605483 = 908225) B908225
theorem B572807 : Blo 267823 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B2047517 : Blo 267823 2047517 := bstep (se 3 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 2047517 = 767819) B767819
theorem B572987 : Blo 267823 572987 := bstep (se 1 (by rfl) ⟨429740, by rfl⟩ : syracuseStep 572987 = 859481) B859481
theorem B605843 : Blo 267823 605843 := bstep (se 1 (by rfl) ⟨454382, by rfl⟩ : syracuseStep 605843 = 908765) B908765
theorem B5193395 : Blo 267823 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B605897 : Blo 267823 605897 := bstep (se 2 (by rfl) ⟨227211, by rfl⟩ : syracuseStep 605897 = 454423) B454423
theorem B2211851 : Blo 267823 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B573473 : Blo 267823 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B606599 : Blo 267823 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B1360313 : Blo 267823 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B606779 : Blo 267823 606779 := bstep (se 1 (by rfl) ⟨455084, by rfl⟩ : syracuseStep 606779 = 910169) B910169
theorem B1294967 : Blo 267823 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B606905 : Blo 267823 606905 := bstep (se 2 (by rfl) ⟨227589, by rfl⟩ : syracuseStep 606905 = 455179) B455179
theorem B574327 : Blo 267823 574327 := bstep (se 1 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 574327 = 861491) B861491
theorem B2933657 : Blo 267823 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B607247 : Blo 267823 607247 := bstep (se 1 (by rfl) ⟨455435, by rfl⟩ : syracuseStep 607247 = 910871) B910871
theorem B607265 : Blo 267823 607265 := bstep (se 2 (by rfl) ⟨227724, by rfl⟩ : syracuseStep 607265 = 455449) B455449
theorem B771191 : Blo 267823 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B607607 : Blo 267823 607607 := bstep (se 1 (by rfl) ⟨455705, by rfl⟩ : syracuseStep 607607 = 911411) B911411
theorem B607787 : Blo 267823 607787 := bstep (se 1 (by rfl) ⟨455840, by rfl⟩ : syracuseStep 607787 = 911681) B911681
theorem B1164887 : Blo 267823 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B2574017 : Blo 267823 2574017 := bstep (se 2 (by rfl) ⟨965256, by rfl⟩ : syracuseStep 2574017 = 1930513) B1930513
theorem B1361609 : Blo 267823 1361609 := bstep (se 2 (by rfl) ⟨510603, by rfl⟩ : syracuseStep 1361609 = 1021207) B1021207
theorem B608147 : Blo 267823 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B608201 : Blo 267823 608201 := bstep (se 2 (by rfl) ⟨228075, by rfl⟩ : syracuseStep 608201 = 456151) B456151
theorem B1296755 : Blo 267823 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B1526161 : Blo 267823 1526161 := bstep (se 2 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 1526161 = 1144621) B1144621
theorem B608903 : Blo 267823 608903 := bstep (se 1 (by rfl) ⟨456677, by rfl⟩ : syracuseStep 608903 = 913355) B913355
theorem B412303 : Blo 267823 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B2444033 : Blo 267823 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B510779 : Blo 267823 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B609083 : Blo 267823 609083 := bstep (se 1 (by rfl) ⟨456812, by rfl⟩ : syracuseStep 609083 = 913625) B913625
theorem B904121 : Blo 267823 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B609209 : Blo 267823 609209 := bstep (se 2 (by rfl) ⟨228453, by rfl⟩ : syracuseStep 609209 = 456907) B456907
theorem B609551 : Blo 267823 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B511265 : Blo 267823 511265 := bstep (se 2 (by rfl) ⟨191724, by rfl⟩ : syracuseStep 511265 = 383449) B383449
theorem B609569 : Blo 267823 609569 := bstep (se 2 (by rfl) ⟨228588, by rfl⟩ : syracuseStep 609569 = 457177) B457177
theorem B904715 : Blo 267823 904715 := bstep (se 1 (by rfl) ⟨678536, by rfl⟩ : syracuseStep 904715 = 1357073) B1357073
theorem B1166891 : Blo 267823 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B773675 : Blo 267823 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B904823 : Blo 267823 904823 := bstep (se 1 (by rfl) ⟨678617, by rfl⟩ : syracuseStep 904823 = 1357235) B1357235
theorem B609911 : Blo 267823 609911 := bstep (se 1 (by rfl) ⟨457433, by rfl⟩ : syracuseStep 609911 = 914867) B914867
theorem B610091 : Blo 267823 610091 := bstep (se 1 (by rfl) ⟨457568, by rfl⟩ : syracuseStep 610091 = 915137) B915137
theorem B2051891 : Blo 267823 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B4640813 : Blo 267823 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B610451 : Blo 267823 610451 := bstep (se 1 (by rfl) ⟨457838, by rfl⟩ : syracuseStep 610451 = 915677) B915677
theorem B905417 : Blo 267823 905417 := bstep (se 2 (by rfl) ⟨339531, by rfl⟩ : syracuseStep 905417 = 679063) B679063
theorem B610505 : Blo 267823 610505 := bstep (se 2 (by rfl) ⟨228939, by rfl⟩ : syracuseStep 610505 = 457879) B457879
theorem B971023 : Blo 267823 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B413995 : Blo 267823 413995 := bstep (se 1 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 413995 = 620993) B620993
theorem B578249 : Blo 267823 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B1528577 : Blo 267823 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B1299215 : Blo 267823 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B1299233 : Blo 267823 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B906119 : Blo 267823 906119 := bstep (se 1 (by rfl) ⟨679589, by rfl⟩ : syracuseStep 906119 = 1359179) B1359179
theorem B611207 : Blo 267823 611207 := bstep (se 1 (by rfl) ⟨458405, by rfl⟩ : syracuseStep 611207 = 916811) B916811
theorem B3265433 : Blo 267823 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B611387 : Blo 267823 611387 := bstep (se 1 (by rfl) ⟨458540, by rfl⟩ : syracuseStep 611387 = 917081) B917081
theorem B1299523 : Blo 267823 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B382087 : Blo 267823 382087 := bstep (se 1 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 382087 = 573131) B573131
theorem B513209 : Blo 267823 513209 := bstep (se 2 (by rfl) ⟨192453, by rfl⟩ : syracuseStep 513209 = 384907) B384907
theorem B611513 : Blo 267823 611513 := bstep (se 2 (by rfl) ⟨229317, by rfl⟩ : syracuseStep 611513 = 458635) B458635
theorem B906497 : Blo 267823 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B579001 : Blo 267823 579001 := bstep (se 2 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 579001 = 434251) B434251
theorem B5199389 : Blo 267823 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B2610731 : Blo 267823 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B382583 : Blo 267823 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B972407 : Blo 267823 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B2185163 : Blo 267823 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B1300445 : Blo 267823 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B1038347 : Blo 267823 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B907307 : Blo 267823 907307 := bstep (se 1 (by rfl) ⟨680480, by rfl⟩ : syracuseStep 907307 = 1360961) B1360961
theorem B678041 : Blo 267823 678041 := bstep (se 2 (by rfl) ⟨254265, by rfl⟩ : syracuseStep 678041 = 508531) B508531
theorem B1464493 : Blo 267823 1464493 := bstep (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) B549185
theorem B678203 : Blo 267823 678203 := bstep (se 1 (by rfl) ⟨508652, by rfl⟩ : syracuseStep 678203 = 1017305) B1017305
theorem B514363 : Blo 267823 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B678415 : Blo 267823 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B383545 : Blo 267823 383545 := bstep (se 2 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 383545 = 287659) B287659
theorem B2775653 : Blo 267823 2775653 := bstep (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) B520435
theorem B678689 : Blo 267823 678689 := bstep (se 2 (by rfl) ⟨254508, by rfl⟩ : syracuseStep 678689 = 509017) B509017
theorem B514849 : Blo 267823 514849 := bstep (se 2 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 514849 = 386137) B386137
theorem B383887 : Blo 267823 383887 := bstep (se 1 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 383887 = 575831) B575831
theorem B973721 : Blo 267823 973721 := bstep (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) B730291
theorem B2579363 : Blo 267823 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B1530809 : Blo 267823 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B1465615 : Blo 267823 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B908603 : Blo 267823 908603 := bstep (se 1 (by rfl) ⟨681452, by rfl⟩ : syracuseStep 908603 = 1362905) B1362905
theorem B3366203 : Blo 267823 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B1367441 : Blo 267823 1367441 := bstep (se 2 (by rfl) ⟨512790, by rfl⟩ : syracuseStep 1367441 = 1025581) B1025581
theorem B1236541 : Blo 267823 1236541 := bstep (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) B463703
theorem B679691 : Blo 267823 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B909089 : Blo 267823 909089 := bstep (se 2 (by rfl) ⟨340908, by rfl⟩ : syracuseStep 909089 = 681817) B681817
theorem B516041 : Blo 267823 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B385015 : Blo 267823 385015 := bstep (se 1 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 385015 = 577523) B577523
theorem B3072005 : Blo 267823 3072005 := bstep (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) B576001
theorem B614459 : Blo 267823 614459 := bstep (se 1 (by rfl) ⟨460844, by rfl⟩ : syracuseStep 614459 = 921689) B921689
theorem B614585 : Blo 267823 614585 := bstep (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) B460939
theorem B286907 : Blo 267823 286907 := bstep (se 1 (by rfl) ⟨215180, by rfl⟩ : syracuseStep 286907 = 430361) B430361
theorem B909683 : Blo 267823 909683 := bstep (se 1 (by rfl) ⟨682262, by rfl⟩ : syracuseStep 909683 = 1364525) B1364525
theorem B680339 : Blo 267823 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B2089475 : Blo 267823 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1466999 : Blo 267823 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1401517 : Blo 267823 1401517 := bstep (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) B525569
theorem B680633 : Blo 267823 680633 := bstep (se 2 (by rfl) ⟨255237, by rfl⟩ : syracuseStep 680633 = 510475) B510475
theorem B1467173 : Blo 267823 1467173 := bstep (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) B275095
theorem B648071 : Blo 267823 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B549817 : Blo 267823 549817 := bstep (se 2 (by rfl) ⟨206181, by rfl⟩ : syracuseStep 549817 = 412363) B412363
theorem B1467395 : Blo 267823 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B1532951 : Blo 267823 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B32531717 : Blo 267823 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B681331 : Blo 267823 681331 := bstep (se 1 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 681331 = 1021997) B1021997
theorem B1369547 : Blo 267823 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B681473 : Blo 267823 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B1533451 : Blo 267823 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B452155 : Blo 267823 452155 := bstep (se 1 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 452155 = 678233) B678233
theorem B452297 : Blo 267823 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B1369871 : Blo 267823 1369871 := bstep (se 1 (by rfl) ⟨1027403, by rfl⟩ : syracuseStep 1369871 = 2054807) B2054807
theorem B1173263 : Blo 267823 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B649079 : Blo 267823 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B550775 : Blo 267823 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B681929 : Blo 267823 681929 := bstep (se 2 (by rfl) ⟨255723, by rfl⟩ : syracuseStep 681929 = 511447) B511447
theorem B419831 : Blo 267823 419831 := bstep (se 1 (by rfl) ⟨314873, by rfl⟩ : syracuseStep 419831 = 629747) B629747
theorem B682283 : Blo 267823 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B452999 : Blo 267823 452999 := bstep (se 1 (by rfl) ⟨339749, by rfl⟩ : syracuseStep 452999 = 679499) B679499
theorem B3303827 : Blo 267823 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B780815 : Blo 267823 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B649847 : Blo 267823 649847 := bstep (se 1 (by rfl) ⟨487385, by rfl⟩ : syracuseStep 649847 = 974771) B974771
theorem B1174135 : Blo 267823 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B3893953 : Blo 267823 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B5499737 : Blo 267823 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B912275 : Blo 267823 912275 := bstep (se 1 (by rfl) ⟨684206, by rfl⟩ : syracuseStep 912275 = 1368413) B1368413
theorem B5565347 : Blo 267823 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B453647 : Blo 267823 453647 := bstep (se 1 (by rfl) ⟨340235, by rfl⟩ : syracuseStep 453647 = 680471) B680471
theorem B1371329 : Blo 267823 1371329 := bstep (se 2 (by rfl) ⟨514248, by rfl⟩ : syracuseStep 1371329 = 1028497) B1028497
theorem B683275 : Blo 267823 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B650539 : Blo 267823 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B2059667 : Blo 267823 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B683417 : Blo 267823 683417 := bstep (se 2 (by rfl) ⟨256281, by rfl⟩ : syracuseStep 683417 = 512563) B512563
theorem B1535435 : Blo 267823 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B814607 : Blo 267823 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B978461 : Blo 267823 978461 := bstep (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) B366923
theorem B454187 : Blo 267823 454187 := bstep (se 1 (by rfl) ⟨340640, by rfl⟩ : syracuseStep 454187 = 681281) B681281
theorem B683579 : Blo 267823 683579 := bstep (se 1 (by rfl) ⟨512684, by rfl⟩ : syracuseStep 683579 = 1025369) B1025369
theorem B5009203 : Blo 267823 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B683923 : Blo 267823 683923 := bstep (se 1 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 683923 = 1025885) B1025885
theorem B454585 : Blo 267823 454585 := bstep (se 2 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 454585 = 340939) B340939
theorem B684065 : Blo 267823 684065 := bstep (se 2 (by rfl) ⟨256524, by rfl⟩ : syracuseStep 684065 = 513049) B513049
theorem B487559 : Blo 267823 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B913679 : Blo 267823 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B1307065 : Blo 267823 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B1372625 : Blo 267823 1372625 := bstep (se 2 (by rfl) ⟨514734, by rfl⟩ : syracuseStep 1372625 = 1029469) B1029469
theorem B913949 : Blo 267823 913949 := bstep (se 3 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 913949 = 342731) B342731
theorem B979499 : Blo 267823 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B455287 : Blo 267823 455287 := bstep (se 1 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 455287 = 682931) B682931
theorem B5796643 : Blo 267823 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B455483 : Blo 267823 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B815933 : Blo 267823 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B685057 : Blo 267823 685057 := bstep (se 2 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 685057 = 513793) B513793
theorem B324751 : Blo 267823 324751 := bstep (se 1 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 324751 = 487127) B487127
theorem B455881 : Blo 267823 455881 := bstep (se 2 (by rfl) ⟨170955, by rfl⟩ : syracuseStep 455881 = 341911) B341911
theorem B1308221 : Blo 267823 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B685655 : Blo 267823 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B2291429 : Blo 267823 2291429 := bstep (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) B429643
theorem B1537825 : Blo 267823 1537825 := bstep (se 2 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 1537825 = 1153369) B1153369
theorem B685867 : Blo 267823 685867 := bstep (se 1 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 685867 = 1028801) B1028801
theorem B1144691 : Blo 267823 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B456583 : Blo 267823 456583 := bstep (se 1 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 456583 = 684875) B684875
theorem B915353 : Blo 267823 915353 := bstep (se 2 (by rfl) ⟨343257, by rfl⟩ : syracuseStep 915353 = 686515) B686515
theorem B686009 : Blo 267823 686009 := bstep (se 2 (by rfl) ⟨257253, by rfl⟩ : syracuseStep 686009 = 514507) B514507
theorem B1112093 : Blo 267823 1112093 := bstep (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) B417035
theorem B2750851 : Blo 267823 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B2587085 : Blo 267823 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B1374731 : Blo 267823 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B457231 : Blo 267823 457231 := bstep (se 1 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 457231 = 685847) B685847
theorem B916055 : Blo 267823 916055 := bstep (se 1 (by rfl) ⟨687041, by rfl⟩ : syracuseStep 916055 = 1374083) B1374083
theorem B326279 : Blo 267823 326279 := bstep (se 1 (by rfl) ⟨244709, by rfl⟩ : syracuseStep 326279 = 489419) B489419
theorem B1374893 : Blo 267823 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B687001 : Blo 267823 687001 := bstep (se 2 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 687001 = 515251) B515251
theorem B1539101 : Blo 267823 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B457771 : Blo 267823 457771 := bstep (se 1 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 457771 = 686657) B686657
theorem B687163 : Blo 267823 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B916541 : Blo 267823 916541 := bstep (se 3 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 916541 = 343703) B343703
theorem B457913 : Blo 267823 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B687305 : Blo 267823 687305 := bstep (se 2 (by rfl) ⟨257739, by rfl⟩ : syracuseStep 687305 = 515479) B515479
theorem B687649 : Blo 267823 687649 := bstep (se 2 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 687649 = 515737) B515737
theorem B458615 : Blo 267823 458615 := bstep (se 1 (by rfl) ⟨343961, by rfl⟩ : syracuseStep 458615 = 687923) B687923
theorem B5898269 : Blo 267823 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2294027 : Blo 267823 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B1638893 : Blo 267823 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B1868689 : Blo 267823 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1017593 : Blo 267823 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B8259479 : Blo 267823 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B919471 : Blo 267823 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1935677 : Blo 267823 1935677 := bstep (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) B725879
theorem B2329489 : Blo 267823 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1019051 : Blo 267823 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B2034881 : Blo 267823 2034881 := bstep (se 2 (by rfl) ⟨763080, by rfl⟩ : syracuseStep 2034881 = 1526161) B1526161
theorem B9637157 : Blo 267823 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B5312087 : Blo 267823 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B921223 : Blo 267823 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B1740487 : Blo 267823 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B692231 : Blo 267823 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B2101277 : Blo 267823 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B1020221 : Blo 267823 1020221 := bstep (se 3 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 1020221 = 382583) B382583
theorem B725543 : Blo 267823 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B922151 : Blo 267823 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 267823 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B595343 : Blo 267823 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B923081 : Blo 267823 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B267855 : Blo 267823 267855 := bstep (se 1 (by rfl) ⟨200891, by rfl⟩ : syracuseStep 267855 = 401783) B401783
theorem B267871 : Blo 267823 267871 := bstep (se 1 (by rfl) ⟨200903, by rfl⟩ : syracuseStep 267871 = 401807) B401807
theorem B267899 : Blo 267823 267899 := bstep (se 1 (by rfl) ⟨200924, by rfl⟩ : syracuseStep 267899 = 401849) B401849
theorem B267951 : Blo 267823 267951 := bstep (se 1 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 267951 = 401927) B401927
theorem B267975 : Blo 267823 267975 := bstep (se 1 (by rfl) ⟨200981, by rfl⟩ : syracuseStep 267975 = 401963) B401963
theorem B267995 : Blo 267823 267995 := bstep (se 1 (by rfl) ⟨200996, by rfl⟩ : syracuseStep 267995 = 401993) B401993
theorem B268071 : Blo 267823 268071 := bstep (se 1 (by rfl) ⟨201053, by rfl⟩ : syracuseStep 268071 = 402107) B402107
theorem B268111 : Blo 267823 268111 := bstep (se 1 (by rfl) ⟨201083, by rfl⟩ : syracuseStep 268111 = 402167) B402167
theorem B268127 : Blo 267823 268127 := bstep (se 1 (by rfl) ⟨201095, by rfl⟩ : syracuseStep 268127 = 402191) B402191
theorem B268155 : Blo 267823 268155 := bstep (se 1 (by rfl) ⟨201116, by rfl⟩ : syracuseStep 268155 = 402233) B402233
theorem B1742753 : Blo 267823 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B268207 : Blo 267823 268207 := bstep (se 1 (by rfl) ⟨201155, by rfl⟩ : syracuseStep 268207 = 402311) B402311
theorem B432047 : Blo 267823 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B268231 : Blo 267823 268231 := bstep (se 1 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 268231 = 402347) B402347
theorem B268251 : Blo 267823 268251 := bstep (se 1 (by rfl) ⟨201188, by rfl⟩ : syracuseStep 268251 = 402377) B402377
theorem B1021967 : Blo 267823 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B2037797 : Blo 267823 2037797 := bstep (se 4 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 2037797 = 382087) B382087
theorem B3708965 : Blo 267823 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B268327 : Blo 267823 268327 := bstep (se 1 (by rfl) ⟨201245, by rfl⟩ : syracuseStep 268327 = 402491) B402491
theorem B268367 : Blo 267823 268367 := bstep (se 1 (by rfl) ⟨201275, by rfl⟩ : syracuseStep 268367 = 402551) B402551
theorem B268383 : Blo 267823 268383 := bstep (se 1 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 268383 = 402575) B402575
theorem B268411 : Blo 267823 268411 := bstep (se 1 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 268411 = 402617) B402617
theorem B268463 : Blo 267823 268463 := bstep (se 1 (by rfl) ⟨201347, by rfl⟩ : syracuseStep 268463 = 402695) B402695
theorem B268487 : Blo 267823 268487 := bstep (se 1 (by rfl) ⟨201365, by rfl⟩ : syracuseStep 268487 = 402731) B402731
theorem B268507 : Blo 267823 268507 := bstep (se 1 (by rfl) ⟨201380, by rfl⟩ : syracuseStep 268507 = 402761) B402761
theorem B268583 : Blo 267823 268583 := bstep (se 1 (by rfl) ⟨201437, by rfl⟩ : syracuseStep 268583 = 402875) B402875
theorem B268623 : Blo 267823 268623 := bstep (se 1 (by rfl) ⟨201467, by rfl⟩ : syracuseStep 268623 = 402935) B402935
theorem B268639 : Blo 267823 268639 := bstep (se 1 (by rfl) ⟨201479, by rfl⟩ : syracuseStep 268639 = 402959) B402959
theorem B268667 : Blo 267823 268667 := bstep (se 1 (by rfl) ⟨201500, by rfl⟩ : syracuseStep 268667 = 403001) B403001
theorem B268719 : Blo 267823 268719 := bstep (se 1 (by rfl) ⟨201539, by rfl⟩ : syracuseStep 268719 = 403079) B403079
theorem B268743 : Blo 267823 268743 := bstep (se 1 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 268743 = 403115) B403115
theorem B301531 : Blo 267823 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B268763 : Blo 267823 268763 := bstep (se 1 (by rfl) ⟨201572, by rfl⟩ : syracuseStep 268763 = 403145) B403145
theorem B268839 : Blo 267823 268839 := bstep (se 1 (by rfl) ⟨201629, by rfl⟩ : syracuseStep 268839 = 403259) B403259
theorem B268879 : Blo 267823 268879 := bstep (se 1 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 268879 = 403319) B403319
theorem B432719 : Blo 267823 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B367183 : Blo 267823 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B268895 : Blo 267823 268895 := bstep (se 1 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 268895 = 403343) B403343
theorem B268923 : Blo 267823 268923 := bstep (se 1 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 268923 = 403385) B403385
theorem B268975 : Blo 267823 268975 := bstep (se 1 (by rfl) ⟨201731, by rfl⟩ : syracuseStep 268975 = 403463) B403463
theorem B268999 : Blo 267823 268999 := bstep (se 1 (by rfl) ⟨201749, by rfl⟩ : syracuseStep 268999 = 403499) B403499
theorem B2071241 : Blo 267823 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B269019 : Blo 267823 269019 := bstep (se 1 (by rfl) ⟨201764, by rfl⟩ : syracuseStep 269019 = 403529) B403529
theorem B269095 : Blo 267823 269095 := bstep (se 1 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 269095 = 403643) B403643
theorem B269135 : Blo 267823 269135 := bstep (se 1 (by rfl) ⟨201851, by rfl⟩ : syracuseStep 269135 = 403703) B403703
theorem B269151 : Blo 267823 269151 := bstep (se 1 (by rfl) ⟨201863, by rfl⟩ : syracuseStep 269151 = 403727) B403727
theorem B433001 : Blo 267823 433001 := bstep (se 2 (by rfl) ⟨162375, by rfl⟩ : syracuseStep 433001 = 324751) B324751
theorem B269179 : Blo 267823 269179 := bstep (se 1 (by rfl) ⟨201884, by rfl⟩ : syracuseStep 269179 = 403769) B403769
theorem B301999 : Blo 267823 301999 := bstep (se 1 (by rfl) ⟨226499, by rfl⟩ : syracuseStep 301999 = 452999) B452999
theorem B269231 : Blo 267823 269231 := bstep (se 1 (by rfl) ⟨201923, by rfl⟩ : syracuseStep 269231 = 403847) B403847
theorem B2202551 : Blo 267823 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B269255 : Blo 267823 269255 := bstep (se 1 (by rfl) ⟨201941, by rfl⟩ : syracuseStep 269255 = 403883) B403883
theorem B269275 : Blo 267823 269275 := bstep (se 1 (by rfl) ⟨201956, by rfl⟩ : syracuseStep 269275 = 403913) B403913
theorem B269351 : Blo 267823 269351 := bstep (se 1 (by rfl) ⟨202013, by rfl⟩ : syracuseStep 269351 = 404027) B404027
theorem B269391 : Blo 267823 269391 := bstep (se 1 (by rfl) ⟨202043, by rfl⟩ : syracuseStep 269391 = 404087) B404087
theorem B433231 : Blo 267823 433231 := bstep (se 1 (by rfl) ⟨324923, by rfl⟩ : syracuseStep 433231 = 649847) B649847
theorem B269407 : Blo 267823 269407 := bstep (se 1 (by rfl) ⟨202055, by rfl⟩ : syracuseStep 269407 = 404111) B404111
theorem B990323 : Blo 267823 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B269435 : Blo 267823 269435 := bstep (se 1 (by rfl) ⟨202076, by rfl⟩ : syracuseStep 269435 = 404153) B404153
theorem B269487 : Blo 267823 269487 := bstep (se 1 (by rfl) ⟨202115, by rfl⟩ : syracuseStep 269487 = 404231) B404231
theorem B269511 : Blo 267823 269511 := bstep (se 1 (by rfl) ⟨202133, by rfl⟩ : syracuseStep 269511 = 404267) B404267
theorem B269531 : Blo 267823 269531 := bstep (se 1 (by rfl) ⟨202148, by rfl⟩ : syracuseStep 269531 = 404297) B404297
theorem B3710231 : Blo 267823 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B269607 : Blo 267823 269607 := bstep (se 1 (by rfl) ⟨202205, by rfl⟩ : syracuseStep 269607 = 404411) B404411
theorem B269647 : Blo 267823 269647 := bstep (se 1 (by rfl) ⟨202235, by rfl⟩ : syracuseStep 269647 = 404471) B404471
theorem B302431 : Blo 267823 302431 := bstep (se 1 (by rfl) ⟨226823, by rfl⟩ : syracuseStep 302431 = 453647) B453647
theorem B269663 : Blo 267823 269663 := bstep (se 1 (by rfl) ⟨202247, by rfl⟩ : syracuseStep 269663 = 404495) B404495
theorem B269691 : Blo 267823 269691 := bstep (se 1 (by rfl) ⟨202268, by rfl⟩ : syracuseStep 269691 = 404537) B404537
theorem B269743 : Blo 267823 269743 := bstep (se 1 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 269743 = 404615) B404615
theorem B269767 : Blo 267823 269767 := bstep (se 1 (by rfl) ⟨202325, by rfl⟩ : syracuseStep 269767 = 404651) B404651
theorem B269787 : Blo 267823 269787 := bstep (se 1 (by rfl) ⟨202340, by rfl⟩ : syracuseStep 269787 = 404681) B404681
theorem B269863 : Blo 267823 269863 := bstep (se 1 (by rfl) ⟨202397, by rfl⟩ : syracuseStep 269863 = 404795) B404795
theorem B269903 : Blo 267823 269903 := bstep (se 1 (by rfl) ⟨202427, by rfl⟩ : syracuseStep 269903 = 404855) B404855
theorem B269919 : Blo 267823 269919 := bstep (se 1 (by rfl) ⟨202439, by rfl⟩ : syracuseStep 269919 = 404879) B404879
theorem B269947 : Blo 267823 269947 := bstep (se 1 (by rfl) ⟨202460, by rfl⟩ : syracuseStep 269947 = 404921) B404921
theorem B1023623 : Blo 267823 1023623 := bstep (se 1 (by rfl) ⟨767717, by rfl⟩ : syracuseStep 1023623 = 1535435) B1535435
theorem B269999 : Blo 267823 269999 := bstep (se 1 (by rfl) ⟨202499, by rfl⟩ : syracuseStep 269999 = 404999) B404999
theorem B302791 : Blo 267823 302791 := bstep (se 1 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 302791 = 454187) B454187
theorem B270023 : Blo 267823 270023 := bstep (se 1 (by rfl) ⟨202517, by rfl⟩ : syracuseStep 270023 = 405035) B405035
theorem B270043 : Blo 267823 270043 := bstep (se 1 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 270043 = 405065) B405065
theorem B270119 : Blo 267823 270119 := bstep (se 1 (by rfl) ⟨202589, by rfl⟩ : syracuseStep 270119 = 405179) B405179
theorem B270159 : Blo 267823 270159 := bstep (se 1 (by rfl) ⟨202619, by rfl⟩ : syracuseStep 270159 = 405239) B405239
theorem B270175 : Blo 267823 270175 := bstep (se 1 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 270175 = 405263) B405263
theorem B270203 : Blo 267823 270203 := bstep (se 1 (by rfl) ⟨202652, by rfl⟩ : syracuseStep 270203 = 405305) B405305
theorem B270255 : Blo 267823 270255 := bstep (se 1 (by rfl) ⟨202691, by rfl⟩ : syracuseStep 270255 = 405383) B405383
theorem B270279 : Blo 267823 270279 := bstep (se 1 (by rfl) ⟨202709, by rfl⟩ : syracuseStep 270279 = 405419) B405419
theorem B270299 : Blo 267823 270299 := bstep (se 1 (by rfl) ⟨202724, by rfl⟩ : syracuseStep 270299 = 405449) B405449
theorem B270375 : Blo 267823 270375 := bstep (se 1 (by rfl) ⟨202781, by rfl⟩ : syracuseStep 270375 = 405563) B405563
theorem B270415 : Blo 267823 270415 := bstep (se 1 (by rfl) ⟨202811, by rfl⟩ : syracuseStep 270415 = 405623) B405623
theorem B270431 : Blo 267823 270431 := bstep (se 1 (by rfl) ⟨202823, by rfl⟩ : syracuseStep 270431 = 405647) B405647
theorem B270459 : Blo 267823 270459 := bstep (se 1 (by rfl) ⟨202844, by rfl⟩ : syracuseStep 270459 = 405689) B405689
theorem B270511 : Blo 267823 270511 := bstep (se 1 (by rfl) ⟨202883, by rfl⟩ : syracuseStep 270511 = 405767) B405767
theorem B270535 : Blo 267823 270535 := bstep (se 1 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 270535 = 405803) B405803
theorem B270555 : Blo 267823 270555 := bstep (se 1 (by rfl) ⟨202916, by rfl⟩ : syracuseStep 270555 = 405833) B405833
theorem B270631 : Blo 267823 270631 := bstep (se 1 (by rfl) ⟨202973, by rfl⟩ : syracuseStep 270631 = 405947) B405947
theorem B270671 : Blo 267823 270671 := bstep (se 1 (by rfl) ⟨203003, by rfl⟩ : syracuseStep 270671 = 406007) B406007
theorem B401759 : Blo 267823 401759 := bstep (se 1 (by rfl) ⟨301319, by rfl⟩ : syracuseStep 401759 = 602639) B602639
theorem B270687 : Blo 267823 270687 := bstep (se 1 (by rfl) ⟨203015, by rfl⟩ : syracuseStep 270687 = 406031) B406031
theorem B401771 : Blo 267823 401771 := bstep (se 1 (by rfl) ⟨301328, by rfl⟩ : syracuseStep 401771 = 602657) B602657
theorem B270715 : Blo 267823 270715 := bstep (se 1 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 270715 = 406073) B406073
theorem B270767 : Blo 267823 270767 := bstep (se 1 (by rfl) ⟨203075, by rfl⟩ : syracuseStep 270767 = 406151) B406151
theorem B270791 : Blo 267823 270791 := bstep (se 1 (by rfl) ⟨203093, by rfl⟩ : syracuseStep 270791 = 406187) B406187
theorem B270811 : Blo 267823 270811 := bstep (se 1 (by rfl) ⟨203108, by rfl⟩ : syracuseStep 270811 = 406217) B406217
theorem B303655 : Blo 267823 303655 := bstep (se 1 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 303655 = 455483) B455483
theorem B270887 : Blo 267823 270887 := bstep (se 1 (by rfl) ⟨203165, by rfl⟩ : syracuseStep 270887 = 406331) B406331
theorem B401999 : Blo 267823 401999 := bstep (se 1 (by rfl) ⟨301499, by rfl⟩ : syracuseStep 401999 = 602999) B602999
theorem B270927 : Blo 267823 270927 := bstep (se 1 (by rfl) ⟨203195, by rfl⟩ : syracuseStep 270927 = 406391) B406391
theorem B270943 : Blo 267823 270943 := bstep (se 1 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 270943 = 406415) B406415
theorem B1024609 : Blo 267823 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B270971 : Blo 267823 270971 := bstep (se 1 (by rfl) ⟨203228, by rfl⟩ : syracuseStep 270971 = 406457) B406457
theorem B271023 : Blo 267823 271023 := bstep (se 1 (by rfl) ⟨203267, by rfl⟩ : syracuseStep 271023 = 406535) B406535
theorem B402119 : Blo 267823 402119 := bstep (se 1 (by rfl) ⟨301589, by rfl⟩ : syracuseStep 402119 = 603179) B603179
theorem B271047 : Blo 267823 271047 := bstep (se 1 (by rfl) ⟨203285, by rfl⟩ : syracuseStep 271047 = 406571) B406571
theorem B271067 : Blo 267823 271067 := bstep (se 1 (by rfl) ⟨203300, by rfl⟩ : syracuseStep 271067 = 406601) B406601
theorem B271143 : Blo 267823 271143 := bstep (se 1 (by rfl) ⟨203357, by rfl⟩ : syracuseStep 271143 = 406715) B406715
theorem B271183 : Blo 267823 271183 := bstep (se 1 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 271183 = 406775) B406775
theorem B271199 : Blo 267823 271199 := bstep (se 1 (by rfl) ⟨203399, by rfl⟩ : syracuseStep 271199 = 406799) B406799
theorem B402281 : Blo 267823 402281 := bstep (se 2 (by rfl) ⟨150855, by rfl⟩ : syracuseStep 402281 = 301711) B301711
theorem B271227 : Blo 267823 271227 := bstep (se 1 (by rfl) ⟨203420, by rfl⟩ : syracuseStep 271227 = 406841) B406841
theorem B271279 : Blo 267823 271279 := bstep (se 1 (by rfl) ⟨203459, by rfl⟩ : syracuseStep 271279 = 406919) B406919
theorem B402359 : Blo 267823 402359 := bstep (se 1 (by rfl) ⟨301769, by rfl⟩ : syracuseStep 402359 = 603539) B603539
theorem B271303 : Blo 267823 271303 := bstep (se 1 (by rfl) ⟨203477, by rfl⟩ : syracuseStep 271303 = 406955) B406955
theorem B402395 : Blo 267823 402395 := bstep (se 1 (by rfl) ⟨301796, by rfl⟩ : syracuseStep 402395 = 603593) B603593
theorem B271323 : Blo 267823 271323 := bstep (se 1 (by rfl) ⟨203492, by rfl⟩ : syracuseStep 271323 = 406985) B406985
theorem B271399 : Blo 267823 271399 := bstep (se 1 (by rfl) ⟨203549, by rfl⟩ : syracuseStep 271399 = 407099) B407099
theorem B1025081 : Blo 267823 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B271439 : Blo 267823 271439 := bstep (se 1 (by rfl) ⟨203579, by rfl⟩ : syracuseStep 271439 = 407159) B407159
theorem B271455 : Blo 267823 271455 := bstep (se 1 (by rfl) ⟨203591, by rfl⟩ : syracuseStep 271455 = 407183) B407183
theorem B271483 : Blo 267823 271483 := bstep (se 1 (by rfl) ⟨203612, by rfl⟩ : syracuseStep 271483 = 407225) B407225
theorem B271535 : Blo 267823 271535 := bstep (se 1 (by rfl) ⟨203651, by rfl⟩ : syracuseStep 271535 = 407303) B407303
theorem B271559 : Blo 267823 271559 := bstep (se 1 (by rfl) ⟨203669, by rfl⟩ : syracuseStep 271559 = 407339) B407339
theorem B271579 : Blo 267823 271579 := bstep (se 1 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 271579 = 407369) B407369
theorem B763127 : Blo 267823 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B533753 : Blo 267823 533753 := bstep (se 2 (by rfl) ⟨200157, by rfl⟩ : syracuseStep 533753 = 400315) B400315
theorem B271655 : Blo 267823 271655 := bstep (se 1 (by rfl) ⟨203741, by rfl⟩ : syracuseStep 271655 = 407483) B407483
theorem B271695 : Blo 267823 271695 := bstep (se 1 (by rfl) ⟨203771, by rfl⟩ : syracuseStep 271695 = 407543) B407543
theorem B271711 : Blo 267823 271711 := bstep (se 1 (by rfl) ⟨203783, by rfl⟩ : syracuseStep 271711 = 407567) B407567
theorem B271739 : Blo 267823 271739 := bstep (se 1 (by rfl) ⟨203804, by rfl⟩ : syracuseStep 271739 = 407609) B407609
theorem B402863 : Blo 267823 402863 := bstep (se 1 (by rfl) ⟨302147, by rfl⟩ : syracuseStep 402863 = 604295) B604295
theorem B271791 : Blo 267823 271791 := bstep (se 1 (by rfl) ⟨203843, by rfl⟩ : syracuseStep 271791 = 407687) B407687
theorem B271815 : Blo 267823 271815 := bstep (se 1 (by rfl) ⟨203861, by rfl⟩ : syracuseStep 271815 = 407723) B407723
theorem B2631113 : Blo 267823 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B402953 : Blo 267823 402953 := bstep (se 2 (by rfl) ⟨151107, by rfl⟩ : syracuseStep 402953 = 302215) B302215
theorem B402983 : Blo 267823 402983 := bstep (se 1 (by rfl) ⟨302237, by rfl⟩ : syracuseStep 402983 = 604475) B604475
theorem B403067 : Blo 267823 403067 := bstep (se 1 (by rfl) ⟨302300, by rfl⟩ : syracuseStep 403067 = 604601) B604601
theorem B403193 : Blo 267823 403193 := bstep (se 2 (by rfl) ⟨151197, by rfl⟩ : syracuseStep 403193 = 302395) B302395
theorem B403295 : Blo 267823 403295 := bstep (se 1 (by rfl) ⟨302471, by rfl⟩ : syracuseStep 403295 = 604943) B604943
theorem B403307 : Blo 267823 403307 := bstep (se 1 (by rfl) ⟨302480, by rfl⟩ : syracuseStep 403307 = 604961) B604961
theorem B1026067 : Blo 267823 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B403535 : Blo 267823 403535 := bstep (se 1 (by rfl) ⟨302651, by rfl⟩ : syracuseStep 403535 = 605303) B605303
theorem B1648721 : Blo 267823 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B305275 : Blo 267823 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B403655 : Blo 267823 403655 := bstep (se 1 (by rfl) ⟨302741, by rfl⟩ : syracuseStep 403655 = 605483) B605483
theorem B403817 : Blo 267823 403817 := bstep (se 2 (by rfl) ⟨151431, by rfl⟩ : syracuseStep 403817 = 302863) B302863
theorem B403895 : Blo 267823 403895 := bstep (se 1 (by rfl) ⟨302921, by rfl⟩ : syracuseStep 403895 = 605843) B605843
theorem B403931 : Blo 267823 403931 := bstep (se 1 (by rfl) ⟨302948, by rfl⟩ : syracuseStep 403931 = 605897) B605897
theorem B305743 : Blo 267823 305743 := bstep (se 1 (by rfl) ⟨229307, by rfl⟩ : syracuseStep 305743 = 458615) B458615
theorem B764615 : Blo 267823 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B404399 : Blo 267823 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B404489 : Blo 267823 404489 := bstep (se 2 (by rfl) ⟨151683, by rfl⟩ : syracuseStep 404489 = 303367) B303367
theorem B404519 : Blo 267823 404519 := bstep (se 1 (by rfl) ⟨303389, by rfl⟩ : syracuseStep 404519 = 606779) B606779
theorem B863311 : Blo 267823 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B404603 : Blo 267823 404603 := bstep (se 1 (by rfl) ⟨303452, by rfl⟩ : syracuseStep 404603 = 606905) B606905
theorem B3058883 : Blo 267823 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B404729 : Blo 267823 404729 := bstep (se 2 (by rfl) ⟨151773, by rfl⟩ : syracuseStep 404729 = 303547) B303547
theorem B404831 : Blo 267823 404831 := bstep (se 1 (by rfl) ⟨303623, by rfl⟩ : syracuseStep 404831 = 607247) B607247
theorem B404843 : Blo 267823 404843 := bstep (se 1 (by rfl) ⟨303632, by rfl⟩ : syracuseStep 404843 = 607265) B607265
theorem B405071 : Blo 267823 405071 := bstep (se 1 (by rfl) ⟨303803, by rfl⟩ : syracuseStep 405071 = 607607) B607607
theorem B405191 : Blo 267823 405191 := bstep (se 1 (by rfl) ⟨303893, by rfl⟩ : syracuseStep 405191 = 607787) B607787
theorem B1027799 : Blo 267823 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B2043629 : Blo 267823 2043629 := bstep (se 3 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 2043629 = 766361) B766361
theorem B1716011 : Blo 267823 1716011 := bstep (se 1 (by rfl) ⟨1287008, by rfl⟩ : syracuseStep 1716011 = 2574017) B2574017
theorem B765769 : Blo 267823 765769 := bstep (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) B574327
theorem B405353 : Blo 267823 405353 := bstep (se 2 (by rfl) ⟨152007, by rfl⟩ : syracuseStep 405353 = 304015) B304015
theorem B405431 : Blo 267823 405431 := bstep (se 1 (by rfl) ⟨304073, by rfl⟩ : syracuseStep 405431 = 608147) B608147
theorem B405467 : Blo 267823 405467 := bstep (se 1 (by rfl) ⟨304100, by rfl⟩ : syracuseStep 405467 = 608201) B608201
theorem B438443 : Blo 267823 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B864503 : Blo 267823 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B405935 : Blo 267823 405935 := bstep (se 1 (by rfl) ⟨304451, by rfl⟩ : syracuseStep 405935 = 608903) B608903
theorem B406025 : Blo 267823 406025 := bstep (se 2 (by rfl) ⟨152259, by rfl⟩ : syracuseStep 406025 = 304519) B304519
theorem B340519 : Blo 267823 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B406055 : Blo 267823 406055 := bstep (se 1 (by rfl) ⟨304541, by rfl⟩ : syracuseStep 406055 = 609083) B609083
theorem B3060341 : Blo 267823 3060341 := bstep (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) B286907
theorem B602747 : Blo 267823 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B406139 : Blo 267823 406139 := bstep (se 1 (by rfl) ⟨304604, by rfl⟩ : syracuseStep 406139 = 609209) B609209
theorem B2044601 : Blo 267823 2044601 := bstep (se 2 (by rfl) ⟨766725, by rfl⟩ : syracuseStep 2044601 = 1533451) B1533451
theorem B602873 : Blo 267823 602873 := bstep (se 2 (by rfl) ⟨226077, by rfl⟩ : syracuseStep 602873 = 452155) B452155
theorem B406265 : Blo 267823 406265 := bstep (se 2 (by rfl) ⟨152349, by rfl⟩ : syracuseStep 406265 = 304699) B304699
theorem B3912461 : Blo 267823 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B10138385 : Blo 267823 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B2175821 : Blo 267823 2175821 := bstep (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) B815933
theorem B406367 : Blo 267823 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B340843 : Blo 267823 340843 := bstep (se 1 (by rfl) ⟨255632, by rfl⟩ : syracuseStep 340843 = 511265) B511265
theorem B406379 : Blo 267823 406379 := bstep (se 1 (by rfl) ⟨304784, by rfl⟩ : syracuseStep 406379 = 609569) B609569
theorem B1028983 : Blo 267823 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B603143 : Blo 267823 603143 := bstep (se 1 (by rfl) ⟨452357, by rfl⟩ : syracuseStep 603143 = 904715) B904715
theorem B1094671 : Blo 267823 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B603215 : Blo 267823 603215 := bstep (se 1 (by rfl) ⟨452411, by rfl⟩ : syracuseStep 603215 = 904823) B904823
theorem B406607 : Blo 267823 406607 := bstep (se 1 (by rfl) ⟨304955, by rfl⟩ : syracuseStep 406607 = 609911) B609911
theorem B406727 : Blo 267823 406727 := bstep (se 1 (by rfl) ⟨305045, by rfl⟩ : syracuseStep 406727 = 610091) B610091
theorem B406889 : Blo 267823 406889 := bstep (se 2 (by rfl) ⟨152583, by rfl⟩ : syracuseStep 406889 = 305167) B305167
theorem B3093875 : Blo 267823 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B406967 : Blo 267823 406967 := bstep (se 1 (by rfl) ⟨305225, by rfl⟩ : syracuseStep 406967 = 610451) B610451
theorem B603611 : Blo 267823 603611 := bstep (se 1 (by rfl) ⟨452708, by rfl⟩ : syracuseStep 603611 = 905417) B905417
theorem B407003 : Blo 267823 407003 := bstep (se 1 (by rfl) ⟨305252, by rfl⟩ : syracuseStep 407003 = 610505) B610505
theorem B2045573 : Blo 267823 2045573 := bstep (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) B383545
theorem B767627 : Blo 267823 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B1029955 : Blo 267823 1029955 := bstep (se 1 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 1029955 = 1544933) B1544933
theorem B866143 : Blo 267823 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B866155 : Blo 267823 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B604079 : Blo 267823 604079 := bstep (se 1 (by rfl) ⟨453059, by rfl⟩ : syracuseStep 604079 = 906119) B906119
theorem B407471 : Blo 267823 407471 := bstep (se 1 (by rfl) ⟨305603, by rfl⟩ : syracuseStep 407471 = 611207) B611207
theorem B2176955 : Blo 267823 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B407561 : Blo 267823 407561 := bstep (se 2 (by rfl) ⟨152835, by rfl⟩ : syracuseStep 407561 = 305671) B305671
theorem B86751245 : Blo 267823 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B407591 : Blo 267823 407591 := bstep (se 1 (by rfl) ⟨305693, by rfl⟩ : syracuseStep 407591 = 611387) B611387
theorem B14727257 : Blo 267823 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B4241497 : Blo 267823 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B1030259 : Blo 267823 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B342139 : Blo 267823 342139 := bstep (se 1 (by rfl) ⟨256604, by rfl⟩ : syracuseStep 342139 = 513209) B513209
theorem B407675 : Blo 267823 407675 := bstep (se 1 (by rfl) ⟨305756, by rfl⟩ : syracuseStep 407675 = 611513) B611513
theorem B604331 : Blo 267823 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B5191937 : Blo 267823 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B1358369 : Blo 267823 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B1030715 : Blo 267823 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B1456775 : Blo 267823 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B866963 : Blo 267823 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B604871 : Blo 267823 604871 := bstep (se 1 (by rfl) ⟨453653, by rfl⟩ : syracuseStep 604871 = 907307) B907307
theorem B867385 : Blo 267823 867385 := bstep (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) B650539
theorem B1850435 : Blo 267823 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B1719575 : Blo 267823 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B3128701 : Blo 267823 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B605735 : Blo 267823 605735 := bstep (se 1 (by rfl) ⟨454301, by rfl⟩ : syracuseStep 605735 = 908603) B908603
theorem B2932357 : Blo 267823 2932357 := bstep (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) B549817
theorem B966467 : Blo 267823 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B606059 : Blo 267823 606059 := bstep (se 1 (by rfl) ⟨454544, by rfl⟩ : syracuseStep 606059 = 909089) B909089
theorem B606113 : Blo 267823 606113 := bstep (se 2 (by rfl) ⟨227292, by rfl⟩ : syracuseStep 606113 = 454585) B454585
theorem B344027 : Blo 267823 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B2048003 : Blo 267823 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B409639 : Blo 267823 409639 := bstep (se 1 (by rfl) ⟨307229, by rfl⟩ : syracuseStep 409639 = 614459) B614459
theorem B606455 : Blo 267823 606455 := bstep (se 1 (by rfl) ⟨454841, by rfl⟩ : syracuseStep 606455 = 909683) B909683
theorem B1392983 : Blo 267823 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B1294697 : Blo 267823 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B770759 : Blo 267823 770759 := bstep (se 1 (by rfl) ⟨578069, by rfl⟩ : syracuseStep 770759 = 1156139) B1156139
theorem B1721033 : Blo 267823 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B607049 : Blo 267823 607049 := bstep (se 2 (by rfl) ⟨227643, by rfl⟩ : syracuseStep 607049 = 455287) B455287
theorem B1098809 : Blo 267823 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B279887 : Blo 267823 279887 := bstep (se 1 (by rfl) ⟨209915, by rfl⟩ : syracuseStep 279887 = 419831) B419831
theorem B1361447 : Blo 267823 1361447 := bstep (se 1 (by rfl) ⟨1021085, by rfl⟩ : syracuseStep 1361447 = 2042171) B2042171
theorem B607841 : Blo 267823 607841 := bstep (se 2 (by rfl) ⟨227940, by rfl⟩ : syracuseStep 607841 = 455881) B455881
theorem B870077 : Blo 267823 870077 := bstep (se 3 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 870077 = 326279) B326279
theorem B772001 : Blo 267823 772001 := bstep (se 2 (by rfl) ⟨289500, by rfl⟩ : syracuseStep 772001 = 579001) B579001
theorem B608183 : Blo 267823 608183 := bstep (se 1 (by rfl) ⟨456137, by rfl⟩ : syracuseStep 608183 = 912275) B912275
theorem B543071 : Blo 267823 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B2050433 : Blo 267823 2050433 := bstep (se 2 (by rfl) ⟨768912, by rfl⟩ : syracuseStep 2050433 = 1537825) B1537825
theorem B16566707 : Blo 267823 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B510391 : Blo 267823 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B608777 : Blo 267823 608777 := bstep (se 2 (by rfl) ⟨228291, by rfl⟩ : syracuseStep 608777 = 456583) B456583
theorem B609119 : Blo 267823 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B1952657 : Blo 267823 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B609299 : Blo 267823 609299 := bstep (se 1 (by rfl) ⟨456974, by rfl⟩ : syracuseStep 609299 = 913949) B913949
theorem B904553 : Blo 267823 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B609641 : Blo 267823 609641 := bstep (se 2 (by rfl) ⟨228615, by rfl⟩ : syracuseStep 609641 = 457231) B457231
theorem B1363553 : Blo 267823 1363553 := bstep (se 2 (by rfl) ⟨511332, by rfl⟩ : syracuseStep 1363553 = 1022665) B1022665
theorem B872147 : Blo 267823 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B1527619 : Blo 267823 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B511849 : Blo 267823 511849 := bstep (se 2 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 511849 = 383887) B383887
theorem B905147 : Blo 267823 905147 := bstep (se 1 (by rfl) ⟨678860, by rfl⟩ : syracuseStep 905147 = 1357721) B1357721
theorem B610235 : Blo 267823 610235 := bstep (se 1 (by rfl) ⟨457676, by rfl⟩ : syracuseStep 610235 = 915353) B915353
theorem B741395 : Blo 267823 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B610361 : Blo 267823 610361 := bstep (se 2 (by rfl) ⟨228885, by rfl⟩ : syracuseStep 610361 = 457771) B457771
theorem B1724723 : Blo 267823 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1954153 : Blo 267823 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B610703 : Blo 267823 610703 := bstep (se 1 (by rfl) ⟨458027, by rfl⟩ : syracuseStep 610703 = 916055) B916055
theorem B8802917 : Blo 267823 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B512723 : Blo 267823 512723 := bstep (se 1 (by rfl) ⟨384542, by rfl⟩ : syracuseStep 512723 = 769085) B769085
theorem B611027 : Blo 267823 611027 := bstep (se 1 (by rfl) ⟨458270, by rfl⟩ : syracuseStep 611027 = 916541) B916541
theorem B381791 : Blo 267823 381791 := bstep (se 1 (by rfl) ⟨286343, by rfl⟩ : syracuseStep 381791 = 572687) B572687
theorem B578411 : Blo 267823 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B381871 : Blo 267823 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B3724289 : Blo 267823 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B1365011 : Blo 267823 1365011 := bstep (se 1 (by rfl) ⟨1023758, by rfl⟩ : syracuseStep 1365011 = 2047517) B2047517
theorem B381991 : Blo 267823 381991 := bstep (se 1 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 381991 = 572987) B572987
theorem B3462263 : Blo 267823 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B513353 : Blo 267823 513353 := bstep (se 2 (by rfl) ⟨192507, by rfl⟩ : syracuseStep 513353 = 385015) B385015
theorem B382315 : Blo 267823 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B906875 : Blo 267823 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B1300157 : Blo 267823 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B907037 : Blo 267823 907037 := bstep (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) B340139
theorem B3888931 : Blo 267823 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B47404865 : Blo 267823 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B1955771 : Blo 267823 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B514127 : Blo 267823 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B776591 : Blo 267823 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B907739 : Blo 267823 907739 := bstep (se 1 (by rfl) ⟨680804, by rfl⟩ : syracuseStep 907739 = 1361609) B1361609
theorem B547499 : Blo 267823 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B2611997 : Blo 267823 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B908441 : Blo 267823 908441 := bstep (se 2 (by rfl) ⟨340665, by rfl⟩ : syracuseStep 908441 = 681331) B681331
theorem B679387 : Blo 267823 679387 := bstep (se 1 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 679387 = 1019081) B1019081
theorem B2186813 : Blo 267823 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B515783 : Blo 267823 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B1367927 : Blo 267823 1367927 := bstep (se 1 (by rfl) ⟨1025945, by rfl⟩ : syracuseStep 1367927 = 2051891) B2051891
theorem B680015 : Blo 267823 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B1531993 : Blo 267823 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B10313891 : Blo 267823 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B909629 : Blo 267823 909629 := bstep (se 3 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 909629 = 341111) B341111
theorem B385499 : Blo 267823 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B680663 : Blo 267823 680663 := bstep (se 1 (by rfl) ⟨510497, by rfl⟩ : syracuseStep 680663 = 1020995) B1020995
theorem B1565513 : Blo 267823 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B549737 : Blo 267823 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B3466259 : Blo 267823 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B648271 : Blo 267823 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B910493 : Blo 267823 910493 := bstep (se 3 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 910493 = 341435) B341435
theorem B452027 : Blo 267823 452027 := bstep (se 1 (by rfl) ⟨339020, by rfl⟩ : syracuseStep 452027 = 678041) B678041
theorem B452135 : Blo 267823 452135 := bstep (se 1 (by rfl) ⟨339101, by rfl⟩ : syracuseStep 452135 = 678203) B678203
theorem B911033 : Blo 267823 911033 := bstep (se 2 (by rfl) ⟨341637, by rfl⟩ : syracuseStep 911033 = 683275) B683275
theorem B452425 : Blo 267823 452425 := bstep (se 2 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 452425 = 339319) B339319
theorem B452459 : Blo 267823 452459 := bstep (se 1 (by rfl) ⟨339344, by rfl⟩ : syracuseStep 452459 = 678689) B678689
theorem B485281 : Blo 267823 485281 := bstep (se 2 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 485281 = 363961) B363961
theorem B649147 : Blo 267823 649147 := bstep (se 1 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 649147 = 973721) B973721
theorem B452857 : Blo 267823 452857 := bstep (se 2 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 452857 = 339643) B339643
theorem B911627 : Blo 267823 911627 := bstep (se 1 (by rfl) ⟨683720, by rfl⟩ : syracuseStep 911627 = 1367441) B1367441
theorem B4385177 : Blo 267823 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B6678937 : Blo 267823 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B2779595 : Blo 267823 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B453127 : Blo 267823 453127 := bstep (se 1 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 453127 = 679691) B679691
theorem B911897 : Blo 267823 911897 := bstep (se 2 (by rfl) ⟨341961, by rfl⟩ : syracuseStep 911897 = 683923) B683923
theorem B486059 : Blo 267823 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B2321297 : Blo 267823 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B486319 : Blo 267823 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B453559 : Blo 267823 453559 := bstep (se 1 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 453559 = 680339) B680339
theorem B551993 : Blo 267823 551993 := bstep (se 2 (by rfl) ⟨206997, by rfl⟩ : syracuseStep 551993 = 413995) B413995
theorem B977999 : Blo 267823 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B453755 : Blo 267823 453755 := bstep (se 1 (by rfl) ⟨340316, by rfl⟩ : syracuseStep 453755 = 680633) B680633
theorem B683255 : Blo 267823 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B978263 : Blo 267823 978263 := bstep (se 1 (by rfl) ⟨733697, by rfl⟩ : syracuseStep 978263 = 1467395) B1467395
theorem B4418959 : Blo 267823 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B3436019 : Blo 267823 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B454153 : Blo 267823 454153 := bstep (se 2 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 454153 = 340615) B340615
theorem B913031 : Blo 267823 913031 := bstep (se 1 (by rfl) ⟨684773, by rfl⟩ : syracuseStep 913031 = 1369547) B1369547
theorem B454315 : Blo 267823 454315 := bstep (se 1 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 454315 = 681473) B681473
theorem B913085 : Blo 267823 913085 := bstep (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) B342407
theorem B7728857 : Blo 267823 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B913247 : Blo 267823 913247 := bstep (se 1 (by rfl) ⟨684935, by rfl⟩ : syracuseStep 913247 = 1369871) B1369871
theorem B487343 : Blo 267823 487343 := bstep (se 1 (by rfl) ⟨365507, by rfl⟩ : syracuseStep 487343 = 731015) B731015
theorem B454619 : Blo 267823 454619 := bstep (se 1 (by rfl) ⟨340964, by rfl⟩ : syracuseStep 454619 = 681929) B681929
theorem B913409 : Blo 267823 913409 := bstep (se 2 (by rfl) ⟨342528, by rfl⟩ : syracuseStep 913409 = 685057) B685057
theorem B1732697 : Blo 267823 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B454855 : Blo 267823 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B520543 : Blo 267823 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B455017 : Blo 267823 455017 := bstep (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) B341263
theorem B3666491 : Blo 267823 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B684683 : Blo 267823 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B6517421 : Blo 267823 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B914219 : Blo 267823 914219 := bstep (se 1 (by rfl) ⟨685664, by rfl⟩ : syracuseStep 914219 = 1371329) B1371329
theorem B684895 : Blo 267823 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B1373111 : Blo 267823 1373111 := bstep (se 1 (by rfl) ⟨1029833, by rfl⟩ : syracuseStep 1373111 = 2059667) B2059667
theorem B455611 : Blo 267823 455611 := bstep (se 1 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 455611 = 683417) B683417
theorem B652307 : Blo 267823 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B455719 : Blo 267823 455719 := bstep (se 1 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 455719 = 683579) B683579
theorem B914489 : Blo 267823 914489 := bstep (se 2 (by rfl) ⟨342933, by rfl⟩ : syracuseStep 914489 = 685867) B685867
theorem B456043 : Blo 267823 456043 := bstep (se 1 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 456043 = 684065) B684065
theorem B914813 : Blo 267823 914813 := bstep (se 3 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 914813 = 343055) B343055
theorem B1734155 : Blo 267823 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B915083 : Blo 267823 915083 := bstep (se 1 (by rfl) ⟨686312, by rfl⟩ : syracuseStep 915083 = 1372625) B1372625
theorem B685817 : Blo 267823 685817 := bstep (se 2 (by rfl) ⟨257181, by rfl⟩ : syracuseStep 685817 = 514363) B514363
theorem B35452673 : Blo 267823 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B3667801 : Blo 267823 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B8976541 : Blo 267823 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B1374569 : Blo 267823 1374569 := bstep (se 2 (by rfl) ⟨515463, by rfl⟩ : syracuseStep 1374569 = 1030927) B1030927
theorem B686465 : Blo 267823 686465 := bstep (se 2 (by rfl) ⟨257424, by rfl⟩ : syracuseStep 686465 = 514849) B514849
theorem B457103 : Blo 267823 457103 := bstep (se 1 (by rfl) ⟨342827, by rfl⟩ : syracuseStep 457103 = 685655) B685655
theorem B916001 : Blo 267823 916001 := bstep (se 2 (by rfl) ⟨343500, by rfl⟩ : syracuseStep 916001 = 687001) B687001
theorem B457339 : Blo 267823 457339 := bstep (se 1 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 457339 = 686009) B686009
theorem B817879 : Blo 267823 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B916217 : Blo 267823 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B3111709 : Blo 267823 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B916487 : Blo 267823 916487 := bstep (se 1 (by rfl) ⟨687365, by rfl⟩ : syracuseStep 916487 = 1374731) B1374731
theorem B916595 : Blo 267823 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B687275 : Blo 267823 687275 := bstep (se 1 (by rfl) ⟨515456, by rfl⟩ : syracuseStep 687275 = 1030913) B1030913
theorem B2063555 : Blo 267823 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B916865 : Blo 267823 916865 := bstep (se 2 (by rfl) ⟨343824, by rfl⟩ : syracuseStep 916865 = 687649) B687649
theorem B3440015 : Blo 267823 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B458203 : Blo 267823 458203 := bstep (se 1 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 458203 = 687305) B687305
theorem B15728717 : Blo 267823 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1147355 : Blo 267823 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B5506319 : Blo 267823 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B2459069 : Blo 267823 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B11044471 : Blo 267823 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B6424771 : Blo 267823 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B1018109 : Blo 267823 1018109 := bstep (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) B381791
theorem B3541391 : Blo 267823 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B494263 : Blo 267823 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B1739485 : Blo 267823 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B1149815 : Blo 267823 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B5868611 : Blo 267823 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B2985461 : Blo 267823 2985461 := bstep (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) B279887
theorem B396895 : Blo 267823 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B2461549 : Blo 267823 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1151081 : Blo 267823 1151081 := bstep (se 2 (by rfl) ⟨431655, by rfl⟩ : syracuseStep 1151081 = 863311) B863311
theorem B364999 : Blo 267823 364999 := bstep (se 1 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 364999 = 547499) B547499
theorem B1380827 : Blo 267823 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1741331 : Blo 267823 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B660215 : Blo 267823 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B9966341 : Blo 267823 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2036825 : Blo 267823 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B1021025 : Blo 267823 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B4396589 : Blo 267823 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B267839 : Blo 267823 267839 := bstep (se 1 (by rfl) ⟨200879, by rfl⟩ : syracuseStep 267839 = 401759) B401759
theorem B267847 : Blo 267823 267847 := bstep (se 1 (by rfl) ⟨200885, by rfl⟩ : syracuseStep 267847 = 401771) B401771
theorem B267999 : Blo 267823 267999 := bstep (se 1 (by rfl) ⟨200999, by rfl⟩ : syracuseStep 267999 = 401999) B401999
theorem B694057 : Blo 267823 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B268079 : Blo 267823 268079 := bstep (se 1 (by rfl) ⟨201059, by rfl⟩ : syracuseStep 268079 = 402119) B402119
theorem B268187 : Blo 267823 268187 := bstep (se 1 (by rfl) ⟨201140, by rfl⟩ : syracuseStep 268187 = 402281) B402281
theorem B366491 : Blo 267823 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B268239 : Blo 267823 268239 := bstep (se 1 (by rfl) ⟨201179, by rfl⟩ : syracuseStep 268239 = 402359) B402359
theorem B268263 : Blo 267823 268263 := bstep (se 1 (by rfl) ⟨201197, by rfl⟩ : syracuseStep 268263 = 402395) B402395
theorem B1448189 : Blo 267823 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B268575 : Blo 267823 268575 := bstep (se 1 (by rfl) ⟨201431, by rfl⟩ : syracuseStep 268575 = 402863) B402863
theorem B301351 : Blo 267823 301351 := bstep (se 1 (by rfl) ⟨226013, by rfl⟩ : syracuseStep 301351 = 452027) B452027
theorem B268635 : Blo 267823 268635 := bstep (se 1 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 268635 = 402953) B402953
theorem B301423 : Blo 267823 301423 := bstep (se 1 (by rfl) ⟨226067, by rfl⟩ : syracuseStep 301423 = 452135) B452135
theorem B268655 : Blo 267823 268655 := bstep (se 1 (by rfl) ⟨201491, by rfl⟩ : syracuseStep 268655 = 402983) B402983
theorem B268711 : Blo 267823 268711 := bstep (se 1 (by rfl) ⟨201533, by rfl⟩ : syracuseStep 268711 = 403067) B403067
theorem B268795 : Blo 267823 268795 := bstep (se 1 (by rfl) ⟨201596, by rfl⟩ : syracuseStep 268795 = 403193) B403193
theorem B268863 : Blo 267823 268863 := bstep (se 1 (by rfl) ⟨201647, by rfl⟩ : syracuseStep 268863 = 403295) B403295
theorem B301639 : Blo 267823 301639 := bstep (se 1 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 301639 = 452459) B452459
theorem B268871 : Blo 267823 268871 := bstep (se 1 (by rfl) ⟨201653, by rfl⟩ : syracuseStep 268871 = 403307) B403307
theorem B269023 : Blo 267823 269023 := bstep (se 1 (by rfl) ⟨201767, by rfl⟩ : syracuseStep 269023 = 403535) B403535
theorem B269103 : Blo 267823 269103 := bstep (se 1 (by rfl) ⟨201827, by rfl⟩ : syracuseStep 269103 = 403655) B403655
theorem B269211 : Blo 267823 269211 := bstep (se 1 (by rfl) ⟨201908, by rfl⟩ : syracuseStep 269211 = 403817) B403817
theorem B2923451 : Blo 267823 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B269263 : Blo 267823 269263 := bstep (se 1 (by rfl) ⟨201947, by rfl⟩ : syracuseStep 269263 = 403895) B403895
theorem B269287 : Blo 267823 269287 := bstep (se 1 (by rfl) ⟨201965, by rfl⟩ : syracuseStep 269287 = 403931) B403931
theorem B1547531 : Blo 267823 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B269599 : Blo 267823 269599 := bstep (se 1 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 269599 = 404399) B404399
theorem B269659 : Blo 267823 269659 := bstep (se 1 (by rfl) ⟨202244, by rfl⟩ : syracuseStep 269659 = 404489) B404489
theorem B269679 : Blo 267823 269679 := bstep (se 1 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 269679 = 404519) B404519
theorem B302503 : Blo 267823 302503 := bstep (se 1 (by rfl) ⟨226877, by rfl⟩ : syracuseStep 302503 = 453755) B453755
theorem B269735 : Blo 267823 269735 := bstep (se 1 (by rfl) ⟨202301, by rfl⟩ : syracuseStep 269735 = 404603) B404603
theorem B2039255 : Blo 267823 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B269819 : Blo 267823 269819 := bstep (se 1 (by rfl) ⟨202364, by rfl⟩ : syracuseStep 269819 = 404729) B404729
theorem B269887 : Blo 267823 269887 := bstep (se 1 (by rfl) ⟨202415, by rfl⟩ : syracuseStep 269887 = 404831) B404831
theorem B269895 : Blo 267823 269895 := bstep (se 1 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 269895 = 404843) B404843
theorem B5185241 : Blo 267823 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B270047 : Blo 267823 270047 := bstep (se 1 (by rfl) ⟨202535, by rfl⟩ : syracuseStep 270047 = 405071) B405071
theorem B4890401 : Blo 267823 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1154857 : Blo 267823 1154857 := bstep (se 2 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 1154857 = 866143) B866143
theorem B270127 : Blo 267823 270127 := bstep (se 1 (by rfl) ⟨202595, by rfl⟩ : syracuseStep 270127 = 405191) B405191
theorem B1154873 : Blo 267823 1154873 := bstep (se 2 (by rfl) ⟨433077, by rfl⟩ : syracuseStep 1154873 = 866155) B866155
theorem B5152571 : Blo 267823 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B270235 : Blo 267823 270235 := bstep (se 1 (by rfl) ⟨202676, by rfl⟩ : syracuseStep 270235 = 405353) B405353
theorem B270287 : Blo 267823 270287 := bstep (se 1 (by rfl) ⟨202715, by rfl⟩ : syracuseStep 270287 = 405431) B405431
theorem B303079 : Blo 267823 303079 := bstep (se 1 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 303079 = 454619) B454619
theorem B270311 : Blo 267823 270311 := bstep (se 1 (by rfl) ⟨202733, by rfl⟩ : syracuseStep 270311 = 405467) B405467
theorem B1155131 : Blo 267823 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B11968721 : Blo 267823 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B270623 : Blo 267823 270623 := bstep (se 1 (by rfl) ⟨202967, by rfl⟩ : syracuseStep 270623 = 405935) B405935
theorem B270683 : Blo 267823 270683 := bstep (se 1 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 270683 = 406025) B406025
theorem B270703 : Blo 267823 270703 := bstep (se 1 (by rfl) ⟨203027, by rfl⟩ : syracuseStep 270703 = 406055) B406055
theorem B2040227 : Blo 267823 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B401831 : Blo 267823 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B270759 : Blo 267823 270759 := bstep (se 1 (by rfl) ⟨203069, by rfl⟩ : syracuseStep 270759 = 406139) B406139
theorem B401915 : Blo 267823 401915 := bstep (se 1 (by rfl) ⟨301436, by rfl⟩ : syracuseStep 401915 = 602873) B602873
theorem B270843 : Blo 267823 270843 := bstep (se 1 (by rfl) ⟨203132, by rfl⟩ : syracuseStep 270843 = 406265) B406265
theorem B6758923 : Blo 267823 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1450547 : Blo 267823 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B270911 : Blo 267823 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B270919 : Blo 267823 270919 := bstep (se 1 (by rfl) ⟨203189, by rfl⟩ : syracuseStep 270919 = 406379) B406379
theorem B402041 : Blo 267823 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B402095 : Blo 267823 402095 := bstep (se 1 (by rfl) ⟨301571, by rfl⟩ : syracuseStep 402095 = 603143) B603143
theorem B402143 : Blo 267823 402143 := bstep (se 1 (by rfl) ⟨301607, by rfl⟩ : syracuseStep 402143 = 603215) B603215
theorem B271071 : Blo 267823 271071 := bstep (se 1 (by rfl) ⟨203303, by rfl⟩ : syracuseStep 271071 = 406607) B406607
theorem B271151 : Blo 267823 271151 := bstep (se 1 (by rfl) ⟨203363, by rfl⟩ : syracuseStep 271151 = 406727) B406727
theorem B271259 : Blo 267823 271259 := bstep (se 1 (by rfl) ⟨203444, by rfl⟩ : syracuseStep 271259 = 406889) B406889
theorem B1090505 : Blo 267823 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B271311 : Blo 267823 271311 := bstep (se 1 (by rfl) ⟨203483, by rfl⟩ : syracuseStep 271311 = 406967) B406967
theorem B402407 : Blo 267823 402407 := bstep (se 1 (by rfl) ⟨301805, by rfl⟩ : syracuseStep 402407 = 603611) B603611
theorem B271335 : Blo 267823 271335 := bstep (se 1 (by rfl) ⟨203501, by rfl⟩ : syracuseStep 271335 = 407003) B407003
theorem B1156103 : Blo 267823 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B23635115 : Blo 267823 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B402665 : Blo 267823 402665 := bstep (se 2 (by rfl) ⟨150999, by rfl⟩ : syracuseStep 402665 = 301999) B301999
theorem B402719 : Blo 267823 402719 := bstep (se 1 (by rfl) ⟨302039, by rfl⟩ : syracuseStep 402719 = 604079) B604079
theorem B271647 : Blo 267823 271647 := bstep (se 1 (by rfl) ⟨203735, by rfl⟩ : syracuseStep 271647 = 407471) B407471
theorem B1451303 : Blo 267823 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B271707 : Blo 267823 271707 := bstep (se 1 (by rfl) ⟨203780, by rfl⟩ : syracuseStep 271707 = 407561) B407561
theorem B271727 : Blo 267823 271727 := bstep (se 1 (by rfl) ⟨203795, by rfl⟩ : syracuseStep 271727 = 407591) B407591
theorem B1156513 : Blo 267823 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B271783 : Blo 267823 271783 := bstep (se 1 (by rfl) ⟨203837, by rfl⟩ : syracuseStep 271783 = 407675) B407675
theorem B402887 : Blo 267823 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B304735 : Blo 267823 304735 := bstep (se 1 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 304735 = 457103) B457103
theorem B403241 : Blo 267823 403241 := bstep (se 2 (by rfl) ⟨151215, by rfl⟩ : syracuseStep 403241 = 302431) B302431
theorem B403247 : Blo 267823 403247 := bstep (se 1 (by rfl) ⟨302435, by rfl⟩ : syracuseStep 403247 = 604871) B604871
theorem B4171601 : Blo 267823 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B3909809 : Blo 267823 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B403721 : Blo 267823 403721 := bstep (se 2 (by rfl) ⟨151395, by rfl⟩ : syracuseStep 403721 = 302791) B302791
theorem B403823 : Blo 267823 403823 := bstep (se 1 (by rfl) ⟨302867, by rfl⟩ : syracuseStep 403823 = 605735) B605735
theorem B404039 : Blo 267823 404039 := bstep (se 1 (by rfl) ⟨303029, by rfl⟩ : syracuseStep 404039 = 606059) B606059
theorem B404075 : Blo 267823 404075 := bstep (se 1 (by rfl) ⟨303056, by rfl⟩ : syracuseStep 404075 = 606113) B606113
theorem B1845949 : Blo 267823 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B2042657 : Blo 267823 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B404303 : Blo 267823 404303 := bstep (se 1 (by rfl) ⟨303227, by rfl⟩ : syracuseStep 404303 = 606455) B606455
theorem B928655 : Blo 267823 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B863131 : Blo 267823 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B1092595 : Blo 267823 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B404699 : Blo 267823 404699 := bstep (se 1 (by rfl) ⟨303524, by rfl⟩ : syracuseStep 404699 = 607049) B607049
theorem B732539 : Blo 267823 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B404873 : Blo 267823 404873 := bstep (se 2 (by rfl) ⟨151827, by rfl⟩ : syracuseStep 404873 = 303655) B303655
theorem B10431989 : Blo 267823 10431989 := bstep (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) B977999
theorem B405227 : Blo 267823 405227 := bstep (se 1 (by rfl) ⟨303920, by rfl⟩ : syracuseStep 405227 = 607841) B607841
theorem B1027997 : Blo 267823 1027997 := bstep (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) B385499
theorem B405455 : Blo 267823 405455 := bstep (se 1 (by rfl) ⟨304091, by rfl⟩ : syracuseStep 405455 = 608183) B608183
theorem B864361 : Blo 267823 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B1290451 : Blo 267823 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B405851 : Blo 267823 405851 := bstep (se 1 (by rfl) ⟨304388, by rfl⟩ : syracuseStep 405851 = 608777) B608777
theorem B406079 : Blo 267823 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B406199 : Blo 267823 406199 := bstep (se 1 (by rfl) ⟨304649, by rfl⟩ : syracuseStep 406199 = 609299) B609299
theorem B1356587 : Blo 267823 1356587 := bstep (se 1 (by rfl) ⟨1017440, by rfl⟩ : syracuseStep 1356587 = 2034881) B2034881
theorem B603035 : Blo 267823 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B406427 : Blo 267823 406427 := bstep (se 1 (by rfl) ⟨304820, by rfl⟩ : syracuseStep 406427 = 609641) B609641
theorem B603233 : Blo 267823 603233 := bstep (se 2 (by rfl) ⟨226212, by rfl⟩ : syracuseStep 603233 = 452425) B452425
theorem B1225961 : Blo 267823 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B865529 : Blo 267823 865529 := bstep (se 2 (by rfl) ⟨324573, by rfl⟩ : syracuseStep 865529 = 649147) B649147
theorem B603431 : Blo 267823 603431 := bstep (se 1 (by rfl) ⟨452573, by rfl⟩ : syracuseStep 603431 = 905147) B905147
theorem B406823 : Blo 267823 406823 := bstep (se 1 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 406823 = 610235) B610235
theorem B406907 : Blo 267823 406907 := bstep (se 1 (by rfl) ⟨305180, by rfl⟩ : syracuseStep 406907 = 610361) B610361
theorem B407033 : Blo 267823 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B407135 : Blo 267823 407135 := bstep (se 1 (by rfl) ⟨305351, by rfl⟩ : syracuseStep 407135 = 610703) B610703
theorem B603809 : Blo 267823 603809 := bstep (se 2 (by rfl) ⟨226428, by rfl⟩ : syracuseStep 603809 = 452857) B452857
theorem B341815 : Blo 267823 341815 := bstep (se 1 (by rfl) ⟨256361, by rfl⟩ : syracuseStep 341815 = 512723) B512723
theorem B407351 : Blo 267823 407351 := bstep (se 1 (by rfl) ⟨305513, by rfl⟩ : syracuseStep 407351 = 611027) B611027
theorem B604169 : Blo 267823 604169 := bstep (se 2 (by rfl) ⟨226563, by rfl⟩ : syracuseStep 604169 = 453127) B453127
theorem B2308175 : Blo 267823 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B407657 : Blo 267823 407657 := bstep (se 2 (by rfl) ⟨152871, by rfl⟩ : syracuseStep 407657 = 305743) B305743
theorem B342235 : Blo 267823 342235 := bstep (se 1 (by rfl) ⟨256676, by rfl⟩ : syracuseStep 342235 = 513353) B513353
theorem B604583 : Blo 267823 604583 := bstep (se 1 (by rfl) ⟨453437, by rfl⟩ : syracuseStep 604583 = 906875) B906875
theorem B866771 : Blo 267823 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B604691 : Blo 267823 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B604745 : Blo 267823 604745 := bstep (se 2 (by rfl) ⟨226779, by rfl⟩ : syracuseStep 604745 = 453559) B453559
theorem B1358531 : Blo 267823 1358531 := bstep (se 1 (by rfl) ⟨1018898, by rfl⟩ : syracuseStep 1358531 = 2037797) B2037797
theorem B2472643 : Blo 267823 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B605159 : Blo 267823 605159 := bstep (se 1 (by rfl) ⟨453869, by rfl⟩ : syracuseStep 605159 = 907739) B907739
theorem B605537 : Blo 267823 605537 := bstep (se 2 (by rfl) ⟨227076, by rfl⟩ : syracuseStep 605537 = 454153) B454153
theorem B605627 : Blo 267823 605627 := bstep (se 1 (by rfl) ⟨454220, by rfl⟩ : syracuseStep 605627 = 908441) B908441
theorem B1228297 : Blo 267823 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B2473487 : Blo 267823 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B605753 : Blo 267823 605753 := bstep (se 2 (by rfl) ⟨227157, by rfl⟩ : syracuseStep 605753 = 454315) B454315
theorem B1457875 : Blo 267823 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B343855 : Blo 267823 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B606419 : Blo 267823 606419 := bstep (se 1 (by rfl) ⟨454814, by rfl⟩ : syracuseStep 606419 = 909629) B909629
theorem B606473 : Blo 267823 606473 := bstep (se 2 (by rfl) ⟨227427, by rfl⟩ : syracuseStep 606473 = 454855) B454855
theorem B2310565 : Blo 267823 2310565 := bstep (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) B433231
theorem B606689 : Blo 267823 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B2605537 : Blo 267823 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B2310839 : Blo 267823 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B606995 : Blo 267823 606995 := bstep (se 1 (by rfl) ⟨455246, by rfl⟩ : syracuseStep 606995 = 910493) B910493
theorem B508751 : Blo 267823 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B1754075 : Blo 267823 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B607355 : Blo 267823 607355 := bstep (se 1 (by rfl) ⟨455516, by rfl⟩ : syracuseStep 607355 = 911033) B911033
theorem B509161 : Blo 267823 509161 := bstep (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) B381871
theorem B607481 : Blo 267823 607481 := bstep (se 2 (by rfl) ⟨227805, by rfl⟩ : syracuseStep 607481 = 455611) B455611
theorem B1459561 : Blo 267823 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B509321 : Blo 267823 509321 := bstep (se 2 (by rfl) ⟨190995, by rfl⟩ : syracuseStep 509321 = 381991) B381991
theorem B607625 : Blo 267823 607625 := bstep (se 2 (by rfl) ⟨227859, by rfl⟩ : syracuseStep 607625 = 455719) B455719
theorem B607751 : Blo 267823 607751 := bstep (se 1 (by rfl) ⟨455813, by rfl⟩ : syracuseStep 607751 = 911627) B911627
theorem B1853063 : Blo 267823 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B607931 : Blo 267823 607931 := bstep (se 1 (by rfl) ⟨455948, by rfl⟩ : syracuseStep 607931 = 911897) B911897
theorem B2311901 : Blo 267823 2311901 := bstep (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) B866963
theorem B1296157 : Blo 267823 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B509743 : Blo 267823 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B509753 : Blo 267823 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B608057 : Blo 267823 608057 := bstep (se 2 (by rfl) ⟨228021, by rfl⟩ : syracuseStep 608057 = 456043) B456043
theorem B608687 : Blo 267823 608687 := bstep (se 1 (by rfl) ⟨456515, by rfl⟩ : syracuseStep 608687 = 913031) B913031
theorem B608723 : Blo 267823 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B1362419 : Blo 267823 1362419 := bstep (se 1 (by rfl) ⟨1021814, by rfl⟩ : syracuseStep 1362419 = 2043629) B2043629
theorem B608831 : Blo 267823 608831 := bstep (se 1 (by rfl) ⟨456623, by rfl⟩ : syracuseStep 608831 = 913247) B913247
theorem B608939 : Blo 267823 608939 := bstep (se 1 (by rfl) ⟨456704, by rfl⟩ : syracuseStep 608939 = 913409) B913409
theorem B5655329 : Blo 267823 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B576335 : Blo 267823 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B2444327 : Blo 267823 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B4344947 : Blo 267823 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B1363067 : Blo 267823 1363067 := bstep (se 1 (by rfl) ⟨1022300, by rfl⟩ : syracuseStep 1363067 = 2044601) B2044601
theorem B2608307 : Blo 267823 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B609479 : Blo 267823 609479 := bstep (se 1 (by rfl) ⟨457109, by rfl⟩ : syracuseStep 609479 = 914219) B914219
theorem B609659 : Blo 267823 609659 := bstep (se 1 (by rfl) ⟨457244, by rfl⟩ : syracuseStep 609659 = 914489) B914489
theorem B609785 : Blo 267823 609785 := bstep (se 2 (by rfl) ⟨228669, by rfl⟩ : syracuseStep 609785 = 457339) B457339
theorem B609875 : Blo 267823 609875 := bstep (se 1 (by rfl) ⟨457406, by rfl⟩ : syracuseStep 609875 = 914813) B914813
theorem B4148945 : Blo 267823 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B1363715 : Blo 267823 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B511751 : Blo 267823 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B610055 : Blo 267823 610055 := bstep (se 1 (by rfl) ⟨457541, by rfl⟩ : syracuseStep 610055 = 915083) B915083
theorem B9818171 : Blo 267823 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B3461291 : Blo 267823 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B905579 : Blo 267823 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B610667 : Blo 267823 610667 := bstep (se 1 (by rfl) ⟨458000, by rfl⟩ : syracuseStep 610667 = 916001) B916001
theorem B971183 : Blo 267823 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B610811 : Blo 267823 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B905849 : Blo 267823 905849 := bstep (se 2 (by rfl) ⟨339693, by rfl⟩ : syracuseStep 905849 = 679387) B679387
theorem B610937 : Blo 267823 610937 := bstep (se 2 (by rfl) ⟨229101, by rfl⟩ : syracuseStep 610937 = 458203) B458203
theorem B610991 : Blo 267823 610991 := bstep (se 1 (by rfl) ⟨458243, by rfl⟩ : syracuseStep 610991 = 916487) B916487
theorem B1233623 : Blo 267823 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B611063 : Blo 267823 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B611243 : Blo 267823 611243 := bstep (se 1 (by rfl) ⟨458432, by rfl⟩ : syracuseStep 611243 = 916865) B916865
theorem B644311 : Blo 267823 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B1365335 : Blo 267823 1365335 := bstep (se 1 (by rfl) ⟨1024001, by rfl⟩ : syracuseStep 1365335 = 2048003) B2048003
theorem B546185 : Blo 267823 546185 := bstep (se 2 (by rfl) ⟨204819, by rfl⟩ : syracuseStep 546185 = 409639) B409639
theorem B1529351 : Blo 267823 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B513839 : Blo 267823 513839 := bstep (se 1 (by rfl) ⟨385379, by rfl⟩ : syracuseStep 513839 = 770759) B770759
theorem B1366145 : Blo 267823 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B907631 : Blo 267823 907631 := bstep (se 1 (by rfl) ⟨680723, by rfl⟩ : syracuseStep 907631 = 1361447) B1361447
theorem B580051 : Blo 267823 580051 := bstep (se 1 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 580051 = 870077) B870077
theorem B678395 : Blo 267823 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B514667 : Blo 267823 514667 := bstep (se 1 (by rfl) ⟨386000, by rfl⟩ : syracuseStep 514667 = 772001) B772001
theorem B1366955 : Blo 267823 1366955 := bstep (se 1 (by rfl) ⟨1025216, by rfl⟩ : syracuseStep 1366955 = 2050433) B2050433
theorem B1301771 : Blo 267823 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B679367 : Blo 267823 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B909035 : Blo 267823 909035 := bstep (se 1 (by rfl) ⟨681776, by rfl⟩ : syracuseStep 909035 = 1363553) B1363553
theorem B581431 : Blo 267823 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B647041 : Blo 267823 647041 := bstep (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) B485281
theorem B1400851 : Blo 267823 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B1368089 : Blo 267823 1368089 := bstep (se 2 (by rfl) ⟨513033, by rfl⟩ : syracuseStep 1368089 = 1026067) B1026067
theorem B680147 : Blo 267823 680147 := bstep (se 1 (by rfl) ⟨510110, by rfl⟩ : syracuseStep 680147 = 1020221) B1020221
theorem B483695 : Blo 267823 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B680359 : Blo 267823 680359 := bstep (se 1 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 680359 = 1020539) B1020539
theorem B8905249 : Blo 267823 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B385607 : Blo 267823 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B680521 : Blo 267823 680521 := bstep (se 2 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 680521 = 510391) B510391
theorem B2482859 : Blo 267823 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B910007 : Blo 267823 910007 := bstep (se 1 (by rfl) ⟨682505, by rfl⟩ : syracuseStep 910007 = 1365011) B1365011
theorem B3105985 : Blo 267823 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B648425 : Blo 267823 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B288031 : Blo 267823 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B1303847 : Blo 267823 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B681311 : Blo 267823 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B517727 : Blo 267823 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B288479 : Blo 267823 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B5891945 : Blo 267823 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B288667 : Blo 267823 288667 := bstep (se 1 (by rfl) ⟨216500, by rfl⟩ : syracuseStep 288667 = 433001) B433001
theorem B1468367 : Blo 267823 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B126412973 : Blo 267823 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B2320649 : Blo 267823 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B4647341 : Blo 267823 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B682415 : Blo 267823 682415 := bstep (se 1 (by rfl) ⟨511811, by rfl⟩ : syracuseStep 682415 = 1023623) B1023623
theorem B682465 : Blo 267823 682465 := bstep (se 2 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 682465 = 511849) B511849
theorem B911951 : Blo 267823 911951 := bstep (se 1 (by rfl) ⟨683963, by rfl⟩ : syracuseStep 911951 = 1367927) B1367927
theorem B453343 : Blo 267823 453343 := bstep (se 1 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 453343 = 680015) B680015
theorem B6875927 : Blo 267823 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B1371005 : Blo 267823 1371005 := bstep (se 3 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 1371005 = 514127) B514127
theorem B453775 : Blo 267823 453775 := bstep (se 1 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 453775 = 680663) B680663
theorem B1043675 : Blo 267823 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B683387 : Blo 267823 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B454025 : Blo 267823 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B355835 : Blo 267823 355835 := bstep (se 1 (by rfl) ⟨266876, by rfl⟩ : syracuseStep 355835 = 533753) B533753
theorem B913193 : Blo 267823 913193 := bstep (se 2 (by rfl) ⟨342447, by rfl⟩ : syracuseStep 913193 = 684895) B684895
theorem B454457 : Blo 267823 454457 := bstep (se 2 (by rfl) ⟨170421, by rfl⟩ : syracuseStep 454457 = 340843) B340843
theorem B1371977 : Blo 267823 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B455503 : Blo 267823 455503 := bstep (se 1 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 455503 = 683255) B683255
theorem B652175 : Blo 267823 652175 := bstep (se 1 (by rfl) ⟨489131, by rfl⟩ : syracuseStep 652175 = 978263) B978263
theorem B2290679 : Blo 267823 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B1373273 : Blo 267823 1373273 := bstep (se 2 (by rfl) ⟨514977, by rfl⟩ : syracuseStep 1373273 = 1029955) B1029955
theorem B685199 : Blo 267823 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B1144007 : Blo 267823 1144007 := bstep (se 1 (by rfl) ⟨858005, by rfl⟩ : syracuseStep 1144007 = 1716011) B1716011
theorem B324895 : Blo 267823 324895 := bstep (se 1 (by rfl) ⟨243671, by rfl⟩ : syracuseStep 324895 = 487343) B487343
theorem B292295 : Blo 267823 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B1471981 : Blo 267823 1471981 := bstep (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) B551993
theorem B456185 : Blo 267823 456185 := bstep (se 2 (by rfl) ⟨171069, by rfl⟩ : syracuseStep 456185 = 342139) B342139
theorem B456455 : Blo 267823 456455 := bstep (se 1 (by rfl) ⟨342341, by rfl⟩ : syracuseStep 456455 = 684683) B684683
theorem B915407 : Blo 267823 915407 := bstep (se 1 (by rfl) ⟨686555, by rfl⟩ : syracuseStep 915407 = 1373111) B1373111
theorem B489577 : Blo 267823 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B2062583 : Blo 267823 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B457211 : Blo 267823 457211 := bstep (se 1 (by rfl) ⟨342908, by rfl⟩ : syracuseStep 457211 = 685817) B685817
theorem B57834163 : Blo 267823 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B686839 : Blo 267823 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B916379 : Blo 267823 916379 := bstep (se 1 (by rfl) ⟨687284, by rfl⟩ : syracuseStep 916379 = 1374569) B1374569
theorem B457643 : Blo 267823 457643 := bstep (se 1 (by rfl) ⟨343232, by rfl⟩ : syracuseStep 457643 = 686465) B686465
theorem B687143 : Blo 267823 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B458183 : Blo 267823 458183 := bstep (se 1 (by rfl) ⟨343637, by rfl⟩ : syracuseStep 458183 = 687275) B687275
theorem B1375703 : Blo 267823 1375703 := bstep (se 1 (by rfl) ⟨1031777, by rfl⟩ : syracuseStep 1375703 = 2063555) B2063555
theorem B1146383 : Blo 267823 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B2293343 : Blo 267823 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B917405 : Blo 267823 917405 := bstep (se 3 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 917405 = 344027) B344027
theorem B1867801 : Blo 267823 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B10485811 : Blo 267823 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B1540559 : Blo 267823 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B3080753 : Blo 267823 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B3474049 : Blo 267823 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B9011897 : Blo 267823 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B3670879 : Blo 267823 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B1639379 : Blo 267823 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1541267 : Blo 267823 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B2360927 : Blo 267823 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B6620957 : Blo 267823 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B3770219 : Blo 267823 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B1542017 : Blo 267823 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B1738871 : Blo 267823 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B920551 : Blo 267823 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B822415 : Blo 267823 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B659017 : Blo 267823 659017 := bstep (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) B494263
theorem B2461265 : Blo 267823 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B364123 : Blo 267823 364123 := bstep (se 1 (by rfl) ⟨273092, by rfl⟩ : syracuseStep 364123 = 546185) B546185
theorem B1019567 : Blo 267823 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B1150841 : Blo 267823 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B529193 : Blo 267823 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B3282065 : Blo 267823 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B1152481 : Blo 267823 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B267887 : Blo 267823 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B267943 : Blo 267823 267943 := bstep (se 1 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 267943 = 401915) B401915
theorem B268027 : Blo 267823 268027 := bstep (se 1 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 268027 = 402041) B402041
theorem B268063 : Blo 267823 268063 := bstep (se 1 (by rfl) ⟨201047, by rfl⟩ : syracuseStep 268063 = 402095) B402095
theorem B268095 : Blo 267823 268095 := bstep (se 1 (by rfl) ⟨201071, by rfl⟩ : syracuseStep 268095 = 402143) B402143
theorem B727003 : Blo 267823 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B268271 : Blo 267823 268271 := bstep (se 1 (by rfl) ⟨201203, by rfl⟩ : syracuseStep 268271 = 402407) B402407
theorem B268443 : Blo 267823 268443 := bstep (se 1 (by rfl) ⟨201332, by rfl⟩ : syracuseStep 268443 = 402665) B402665
theorem B268479 : Blo 267823 268479 := bstep (se 1 (by rfl) ⟨201359, by rfl⟩ : syracuseStep 268479 = 402719) B402719
theorem B268591 : Blo 267823 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B12392909 : Blo 267823 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B268827 : Blo 267823 268827 := bstep (se 1 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 268827 = 403241) B403241
theorem B268831 : Blo 267823 268831 := bstep (se 1 (by rfl) ⟨201623, by rfl⟩ : syracuseStep 268831 = 403247) B403247
theorem B269147 : Blo 267823 269147 := bstep (se 1 (by rfl) ⟨201860, by rfl⟩ : syracuseStep 269147 = 403721) B403721
theorem B1547099 : Blo 267823 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B269215 : Blo 267823 269215 := bstep (se 1 (by rfl) ⟨201911, by rfl⟩ : syracuseStep 269215 = 403823) B403823
theorem B859081 : Blo 267823 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B433193 : Blo 267823 433193 := bstep (se 2 (by rfl) ⟨162447, by rfl⟩ : syracuseStep 433193 = 324895) B324895
theorem B269359 : Blo 267823 269359 := bstep (se 1 (by rfl) ⟨202019, by rfl⟩ : syracuseStep 269359 = 404039) B404039
theorem B269383 : Blo 267823 269383 := bstep (se 1 (by rfl) ⟨202037, by rfl⟩ : syracuseStep 269383 = 404075) B404075
theorem B269535 : Blo 267823 269535 := bstep (se 1 (by rfl) ⟨202151, by rfl⟩ : syracuseStep 269535 = 404303) B404303
theorem B269799 : Blo 267823 269799 := bstep (se 1 (by rfl) ⟨202349, by rfl⟩ : syracuseStep 269799 = 404699) B404699
theorem B695783 : Blo 267823 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B302683 : Blo 267823 302683 := bstep (se 1 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 302683 = 454025) B454025
theorem B269915 : Blo 267823 269915 := bstep (se 1 (by rfl) ⟨202436, by rfl⟩ : syracuseStep 269915 = 404873) B404873
theorem B6954659 : Blo 267823 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B925409 : Blo 267823 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B270151 : Blo 267823 270151 := bstep (se 1 (by rfl) ⟨202613, by rfl⟩ : syracuseStep 270151 = 405227) B405227
theorem B302971 : Blo 267823 302971 := bstep (se 1 (by rfl) ⟨227228, by rfl⟩ : syracuseStep 302971 = 454457) B454457
theorem B270303 : Blo 267823 270303 := bstep (se 1 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 270303 = 405455) B405455
theorem B270567 : Blo 267823 270567 := bstep (se 1 (by rfl) ⟨202925, by rfl⟩ : syracuseStep 270567 = 405851) B405851
theorem B270719 : Blo 267823 270719 := bstep (se 1 (by rfl) ⟨203039, by rfl⟩ : syracuseStep 270719 = 406079) B406079
theorem B401801 : Blo 267823 401801 := bstep (se 2 (by rfl) ⟨150675, by rfl⟩ : syracuseStep 401801 = 301351) B301351
theorem B270799 : Blo 267823 270799 := bstep (se 1 (by rfl) ⟨203099, by rfl⟩ : syracuseStep 270799 = 406199) B406199
theorem B401897 : Blo 267823 401897 := bstep (se 2 (by rfl) ⟨150711, by rfl⟩ : syracuseStep 401897 = 301423) B301423
theorem B434783 : Blo 267823 434783 := bstep (se 1 (by rfl) ⟨326087, by rfl⟩ : syracuseStep 434783 = 652175) B652175
theorem B402023 : Blo 267823 402023 := bstep (se 1 (by rfl) ⟨301517, by rfl⟩ : syracuseStep 402023 = 603035) B603035
theorem B270951 : Blo 267823 270951 := bstep (se 1 (by rfl) ⟨203213, by rfl⟩ : syracuseStep 270951 = 406427) B406427
theorem B402155 : Blo 267823 402155 := bstep (se 1 (by rfl) ⟨301616, by rfl⟩ : syracuseStep 402155 = 603233) B603233
theorem B402185 : Blo 267823 402185 := bstep (se 2 (by rfl) ⟨150819, by rfl⟩ : syracuseStep 402185 = 301639) B301639
theorem B762671 : Blo 267823 762671 := bstep (se 1 (by rfl) ⟨572003, by rfl⟩ : syracuseStep 762671 = 1144007) B1144007
theorem B402287 : Blo 267823 402287 := bstep (se 1 (by rfl) ⟨301715, by rfl⟩ : syracuseStep 402287 = 603431) B603431
theorem B271215 : Blo 267823 271215 := bstep (se 1 (by rfl) ⟨203411, by rfl⟩ : syracuseStep 271215 = 406823) B406823
theorem B77112217 : Blo 267823 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B271271 : Blo 267823 271271 := bstep (se 1 (by rfl) ⟨203453, by rfl⟩ : syracuseStep 271271 = 406907) B406907
theorem B304123 : Blo 267823 304123 := bstep (se 1 (by rfl) ⟨228092, by rfl⟩ : syracuseStep 304123 = 456185) B456185
theorem B271355 : Blo 267823 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B271423 : Blo 267823 271423 := bstep (se 1 (by rfl) ⟨203567, by rfl⟩ : syracuseStep 271423 = 407135) B407135
theorem B402539 : Blo 267823 402539 := bstep (se 1 (by rfl) ⟨301904, by rfl⟩ : syracuseStep 402539 = 603809) B603809
theorem B304303 : Blo 267823 304303 := bstep (se 1 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 304303 = 456455) B456455
theorem B271567 : Blo 267823 271567 := bstep (se 1 (by rfl) ⟨203675, by rfl⟩ : syracuseStep 271567 = 407351) B407351
theorem B402779 : Blo 267823 402779 := bstep (se 1 (by rfl) ⟨302084, by rfl⟩ : syracuseStep 402779 = 604169) B604169
theorem B271771 : Blo 267823 271771 := bstep (se 1 (by rfl) ⟨203828, by rfl⟩ : syracuseStep 271771 = 407657) B407657
theorem B403055 : Blo 267823 403055 := bstep (se 1 (by rfl) ⟨302291, by rfl⟩ : syracuseStep 403055 = 604583) B604583
theorem B304807 : Blo 267823 304807 := bstep (se 1 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 304807 = 457211) B457211
theorem B403127 : Blo 267823 403127 := bstep (se 1 (by rfl) ⟨302345, by rfl⟩ : syracuseStep 403127 = 604691) B604691
theorem B403163 : Blo 267823 403163 := bstep (se 1 (by rfl) ⟨302372, by rfl⟩ : syracuseStep 403163 = 604745) B604745
theorem B403337 : Blo 267823 403337 := bstep (se 2 (by rfl) ⟨151251, by rfl⟩ : syracuseStep 403337 = 302503) B302503
theorem B305095 : Blo 267823 305095 := bstep (se 1 (by rfl) ⟨228821, by rfl⟩ : syracuseStep 305095 = 457643) B457643
theorem B403439 : Blo 267823 403439 := bstep (se 1 (by rfl) ⟨302579, by rfl⟩ : syracuseStep 403439 = 605159) B605159
theorem B403691 : Blo 267823 403691 := bstep (se 1 (by rfl) ⟨302768, by rfl⟩ : syracuseStep 403691 = 605537) B605537
theorem B1943833 : Blo 267823 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B403751 : Blo 267823 403751 := bstep (se 1 (by rfl) ⟨302813, by rfl⟩ : syracuseStep 403751 = 605627) B605627
theorem B305455 : Blo 267823 305455 := bstep (se 1 (by rfl) ⟨229091, by rfl⟩ : syracuseStep 305455 = 458183) B458183
theorem B764255 : Blo 267823 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B1648991 : Blo 267823 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B403835 : Blo 267823 403835 := bstep (se 1 (by rfl) ⟨302876, by rfl⟩ : syracuseStep 403835 = 605753) B605753
theorem B862721 : Blo 267823 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B404105 : Blo 267823 404105 := bstep (se 2 (by rfl) ⟨151539, by rfl⟩ : syracuseStep 404105 = 303079) B303079
theorem B404279 : Blo 267823 404279 := bstep (se 1 (by rfl) ⟨303209, by rfl⟩ : syracuseStep 404279 = 606419) B606419
theorem B404315 : Blo 267823 404315 := bstep (se 1 (by rfl) ⟨303236, by rfl⟩ : syracuseStep 404315 = 606473) B606473
theorem B764903 : Blo 267823 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B404459 : Blo 267823 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B404663 : Blo 267823 404663 := bstep (se 1 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 404663 = 606995) B606995
theorem B339167 : Blo 267823 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B11873665 : Blo 267823 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B404903 : Blo 267823 404903 := bstep (se 1 (by rfl) ⟨303677, by rfl⟩ : syracuseStep 404903 = 607355) B607355
theorem B404987 : Blo 267823 404987 := bstep (se 1 (by rfl) ⟨303740, by rfl⟩ : syracuseStep 404987 = 607481) B607481
theorem B339547 : Blo 267823 339547 := bstep (se 1 (by rfl) ⟨254660, by rfl⟩ : syracuseStep 339547 = 509321) B509321
theorem B405083 : Blo 267823 405083 := bstep (se 1 (by rfl) ⟨303812, by rfl⟩ : syracuseStep 405083 = 607625) B607625
theorem B405167 : Blo 267823 405167 := bstep (se 1 (by rfl) ⟨303875, by rfl⟩ : syracuseStep 405167 = 607751) B607751
theorem B405287 : Blo 267823 405287 := bstep (se 1 (by rfl) ⟨303965, by rfl⟩ : syracuseStep 405287 = 607931) B607931
theorem B405371 : Blo 267823 405371 := bstep (se 1 (by rfl) ⟨304028, by rfl⟩ : syracuseStep 405371 = 608057) B608057
theorem B1028285 : Blo 267823 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B4141313 : Blo 267823 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B405791 : Blo 267823 405791 := bstep (se 1 (by rfl) ⟨304343, by rfl⟩ : syracuseStep 405791 = 608687) B608687
theorem B405815 : Blo 267823 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B405887 : Blo 267823 405887 := bstep (se 1 (by rfl) ⟨304415, by rfl⟩ : syracuseStep 405887 = 608831) B608831
theorem B405959 : Blo 267823 405959 := bstep (se 1 (by rfl) ⟨304469, by rfl⟩ : syracuseStep 405959 = 608939) B608939
theorem B1946081 : Blo 267823 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B3912407 : Blo 267823 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B2896631 : Blo 267823 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B406313 : Blo 267823 406313 := bstep (se 2 (by rfl) ⟨152367, by rfl⟩ : syracuseStep 406313 = 304735) B304735
theorem B406319 : Blo 267823 406319 := bstep (se 1 (by rfl) ⟨304739, by rfl⟩ : syracuseStep 406319 = 609479) B609479
theorem B14725961 : Blo 267823 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B406439 : Blo 267823 406439 := bstep (se 1 (by rfl) ⟨304829, by rfl⟩ : syracuseStep 406439 = 609659) B609659
theorem B406523 : Blo 267823 406523 := bstep (se 1 (by rfl) ⟨304892, by rfl⟩ : syracuseStep 406523 = 609785) B609785
theorem B406583 : Blo 267823 406583 := bstep (se 1 (by rfl) ⟨304937, by rfl⟩ : syracuseStep 406583 = 609875) B609875
theorem B2765963 : Blo 267823 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B341167 : Blo 267823 341167 := bstep (se 1 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 341167 = 511751) B511751
theorem B406703 : Blo 267823 406703 := bstep (se 1 (by rfl) ⟨305027, by rfl⟩ : syracuseStep 406703 = 610055) B610055
theorem B767387 : Blo 267823 767387 := bstep (se 1 (by rfl) ⟨575540, by rfl⟩ : syracuseStep 767387 = 1151081) B1151081
theorem B2307527 : Blo 267823 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B603719 : Blo 267823 603719 := bstep (se 1 (by rfl) ⟨452789, by rfl⟩ : syracuseStep 603719 = 905579) B905579
theorem B407111 : Blo 267823 407111 := bstep (se 1 (by rfl) ⟨305333, by rfl⟩ : syracuseStep 407111 = 610667) B610667
theorem B8566361 : Blo 267823 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B407207 : Blo 267823 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B1160887 : Blo 267823 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B603899 : Blo 267823 603899 := bstep (se 1 (by rfl) ⟨452924, by rfl⟩ : syracuseStep 603899 = 905849) B905849
theorem B407291 : Blo 267823 407291 := bstep (se 1 (by rfl) ⟨305468, by rfl⟩ : syracuseStep 407291 = 610937) B610937
theorem B407327 : Blo 267823 407327 := bstep (se 1 (by rfl) ⟨305495, by rfl⟩ : syracuseStep 407327 = 610991) B610991
theorem B440143 : Blo 267823 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B407375 : Blo 267823 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B407495 : Blo 267823 407495 := bstep (se 1 (by rfl) ⟨305621, by rfl⟩ : syracuseStep 407495 = 611243) B611243
theorem B1357883 : Blo 267823 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B604457 : Blo 267823 604457 := bstep (se 2 (by rfl) ⟨226671, by rfl⟩ : syracuseStep 604457 = 453343) B453343
theorem B2931059 : Blo 267823 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B342559 : Blo 267823 342559 := bstep (se 1 (by rfl) ⟨256919, by rfl⟩ : syracuseStep 342559 = 513839) B513839
theorem B1456793 : Blo 267823 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B965459 : Blo 267823 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B605033 : Blo 267823 605033 := bstep (se 2 (by rfl) ⟨226887, by rfl⟩ : syracuseStep 605033 = 453775) B453775
theorem B605087 : Blo 267823 605087 := bstep (se 1 (by rfl) ⟨453815, by rfl⟩ : syracuseStep 605087 = 907631) B907631
theorem B343111 : Blo 267823 343111 := bstep (se 1 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 343111 = 514667) B514667
theorem B769277 : Blo 267823 769277 := bstep (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) B288479
theorem B1948967 : Blo 267823 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B1359341 : Blo 267823 1359341 := bstep (se 3 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 1359341 = 509753) B509753
theorem B867847 : Blo 267823 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B1031687 : Blo 267823 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B15711853 : Blo 267823 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B1359503 : Blo 267823 1359503 := bstep (se 1 (by rfl) ⟨1019627, by rfl⟩ : syracuseStep 1359503 = 2039255) B2039255
theorem B3456827 : Blo 267823 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B606023 : Blo 267823 606023 := bstep (se 1 (by rfl) ⟨454517, by rfl⟩ : syracuseStep 606023 = 909035) B909035
theorem B3260267 : Blo 267823 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B769915 : Blo 267823 769915 := bstep (se 1 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 769915 = 1154873) B1154873
theorem B770087 : Blo 267823 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B7979147 : Blo 267823 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1360151 : Blo 267823 1360151 := bstep (se 1 (by rfl) ⟨1020113, by rfl⟩ : syracuseStep 1360151 = 2040227) B2040227
theorem B1720601 : Blo 267823 1720601 := bstep (se 2 (by rfl) ⟨645225, by rfl⟩ : syracuseStep 1720601 = 1290451) B1290451
theorem B967031 : Blo 267823 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B606671 : Blo 267823 606671 := bstep (se 1 (by rfl) ⟨455003, by rfl⟩ : syracuseStep 606671 = 910007) B910007
theorem B770735 : Blo 267823 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B967535 : Blo 267823 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B869231 : Blo 267823 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B345151 : Blo 267823 345151 := bstep (se 1 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 345151 = 517727) B517727
theorem B607337 : Blo 267823 607337 := bstep (se 2 (by rfl) ⟨227751, by rfl⟩ : syracuseStep 607337 = 455503) B455503
theorem B2606539 : Blo 267823 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B607967 : Blo 267823 607967 := bstep (se 1 (by rfl) ⟨455975, by rfl⟩ : syracuseStep 607967 = 911951) B911951
theorem B1361771 : Blo 267823 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B3066173 : Blo 267823 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B608795 : Blo 267823 608795 := bstep (se 1 (by rfl) ⟨456596, by rfl⟩ : syracuseStep 608795 = 913193) B913193
theorem B904391 : Blo 267823 904391 := bstep (se 1 (by rfl) ⟨678293, by rfl⟩ : syracuseStep 904391 = 1356587) B1356587
theorem B773401 : Blo 267823 773401 := bstep (se 2 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 773401 = 580051) B580051
theorem B1527119 : Blo 267823 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B577019 : Blo 267823 577019 := bstep (se 1 (by rfl) ⟨432764, by rfl⟩ : syracuseStep 577019 = 865529) B865529
theorem B3296857 : Blo 267823 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B610271 : Blo 267823 610271 := bstep (se 1 (by rfl) ⟨457703, by rfl⟩ : syracuseStep 610271 = 915407) B915407
theorem B577847 : Blo 267823 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B905687 : Blo 267823 905687 := bstep (se 1 (by rfl) ⟨679265, by rfl⟩ : syracuseStep 905687 = 1358531) B1358531
theorem B610919 : Blo 267823 610919 := bstep (se 1 (by rfl) ⟨458189, by rfl⟩ : syracuseStep 610919 = 916379) B916379
theorem B1528895 : Blo 267823 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B775241 : Blo 267823 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B611603 : Blo 267823 611603 := bstep (se 1 (by rfl) ⟨458702, by rfl⟩ : syracuseStep 611603 = 917405) B917405
theorem B907145 : Blo 267823 907145 := bstep (se 2 (by rfl) ⟨340179, by rfl⟩ : syracuseStep 907145 = 680359) B680359
theorem B1169383 : Blo 267823 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B907361 : Blo 267823 907361 := bstep (se 2 (by rfl) ⟨340260, by rfl⟩ : syracuseStep 907361 = 680521) B680521
theorem B1235375 : Blo 267823 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B678739 : Blo 267823 678739 := bstep (se 1 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 678739 = 1018109) B1018109
theorem B678881 : Blo 267823 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B908279 : Blo 267823 908279 := bstep (se 1 (by rfl) ⟨681209, by rfl⟩ : syracuseStep 908279 = 1362419) B1362419
theorem B384041 : Blo 267823 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B1629551 : Blo 267823 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B908711 : Blo 267823 908711 := bstep (se 1 (by rfl) ⟨681533, by rfl⟩ : syracuseStep 908711 = 1363067) B1363067
theorem B1990307 : Blo 267823 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B1728209 : Blo 267823 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B679657 : Blo 267823 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B909143 : Blo 267823 909143 := bstep (se 1 (by rfl) ⟨681857, by rfl⟩ : syracuseStep 909143 = 1363715) B1363715
theorem B6545447 : Blo 267823 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B647455 : Blo 267823 647455 := bstep (se 1 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 647455 = 971183) B971183
theorem B6644227 : Blo 267823 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1729133 : Blo 267823 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B909953 : Blo 267823 909953 := bstep (se 2 (by rfl) ⟨341232, by rfl⟩ : syracuseStep 909953 = 682465) B682465
theorem B680683 : Blo 267823 680683 := bstep (se 1 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 680683 = 1021025) B1021025
theorem B910223 : Blo 267823 910223 := bstep (se 1 (by rfl) ⟨682667, by rfl⟩ : syracuseStep 910223 = 1365335) B1365335
theorem B2319313 : Blo 267823 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B779453 : Blo 267823 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B910763 : Blo 267823 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B452263 : Blo 267823 452263 := bstep (se 1 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 452263 = 678395) B678395
theorem B911303 : Blo 267823 911303 := bstep (se 1 (by rfl) ⟨683477, by rfl⟩ : syracuseStep 911303 = 1366955) B1366955
theorem B452911 : Blo 267823 452911 := bstep (se 1 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 452911 = 679367) B679367
theorem B977309 : Blo 267823 977309 := bstep (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) B366491
theorem B3435047 : Blo 267823 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B912059 : Blo 267823 912059 := bstep (se 1 (by rfl) ⟨684044, by rfl⟩ : syracuseStep 912059 = 1368089) B1368089
theorem B453431 : Blo 267823 453431 := bstep (se 1 (by rfl) ⟨340073, by rfl⟩ : syracuseStep 453431 = 680147) B680147
theorem B322463 : Blo 267823 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B486665 : Blo 267823 486665 := bstep (se 2 (by rfl) ⟨182499, by rfl⟩ : syracuseStep 486665 = 364999) B364999
theorem B15756743 : Blo 267823 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B454207 : Blo 267823 454207 := bstep (se 1 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 454207 = 681311) B681311
theorem B2781067 : Blo 267823 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B978911 : Blo 267823 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B84275315 : Blo 267823 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B454943 : Blo 267823 454943 := bstep (se 1 (by rfl) ⟨341207, by rfl⟩ : syracuseStep 454943 = 682415) B682415
theorem B4583951 : Blo 267823 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B914003 : Blo 267823 914003 := bstep (se 1 (by rfl) ⟨685502, by rfl⟩ : syracuseStep 914003 = 1371005) B1371005
theorem B619103 : Blo 267823 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B1962641 : Blo 267823 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B1536893 : Blo 267823 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B455591 : Blo 267823 455591 := bstep (se 1 (by rfl) ⟨341693, by rfl⟩ : syracuseStep 455591 = 683387) B683387
theorem B488359 : Blo 267823 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B455753 : Blo 267823 455753 := bstep (se 2 (by rfl) ⟨170907, by rfl⟩ : syracuseStep 455753 = 341815) B341815
theorem B914651 : Blo 267823 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B685331 : Blo 267823 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B652769 : Blo 267823 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B456313 : Blo 267823 456313 := bstep (se 2 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 456313 = 342235) B342235
theorem B915515 : Blo 267823 915515 := bstep (se 1 (by rfl) ⟨686636, by rfl⟩ : syracuseStep 915515 = 1373273) B1373273
theorem B456799 : Blo 267823 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B817307 : Blo 267823 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B915785 : Blo 267823 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B948893 : Blo 267823 948893 := bstep (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) B355835
theorem B1538783 : Blo 267823 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B1375055 : Blo 267823 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B1637729 : Blo 267823 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B458095 : Blo 267823 458095 := bstep (se 1 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 458095 = 687143) B687143
theorem B1539557 : Blo 267823 1539557 := bstep (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) B288667
theorem B917135 : Blo 267823 917135 := bstep (se 1 (by rfl) ⟨687851, by rfl⟩ : syracuseStep 917135 = 1375703) B1375703
theorem B1539809 : Blo 267823 1539809 := bstep (se 2 (by rfl) ⟨577428, by rfl⟩ : syracuseStep 1539809 = 1154857) B1154857
theorem B458473 : Blo 267823 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B2490401 : Blo 267823 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1147067 : Blo 267823 1147067 := bstep (se 1 (by rfl) ⟨860300, by rfl⟩ : syracuseStep 1147067 = 1720601) B1720601
theorem B460201 : Blo 267823 460201 := bstep (se 2 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 460201 = 345151) B345151
theorem B3475385 : Blo 267823 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B1411181 : Blo 267823 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B1018079 : Blo 267823 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B1640843 : Blo 267823 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B2591777 : Blo 267823 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1019263 : Blo 267823 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B6295805 : Blo 267823 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B823583 : Blo 267823 823583 := bstep (se 1 (by rfl) ⟨617687, by rfl⟩ : syracuseStep 823583 = 1235375) B1235375
theorem B8261939 : Blo 267823 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B15831553 : Blo 267823 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B4395809 : Blo 267823 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1086367 : Blo 267823 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B463855 : Blo 267823 463855 := bstep (se 1 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 463855 = 695783) B695783
theorem B1152139 : Blo 267823 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B3708089 : Blo 267823 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B4363631 : Blo 267823 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B267867 : Blo 267823 267867 := bstep (se 1 (by rfl) ⟨200900, by rfl⟩ : syracuseStep 267867 = 401801) B401801
theorem B267931 : Blo 267823 267931 := bstep (se 1 (by rfl) ⟨200948, by rfl⟩ : syracuseStep 267931 = 401897) B401897
theorem B268015 : Blo 267823 268015 := bstep (se 1 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 268015 = 402023) B402023
theorem B1152755 : Blo 267823 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B268103 : Blo 267823 268103 := bstep (se 1 (by rfl) ⟨201077, by rfl⟩ : syracuseStep 268103 = 402155) B402155
theorem B268123 : Blo 267823 268123 := bstep (se 1 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 268123 = 402185) B402185
theorem B268191 : Blo 267823 268191 := bstep (se 1 (by rfl) ⟨201143, by rfl⟩ : syracuseStep 268191 = 402287) B402287
theorem B268359 : Blo 267823 268359 := bstep (se 1 (by rfl) ⟨201269, by rfl⟩ : syracuseStep 268359 = 402539) B402539
theorem B268519 : Blo 267823 268519 := bstep (se 1 (by rfl) ⟨201389, by rfl⟩ : syracuseStep 268519 = 402779) B402779
theorem B268703 : Blo 267823 268703 := bstep (se 1 (by rfl) ⟨201527, by rfl⟩ : syracuseStep 268703 = 403055) B403055
theorem B268751 : Blo 267823 268751 := bstep (se 1 (by rfl) ⟨201563, by rfl⟩ : syracuseStep 268751 = 403127) B403127
theorem B268775 : Blo 267823 268775 := bstep (se 1 (by rfl) ⟨201581, by rfl⟩ : syracuseStep 268775 = 403163) B403163
theorem B268891 : Blo 267823 268891 := bstep (se 1 (by rfl) ⟨201668, by rfl⟩ : syracuseStep 268891 = 403337) B403337
theorem B268959 : Blo 267823 268959 := bstep (se 1 (by rfl) ⟨201719, by rfl⟩ : syracuseStep 268959 = 403439) B403439
theorem B269127 : Blo 267823 269127 := bstep (se 1 (by rfl) ⟨201845, by rfl⟩ : syracuseStep 269127 = 403691) B403691
theorem B269167 : Blo 267823 269167 := bstep (se 1 (by rfl) ⟨201875, by rfl⟩ : syracuseStep 269167 = 403751) B403751
theorem B269223 : Blo 267823 269223 := bstep (se 1 (by rfl) ⟨201917, by rfl⟩ : syracuseStep 269223 = 403835) B403835
theorem B2530381 : Blo 267823 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B269403 : Blo 267823 269403 := bstep (se 1 (by rfl) ⟨202052, by rfl⟩ : syracuseStep 269403 = 404105) B404105
theorem B302287 : Blo 267823 302287 := bstep (se 1 (by rfl) ⟨226715, by rfl⟩ : syracuseStep 302287 = 453431) B453431
theorem B269519 : Blo 267823 269519 := bstep (se 1 (by rfl) ⟨202139, by rfl⟩ : syracuseStep 269519 = 404279) B404279
theorem B269543 : Blo 267823 269543 := bstep (se 1 (by rfl) ⟨202157, by rfl⟩ : syracuseStep 269543 = 404315) B404315
theorem B269639 : Blo 267823 269639 := bstep (se 1 (by rfl) ⟨202229, by rfl⟩ : syracuseStep 269639 = 404459) B404459
theorem B269775 : Blo 267823 269775 := bstep (se 1 (by rfl) ⟨202331, by rfl⟩ : syracuseStep 269775 = 404663) B404663
theorem B1547849 : Blo 267823 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B269935 : Blo 267823 269935 := bstep (se 1 (by rfl) ⟨202451, by rfl⟩ : syracuseStep 269935 = 404903) B404903
theorem B269991 : Blo 267823 269991 := bstep (se 1 (by rfl) ⟨202493, by rfl⟩ : syracuseStep 269991 = 404987) B404987
theorem B270055 : Blo 267823 270055 := bstep (se 1 (by rfl) ⟨202541, by rfl⟩ : syracuseStep 270055 = 405083) B405083
theorem B859901 : Blo 267823 859901 := bstep (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) B322463
theorem B270111 : Blo 267823 270111 := bstep (se 1 (by rfl) ⟨202583, by rfl⟩ : syracuseStep 270111 = 405167) B405167
theorem B270191 : Blo 267823 270191 := bstep (se 1 (by rfl) ⟨202643, by rfl⟩ : syracuseStep 270191 = 405287) B405287
theorem B270247 : Blo 267823 270247 := bstep (se 1 (by rfl) ⟨202685, by rfl⟩ : syracuseStep 270247 = 405371) B405371
theorem B2039741 : Blo 267823 2039741 := bstep (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) B764903
theorem B1024109 : Blo 267823 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B1155181 : Blo 267823 1155181 := bstep (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) B433193
theorem B2760875 : Blo 267823 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B303295 : Blo 267823 303295 := bstep (se 1 (by rfl) ⟨227471, by rfl⟩ : syracuseStep 303295 = 454943) B454943
theorem B270527 : Blo 267823 270527 := bstep (se 1 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 270527 = 405791) B405791
theorem B270543 : Blo 267823 270543 := bstep (se 1 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 270543 = 405815) B405815
theorem B270591 : Blo 267823 270591 := bstep (se 1 (by rfl) ⟨202943, by rfl⟩ : syracuseStep 270591 = 405887) B405887
theorem B270639 : Blo 267823 270639 := bstep (se 1 (by rfl) ⟨202979, by rfl⟩ : syracuseStep 270639 = 405959) B405959
theorem B3055967 : Blo 267823 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B3514757 : Blo 267823 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B270875 : Blo 267823 270875 := bstep (se 1 (by rfl) ⟨203156, by rfl⟩ : syracuseStep 270875 = 406313) B406313
theorem B270879 : Blo 267823 270879 := bstep (se 1 (by rfl) ⟨203159, by rfl⟩ : syracuseStep 270879 = 406319) B406319
theorem B1024595 : Blo 267823 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B303727 : Blo 267823 303727 := bstep (se 1 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 303727 = 455591) B455591
theorem B270959 : Blo 267823 270959 := bstep (se 1 (by rfl) ⟨203219, by rfl⟩ : syracuseStep 270959 = 406439) B406439
theorem B271015 : Blo 267823 271015 := bstep (se 1 (by rfl) ⟨203261, by rfl⟩ : syracuseStep 271015 = 406523) B406523
theorem B271055 : Blo 267823 271055 := bstep (se 1 (by rfl) ⟨203291, by rfl⟩ : syracuseStep 271055 = 406583) B406583
theorem B303835 : Blo 267823 303835 := bstep (se 1 (by rfl) ⟨227876, by rfl⟩ : syracuseStep 303835 = 455753) B455753
theorem B1843975 : Blo 267823 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B271135 : Blo 267823 271135 := bstep (se 1 (by rfl) ⟨203351, by rfl⟩ : syracuseStep 271135 = 406703) B406703
theorem B435179 : Blo 267823 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B402479 : Blo 267823 402479 := bstep (se 1 (by rfl) ⟨301859, by rfl⟩ : syracuseStep 402479 = 603719) B603719
theorem B271407 : Blo 267823 271407 := bstep (se 1 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 271407 = 407111) B407111
theorem B5710907 : Blo 267823 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B271471 : Blo 267823 271471 := bstep (se 1 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 271471 = 407207) B407207
theorem B402599 : Blo 267823 402599 := bstep (se 1 (by rfl) ⟨301949, by rfl⟩ : syracuseStep 402599 = 603899) B603899
theorem B271527 : Blo 267823 271527 := bstep (se 1 (by rfl) ⟨203645, by rfl⟩ : syracuseStep 271527 = 407291) B407291
theorem B271551 : Blo 267823 271551 := bstep (se 1 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 271551 = 407327) B407327
theorem B271583 : Blo 267823 271583 := bstep (se 1 (by rfl) ⟨203687, by rfl⟩ : syracuseStep 271583 = 407375) B407375
theorem B271663 : Blo 267823 271663 := bstep (se 1 (by rfl) ⟨203747, by rfl⟩ : syracuseStep 271663 = 407495) B407495
theorem B402971 : Blo 267823 402971 := bstep (se 1 (by rfl) ⟨302228, by rfl⟩ : syracuseStep 402971 = 604457) B604457
theorem B1025855 : Blo 267823 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B403355 : Blo 267823 403355 := bstep (se 1 (by rfl) ⟨302516, by rfl⟩ : syracuseStep 403355 = 605033) B605033
theorem B403391 : Blo 267823 403391 := bstep (se 1 (by rfl) ⟨302543, by rfl⟩ : syracuseStep 403391 = 605087) B605087
theorem B1157129 : Blo 267823 1157129 := bstep (se 2 (by rfl) ⟨433923, by rfl⟩ : syracuseStep 1157129 = 867847) B867847
theorem B403577 : Blo 267823 403577 := bstep (se 2 (by rfl) ⟨151341, by rfl⟩ : syracuseStep 403577 = 302683) B302683
theorem B20949137 : Blo 267823 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1091819 : Blo 267823 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B1026371 : Blo 267823 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B1026539 : Blo 267823 1026539 := bstep (se 1 (by rfl) ⟨769904, by rfl⟩ : syracuseStep 1026539 = 1539809) B1539809
theorem B403961 : Blo 267823 403961 := bstep (se 2 (by rfl) ⟨151485, by rfl⟩ : syracuseStep 403961 = 302971) B302971
theorem B1026553 : Blo 267823 1026553 := bstep (se 2 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 1026553 = 769915) B769915
theorem B2304551 : Blo 267823 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B404015 : Blo 267823 404015 := bstep (se 1 (by rfl) ⟨303011, by rfl⟩ : syracuseStep 404015 = 606023) B606023
theorem B2173511 : Blo 267823 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B5319431 : Blo 267823 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B404447 : Blo 267823 404447 := bstep (se 1 (by rfl) ⟨303335, by rfl⟩ : syracuseStep 404447 = 606671) B606671
theorem B1027039 : Blo 267823 1027039 := bstep (se 1 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 1027039 = 1540559) B1540559
theorem B863273 : Blo 267823 863273 := bstep (se 2 (by rfl) ⟨323727, by rfl⟩ : syracuseStep 863273 = 647455) B647455
theorem B6007931 : Blo 267823 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B8858969 : Blo 267823 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B404891 : Blo 267823 404891 := bstep (se 1 (by rfl) ⟨303668, by rfl⟩ : syracuseStep 404891 = 607337) B607337
theorem B1027511 : Blo 267823 1027511 := bstep (se 1 (by rfl) ⟨770633, by rfl⟩ : syracuseStep 1027511 = 1541267) B1541267
theorem B4632065 : Blo 267823 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B4894505 : Blo 267823 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B405311 : Blo 267823 405311 := bstep (se 1 (by rfl) ⟨303983, by rfl⟩ : syracuseStep 405311 = 607967) B607967
theorem B1028011 : Blo 267823 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B3092417 : Blo 267823 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B405497 : Blo 267823 405497 := bstep (se 2 (by rfl) ⟨152061, by rfl⟩ : syracuseStep 405497 = 304123) B304123
theorem B1159247 : Blo 267823 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B2044115 : Blo 267823 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B405737 : Blo 267823 405737 := bstep (se 2 (by rfl) ⟨152151, by rfl⟩ : syracuseStep 405737 = 304303) B304303
theorem B1650941 : Blo 267823 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B405863 : Blo 267823 405863 := bstep (se 1 (by rfl) ⟨304397, by rfl⟩ : syracuseStep 405863 = 608795) B608795
theorem B602927 : Blo 267823 602927 := bstep (se 1 (by rfl) ⟨452195, by rfl⟩ : syracuseStep 602927 = 904391) B904391
theorem B603017 : Blo 267823 603017 := bstep (se 2 (by rfl) ⟨226131, by rfl⟩ : syracuseStep 603017 = 452263) B452263
theorem B406409 : Blo 267823 406409 := bstep (se 2 (by rfl) ⟨152403, by rfl⟩ : syracuseStep 406409 = 304807) B304807
theorem B4371677 : Blo 267823 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B767227 : Blo 267823 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B406793 : Blo 267823 406793 := bstep (se 2 (by rfl) ⟨152547, by rfl⟩ : syracuseStep 406793 = 305095) B305095
theorem B406847 : Blo 267823 406847 := bstep (se 1 (by rfl) ⟨305135, by rfl⟩ : syracuseStep 406847 = 610271) B610271
theorem B603791 : Blo 267823 603791 := bstep (se 1 (by rfl) ⟨452843, by rfl⟩ : syracuseStep 603791 = 905687) B905687
theorem B603881 : Blo 267823 603881 := bstep (se 2 (by rfl) ⟨226455, by rfl⟩ : syracuseStep 603881 = 452911) B452911
theorem B407273 : Blo 267823 407273 := bstep (se 2 (by rfl) ⟨152727, by rfl⟩ : syracuseStep 407273 = 305455) B305455
theorem B407279 : Blo 267823 407279 := bstep (se 1 (by rfl) ⟨305459, by rfl⟩ : syracuseStep 407279 = 610919) B610919
theorem B407735 : Blo 267823 407735 := bstep (se 1 (by rfl) ⟨305801, by rfl⟩ : syracuseStep 407735 = 611603) B611603
theorem B604763 : Blo 267823 604763 := bstep (se 1 (by rfl) ⟨453572, by rfl⟩ : syracuseStep 604763 = 907145) B907145
theorem B1227401 : Blo 267823 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B604907 : Blo 267823 604907 := bstep (se 1 (by rfl) ⟨453680, by rfl⟩ : syracuseStep 604907 = 907361) B907361
theorem B1096553 : Blo 267823 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B1031201 : Blo 267823 1031201 := bstep (se 2 (by rfl) ⟨386700, by rfl⟩ : syracuseStep 1031201 = 773401) B773401
theorem B1031399 : Blo 267823 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B605519 : Blo 267823 605519 := bstep (se 1 (by rfl) ⟨454139, by rfl⟩ : syracuseStep 605519 = 908279) B908279
theorem B605609 : Blo 267823 605609 := bstep (se 2 (by rfl) ⟨227103, by rfl⟩ : syracuseStep 605609 = 454207) B454207
theorem B2604581 : Blo 267823 2604581 := bstep (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) B488359
theorem B605807 : Blo 267823 605807 := bstep (se 1 (by rfl) ⟨454355, by rfl⟩ : syracuseStep 605807 = 908711) B908711
theorem B1326871 : Blo 267823 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B4636439 : Blo 267823 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B606095 : Blo 267823 606095 := bstep (se 1 (by rfl) ⟨454571, by rfl⟩ : syracuseStep 606095 = 909143) B909143
theorem B606635 : Blo 267823 606635 := bstep (se 1 (by rfl) ⟨454976, by rfl⟩ : syracuseStep 606635 = 909953) B909953
theorem B508447 : Blo 267823 508447 := bstep (se 1 (by rfl) ⟨381335, by rfl⟩ : syracuseStep 508447 = 762671) B762671
theorem B606815 : Blo 267823 606815 := bstep (se 1 (by rfl) ⟨455111, by rfl⟩ : syracuseStep 606815 = 910223) B910223
theorem B607175 : Blo 267823 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B607535 : Blo 267823 607535 := bstep (se 1 (by rfl) ⟨455651, by rfl⟩ : syracuseStep 607535 = 911303) B911303
theorem B509503 : Blo 267823 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B1099327 : Blo 267823 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B575147 : Blo 267823 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B608039 : Blo 267823 608039 := bstep (se 1 (by rfl) ⟨456029, by rfl⟩ : syracuseStep 608039 = 912059) B912059
theorem B608417 : Blo 267823 608417 := bstep (se 2 (by rfl) ⟨228156, by rfl⟩ : syracuseStep 608417 = 456313) B456313
theorem B10504495 : Blo 267823 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B969337 : Blo 267823 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1559177 : Blo 267823 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B56183543 : Blo 267823 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B609065 : Blo 267823 609065 := bstep (se 2 (by rfl) ⟨228399, by rfl⟩ : syracuseStep 609065 = 456799) B456799
theorem B1297387 : Blo 267823 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B609335 : Blo 267823 609335 := bstep (se 1 (by rfl) ⟨457001, by rfl⟩ : syracuseStep 609335 = 914003) B914003
theorem B2608271 : Blo 267823 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B9817307 : Blo 267823 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B904445 : Blo 267823 904445 := bstep (se 3 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 904445 = 339167) B339167
theorem B2051405 : Blo 267823 2051405 := bstep (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) B769277
theorem B609767 : Blo 267823 609767 := bstep (se 1 (by rfl) ⟨457325, by rfl⟩ : syracuseStep 609767 = 914651) B914651
theorem B511591 : Blo 267823 511591 := bstep (se 1 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 511591 = 767387) B767387
theorem B904985 : Blo 267823 904985 := bstep (se 2 (by rfl) ⟨339369, by rfl⟩ : syracuseStep 904985 = 678739) B678739
theorem B905255 : Blo 267823 905255 := bstep (se 1 (by rfl) ⟨678941, by rfl⟩ : syracuseStep 905255 = 1357883) B1357883
theorem B610343 : Blo 267823 610343 := bstep (se 1 (by rfl) ⟨457757, by rfl⟩ : syracuseStep 610343 = 915515) B915515
theorem B544871 : Blo 267823 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B610523 : Blo 267823 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B1954039 : Blo 267823 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B2347429 : Blo 267823 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B971195 : Blo 267823 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B610793 : Blo 267823 610793 := bstep (se 2 (by rfl) ⟨229047, by rfl⟩ : syracuseStep 610793 = 458095) B458095
theorem B643639 : Blo 267823 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B1299311 : Blo 267823 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B906209 : Blo 267823 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B611297 : Blo 267823 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B906227 : Blo 267823 906227 := bstep (se 1 (by rfl) ⟨679670, by rfl⟩ : syracuseStep 906227 = 1359341) B1359341
theorem B906335 : Blo 267823 906335 := bstep (se 1 (by rfl) ⟨679751, by rfl⟩ : syracuseStep 906335 = 1359503) B1359503
theorem B611423 : Blo 267823 611423 := bstep (se 1 (by rfl) ⟨458567, by rfl⟩ : syracuseStep 611423 = 917135) B917135
theorem B513391 : Blo 267823 513391 := bstep (se 1 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 513391 = 770087) B770087
theorem B13981081 : Blo 267823 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B906767 : Blo 267823 906767 := bstep (se 1 (by rfl) ⟨680075, by rfl⟩ : syracuseStep 906767 = 1360151) B1360151
theorem B644687 : Blo 267823 644687 := bstep (se 1 (by rfl) ⟨483515, by rfl⟩ : syracuseStep 644687 = 967031) B967031
theorem B2053835 : Blo 267823 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B645023 : Blo 267823 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B579487 : Blo 267823 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B907577 : Blo 267823 907577 := bstep (se 2 (by rfl) ⟨340341, by rfl⟩ : syracuseStep 907577 = 680683) B680683
theorem B4413971 : Blo 267823 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B102816289 : Blo 267823 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B907847 : Blo 267823 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B2513479 : Blo 267823 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B5233709 : Blo 267823 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B2055293 : Blo 267823 2055293 := bstep (se 3 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 2055293 = 770735) B770735
theorem B384679 : Blo 267823 384679 := bstep (se 1 (by rfl) ⟨288509, by rfl⟩ : syracuseStep 384679 = 577019) B577019
theorem B679711 : Blo 267823 679711 := bstep (se 1 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 679711 = 1019567) B1019567
theorem B385231 : Blo 267823 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B516827 : Blo 267823 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B2188043 : Blo 267823 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B452587 : Blo 267823 452587 := bstep (se 1 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 452587 = 678881) B678881
theorem B452729 : Blo 267823 452729 := bstep (se 2 (by rfl) ⟨169773, by rfl⟩ : syracuseStep 452729 = 339547) B339547
theorem B485497 : Blo 267823 485497 := bstep (se 2 (by rfl) ⟨182061, by rfl⟩ : syracuseStep 485497 = 364123) B364123
theorem B616939 : Blo 267823 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B289855 : Blo 267823 289855 := bstep (se 1 (by rfl) ⟨217391, by rfl⟩ : syracuseStep 289855 = 434783) B434783
theorem B519635 : Blo 267823 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B454889 : Blo 267823 454889 := bstep (se 2 (by rfl) ⟨170583, by rfl⟩ : syracuseStep 454889 = 341167) B341167
theorem B651539 : Blo 267823 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B2290031 : Blo 267823 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B1536641 : Blo 267823 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B324443 : Blo 267823 324443 := bstep (se 1 (by rfl) ⟨243332, by rfl⟩ : syracuseStep 324443 = 486665) B486665
theorem B652607 : Blo 267823 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B685523 : Blo 267823 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B1931087 : Blo 267823 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B456745 : Blo 267823 456745 := bstep (se 2 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 456745 = 342559) B342559
theorem B456887 : Blo 267823 456887 := bstep (se 1 (by rfl) ⟨342665, by rfl⟩ : syracuseStep 456887 = 685331) B685331
theorem B1538351 : Blo 267823 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B1145441 : Blo 267823 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B457481 : Blo 267823 457481 := bstep (se 2 (by rfl) ⟨171555, by rfl⟩ : syracuseStep 457481 = 343111) B343111
theorem B916703 : Blo 267823 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B687791 : Blo 267823 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B1540241 : Blo 267823 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B2589317 : Blo 267823 2589317 := bstep (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) B485497
theorem B2458633 : Blo 267823 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B9372685 : Blo 267823 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B2589853 : Blo 267823 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B37455695 : Blo 267823 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B1378205 : Blo 267823 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B1738847 : Blo 267823 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B363247 : Blo 267823 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B4197203 : Blo 267823 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B5507959 : Blo 267823 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B429791 : Blo 267823 429791 := bstep (se 1 (by rfl) ⟨322343, by rfl⟩ : syracuseStep 429791 = 644687) B644687
theorem B5149565 : Blo 267823 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B1840583 : Blo 267823 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B2037311 : Blo 267823 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B21108737 : Blo 267823 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B268319 : Blo 267823 268319 := bstep (se 1 (by rfl) ⟨201239, by rfl⟩ : syracuseStep 268319 = 402479) B402479
theorem B3807271 : Blo 267823 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B858185 : Blo 267823 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B268399 : Blo 267823 268399 := bstep (se 1 (by rfl) ⟨201299, by rfl⟩ : syracuseStep 268399 = 402599) B402599
theorem B268647 : Blo 267823 268647 := bstep (se 1 (by rfl) ⟨201485, by rfl⟩ : syracuseStep 268647 = 402971) B402971
theorem B1448489 : Blo 267823 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B268903 : Blo 267823 268903 := bstep (se 1 (by rfl) ⟨201677, by rfl⟩ : syracuseStep 268903 = 403355) B403355
theorem B268927 : Blo 267823 268927 := bstep (se 1 (by rfl) ⟨201695, by rfl⟩ : syracuseStep 268927 = 403391) B403391
theorem B301819 : Blo 267823 301819 := bstep (se 1 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 301819 = 452729) B452729
theorem B269051 : Blo 267823 269051 := bstep (se 1 (by rfl) ⟨201788, by rfl⟩ : syracuseStep 269051 = 403577) B403577
theorem B13966091 : Blo 267823 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B727879 : Blo 267823 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B3054509 : Blo 267823 3054509 := bstep (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) B1145441
theorem B1022969 : Blo 267823 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B269307 : Blo 267823 269307 := bstep (se 1 (by rfl) ⟨201980, by rfl⟩ : syracuseStep 269307 = 403961) B403961
theorem B269343 : Blo 267823 269343 := bstep (se 1 (by rfl) ⟨202007, by rfl⟩ : syracuseStep 269343 = 404015) B404015
theorem B3546287 : Blo 267823 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B269631 : Blo 267823 269631 := bstep (se 1 (by rfl) ⟨202223, by rfl⟩ : syracuseStep 269631 = 404447) B404447
theorem B4005287 : Blo 267823 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B5905979 : Blo 267823 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B269927 : Blo 267823 269927 := bstep (se 1 (by rfl) ⟨202445, by rfl⟩ : syracuseStep 269927 = 404891) B404891
theorem B3088043 : Blo 267823 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B270207 : Blo 267823 270207 := bstep (se 1 (by rfl) ⟨202655, by rfl⟩ : syracuseStep 270207 = 405311) B405311
theorem B270331 : Blo 267823 270331 := bstep (se 1 (by rfl) ⟨202748, by rfl⟩ : syracuseStep 270331 = 405497) B405497
theorem B303259 : Blo 267823 303259 := bstep (se 1 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 303259 = 454889) B454889
theorem B270491 : Blo 267823 270491 := bstep (se 1 (by rfl) ⟨202868, by rfl⟩ : syracuseStep 270491 = 405737) B405737
theorem B434359 : Blo 267823 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B270575 : Blo 267823 270575 := bstep (se 1 (by rfl) ⟨202931, by rfl⟩ : syracuseStep 270575 = 405863) B405863
theorem B1024427 : Blo 267823 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B401951 : Blo 267823 401951 := bstep (se 1 (by rfl) ⟨301463, by rfl⟩ : syracuseStep 401951 = 602927) B602927
theorem B402011 : Blo 267823 402011 := bstep (se 1 (by rfl) ⟨301508, by rfl⟩ : syracuseStep 402011 = 603017) B603017
theorem B270939 : Blo 267823 270939 := bstep (se 1 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 270939 = 406409) B406409
theorem B3351305 : Blo 267823 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B271195 : Blo 267823 271195 := bstep (se 1 (by rfl) ⟨203396, by rfl⟩ : syracuseStep 271195 = 406793) B406793
theorem B271231 : Blo 267823 271231 := bstep (se 1 (by rfl) ⟨203423, by rfl⟩ : syracuseStep 271231 = 406847) B406847
theorem B435071 : Blo 267823 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B402527 : Blo 267823 402527 := bstep (se 1 (by rfl) ⟨301895, by rfl⟩ : syracuseStep 402527 = 603791) B603791
theorem B402587 : Blo 267823 402587 := bstep (se 1 (by rfl) ⟨301940, by rfl⟩ : syracuseStep 402587 = 603881) B603881
theorem B271515 : Blo 267823 271515 := bstep (se 1 (by rfl) ⟨203636, by rfl⟩ : syracuseStep 271515 = 407273) B407273
theorem B271519 : Blo 267823 271519 := bstep (se 1 (by rfl) ⟨203639, by rfl⟩ : syracuseStep 271519 = 407279) B407279
theorem B304591 : Blo 267823 304591 := bstep (se 1 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 304591 = 456887) B456887
theorem B271823 : Blo 267823 271823 := bstep (se 1 (by rfl) ⟨203867, by rfl⟩ : syracuseStep 271823 = 407735) B407735
theorem B1025567 : Blo 267823 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B403049 : Blo 267823 403049 := bstep (se 2 (by rfl) ⟨151143, by rfl⟩ : syracuseStep 403049 = 302287) B302287
theorem B403175 : Blo 267823 403175 := bstep (se 1 (by rfl) ⟨302381, by rfl⟩ : syracuseStep 403175 = 604763) B604763
theorem B403271 : Blo 267823 403271 := bstep (se 1 (by rfl) ⟨302453, by rfl⟩ : syracuseStep 403271 = 604907) B604907
theorem B304987 : Blo 267823 304987 := bstep (se 1 (by rfl) ⟨228740, by rfl⟩ : syracuseStep 304987 = 457481) B457481
theorem B731035 : Blo 267823 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B403679 : Blo 267823 403679 := bstep (se 1 (by rfl) ⟨302759, by rfl⟩ : syracuseStep 403679 = 605519) B605519
theorem B403739 : Blo 267823 403739 := bstep (se 1 (by rfl) ⟨302804, by rfl⟩ : syracuseStep 403739 = 605609) B605609
theorem B403871 : Blo 267823 403871 := bstep (se 1 (by rfl) ⟨302903, by rfl⟩ : syracuseStep 403871 = 605807) B605807
theorem B3090959 : Blo 267823 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B404063 : Blo 267823 404063 := bstep (se 1 (by rfl) ⟨303047, by rfl⟩ : syracuseStep 404063 = 606095) B606095
theorem B764711 : Blo 267823 764711 := bstep (se 1 (by rfl) ⟨573533, by rfl⟩ : syracuseStep 764711 = 1147067) B1147067
theorem B404393 : Blo 267823 404393 := bstep (se 2 (by rfl) ⟨151647, by rfl⟩ : syracuseStep 404393 = 303295) B303295
theorem B404423 : Blo 267823 404423 := bstep (se 1 (by rfl) ⟨303317, by rfl⟩ : syracuseStep 404423 = 606635) B606635
theorem B404543 : Blo 267823 404543 := bstep (se 1 (by rfl) ⟨303407, by rfl⟩ : syracuseStep 404543 = 606815) B606815
theorem B404783 : Blo 267823 404783 := bstep (se 1 (by rfl) ⟨303587, by rfl⟩ : syracuseStep 404783 = 607175) B607175
theorem B404969 : Blo 267823 404969 := bstep (se 2 (by rfl) ⟨151863, by rfl⟩ : syracuseStep 404969 = 303727) B303727
theorem B405023 : Blo 267823 405023 := bstep (se 1 (by rfl) ⟨303767, by rfl⟩ : syracuseStep 405023 = 607535) B607535
theorem B405113 : Blo 267823 405113 := bstep (se 2 (by rfl) ⟨151917, by rfl⟩ : syracuseStep 405113 = 303835) B303835
theorem B405359 : Blo 267823 405359 := bstep (se 1 (by rfl) ⟨304019, by rfl⟩ : syracuseStep 405359 = 608039) B608039
theorem B405611 : Blo 267823 405611 := bstep (se 1 (by rfl) ⟨304208, by rfl⟩ : syracuseStep 405611 = 608417) B608417
theorem B1093895 : Blo 267823 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B406043 : Blo 267823 406043 := bstep (se 1 (by rfl) ⟨304532, by rfl⟩ : syracuseStep 406043 = 609065) B609065
theorem B406223 : Blo 267823 406223 := bstep (se 1 (by rfl) ⟨304667, by rfl⟩ : syracuseStep 406223 = 609335) B609335
theorem B602963 : Blo 267823 602963 := bstep (se 1 (by rfl) ⟨452222, by rfl⟩ : syracuseStep 602963 = 904445) B904445
theorem B865181 : Blo 267823 865181 := bstep (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) B324443
theorem B406511 : Blo 267823 406511 := bstep (se 1 (by rfl) ⟨304883, by rfl⟩ : syracuseStep 406511 = 609767) B609767
theorem B603323 : Blo 267823 603323 := bstep (se 1 (by rfl) ⟨452492, by rfl⟩ : syracuseStep 603323 = 904985) B904985
theorem B1160477 : Blo 267823 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B603449 : Blo 267823 603449 := bstep (se 2 (by rfl) ⟨226293, by rfl⟩ : syracuseStep 603449 = 452587) B452587
theorem B603503 : Blo 267823 603503 := bstep (se 1 (by rfl) ⟨452627, by rfl⟩ : syracuseStep 603503 = 905255) B905255
theorem B406895 : Blo 267823 406895 := bstep (se 1 (by rfl) ⟨305171, by rfl⟩ : syracuseStep 406895 = 610343) B610343
theorem B407015 : Blo 267823 407015 := bstep (se 1 (by rfl) ⟨305261, by rfl⟩ : syracuseStep 407015 = 610523) B610523
theorem B407195 : Blo 267823 407195 := bstep (se 1 (by rfl) ⟨305396, by rfl⟩ : syracuseStep 407195 = 610793) B610793
theorem B14005993 : Blo 267823 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B2930539 : Blo 267823 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B866207 : Blo 267823 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B604139 : Blo 267823 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B407531 : Blo 267823 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B604151 : Blo 267823 604151 := bstep (se 1 (by rfl) ⟨453113, by rfl⟩ : syracuseStep 604151 = 906227) B906227
theorem B604223 : Blo 267823 604223 := bstep (se 1 (by rfl) ⟨453167, by rfl⟩ : syracuseStep 604223 = 906335) B906335
theorem B407615 : Blo 267823 407615 := bstep (se 1 (by rfl) ⟨305711, by rfl⟩ : syracuseStep 407615 = 611423) B611423
theorem B2472059 : Blo 267823 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B1292449 : Blo 267823 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B604511 : Blo 267823 604511 := bstep (se 1 (by rfl) ⟨453383, by rfl⟩ : syracuseStep 604511 = 906767) B906767
theorem B768503 : Blo 267823 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B605051 : Blo 267823 605051 := bstep (se 1 (by rfl) ⟨453788, by rfl⟩ : syracuseStep 605051 = 907577) B907577
theorem B605231 : Blo 267823 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B1359017 : Blo 267823 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B3489139 : Blo 267823 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B1031899 : Blo 267823 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B1720061 : Blo 267823 1720061 := bstep (se 3 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 1720061 = 645023) B645023
theorem B1359827 : Blo 267823 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B2605385 : Blo 267823 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B1458695 : Blo 267823 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B3129905 : Blo 267823 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B771419 : Blo 267823 771419 := bstep (se 1 (by rfl) ⟨578564, by rfl⟩ : syracuseStep 771419 = 1157129) B1157129
theorem B575515 : Blo 267823 575515 := bstep (se 1 (by rfl) ⟨431636, by rfl⟩ : syracuseStep 575515 = 863273) B863273
theorem B346423 : Blo 267823 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B3263003 : Blo 267823 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B772649 : Blo 267823 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B772831 : Blo 267823 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B608993 : Blo 267823 608993 := bstep (se 2 (by rfl) ⟨228372, by rfl⟩ : syracuseStep 608993 = 456745) B456745
theorem B1362743 : Blo 267823 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1100627 : Blo 267823 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B1526687 : Blo 267823 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B137088385 : Blo 267823 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B611135 : Blo 267823 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B512905 : Blo 267823 512905 := bstep (se 2 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 512905 = 384679) B384679
theorem B13161365 : Blo 267823 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B906281 : Blo 267823 906281 := bstep (se 2 (by rfl) ⟨339855, by rfl⟩ : syracuseStep 906281 = 679711) B679711
theorem B1660267 : Blo 267823 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B513641 : Blo 267823 513641 := bstep (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) B385231
theorem B677929 : Blo 267823 677929 := bstep (se 2 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 677929 = 508447) B508447
theorem B2316923 : Blo 267823 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B940787 : Blo 267823 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B678719 : Blo 267823 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B1039451 : Blo 267823 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B613601 : Blo 267823 613601 := bstep (se 2 (by rfl) ⟨230100, by rfl⟩ : syracuseStep 613601 = 460201) B460201
theorem B1727851 : Blo 267823 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B679337 : Blo 267823 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B1465769 : Blo 267823 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B6544871 : Blo 267823 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B1367603 : Blo 267823 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B549055 : Blo 267823 549055 := bstep (se 1 (by rfl) ⟨411791, by rfl⟩ : syracuseStep 549055 = 823583) B823583
theorem B1368737 : Blo 267823 1368737 := bstep (se 2 (by rfl) ⟨513276, by rfl⟩ : syracuseStep 1368737 = 1026553) B1026553
theorem B2909087 : Blo 267823 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B1369223 : Blo 267823 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B1369385 : Blo 267823 1369385 := bstep (se 2 (by rfl) ⟨513519, by rfl⟩ : syracuseStep 1369385 = 1027039) B1027039
theorem B1729849 : Blo 267823 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B386473 : Blo 267823 386473 := bstep (se 2 (by rfl) ⟨144927, by rfl⟩ : syracuseStep 386473 = 289855) B289855
theorem B2942647 : Blo 267823 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B1533725 : Blo 267823 1533725 := bstep (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) B575147
theorem B1370195 : Blo 267823 1370195 := bstep (se 1 (by rfl) ⟨1027646, by rfl⟩ : syracuseStep 1370195 = 2055293) B2055293
theorem B682121 : Blo 267823 682121 := bstep (se 2 (by rfl) ⟨255795, by rfl⟩ : syracuseStep 682121 = 511591) B511591
theorem B1370681 : Blo 267823 1370681 := bstep (se 2 (by rfl) ⟨514005, by rfl⟩ : syracuseStep 1370681 = 1028011) B1028011
theorem B682739 : Blo 267823 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B683063 : Blo 267823 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B683903 : Blo 267823 683903 := bstep (se 1 (by rfl) ⟨512927, by rfl⟩ : syracuseStep 683903 = 1025855) B1025855
theorem B618473 : Blo 267823 618473 := bstep (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) B463855
theorem B1536185 : Blo 267823 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B5796029 : Blo 267823 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B684247 : Blo 267823 684247 := bstep (se 1 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 684247 = 1026371) B1026371
theorem B684359 : Blo 267823 684359 := bstep (se 1 (by rfl) ⟨513269, by rfl⟩ : syracuseStep 684359 = 1026539) B1026539
theorem B1536367 : Blo 267823 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B684521 : Blo 267823 684521 := bstep (se 2 (by rfl) ⟨256695, by rfl⟩ : syracuseStep 684521 = 513391) B513391
theorem B18641441 : Blo 267823 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B685007 : Blo 267823 685007 := bstep (se 1 (by rfl) ⟨513755, by rfl⟩ : syracuseStep 685007 = 1027511) B1027511
theorem B2061611 : Blo 267823 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B2914451 : Blo 267823 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B457015 : Blo 267823 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B3373841 : Blo 267823 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B818267 : Blo 267823 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B2293069 : Blo 267823 2293069 := bstep (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) B859901
theorem B687467 : Blo 267823 687467 := bstep (se 1 (by rfl) ⟨515600, by rfl⟩ : syracuseStep 687467 = 1031201) B1031201
theorem B687599 : Blo 267823 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B1736387 : Blo 267823 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1769161 : Blo 267823 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B458527 : Blo 267823 458527 := bstep (se 1 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 458527 = 687791) B687791
theorem B1736923 : Blo 267823 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B24970463 : Blo 267823 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B918803 : Blo 267823 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B3278177 : Blo 267823 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B1017791 : Blo 267823 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B461897 : Blo 267823 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B7343945 : Blo 267823 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B1937317 : Blo 267823 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B1544615 : Blo 267823 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B627191 : Blo 267823 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B9310727 : Blo 267823 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B2036339 : Blo 267823 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B2364191 : Blo 267823 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B4363247 : Blo 267823 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B3937319 : Blo 267823 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B1611037 : Blo 267823 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B267967 : Blo 267823 267967 := bstep (se 1 (by rfl) ⟨200975, by rfl⟩ : syracuseStep 267967 = 401951) B401951
theorem B268007 : Blo 267823 268007 := bstep (se 1 (by rfl) ⟨201005, by rfl⟩ : syracuseStep 268007 = 402011) B402011
theorem B1939391 : Blo 267823 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B268351 : Blo 267823 268351 := bstep (se 1 (by rfl) ⟨201263, by rfl⟩ : syracuseStep 268351 = 402527) B402527
theorem B268391 : Blo 267823 268391 := bstep (se 1 (by rfl) ⟨201293, by rfl⟩ : syracuseStep 268391 = 402587) B402587
theorem B268699 : Blo 267823 268699 := bstep (se 1 (by rfl) ⟨201524, by rfl⟩ : syracuseStep 268699 = 403049) B403049
theorem B268783 : Blo 267823 268783 := bstep (se 1 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 268783 = 403175) B403175
theorem B1022483 : Blo 267823 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B268847 : Blo 267823 268847 := bstep (se 1 (by rfl) ⟨201635, by rfl⟩ : syracuseStep 268847 = 403271) B403271
theorem B269119 : Blo 267823 269119 := bstep (se 1 (by rfl) ⟨201839, by rfl⟩ : syracuseStep 269119 = 403679) B403679
theorem B269159 : Blo 267823 269159 := bstep (se 1 (by rfl) ⟨201869, by rfl⟩ : syracuseStep 269159 = 403739) B403739
theorem B269247 : Blo 267823 269247 := bstep (se 1 (by rfl) ⟨201935, by rfl⟩ : syracuseStep 269247 = 403871) B403871
theorem B269375 : Blo 267823 269375 := bstep (se 1 (by rfl) ⟨202031, by rfl⟩ : syracuseStep 269375 = 404063) B404063
theorem B269595 : Blo 267823 269595 := bstep (se 1 (by rfl) ⟨202196, by rfl⟩ : syracuseStep 269595 = 404393) B404393
theorem B269615 : Blo 267823 269615 := bstep (se 1 (by rfl) ⟨202211, by rfl⟩ : syracuseStep 269615 = 404423) B404423
theorem B269695 : Blo 267823 269695 := bstep (se 1 (by rfl) ⟨202271, by rfl⟩ : syracuseStep 269695 = 404543) B404543
theorem B269855 : Blo 267823 269855 := bstep (se 1 (by rfl) ⟨202391, by rfl⟩ : syracuseStep 269855 = 404783) B404783
theorem B269979 : Blo 267823 269979 := bstep (se 1 (by rfl) ⟨202484, by rfl⟩ : syracuseStep 269979 = 404969) B404969
theorem B270015 : Blo 267823 270015 := bstep (se 1 (by rfl) ⟨202511, by rfl⟩ : syracuseStep 270015 = 405023) B405023
theorem B270075 : Blo 267823 270075 := bstep (se 1 (by rfl) ⟨202556, by rfl⟩ : syracuseStep 270075 = 405113) B405113
theorem B3907385 : Blo 267823 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B270239 : Blo 267823 270239 := bstep (se 1 (by rfl) ⟨202679, by rfl⟩ : syracuseStep 270239 = 405359) B405359
theorem B2924552213 : Blo 267823 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B270407 : Blo 267823 270407 := bstep (se 1 (by rfl) ⟨202805, by rfl⟩ : syracuseStep 270407 = 405611) B405611
theorem B1024123 : Blo 267823 1024123 := bstep (se 1 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 1024123 = 1536185) B1536185
theorem B729263 : Blo 267823 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B270695 : Blo 267823 270695 := bstep (se 1 (by rfl) ⟨203021, by rfl⟩ : syracuseStep 270695 = 406043) B406043
theorem B12427627 : Blo 267823 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B270815 : Blo 267823 270815 := bstep (se 1 (by rfl) ⟨203111, by rfl⟩ : syracuseStep 270815 = 406223) B406223
theorem B401975 : Blo 267823 401975 := bstep (se 1 (by rfl) ⟨301481, by rfl⟩ : syracuseStep 401975 = 602963) B602963
theorem B271007 : Blo 267823 271007 := bstep (se 1 (by rfl) ⟨203255, by rfl⟩ : syracuseStep 271007 = 406511) B406511
theorem B402215 : Blo 267823 402215 := bstep (se 1 (by rfl) ⟨301661, by rfl⟩ : syracuseStep 402215 = 603323) B603323
theorem B402299 : Blo 267823 402299 := bstep (se 1 (by rfl) ⟨301724, by rfl⟩ : syracuseStep 402299 = 603449) B603449
theorem B402335 : Blo 267823 402335 := bstep (se 1 (by rfl) ⟨301751, by rfl⟩ : syracuseStep 402335 = 603503) B603503
theorem B271263 : Blo 267823 271263 := bstep (se 1 (by rfl) ⟨203447, by rfl⟩ : syracuseStep 271263 = 406895) B406895
theorem B271343 : Blo 267823 271343 := bstep (se 1 (by rfl) ⟨203507, by rfl⟩ : syracuseStep 271343 = 407015) B407015
theorem B402425 : Blo 267823 402425 := bstep (se 2 (by rfl) ⟨150909, by rfl⟩ : syracuseStep 402425 = 301819) B301819
theorem B271463 : Blo 267823 271463 := bstep (se 1 (by rfl) ⟨203597, by rfl⟩ : syracuseStep 271463 = 407195) B407195
theorem B271687 : Blo 267823 271687 := bstep (se 1 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 271687 = 407531) B407531
theorem B402767 : Blo 267823 402767 := bstep (se 1 (by rfl) ⟨302075, by rfl⟩ : syracuseStep 402767 = 604151) B604151
theorem B402815 : Blo 267823 402815 := bstep (se 1 (by rfl) ⟨302111, by rfl⟩ : syracuseStep 402815 = 604223) B604223
theorem B271743 : Blo 267823 271743 := bstep (se 1 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 271743 = 407615) B407615
theorem B1648039 : Blo 267823 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B1942967 : Blo 267823 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B403007 : Blo 267823 403007 := bstep (se 1 (by rfl) ⟨302255, by rfl⟩ : syracuseStep 403007 = 604511) B604511
theorem B3057425 : Blo 267823 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B2303801 : Blo 267823 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B403367 : Blo 267823 403367 := bstep (se 1 (by rfl) ⟨302525, by rfl⟩ : syracuseStep 403367 = 605051) B605051
theorem B403487 : Blo 267823 403487 := bstep (se 1 (by rfl) ⟨302615, by rfl⟩ : syracuseStep 403487 = 605231) B605231
theorem B1157591 : Blo 267823 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B1649261 : Blo 267823 1649261 := bstep (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) B618473
theorem B1026827 : Blo 267823 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B404345 : Blo 267823 404345 := bstep (se 2 (by rfl) ⟨151629, by rfl⟩ : syracuseStep 404345 = 303259) B303259
theorem B732073 : Blo 267823 732073 := bstep (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) B549055
theorem B8728181 : Blo 267823 8728181 := bstep (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) B818267
theorem B12496913 : Blo 267823 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B1159231 : Blo 267823 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B3453137 : Blo 267823 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B2175335 : Blo 267823 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B2306465 : Blo 267823 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B405995 : Blo 267823 405995 := bstep (se 1 (by rfl) ⟨304496, by rfl⟩ : syracuseStep 405995 = 608993) B608993
theorem B2798135 : Blo 267823 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B733751 : Blo 267823 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B406121 : Blo 267823 406121 := bstep (se 2 (by rfl) ⟨152295, by rfl⟩ : syracuseStep 406121 = 304591) B304591
theorem B1160189 : Blo 267823 1160189 := bstep (se 3 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 1160189 = 435071) B435071
theorem B2307149 : Blo 267823 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B406649 : Blo 267823 406649 := bstep (se 2 (by rfl) ⟨152493, by rfl⟩ : syracuseStep 406649 = 304987) B304987
theorem B767353 : Blo 267823 767353 := bstep (se 2 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 767353 = 575515) B575515
theorem B407423 : Blo 267823 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B604187 : Blo 267823 604187 := bstep (se 1 (by rfl) ⟨453140, by rfl⟩ : syracuseStep 604187 = 906281) B906281
theorem B1030441 : Blo 267823 1030441 := bstep (se 2 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 1030441 = 772831) B772831
theorem B1358207 : Blo 267823 1358207 := bstep (se 1 (by rfl) ⟨1018655, by rfl⟩ : syracuseStep 1358207 = 2037311) B2037311
theorem B14072491 : Blo 267823 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B572123 : Blo 267823 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B409067 : Blo 267823 409067 := bstep (se 1 (by rfl) ⟨306800, by rfl⟩ : syracuseStep 409067 = 613601) B613601
theorem B2670191 : Blo 267823 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B2048489 : Blo 267823 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B2213689 : Blo 267823 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B509807 : Blo 267823 509807 := bstep (se 1 (by rfl) ⟨382355, by rfl⟩ : syracuseStep 509807 = 764711) B764711
theorem B903905 : Blo 267823 903905 := bstep (se 2 (by rfl) ⟨338964, by rfl⟩ : syracuseStep 903905 = 677929) B677929
theorem B1723265 : Blo 267823 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B2771869 : Blo 267823 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B609353 : Blo 267823 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B773651 : Blo 267823 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B970505 : Blo 267823 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B577471 : Blo 267823 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B512335 : Blo 267823 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B2249227 : Blo 267823 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B906011 : Blo 267823 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B611369 : Blo 267823 611369 := bstep (se 2 (by rfl) ⟨229263, by rfl⟩ : syracuseStep 611369 = 458527) B458527
theorem B906551 : Blo 267823 906551 := bstep (se 1 (by rfl) ⟨679913, by rfl⟩ : syracuseStep 906551 = 1359827) B1359827
theorem B579145 : Blo 267823 579145 := bstep (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) B434359
theorem B2086603 : Blo 267823 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1726211 : Blo 267823 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B514279 : Blo 267823 514279 := bstep (se 1 (by rfl) ⟨385709, by rfl⟩ : syracuseStep 514279 = 771419) B771419
theorem B3889853 : Blo 267823 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B515099 : Blo 267823 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B908495 : Blo 267823 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B515297 : Blo 267823 515297 := bstep (se 2 (by rfl) ⟨193236, by rfl⟩ : syracuseStep 515297 = 386473) B386473
theorem B8936813 : Blo 267823 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B3433043 : Blo 267823 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B8774243 : Blo 267823 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B4908221 : Blo 267823 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B1369709 : Blo 267823 1369709 := bstep (se 3 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 1369709 = 513641) B513641
theorem B452479 : Blo 267823 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B681979 : Blo 267823 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B452891 : Blo 267823 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B977179 : Blo 267823 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B911735 : Blo 267823 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B2058695 : Blo 267823 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B682951 : Blo 267823 682951 := bstep (se 1 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 682951 = 1024427) B1024427
theorem B912329 : Blo 267823 912329 := bstep (se 2 (by rfl) ⟨342123, by rfl⟩ : syracuseStep 912329 = 684247) B684247
theorem B912491 : Blo 267823 912491 := bstep (se 1 (by rfl) ⟨684368, by rfl⟩ : syracuseStep 912491 = 1368737) B1368737
theorem B912815 : Blo 267823 912815 := bstep (se 1 (by rfl) ⟨684611, by rfl⟩ : syracuseStep 912815 = 1369223) B1369223
theorem B912923 : Blo 267823 912923 := bstep (se 1 (by rfl) ⟨684692, by rfl⟩ : syracuseStep 912923 = 1369385) B1369385
theorem B683711 : Blo 267823 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B683873 : Blo 267823 683873 := bstep (se 2 (by rfl) ⟨256452, by rfl⟩ : syracuseStep 683873 = 512905) B512905
theorem B913463 : Blo 267823 913463 := bstep (se 1 (by rfl) ⟨685097, by rfl⟩ : syracuseStep 913463 = 1370195) B1370195
theorem B454747 : Blo 267823 454747 := bstep (se 1 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 454747 = 682121) B682121
theorem B3862637 : Blo 267823 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B2060639 : Blo 267823 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B913787 : Blo 267823 913787 := bstep (se 1 (by rfl) ⟨685340, by rfl⟩ : syracuseStep 913787 = 1370681) B1370681
theorem B455159 : Blo 267823 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B455375 : Blo 267823 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B18674657 : Blo 267823 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B455935 : Blo 267823 455935 := bstep (se 1 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 455935 = 683903) B683903
theorem B5076361 : Blo 267823 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B3864019 : Blo 267823 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B456239 : Blo 267823 456239 := bstep (se 1 (by rfl) ⟨342179, by rfl⟩ : syracuseStep 456239 = 684359) B684359
theorem B456347 : Blo 267823 456347 := bstep (se 1 (by rfl) ⟨342260, by rfl⟩ : syracuseStep 456347 = 684521) B684521
theorem B456671 : Blo 267823 456671 := bstep (se 1 (by rfl) ⟨342503, by rfl⟩ : syracuseStep 456671 = 685007) B685007
theorem B1374407 : Blo 267823 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B15694117 : Blo 267823 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B4652185 : Blo 267823 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B1146109 : Blo 267823 1146109 := bstep (se 3 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 1146109 = 429791) B429791
theorem B3898853 : Blo 267823 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B458311 : Blo 267823 458311 := bstep (se 1 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 458311 = 687467) B687467
theorem B2358881 : Blo 267823 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B1375865 : Blo 267823 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B458399 : Blo 267823 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B1146707 : Blo 267823 1146707 := bstep (se 1 (by rfl) ⟨860030, by rfl⟩ : syracuseStep 1146707 = 1720061) B1720061
theorem B16646975 : Blo 267823 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B2197385 : Blo 267823 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B1148843 : Blo 267823 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B2951585 : Blo 267823 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B11995877 : Blo 267823 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B1576127 : Blo 267823 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B2624879 : Blo 267823 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B5181245 : Blo 267823 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B1150807 : Blo 267823 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2593235 : Blo 267823 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B1949701475 : Blo 267823 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B1545641 : Blo 267823 1545641 := bstep (se 2 (by rfl) ⟨579615, by rfl⟩ : syracuseStep 1545641 = 1159231) B1159231
theorem B267983 : Blo 267823 267983 := bstep (se 1 (by rfl) ⟨200987, by rfl⟩ : syracuseStep 267983 = 401975) B401975
theorem B268143 : Blo 267823 268143 := bstep (se 1 (by rfl) ⟨201107, by rfl⟩ : syracuseStep 268143 = 402215) B402215
theorem B268199 : Blo 267823 268199 := bstep (se 1 (by rfl) ⟨201149, by rfl⟩ : syracuseStep 268199 = 402299) B402299
theorem B268223 : Blo 267823 268223 := bstep (se 1 (by rfl) ⟨201167, by rfl⟩ : syracuseStep 268223 = 402335) B402335
theorem B268283 : Blo 267823 268283 := bstep (se 1 (by rfl) ⟨201212, by rfl⟩ : syracuseStep 268283 = 402425) B402425
theorem B268511 : Blo 267823 268511 := bstep (se 1 (by rfl) ⟨201383, by rfl⟩ : syracuseStep 268511 = 402767) B402767
theorem B268543 : Blo 267823 268543 := bstep (se 1 (by rfl) ⟨201407, by rfl⟩ : syracuseStep 268543 = 402815) B402815
theorem B268671 : Blo 267823 268671 := bstep (se 1 (by rfl) ⟨201503, by rfl⟩ : syracuseStep 268671 = 403007) B403007
theorem B2038283 : Blo 267823 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B268911 : Blo 267823 268911 := bstep (se 1 (by rfl) ⟨201683, by rfl⟩ : syracuseStep 268911 = 403367) B403367
theorem B268991 : Blo 267823 268991 := bstep (se 1 (by rfl) ⟨201743, by rfl⟩ : syracuseStep 268991 = 403487) B403487
theorem B301927 : Blo 267823 301927 := bstep (se 1 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 301927 = 452891) B452891
theorem B1023137 : Blo 267823 1023137 := bstep (se 2 (by rfl) ⟨383676, by rfl⟩ : syracuseStep 1023137 = 767353) B767353
theorem B269563 : Blo 267823 269563 := bstep (se 1 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 269563 = 404345) B404345
theorem B5152025 : Blo 267823 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B8331275 : Blo 267823 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B2302091 : Blo 267823 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B1450223 : Blo 267823 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B270663 : Blo 267823 270663 := bstep (se 1 (by rfl) ⟨202997, by rfl⟩ : syracuseStep 270663 = 405995) B405995
theorem B303439 : Blo 267823 303439 := bstep (se 1 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 303439 = 455159) B455159
theorem B270747 : Blo 267823 270747 := bstep (se 1 (by rfl) ⟨203060, by rfl⟩ : syracuseStep 270747 = 406121) B406121
theorem B303583 : Blo 267823 303583 := bstep (se 1 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 303583 = 455375) B455375
theorem B271099 : Blo 267823 271099 := bstep (se 1 (by rfl) ⟨203324, by rfl⟩ : syracuseStep 271099 = 406649) B406649
theorem B304159 : Blo 267823 304159 := bstep (se 1 (by rfl) ⟨228119, by rfl⟩ : syracuseStep 304159 = 456239) B456239
theorem B304231 : Blo 267823 304231 := bstep (se 1 (by rfl) ⟨228173, by rfl⟩ : syracuseStep 304231 = 456347) B456347
theorem B271615 : Blo 267823 271615 := bstep (se 1 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 271615 = 407423) B407423
theorem B304447 : Blo 267823 304447 := bstep (se 1 (by rfl) ⟨228335, by rfl⟩ : syracuseStep 304447 = 456671) B456671
theorem B402791 : Blo 267823 402791 := bstep (se 1 (by rfl) ⟨302093, by rfl⟩ : syracuseStep 402791 = 604187) B604187
theorem B6202913 : Blo 267823 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B2599235 : Blo 267823 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B272711 : Blo 267823 272711 := bstep (se 1 (by rfl) ⟨204533, by rfl⟩ : syracuseStep 272711 = 409067) B409067
theorem B1780127 : Blo 267823 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B305599 : Blo 267823 305599 := bstep (se 1 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 305599 = 458399) B458399
theorem B764471 : Blo 267823 764471 := bstep (se 1 (by rfl) ⟨573353, by rfl⟩ : syracuseStep 764471 = 1146707) B1146707
theorem B4926901 : Blo 267823 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B339871 : Blo 267823 339871 := bstep (se 1 (by rfl) ⟨254903, by rfl⟩ : syracuseStep 339871 = 509807) B509807
theorem B83701957 : Blo 267823 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B602603 : Blo 267823 602603 := bstep (se 1 (by rfl) ⟨451952, by rfl⟩ : syracuseStep 602603 = 903905) B903905
theorem B406235 : Blo 267823 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B603305 : Blo 267823 603305 := bstep (se 2 (by rfl) ⟨226239, by rfl⟩ : syracuseStep 603305 = 452479) B452479
theorem B4895963 : Blo 267823 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B1029743 : Blo 267823 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B6207151 : Blo 267823 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B1357559 : Blo 267823 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B604007 : Blo 267823 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B407579 : Blo 267823 407579 := bstep (se 1 (by rfl) ⟨305684, by rfl⟩ : syracuseStep 407579 = 611369) B611369
theorem B604367 : Blo 267823 604367 := bstep (se 1 (by rfl) ⟨453275, by rfl⟩ : syracuseStep 604367 = 906551) B906551
theorem B1292927 : Blo 267823 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B605663 : Blo 267823 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B343531 : Blo 267823 343531 := bstep (se 1 (by rfl) ⟨257648, by rfl⟩ : syracuseStep 343531 = 515297) B515297
theorem B2604923 : Blo 267823 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B769961 : Blo 267823 769961 := bstep (se 2 (by rfl) ⟨288735, by rfl⟩ : syracuseStep 769961 = 577471) B577471
theorem B606329 : Blo 267823 606329 := bstep (se 2 (by rfl) ⟨227373, by rfl⟩ : syracuseStep 606329 = 454747) B454747
theorem B5849495 : Blo 267823 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B607823 : Blo 267823 607823 := bstep (se 1 (by rfl) ⟨455867, by rfl⟩ : syracuseStep 607823 = 911735) B911735
theorem B771727 : Blo 267823 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B607913 : Blo 267823 607913 := bstep (se 2 (by rfl) ⟨227967, by rfl⟩ : syracuseStep 607913 = 455935) B455935
theorem B2148049 : Blo 267823 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1099507 : Blo 267823 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B6768481 : Blo 267823 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B1525661 : Blo 267823 1525661 := bstep (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) B572123
theorem B608219 : Blo 267823 608219 := bstep (se 1 (by rfl) ⟨456164, by rfl⟩ : syracuseStep 608219 = 912329) B912329
theorem B608327 : Blo 267823 608327 := bstep (se 1 (by rfl) ⟨456245, by rfl⟩ : syracuseStep 608327 = 912491) B912491
theorem B772193 : Blo 267823 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B608543 : Blo 267823 608543 := bstep (se 1 (by rfl) ⟨456407, by rfl⟩ : syracuseStep 608543 = 912815) B912815
theorem B608615 : Blo 267823 608615 := bstep (se 1 (by rfl) ⟨456461, by rfl⟩ : syracuseStep 608615 = 912923) B912923
theorem B5818787 : Blo 267823 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B608975 : Blo 267823 608975 := bstep (se 1 (by rfl) ⟨456731, by rfl⟩ : syracuseStep 608975 = 913463) B913463
theorem B2575091 : Blo 267823 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B609191 : Blo 267823 609191 := bstep (se 1 (by rfl) ⟨456893, by rfl⟩ : syracuseStep 609191 = 913787) B913787
theorem B773459 : Blo 267823 773459 := bstep (se 1 (by rfl) ⟨580094, by rfl⟩ : syracuseStep 773459 = 1160189) B1160189
theorem B18763321 : Blo 267823 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B11128549 : Blo 267823 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B905471 : Blo 267823 905471 := bstep (se 1 (by rfl) ⟨679103, by rfl⟩ : syracuseStep 905471 = 1358207) B1358207
theorem B1528145 : Blo 267823 1528145 := bstep (se 2 (by rfl) ⟨573054, by rfl⟩ : syracuseStep 1528145 = 1146109) B1146109
theorem B611081 : Blo 267823 611081 := bstep (se 2 (by rfl) ⟨229155, by rfl⟩ : syracuseStep 611081 = 458311) B458311
theorem B1365497 : Blo 267823 1365497 := bstep (se 2 (by rfl) ⟨512061, by rfl⟩ : syracuseStep 1365497 = 1024123) B1024123
theorem B2315897 : Blo 267823 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B1365659 : Blo 267823 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B16570169 : Blo 267823 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B612535 : Blo 267823 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B2185451 : Blo 267823 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B678527 : Blo 267823 678527 := bstep (se 1 (by rfl) ⟨508895, by rfl⟩ : syracuseStep 678527 = 1017791) B1017791
theorem B647003 : Blo 267823 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B909305 : Blo 267823 909305 := bstep (se 2 (by rfl) ⟨340989, by rfl⟩ : syracuseStep 909305 = 681979) B681979
theorem B418127 : Blo 267823 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B1302905 : Blo 267823 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B2908831 : Blo 267823 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B3695825 : Blo 267823 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B976097 : Blo 267823 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B910601 : Blo 267823 910601 := bstep (se 2 (by rfl) ⟨341475, by rfl⟩ : syracuseStep 910601 = 682951) B682951
theorem B681655 : Blo 267823 681655 := bstep (se 1 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 681655 = 1022483) B1022483
theorem B5957875 : Blo 267823 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B2583089 : Blo 267823 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B486175 : Blo 267823 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B2288695 : Blo 267823 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B683113 : Blo 267823 683113 := bstep (se 2 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 683113 = 512335) B512335
theorem B3272147 : Blo 267823 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B913139 : Blo 267823 913139 := bstep (se 1 (by rfl) ⟨684854, by rfl⟩ : syracuseStep 913139 = 1369709) B1369709
theorem B1535867 : Blo 267823 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B1372463 : Blo 267823 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B684551 : Blo 267823 684551 := bstep (se 1 (by rfl) ⟨513413, by rfl⟩ : syracuseStep 684551 = 1026827) B1026827
theorem B455807 : Blo 267823 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B455915 : Blo 267823 455915 := bstep (se 1 (by rfl) ⟨341936, by rfl⟩ : syracuseStep 455915 = 683873) B683873
theorem B1373597 : Blo 267823 1373597 := bstep (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) B515099
theorem B1373759 : Blo 267823 1373759 := bstep (se 1 (by rfl) ⟨1030319, by rfl⟩ : syracuseStep 1373759 = 2060639) B2060639
theorem B1537643 : Blo 267823 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B685705 : Blo 267823 685705 := bstep (se 2 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 685705 = 514279) B514279
theorem B1865423 : Blo 267823 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B489167 : Blo 267823 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B1373921 : Blo 267823 1373921 := bstep (se 2 (by rfl) ⟨515220, by rfl⟩ : syracuseStep 1373921 = 1030441) B1030441
theorem B12449771 : Blo 267823 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1538099 : Blo 267823 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B2063069 : Blo 267823 2063069 := bstep (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) B773651
theorem B916271 : Blo 267823 916271 := bstep (se 1 (by rfl) ⟨687203, by rfl⟩ : syracuseStep 916271 = 1374407) B1374407
theorem B1572587 : Blo 267823 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B917243 : Blo 267823 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B3899663 : Blo 267823 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B1115005 : Blo 267823 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B3474413 : Blo 267823 3474413 := bstep (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) B1302905
theorem B6915293 : Blo 267823 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B1017107 : Blo 267823 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B1967723 : Blo 267823 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B7997251 : Blo 267823 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B1050751 : Blo 267823 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B1018763 : Blo 267823 1018763 := bstep (se 1 (by rfl) ⟨764072, by rfl⟩ : syracuseStep 1018763 = 1528145) B1528145
theorem B5199203933 : Blo 267823 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B1543931 : Blo 267823 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B11046779 : Blo 267823 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B3051593 : Blo 267823 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B431335 : Blo 267823 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B727229 : Blo 267823 727229 := bstep (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) B272711
theorem B268527 : Blo 267823 268527 := bstep (se 1 (by rfl) ⟨201395, by rfl⟩ : syracuseStep 268527 = 402791) B402791
theorem B1186751 : Blo 267823 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B3447805 : Blo 267823 3447805 := bstep (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) B1292927
theorem B1023911 : Blo 267823 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B401735 : Blo 267823 401735 := bstep (se 1 (by rfl) ⟨301301, by rfl⟩ : syracuseStep 401735 = 602603) B602603
theorem B270823 : Blo 267823 270823 := bstep (se 1 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 270823 = 406235) B406235
theorem B303871 : Blo 267823 303871 := bstep (se 1 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 303871 = 455807) B455807
theorem B402203 : Blo 267823 402203 := bstep (se 1 (by rfl) ⟨301652, by rfl⟩ : syracuseStep 402203 = 603305) B603305
theorem B303943 : Blo 267823 303943 := bstep (se 1 (by rfl) ⟨227957, by rfl⟩ : syracuseStep 303943 = 455915) B455915
theorem B1025095 : Blo 267823 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B402569 : Blo 267823 402569 := bstep (se 2 (by rfl) ⟨150963, by rfl⟩ : syracuseStep 402569 = 301927) B301927
theorem B402671 : Blo 267823 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B8299847 : Blo 267823 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B271719 : Blo 267823 271719 := bstep (se 1 (by rfl) ⟨203789, by rfl⟩ : syracuseStep 271719 = 407579) B407579
theorem B1025399 : Blo 267823 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B402911 : Blo 267823 402911 := bstep (se 1 (by rfl) ⟨302183, by rfl⟩ : syracuseStep 402911 = 604367) B604367
theorem B403775 : Blo 267823 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B404219 : Blo 267823 404219 := bstep (se 1 (by rfl) ⟨303164, by rfl⟩ : syracuseStep 404219 = 606329) B606329
theorem B404585 : Blo 267823 404585 := bstep (se 2 (by rfl) ⟨151719, by rfl⟩ : syracuseStep 404585 = 303439) B303439
theorem B404777 : Blo 267823 404777 := bstep (se 2 (by rfl) ⟨151791, by rfl⟩ : syracuseStep 404777 = 303583) B303583
theorem B3878441 : Blo 267823 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B405215 : Blo 267823 405215 := bstep (se 1 (by rfl) ⟨303911, by rfl⟩ : syracuseStep 405215 = 607823) B607823
theorem B405275 : Blo 267823 405275 := bstep (se 1 (by rfl) ⟨303956, by rfl⟩ : syracuseStep 405275 = 607913) B607913
theorem B765895 : Blo 267823 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B405479 : Blo 267823 405479 := bstep (se 1 (by rfl) ⟨304109, by rfl⟩ : syracuseStep 405479 = 608219) B608219
theorem B405545 : Blo 267823 405545 := bstep (se 2 (by rfl) ⟨152079, by rfl⟩ : syracuseStep 405545 = 304159) B304159
theorem B405551 : Blo 267823 405551 := bstep (se 1 (by rfl) ⟨304163, by rfl⟩ : syracuseStep 405551 = 608327) B608327
theorem B405641 : Blo 267823 405641 := bstep (se 2 (by rfl) ⟨152115, by rfl⟩ : syracuseStep 405641 = 304231) B304231
theorem B405695 : Blo 267823 405695 := bstep (se 1 (by rfl) ⟨304271, by rfl⟩ : syracuseStep 405695 = 608543) B608543
theorem B405743 : Blo 267823 405743 := bstep (se 1 (by rfl) ⟨304307, by rfl⟩ : syracuseStep 405743 = 608615) B608615
theorem B3879191 : Blo 267823 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B405929 : Blo 267823 405929 := bstep (se 2 (by rfl) ⟨152223, by rfl⟩ : syracuseStep 405929 = 304447) B304447
theorem B405983 : Blo 267823 405983 := bstep (se 1 (by rfl) ⟨304487, by rfl⟩ : syracuseStep 405983 = 608975) B608975
theorem B1716727 : Blo 267823 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B406127 : Blo 267823 406127 := bstep (se 1 (by rfl) ⟨304595, by rfl⟩ : syracuseStep 406127 = 609191) B609191
theorem B1028969 : Blo 267823 1028969 := bstep (se 2 (by rfl) ⟨385863, by rfl⟩ : syracuseStep 1028969 = 771727) B771727
theorem B1749919 : Blo 267823 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B2864065 : Blo 267823 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B9024641 : Blo 267823 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B3454163 : Blo 267823 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B603647 : Blo 267823 603647 := bstep (se 1 (by rfl) ⟨452735, by rfl⟩ : syracuseStep 603647 = 905471) B905471
theorem B407387 : Blo 267823 407387 := bstep (se 1 (by rfl) ⟨305540, by rfl⟩ : syracuseStep 407387 = 611081) B611081
theorem B407465 : Blo 267823 407465 := bstep (se 2 (by rfl) ⟨152799, by rfl⟩ : syracuseStep 407465 = 305599) B305599
theorem B2602925 : Blo 267823 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B1030427 : Blo 267823 1030427 := bstep (se 1 (by rfl) ⟨772820, by rfl⟩ : syracuseStep 1030427 = 1545641) B1545641
theorem B1456967 : Blo 267823 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1358855 : Blo 267823 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B6569201 : Blo 267823 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B25017761 : Blo 267823 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B606203 : Blo 267823 606203 := bstep (se 1 (by rfl) ⟨454652, by rfl⟩ : syracuseStep 606203 = 909305) B909305
theorem B5554183 : Blo 267823 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B966815 : Blo 267823 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B607067 : Blo 267823 607067 := bstep (se 1 (by rfl) ⟨455300, by rfl⟩ : syracuseStep 607067 = 910601) B910601
theorem B1722059 : Blo 267823 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B509647 : Blo 267823 509647 := bstep (se 1 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 509647 = 764471) B764471
theorem B8276201 : Blo 267823 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B2181431 : Blo 267823 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B608759 : Blo 267823 608759 := bstep (se 1 (by rfl) ⟨456569, by rfl⟩ : syracuseStep 608759 = 913139) B913139
theorem B3263975 : Blo 267823 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B905039 : Blo 267823 905039 := bstep (se 1 (by rfl) ⟨678779, by rfl⟩ : syracuseStep 905039 = 1357559) B1357559
theorem B610847 : Blo 267823 610847 := bstep (se 1 (by rfl) ⟨458135, by rfl⟩ : syracuseStep 610847 = 916271) B916271
theorem B611495 : Blo 267823 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B513307 : Blo 267823 513307 := bstep (se 1 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 513307 = 769961) B769961
theorem B11097983 : Blo 267823 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B1464923 : Blo 267823 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B31775333 : Blo 267823 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B515639 : Blo 267823 515639 := bstep (se 1 (by rfl) ⟨386729, by rfl⟩ : syracuseStep 515639 = 773459) B773459
theorem B908873 : Blo 267823 908873 := bstep (se 2 (by rfl) ⟨340827, by rfl⟩ : syracuseStep 908873 = 681655) B681655
theorem B1466009 : Blo 267823 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B9855533 : Blo 267823 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B910331 : Blo 267823 910331 := bstep (se 1 (by rfl) ⟨682748, by rfl⟩ : syracuseStep 910331 = 1365497) B1365497
theorem B648233 : Blo 267823 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B910439 : Blo 267823 910439 := bstep (se 1 (by rfl) ⟨682829, by rfl⟩ : syracuseStep 910439 = 1365659) B1365659
theorem B16541101 : Blo 267823 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B910817 : Blo 267823 910817 := bstep (se 2 (by rfl) ⟨341556, by rfl⟩ : syracuseStep 910817 = 683113) B683113
theorem B452351 : Blo 267823 452351 := bstep (se 1 (by rfl) ⟨339263, by rfl⟩ : syracuseStep 452351 = 678527) B678527
theorem B682091 : Blo 267823 682091 := bstep (se 1 (by rfl) ⟨511568, by rfl⟩ : syracuseStep 682091 = 1023137) B1023137
theorem B3434683 : Blo 267823 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B14838065 : Blo 267823 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B1534409 : Blo 267823 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B453161 : Blo 267823 453161 := bstep (se 2 (by rfl) ⟨169935, by rfl⟩ : syracuseStep 453161 = 339871) B339871
theorem B1534727 : Blo 267823 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B2059181 : Blo 267823 2059181 := bstep (se 3 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 2059181 = 772193) B772193
theorem B111602609 : Blo 267823 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B1732823 : Blo 267823 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B914273 : Blo 267823 914273 := bstep (se 2 (by rfl) ⟨342852, by rfl⟩ : syracuseStep 914273 = 685705) B685705
theorem B914975 : Blo 267823 914975 := bstep (se 1 (by rfl) ⟨686231, by rfl⟩ : syracuseStep 914975 = 1372463) B1372463
theorem B816713 : Blo 267823 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B456367 : Blo 267823 456367 := bstep (se 1 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 456367 = 684551) B684551
theorem B915731 : Blo 267823 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B915839 : Blo 267823 915839 := bstep (se 1 (by rfl) ⟨686879, by rfl⟩ : syracuseStep 915839 = 1373759) B1373759
theorem B686495 : Blo 267823 686495 := bstep (se 1 (by rfl) ⟨514871, by rfl⟩ : syracuseStep 686495 = 1029743) B1029743
theorem B1243615 : Blo 267823 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B326111 : Blo 267823 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B915947 : Blo 267823 915947 := bstep (se 1 (by rfl) ⟨686960, by rfl⟩ : syracuseStep 915947 = 1373921) B1373921
theorem B1375379 : Blo 267823 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B458041 : Blo 267823 458041 := bstep (se 2 (by rfl) ⟨171765, by rfl⟩ : syracuseStep 458041 = 343531) B343531
theorem B1048391 : Blo 267823 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B1736615 : Blo 267823 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B7405577 : Blo 267823 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B1311815 : Blo 267823 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1148039 : Blo 267823 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B26281421 : Blo 267823 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B22054801 : Blo 267823 22054801 := bstep (se 2 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 22054801 = 16541101) B16541101
theorem B3466135955 : Blo 267823 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B2034395 : Blo 267823 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B791167 : Blo 267823 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B29594621 : Blo 267823 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1021193 : Blo 267823 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B267823 : Blo 267823 267823 := bstep (se 1 (by rfl) ⟨200867, by rfl⟩ : syracuseStep 267823 = 401735) B401735
theorem B1939277 : Blo 267823 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B268135 : Blo 267823 268135 := bstep (se 1 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 268135 = 402203) B402203
theorem B432155 : Blo 267823 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B268379 : Blo 267823 268379 := bstep (se 1 (by rfl) ⟨201284, by rfl⟩ : syracuseStep 268379 = 402569) B402569
theorem B268447 : Blo 267823 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B268607 : Blo 267823 268607 := bstep (se 1 (by rfl) ⟨201455, by rfl⟩ : syracuseStep 268607 = 402911) B402911
theorem B301567 : Blo 267823 301567 := bstep (se 1 (by rfl) ⟨226175, by rfl⟩ : syracuseStep 301567 = 452351) B452351
theorem B2333225 : Blo 267823 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B269183 : Blo 267823 269183 := bstep (se 1 (by rfl) ⟨201887, by rfl⟩ : syracuseStep 269183 = 403775) B403775
theorem B3906461 : Blo 267823 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B1022939 : Blo 267823 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B302107 : Blo 267823 302107 := bstep (se 1 (by rfl) ⟨226580, by rfl⟩ : syracuseStep 302107 = 453161) B453161
theorem B269479 : Blo 267823 269479 := bstep (se 1 (by rfl) ⟨202109, by rfl⟩ : syracuseStep 269479 = 404219) B404219
theorem B1023151 : Blo 267823 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B269723 : Blo 267823 269723 := bstep (se 1 (by rfl) ⟨202292, by rfl⟩ : syracuseStep 269723 = 404585) B404585
theorem B269851 : Blo 267823 269851 := bstep (se 1 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 269851 = 404777) B404777
theorem B270143 : Blo 267823 270143 := bstep (se 1 (by rfl) ⟨202607, by rfl⟩ : syracuseStep 270143 = 405215) B405215
theorem B270183 : Blo 267823 270183 := bstep (se 1 (by rfl) ⟨202637, by rfl⟩ : syracuseStep 270183 = 405275) B405275
theorem B270319 : Blo 267823 270319 := bstep (se 1 (by rfl) ⟨202739, by rfl⟩ : syracuseStep 270319 = 405479) B405479
theorem B270363 : Blo 267823 270363 := bstep (se 1 (by rfl) ⟨202772, by rfl⟩ : syracuseStep 270363 = 405545) B405545
theorem B270367 : Blo 267823 270367 := bstep (se 1 (by rfl) ⟨202775, by rfl⟩ : syracuseStep 270367 = 405551) B405551
theorem B270427 : Blo 267823 270427 := bstep (se 1 (by rfl) ⟨202820, by rfl⟩ : syracuseStep 270427 = 405641) B405641
theorem B270463 : Blo 267823 270463 := bstep (se 1 (by rfl) ⟨202847, by rfl⟩ : syracuseStep 270463 = 405695) B405695
theorem B1155215 : Blo 267823 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B270495 : Blo 267823 270495 := bstep (se 1 (by rfl) ⟨202871, by rfl⟩ : syracuseStep 270495 = 405743) B405743
theorem B270619 : Blo 267823 270619 := bstep (se 1 (by rfl) ⟨202964, by rfl⟩ : syracuseStep 270619 = 405929) B405929
theorem B270655 : Blo 267823 270655 := bstep (se 1 (by rfl) ⟨202991, by rfl⟩ : syracuseStep 270655 = 405983) B405983
theorem B270751 : Blo 267823 270751 := bstep (se 1 (by rfl) ⟨203063, by rfl⟩ : syracuseStep 270751 = 406127) B406127
theorem B2302775 : Blo 267823 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B402431 : Blo 267823 402431 := bstep (se 1 (by rfl) ⟨301823, by rfl⟩ : syracuseStep 402431 = 603647) B603647
theorem B271591 : Blo 267823 271591 := bstep (se 1 (by rfl) ⟨203693, by rfl⟩ : syracuseStep 271591 = 407387) B407387
theorem B271643 : Blo 267823 271643 := bstep (se 1 (by rfl) ⟨203732, by rfl⟩ : syracuseStep 271643 = 407465) B407465
theorem B4597073 : Blo 267823 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B698927 : Blo 267823 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B1157743 : Blo 267823 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B404135 : Blo 267823 404135 := bstep (se 1 (by rfl) ⟨303101, by rfl⟩ : syracuseStep 404135 = 606203) B606203
theorem B2599775 : Blo 267823 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B404711 : Blo 267823 404711 := bstep (se 1 (by rfl) ⟨303533, by rfl⟩ : syracuseStep 404711 = 607067) B607067
theorem B405161 : Blo 267823 405161 := bstep (se 2 (by rfl) ⟨151935, by rfl⟩ : syracuseStep 405161 = 303871) B303871
theorem B405257 : Blo 267823 405257 := bstep (se 2 (by rfl) ⟨151971, by rfl⟩ : syracuseStep 405257 = 303943) B303943
theorem B1486673 : Blo 267823 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B5517467 : Blo 267823 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B1454287 : Blo 267823 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B405839 : Blo 267823 405839 := bstep (se 1 (by rfl) ⟨304379, by rfl⟩ : syracuseStep 405839 = 608759) B608759
theorem B2175983 : Blo 267823 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B10663001 : Blo 267823 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B1029287 : Blo 267823 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B603359 : Blo 267823 603359 := bstep (se 1 (by rfl) ⟨452519, by rfl⟩ : syracuseStep 603359 = 905039) B905039
theorem B407231 : Blo 267823 407231 := bstep (se 1 (by rfl) ⟨305423, by rfl⟩ : syracuseStep 407231 = 610847) B610847
theorem B407663 : Blo 267823 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B343759 : Blo 267823 343759 := bstep (se 1 (by rfl) ⟨257819, by rfl⟩ : syracuseStep 343759 = 515639) B515639
theorem B605915 : Blo 267823 605915 := bstep (se 1 (by rfl) ⟨454436, by rfl⟩ : syracuseStep 605915 = 908873) B908873
theorem B606887 : Blo 267823 606887 := bstep (se 1 (by rfl) ⟨455165, by rfl⟩ : syracuseStep 606887 = 910331) B910331
theorem B606959 : Blo 267823 606959 := bstep (se 1 (by rfl) ⟨455219, by rfl⟩ : syracuseStep 606959 = 910439) B910439
theorem B607211 : Blo 267823 607211 := bstep (se 1 (by rfl) ⟨455408, by rfl⟩ : syracuseStep 607211 = 910817) B910817
theorem B338936885 : Blo 267823 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B869629 : Blo 267823 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B3818753 : Blo 267823 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B575113 : Blo 267823 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B74401739 : Blo 267823 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B608489 : Blo 267823 608489 := bstep (se 2 (by rfl) ⟨228183, by rfl⟩ : syracuseStep 608489 = 456367) B456367
theorem B609515 : Blo 267823 609515 := bstep (se 1 (by rfl) ⟨457136, by rfl⟩ : syracuseStep 609515 = 914273) B914273
theorem B1658153 : Blo 267823 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B6016427 : Blo 267823 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B609983 : Blo 267823 609983 := bstep (se 1 (by rfl) ⟨457487, by rfl⟩ : syracuseStep 609983 = 914975) B914975
theorem B544475 : Blo 267823 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B610487 : Blo 267823 610487 := bstep (se 1 (by rfl) ⟨457865, by rfl⟩ : syracuseStep 610487 = 915731) B915731
theorem B610559 : Blo 267823 610559 := bstep (se 1 (by rfl) ⟨457919, by rfl⟩ : syracuseStep 610559 = 915839) B915839
theorem B610631 : Blo 267823 610631 := bstep (se 1 (by rfl) ⟨457973, by rfl⟩ : syracuseStep 610631 = 915947) B915947
theorem B610721 : Blo 267823 610721 := bstep (se 2 (by rfl) ⟨229020, by rfl⟩ : syracuseStep 610721 = 458041) B458041
theorem B971311 : Blo 267823 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B905903 : Blo 267823 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B4379467 : Blo 267823 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B644543 : Blo 267823 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B2316275 : Blo 267823 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B4610195 : Blo 267823 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B678071 : Blo 267823 678071 := bstep (se 1 (by rfl) ⟨508553, by rfl⟩ : syracuseStep 678071 = 1017107) B1017107
theorem B1366793 : Blo 267823 1366793 := bstep (se 2 (by rfl) ⟨512547, by rfl⟩ : syracuseStep 1366793 = 1025095) B1025095
theorem B679175 : Blo 267823 679175 := bstep (se 1 (by rfl) ⟨509381, by rfl⟩ : syracuseStep 679175 = 1018763) B1018763
theorem B679529 : Blo 267823 679529 := bstep (se 2 (by rfl) ⟨254823, by rfl⟩ : syracuseStep 679529 = 509647) B509647
theorem B7364519 : Blo 267823 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1401001 : Blo 267823 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B4579577 : Blo 267823 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B977339 : Blo 267823 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B682607 : Blo 267823 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B2288969 : Blo 267823 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B5533231 : Blo 267823 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B683599 : Blo 267823 683599 := bstep (se 1 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 683599 = 1025399) B1025399
theorem B454727 : Blo 267823 454727 := bstep (se 1 (by rfl) ⟨341045, by rfl⟩ : syracuseStep 454727 = 682091) B682091
theorem B9892043 : Blo 267823 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B684409 : Blo 267823 684409 := bstep (se 2 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 684409 = 513307) B513307
theorem B1372787 : Blo 267823 1372787 := bstep (se 1 (by rfl) ⟨1029590, by rfl⟩ : syracuseStep 1372787 = 2059181) B2059181
theorem B2585627 : Blo 267823 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B2586127 : Blo 267823 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B685979 : Blo 267823 685979 := bstep (se 1 (by rfl) ⟨514484, by rfl⟩ : syracuseStep 685979 = 1028969) B1028969
theorem B1735283 : Blo 267823 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B686951 : Blo 267823 686951 := bstep (se 1 (by rfl) ⟨515213, by rfl⟩ : syracuseStep 686951 = 1030427) B1030427
theorem B457663 : Blo 267823 457663 := bstep (se 1 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 457663 = 686495) B686495
theorem B916919 : Blo 267823 916919 := bstep (se 1 (by rfl) ⟨687689, by rfl⟩ : syracuseStep 916919 = 1375379) B1375379
theorem B16678507 : Blo 267823 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B362983 : Blo 267823 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B19729747 : Blo 267823 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B1543657 : Blo 267823 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B29888021 : Blo 267823 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B429695 : Blo 267823 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B1544183 : Blo 267823 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B7377641 : Blo 267823 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B1152413 : Blo 267823 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B3053051 : Blo 267823 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B1939049 : Blo 267823 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B268287 : Blo 267823 268287 := bstep (se 1 (by rfl) ⟨201215, by rfl⟩ : syracuseStep 268287 = 402431) B402431
theorem B1054889 : Blo 267823 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B5839289 : Blo 267823 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B269423 : Blo 267823 269423 := bstep (se 1 (by rfl) ⟨202067, by rfl⟩ : syracuseStep 269423 = 404135) B404135
theorem B3448169 : Blo 267823 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B269807 : Blo 267823 269807 := bstep (se 1 (by rfl) ⟨202355, by rfl⟩ : syracuseStep 269807 = 404711) B404711
theorem B270107 : Blo 267823 270107 := bstep (se 1 (by rfl) ⟨202580, by rfl⟩ : syracuseStep 270107 = 405161) B405161
theorem B270171 : Blo 267823 270171 := bstep (se 1 (by rfl) ⟨202628, by rfl⟩ : syracuseStep 270171 = 405257) B405257
theorem B991115 : Blo 267823 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B303151 : Blo 267823 303151 := bstep (se 1 (by rfl) ⟨227363, by rfl⟩ : syracuseStep 303151 = 454727) B454727
theorem B3678311 : Blo 267823 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B6594695 : Blo 267823 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B270559 : Blo 267823 270559 := bstep (se 1 (by rfl) ⟨202919, by rfl⟩ : syracuseStep 270559 = 405839) B405839
theorem B1450655 : Blo 267823 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B402089 : Blo 267823 402089 := bstep (se 2 (by rfl) ⟨150783, by rfl⟩ : syracuseStep 402089 = 301567) B301567
theorem B402239 : Blo 267823 402239 := bstep (se 1 (by rfl) ⟨301679, by rfl⟩ : syracuseStep 402239 = 603359) B603359
theorem B271487 : Blo 267823 271487 := bstep (se 1 (by rfl) ⟨203615, by rfl⟩ : syracuseStep 271487 = 407231) B407231
theorem B402809 : Blo 267823 402809 := bstep (se 2 (by rfl) ⟨151053, by rfl⟩ : syracuseStep 402809 = 302107) B302107
theorem B271775 : Blo 267823 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B1156855 : Blo 267823 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B403943 : Blo 267823 403943 := bstep (se 1 (by rfl) ⟨302957, by rfl⟩ : syracuseStep 403943 = 605915) B605915
theorem B404591 : Blo 267823 404591 := bstep (se 1 (by rfl) ⟨303443, by rfl⟩ : syracuseStep 404591 = 606887) B606887
theorem B404639 : Blo 267823 404639 := bstep (se 1 (by rfl) ⟨303479, by rfl⟩ : syracuseStep 404639 = 606959) B606959
theorem B404807 : Blo 267823 404807 := bstep (se 1 (by rfl) ⟨303605, by rfl⟩ : syracuseStep 404807 = 607211) B607211
theorem B765359 : Blo 267823 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B405659 : Blo 267823 405659 := bstep (se 1 (by rfl) ⟨304244, by rfl⟩ : syracuseStep 405659 = 608489) B608489
theorem B1159505 : Blo 267823 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B1356263 : Blo 267823 1356263 := bstep (se 1 (by rfl) ⟨1017197, by rfl⟩ : syracuseStep 1356263 = 2034395) B2034395
theorem B406343 : Blo 267823 406343 := bstep (se 1 (by rfl) ⟨304757, by rfl⟩ : syracuseStep 406343 = 609515) B609515
theorem B766817 : Blo 267823 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B4010951 : Blo 267823 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B406655 : Blo 267823 406655 := bstep (se 1 (by rfl) ⟨304991, by rfl⟩ : syracuseStep 406655 = 609983) B609983
theorem B29406401 : Blo 267823 29406401 := bstep (se 2 (by rfl) ⟨11027400, by rfl⟩ : syracuseStep 29406401 = 22054801) B22054801
theorem B406991 : Blo 267823 406991 := bstep (se 1 (by rfl) ⟨305243, by rfl⟩ : syracuseStep 406991 = 610487) B610487
theorem B407039 : Blo 267823 407039 := bstep (se 1 (by rfl) ⟨305279, by rfl⟩ : syracuseStep 407039 = 610559) B610559
theorem B407087 : Blo 267823 407087 := bstep (se 1 (by rfl) ⟨305315, by rfl⟩ : syracuseStep 407087 = 610631) B610631
theorem B407147 : Blo 267823 407147 := bstep (se 1 (by rfl) ⟨305360, by rfl⟩ : syracuseStep 407147 = 610721) B610721
theorem B603935 : Blo 267823 603935 := bstep (se 1 (by rfl) ⟨452951, by rfl⟩ : syracuseStep 603935 = 905903) B905903
theorem B1292851 : Blo 267823 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B2604307 : Blo 267823 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B770143 : Blo 267823 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B1295081 : Blo 267823 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B3064715 : Blo 267823 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B1525979 : Blo 267823 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B1723751 : Blo 267823 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B610217 : Blo 267823 610217 := bstep (se 2 (by rfl) ⟨228831, by rfl⟩ : syracuseStep 610217 = 457663) B457663
theorem B1364201 : Blo 267823 1364201 := bstep (se 2 (by rfl) ⟨511575, by rfl⟩ : syracuseStep 1364201 = 1023151) B1023151
theorem B22238009 : Blo 267823 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B611279 : Blo 267823 611279 := bstep (se 1 (by rfl) ⟨458459, by rfl⟩ : syracuseStep 611279 = 916919) B916919
theorem B4937051 : Blo 267823 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B225957923 : Blo 267823 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B2545835 : Blo 267823 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B17520947 : Blo 267823 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B49601159 : Blo 267823 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B2310757303 : Blo 267823 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B1105435 : Blo 267823 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B3498173 : Blo 267823 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B680795 : Blo 267823 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B3073463 : Blo 267823 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B452047 : Blo 267823 452047 := bstep (se 1 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 452047 = 678071) B678071
theorem B911195 : Blo 267823 911195 := bstep (se 1 (by rfl) ⟨683396, by rfl⟩ : syracuseStep 911195 = 1366793) B1366793
theorem B681959 : Blo 267823 681959 := bstep (se 1 (by rfl) ⟨511469, by rfl⟩ : syracuseStep 681959 = 1022939) B1022939
theorem B911465 : Blo 267823 911465 := bstep (se 2 (by rfl) ⟨341799, by rfl⟩ : syracuseStep 911465 = 683599) B683599
theorem B452783 : Blo 267823 452783 := bstep (se 1 (by rfl) ⟨339587, by rfl⟩ : syracuseStep 452783 = 679175) B679175
theorem B453019 : Blo 267823 453019 := bstep (se 1 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 453019 = 679529) B679529
theorem B4909679 : Blo 267823 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B912545 : Blo 267823 912545 := bstep (se 2 (by rfl) ⟨342204, by rfl⟩ : syracuseStep 912545 = 684409) B684409
theorem B1535183 : Blo 267823 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B6221933 : Blo 267823 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1863805 : Blo 267823 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B651559 : Blo 267823 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B455071 : Blo 267823 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B1733183 : Blo 267823 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B915191 : Blo 267823 915191 := bstep (se 1 (by rfl) ⟨686393, by rfl⟩ : syracuseStep 915191 = 1372787) B1372787
theorem B7108667 : Blo 267823 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B686191 : Blo 267823 686191 := bstep (se 1 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 686191 = 1029287) B1029287
theorem B457319 : Blo 267823 457319 := bstep (se 1 (by rfl) ⟨342989, by rfl⟩ : syracuseStep 457319 = 685979) B685979
theorem B457967 : Blo 267823 457967 := bstep (se 1 (by rfl) ⟨343475, by rfl⟩ : syracuseStep 457967 = 686951) B686951
theorem B458345 : Blo 267823 458345 := bstep (se 2 (by rfl) ⟨171879, by rfl⟩ : syracuseStep 458345 = 343759) B343759
theorem B1017319 : Blo 267823 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B1149167 : Blo 267823 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B1542473 : Blo 267823 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B19925347 : Blo 267823 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B4918427 : Blo 267823 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B2035367 : Blo 267823 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B150638615 : Blo 267823 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B33067439 : Blo 267823 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B2298779 : Blo 267823 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B660743 : Blo 267823 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B4396463 : Blo 267823 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B2332115 : Blo 267823 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B268059 : Blo 267823 268059 := bstep (se 1 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 268059 = 402089) B402089
theorem B6788893 : Blo 267823 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B268159 : Blo 267823 268159 := bstep (se 1 (by rfl) ⟨201119, by rfl⟩ : syracuseStep 268159 = 402239) B402239
theorem B268539 : Blo 267823 268539 := bstep (se 1 (by rfl) ⟨201404, by rfl⟩ : syracuseStep 268539 = 402809) B402809
theorem B301855 : Blo 267823 301855 := bstep (se 1 (by rfl) ⟨226391, by rfl⟩ : syracuseStep 301855 = 452783) B452783
theorem B269295 : Blo 267823 269295 := bstep (se 1 (by rfl) ⟨201971, by rfl⟩ : syracuseStep 269295 = 403943) B403943
theorem B269727 : Blo 267823 269727 := bstep (se 1 (by rfl) ⟨202295, by rfl⟩ : syracuseStep 269727 = 404591) B404591
theorem B269759 : Blo 267823 269759 := bstep (se 1 (by rfl) ⟨202319, by rfl⟩ : syracuseStep 269759 = 404639) B404639
theorem B1023455 : Blo 267823 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B269871 : Blo 267823 269871 := bstep (se 1 (by rfl) ⟨202403, by rfl⟩ : syracuseStep 269871 = 404807) B404807
theorem B270439 : Blo 267823 270439 := bstep (se 1 (by rfl) ⟨202829, by rfl⟩ : syracuseStep 270439 = 405659) B405659
theorem B1155455 : Blo 267823 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B270895 : Blo 267823 270895 := bstep (se 1 (by rfl) ⟨203171, by rfl⟩ : syracuseStep 270895 = 406343) B406343
theorem B271103 : Blo 267823 271103 := bstep (se 1 (by rfl) ⟨203327, by rfl⟩ : syracuseStep 271103 = 406655) B406655
theorem B19604267 : Blo 267823 19604267 := bstep (se 1 (by rfl) ⟨14703200, by rfl⟩ : syracuseStep 19604267 = 29406401) B29406401
theorem B271327 : Blo 267823 271327 := bstep (se 1 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 271327 = 406991) B406991
theorem B271359 : Blo 267823 271359 := bstep (se 1 (by rfl) ⟨203519, by rfl⟩ : syracuseStep 271359 = 407039) B407039
theorem B271391 : Blo 267823 271391 := bstep (se 1 (by rfl) ⟨203543, by rfl⟩ : syracuseStep 271391 = 407087) B407087
theorem B271431 : Blo 267823 271431 := bstep (se 1 (by rfl) ⟨203573, by rfl⟩ : syracuseStep 271431 = 407147) B407147
theorem B402623 : Blo 267823 402623 := bstep (se 1 (by rfl) ⟨301967, by rfl⟩ : syracuseStep 402623 = 603935) B603935
theorem B304879 : Blo 267823 304879 := bstep (se 1 (by rfl) ⟨228659, by rfl⟩ : syracuseStep 304879 = 457319) B457319
theorem B305311 : Blo 267823 305311 := bstep (se 1 (by rfl) ⟨228983, by rfl⟩ : syracuseStep 305311 = 457967) B457967
theorem B305563 : Blo 267823 305563 := bstep (se 1 (by rfl) ⟨229172, by rfl⟩ : syracuseStep 305563 = 458345) B458345
theorem B404201 : Blo 267823 404201 := bstep (se 2 (by rfl) ⟨151575, by rfl⟩ : syracuseStep 404201 = 303151) B303151
theorem B1026857 : Blo 267823 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B863387 : Blo 267823 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B2043143 : Blo 267823 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B602729 : Blo 267823 602729 := bstep (se 2 (by rfl) ⟨226023, by rfl⟩ : syracuseStep 602729 = 452047) B452047
theorem B406811 : Blo 267823 406811 := bstep (se 1 (by rfl) ⟨305108, by rfl⟩ : syracuseStep 406811 = 610217) B610217
theorem B1029455 : Blo 267823 1029455 := bstep (se 1 (by rfl) ⟨772091, by rfl⟩ : syracuseStep 1029455 = 1544183) B1544183
theorem B604025 : Blo 267823 604025 := bstep (se 2 (by rfl) ⟨226509, by rfl⟩ : syracuseStep 604025 = 453019) B453019
theorem B14825339 : Blo 267823 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B407519 : Blo 267823 407519 := bstep (se 1 (by rfl) ⟨305639, by rfl⟩ : syracuseStep 407519 = 611279) B611279
theorem B3291367 : Blo 267823 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B768275 : Blo 267823 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B1292699 : Blo 267823 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B703259 : Blo 267823 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B11680631 : Blo 267823 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B868745 : Blo 267823 868745 := bstep (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) B651559
theorem B967103 : Blo 267823 967103 := bstep (se 1 (by rfl) ⟨725327, by rfl⟩ : syracuseStep 967103 = 1450655) B1450655
theorem B606761 : Blo 267823 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B2048975 : Blo 267823 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B607463 : Blo 267823 607463 := bstep (se 1 (by rfl) ⟨455597, by rfl⟩ : syracuseStep 607463 = 911195) B911195
theorem B607643 : Blo 267823 607643 := bstep (se 1 (by rfl) ⟨455732, by rfl⟩ : syracuseStep 607643 = 911465) B911465
theorem B608363 : Blo 267823 608363 := bstep (se 1 (by rfl) ⟨456272, by rfl⟩ : syracuseStep 608363 = 912545) B912545
theorem B510239 : Blo 267823 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B4147955 : Blo 267823 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B773003 : Blo 267823 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B904175 : Blo 267823 904175 := bstep (se 1 (by rfl) ⟨678131, by rfl⟩ : syracuseStep 904175 = 1356263) B1356263
theorem B511211 : Blo 267823 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B2673967 : Blo 267823 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B1723801 : Blo 267823 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B610127 : Blo 267823 610127 := bstep (se 1 (by rfl) ⟨457595, by rfl⟩ : syracuseStep 610127 = 915191) B915191
theorem B4739111 : Blo 267823 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B286463 : Blo 267823 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B909467 : Blo 267823 909467 := bstep (se 1 (by rfl) ⟨682100, by rfl⟩ : syracuseStep 909467 = 1364201) B1364201
theorem B483977 : Blo 267823 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B3892859 : Blo 267823 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B26306329 : Blo 267823 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B2058209 : Blo 267823 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B2452207 : Blo 267823 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B2485073 : Blo 267823 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B453863 : Blo 267823 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B454639 : Blo 267823 454639 := bstep (se 1 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 454639 = 681959) B681959
theorem B3273119 : Blo 267823 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B914921 : Blo 267823 914921 := bstep (se 2 (by rfl) ⟨343095, by rfl⟩ : syracuseStep 914921 = 686191) B686191
theorem B3081009737 : Blo 267823 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B3472409 : Blo 267823 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B1473913 : Blo 267823 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B3278951 : Blo 267823 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B2298401 : Blo 267823 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B268415 : Blo 267823 268415 := bstep (se 1 (by rfl) ⟨201311, by rfl⟩ : syracuseStep 268415 = 402623) B402623
theorem B2595239 : Blo 267823 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B8216025965 : Blo 267823 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B269467 : Blo 267823 269467 := bstep (se 1 (by rfl) ⟨202100, by rfl⟩ : syracuseStep 269467 = 404201) B404201
theorem B302575 : Blo 267823 302575 := bstep (se 1 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 302575 = 453863) B453863
theorem B6626861 : Blo 267823 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B9051857 : Blo 267823 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B401819 : Blo 267823 401819 := bstep (se 1 (by rfl) ⟨301364, by rfl⟩ : syracuseStep 401819 = 602729) B602729
theorem B271207 : Blo 267823 271207 := bstep (se 1 (by rfl) ⟨203405, by rfl⟩ : syracuseStep 271207 = 406811) B406811
theorem B402473 : Blo 267823 402473 := bstep (se 2 (by rfl) ⟨150927, by rfl⟩ : syracuseStep 402473 = 301855) B301855
theorem B402683 : Blo 267823 402683 := bstep (se 1 (by rfl) ⟨302012, by rfl⟩ : syracuseStep 402683 = 604025) B604025
theorem B271679 : Blo 267823 271679 := bstep (se 1 (by rfl) ⟨203759, by rfl⟩ : syracuseStep 271679 = 407519) B407519
theorem B861799 : Blo 267823 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B468839 : Blo 267823 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B763901 : Blo 267823 763901 := bstep (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) B286463
theorem B404507 : Blo 267823 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B404975 : Blo 267823 404975 := bstep (se 1 (by rfl) ⟨303731, by rfl⟩ : syracuseStep 404975 = 607463) B607463
theorem B405095 : Blo 267823 405095 := bstep (se 1 (by rfl) ⟨303821, by rfl⟩ : syracuseStep 405095 = 607643) B607643
theorem B405575 : Blo 267823 405575 := bstep (se 1 (by rfl) ⟨304181, by rfl⟩ : syracuseStep 405575 = 608363) B608363
theorem B766111 : Blo 267823 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B1028315 : Blo 267823 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B2765303 : Blo 267823 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B1356425 : Blo 267823 1356425 := bstep (se 2 (by rfl) ⟨508659, by rfl⟩ : syracuseStep 1356425 = 1017319) B1017319
theorem B602783 : Blo 267823 602783 := bstep (se 1 (by rfl) ⟨452087, by rfl⟩ : syracuseStep 602783 = 904175) B904175
theorem B406505 : Blo 267823 406505 := bstep (se 2 (by rfl) ⟨152439, by rfl⟩ : syracuseStep 406505 = 304879) B304879
theorem B35075105 : Blo 267823 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B1356911 : Blo 267823 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B406751 : Blo 267823 406751 := bstep (se 1 (by rfl) ⟨305063, by rfl⟩ : syracuseStep 406751 = 610127) B610127
theorem B3159407 : Blo 267823 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B407081 : Blo 267823 407081 := bstep (se 2 (by rfl) ⟨152655, by rfl⟩ : syracuseStep 407081 = 305311) B305311
theorem B407417 : Blo 267823 407417 := bstep (se 2 (by rfl) ⟨152781, by rfl⟩ : syracuseStep 407417 = 305563) B305563
theorem B440495 : Blo 267823 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B2930975 : Blo 267823 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B1554743 : Blo 267823 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B606185 : Blo 267823 606185 := bstep (se 2 (by rfl) ⟨227319, by rfl⟩ : syracuseStep 606185 = 454639) B454639
theorem B606311 : Blo 267823 606311 := bstep (se 1 (by rfl) ⟨454733, by rfl⟩ : syracuseStep 606311 = 909467) B909467
theorem B770303 : Blo 267823 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B1360637 : Blo 267823 1360637 := bstep (se 3 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 1360637 = 510239) B510239
theorem B575591 : Blo 267823 575591 := bstep (se 1 (by rfl) ⟨431693, by rfl⟩ : syracuseStep 575591 = 863387) B863387
theorem B1362095 : Blo 267823 1362095 := bstep (se 1 (by rfl) ⟨1021571, by rfl⟩ : syracuseStep 1362095 = 2043143) B2043143
theorem B2182079 : Blo 267823 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1363229 : Blo 267823 1363229 := bstep (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) B511211
theorem B609947 : Blo 267823 609947 := bstep (se 1 (by rfl) ⟨457460, by rfl⟩ : syracuseStep 609947 = 914921) B914921
theorem B9883559 : Blo 267823 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B512183 : Blo 267823 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B7787087 : Blo 267823 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B2314939 : Blo 267823 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B579163 : Blo 267823 579163 := bstep (se 1 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 579163 = 868745) B868745
theorem B644735 : Blo 267823 644735 := bstep (se 1 (by rfl) ⟨483551, by rfl⟩ : syracuseStep 644735 = 967103) B967103
theorem B1365983 : Blo 267823 1365983 := bstep (se 1 (by rfl) ⟨1024487, by rfl⟩ : syracuseStep 1365983 = 2048975) B2048975
theorem B515335 : Blo 267823 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B100425743 : Blo 267823 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B22044959 : Blo 267823 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B26567129 : Blo 267823 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B1532519 : Blo 267823 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B3269609 : Blo 267823 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B3565289 : Blo 267823 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B682303 : Blo 267823 682303 := bstep (se 1 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 682303 = 1023455) B1023455
theorem B322651 : Blo 267823 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B13069511 : Blo 267823 13069511 := bstep (se 1 (by rfl) ⟨9802133, by rfl⟩ : syracuseStep 13069511 = 19604267) B19604267
theorem B1372139 : Blo 267823 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B684571 : Blo 267823 684571 := bstep (se 1 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 684571 = 1026857) B1026857
theorem B4388489 : Blo 267823 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B686303 : Blo 267823 686303 := bstep (se 1 (by rfl) ⟨514727, by rfl⟩ : syracuseStep 686303 = 1029455) B1029455
theorem B1965217 : Blo 267823 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1149065 : Blo 267823 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B6589039 : Blo 267823 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B429823 : Blo 267823 429823 := bstep (se 1 (by rfl) ⟨322367, by rfl⟩ : syracuseStep 429823 = 644735) B644735
theorem B430201 : Blo 267823 430201 := bstep (se 2 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 430201 = 322651) B322651
theorem B6034571 : Blo 267823 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B66950495 : Blo 267823 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B1021481 : Blo 267823 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B267879 : Blo 267823 267879 := bstep (se 1 (by rfl) ⟨200909, by rfl⟩ : syracuseStep 267879 = 401819) B401819
theorem B1021679 : Blo 267823 1021679 := bstep (se 1 (by rfl) ⟨766259, by rfl⟩ : syracuseStep 1021679 = 1532519) B1532519
theorem B268315 : Blo 267823 268315 := bstep (se 1 (by rfl) ⟨201236, by rfl⟩ : syracuseStep 268315 = 402473) B402473
theorem B268455 : Blo 267823 268455 := bstep (se 1 (by rfl) ⟨201341, by rfl⟩ : syracuseStep 268455 = 402683) B402683
theorem B3086585 : Blo 267823 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B269671 : Blo 267823 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B269983 : Blo 267823 269983 := bstep (se 1 (by rfl) ⟨202487, by rfl⟩ : syracuseStep 269983 = 404975) B404975
theorem B270063 : Blo 267823 270063 := bstep (se 1 (by rfl) ⟨202547, by rfl⟩ : syracuseStep 270063 = 405095) B405095
theorem B270383 : Blo 267823 270383 := bstep (se 1 (by rfl) ⟨202787, by rfl⟩ : syracuseStep 270383 = 405575) B405575
theorem B1843535 : Blo 267823 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B401855 : Blo 267823 401855 := bstep (se 1 (by rfl) ⟨301391, by rfl⟩ : syracuseStep 401855 = 602783) B602783
theorem B271003 : Blo 267823 271003 := bstep (se 1 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 271003 = 406505) B406505
theorem B271167 : Blo 267823 271167 := bstep (se 1 (by rfl) ⟨203375, by rfl⟩ : syracuseStep 271167 = 406751) B406751
theorem B2106271 : Blo 267823 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B271387 : Blo 267823 271387 := bstep (se 1 (by rfl) ⟨203540, by rfl⟩ : syracuseStep 271387 = 407081) B407081
theorem B2925659 : Blo 267823 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B271611 : Blo 267823 271611 := bstep (se 1 (by rfl) ⟨203708, by rfl⟩ : syracuseStep 271611 = 407417) B407417
theorem B403433 : Blo 267823 403433 := bstep (se 2 (by rfl) ⟨151287, by rfl⟩ : syracuseStep 403433 = 302575) B302575
theorem B404123 : Blo 267823 404123 := bstep (se 1 (by rfl) ⟨303092, by rfl⟩ : syracuseStep 404123 = 606185) B606185
theorem B404207 : Blo 267823 404207 := bstep (se 1 (by rfl) ⟨303155, by rfl⟩ : syracuseStep 404207 = 606311) B606311
theorem B1454719 : Blo 267823 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B406631 : Blo 267823 406631 := bstep (se 1 (by rfl) ⟨304973, by rfl⟩ : syracuseStep 406631 = 609947) B609947
theorem B5191391 : Blo 267823 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B5477350643 : Blo 267823 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B14696639 : Blo 267823 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B17711419 : Blo 267823 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B2179739 : Blo 267823 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B2376859 : Blo 267823 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B312559 : Blo 267823 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B509267 : Blo 267823 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B772217 : Blo 267823 772217 := bstep (se 2 (by rfl) ⟨289581, by rfl⟩ : syracuseStep 772217 = 579163) B579163
theorem B904283 : Blo 267823 904283 := bstep (se 1 (by rfl) ⟨678212, by rfl⟩ : syracuseStep 904283 = 1356425) B1356425
theorem B23383403 : Blo 267823 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B904607 : Blo 267823 904607 := bstep (se 1 (by rfl) ⟨678455, by rfl⟩ : syracuseStep 904607 = 1356911) B1356911
theorem B1953983 : Blo 267823 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B1036495 : Blo 267823 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B513535 : Blo 267823 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B1365821 : Blo 267823 1365821 := bstep (se 3 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 1365821 = 512183) B512183
theorem B907091 : Blo 267823 907091 := bstep (se 1 (by rfl) ⟨680318, by rfl⟩ : syracuseStep 907091 = 1360637) B1360637
theorem B2185967 : Blo 267823 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B908063 : Blo 267823 908063 := bstep (se 1 (by rfl) ⟨681047, by rfl⟩ : syracuseStep 908063 = 1362095) B1362095
theorem B908819 : Blo 267823 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B1532267 : Blo 267823 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B909737 : Blo 267823 909737 := bstep (se 2 (by rfl) ⟨341151, by rfl⟩ : syracuseStep 909737 = 682303) B682303
theorem B910655 : Blo 267823 910655 := bstep (se 1 (by rfl) ⟨682991, by rfl⟩ : syracuseStep 910655 = 1365983) B1365983
theorem B1730159 : Blo 267823 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B4417907 : Blo 267823 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B1534909 : Blo 267823 1534909 := bstep (se 3 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 1534909 = 575591) B575591
theorem B912761 : Blo 267823 912761 := bstep (se 2 (by rfl) ⟨342285, by rfl⟩ : syracuseStep 912761 = 684571) B684571
theorem B8713007 : Blo 267823 8713007 := bstep (se 1 (by rfl) ⟨6534755, by rfl⟩ : syracuseStep 8713007 = 13069511) B13069511
theorem B914759 : Blo 267823 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B685543 : Blo 267823 685543 := bstep (se 1 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 685543 = 1028315) B1028315
theorem B293663 : Blo 267823 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B457535 : Blo 267823 457535 := bstep (se 1 (by rfl) ⟨343151, by rfl⟩ : syracuseStep 457535 = 686303) B686303
theorem B2620289 : Blo 267823 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B687113 : Blo 267823 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B9797759 : Blo 267823 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B2294405 : Blo 267823 2294405 := bstep (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) B430201
theorem B8785385 : Blo 267823 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B44633663 : Blo 267823 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B1021511 : Blo 267823 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B267903 : Blo 267823 267903 := bstep (se 1 (by rfl) ⟨200927, by rfl⟩ : syracuseStep 267903 = 401855) B401855
theorem B1939625 : Blo 267823 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B1153439 : Blo 267823 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B268955 : Blo 267823 268955 := bstep (se 1 (by rfl) ⟨201716, by rfl⟩ : syracuseStep 268955 = 403433) B403433
theorem B269415 : Blo 267823 269415 := bstep (se 1 (by rfl) ⟨202061, by rfl⟩ : syracuseStep 269415 = 404123) B404123
theorem B269471 : Blo 267823 269471 := bstep (se 1 (by rfl) ⟨202103, by rfl⟩ : syracuseStep 269471 = 404207) B404207
theorem B5808671 : Blo 267823 5808671 := bstep (se 1 (by rfl) ⟨4356503, by rfl⟩ : syracuseStep 5808671 = 8713007) B8713007
theorem B271087 : Blo 267823 271087 := bstep (se 1 (by rfl) ⟨203315, by rfl⟩ : syracuseStep 271087 = 406631) B406631
theorem B305023 : Blo 267823 305023 := bstep (se 1 (by rfl) ⟨228767, by rfl⟩ : syracuseStep 305023 = 457535) B457535
theorem B1746859 : Blo 267823 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B1453159 : Blo 267823 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B766043 : Blo 267823 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B602855 : Blo 267823 602855 := bstep (se 1 (by rfl) ⟨452141, by rfl⟩ : syracuseStep 602855 = 904283) B904283
theorem B603071 : Blo 267823 603071 := bstep (se 1 (by rfl) ⟨452303, by rfl⟩ : syracuseStep 603071 = 904607) B904607
theorem B1358045 : Blo 267823 1358045 := bstep (se 3 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 1358045 = 509267) B509267
theorem B604727 : Blo 267823 604727 := bstep (se 1 (by rfl) ⟨453545, by rfl⟩ : syracuseStep 604727 = 907091) B907091
theorem B2046545 : Blo 267823 2046545 := bstep (se 2 (by rfl) ⟨767454, by rfl⟩ : syracuseStep 2046545 = 1534909) B1534909
theorem B605375 : Blo 267823 605375 := bstep (se 1 (by rfl) ⟨454031, by rfl⟩ : syracuseStep 605375 = 908063) B908063
theorem B573097 : Blo 267823 573097 := bstep (se 2 (by rfl) ⟨214911, by rfl⟩ : syracuseStep 573097 = 429823) B429823
theorem B605879 : Blo 267823 605879 := bstep (se 1 (by rfl) ⟨454409, by rfl⟩ : syracuseStep 605879 = 908819) B908819
theorem B1229023 : Blo 267823 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B606491 : Blo 267823 606491 := bstep (se 1 (by rfl) ⟨454868, by rfl⟩ : syracuseStep 606491 = 909737) B909737
theorem B1950439 : Blo 267823 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B607103 : Blo 267823 607103 := bstep (se 1 (by rfl) ⟨455327, by rfl⟩ : syracuseStep 607103 = 910655) B910655
theorem B11781085 : Blo 267823 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B608507 : Blo 267823 608507 := bstep (se 1 (by rfl) ⟨456380, by rfl⟩ : syracuseStep 608507 = 912761) B912761
theorem B609839 : Blo 267823 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B3460927 : Blo 267823 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B23615225 : Blo 267823 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B5527973 : Blo 267823 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B2808361 : Blo 267823 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B514811 : Blo 267823 514811 := bstep (se 1 (by rfl) ⟨386108, by rfl⟩ : syracuseStep 514811 = 772217) B772217
theorem B3169145 : Blo 267823 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B15588935 : Blo 267823 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B1302655 : Blo 267823 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B4023047 : Blo 267823 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B680987 : Blo 267823 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B681119 : Blo 267823 681119 := bstep (se 1 (by rfl) ⟨510839, by rfl⟩ : syracuseStep 681119 = 1021679) B1021679
theorem B910547 : Blo 267823 910547 := bstep (se 1 (by rfl) ⟨682910, by rfl⟩ : syracuseStep 910547 = 1365821) B1365821
theorem B2057723 : Blo 267823 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B1666981 : Blo 267823 1666981 := bstep (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) B312559
theorem B5829245 : Blo 267823 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B914057 : Blo 267823 914057 := bstep (se 2 (by rfl) ⟨342771, by rfl⟩ : syracuseStep 914057 = 685543) B685543
theorem B684713 : Blo 267823 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B783101 : Blo 267823 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B458075 : Blo 267823 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B3651567095 : Blo 267823 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B1736873 : Blo 267823 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B6554789 : Blo 267823 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B29755775 : Blo 267823 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B2329145 : Blo 267823 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B10392623 : Blo 267823 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B3872447 : Blo 267823 3872447 := bstep (se 1 (by rfl) ⟨2904335, by rfl⟩ : syracuseStep 3872447 = 5808671) B5808671
theorem B401903 : Blo 267823 401903 := bstep (se 1 (by rfl) ⟨301427, by rfl⟩ : syracuseStep 401903 = 602855) B602855
theorem B402047 : Blo 267823 402047 := bstep (se 1 (by rfl) ⟨301535, by rfl⟩ : syracuseStep 402047 = 603071) B603071
theorem B3744481 : Blo 267823 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B403151 : Blo 267823 403151 := bstep (se 1 (by rfl) ⟨302363, by rfl⟩ : syracuseStep 403151 = 604727) B604727
theorem B403583 : Blo 267823 403583 := bstep (se 1 (by rfl) ⟨302687, by rfl⟩ : syracuseStep 403583 = 605375) B605375
theorem B8890565 : Blo 267823 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B764129 : Blo 267823 764129 := bstep (se 2 (by rfl) ⟨286548, by rfl⟩ : syracuseStep 764129 = 573097) B573097
theorem B305383 : Blo 267823 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B2434378063 : Blo 267823 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B403919 : Blo 267823 403919 := bstep (se 1 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 403919 = 605879) B605879
theorem B6531839 : Blo 267823 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B404327 : Blo 267823 404327 := bstep (se 1 (by rfl) ⟨303245, by rfl⟩ : syracuseStep 404327 = 606491) B606491
theorem B404735 : Blo 267823 404735 := bstep (se 1 (by rfl) ⟨303551, by rfl⟩ : syracuseStep 404735 = 607103) B607103
theorem B2600585 : Blo 267823 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B15708113 : Blo 267823 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B405671 : Blo 267823 405671 := bstep (se 1 (by rfl) ⟨304253, by rfl⟩ : syracuseStep 405671 = 608507) B608507
theorem B10728125 : Blo 267823 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B406559 : Blo 267823 406559 := bstep (se 1 (by rfl) ⟨304919, by rfl⟩ : syracuseStep 406559 = 609839) B609839
theorem B406697 : Blo 267823 406697 := bstep (se 2 (by rfl) ⟨152511, by rfl⟩ : syracuseStep 406697 = 305023) B305023
theorem B15743483 : Blo 267823 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B1293083 : Blo 267823 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B768959 : Blo 267823 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B343207 : Blo 267823 343207 := bstep (se 1 (by rfl) ⟨257405, by rfl⟩ : syracuseStep 343207 = 514811) B514811
theorem B2112763 : Blo 267823 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B7750181 : Blo 267823 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B607031 : Blo 267823 607031 := bstep (se 1 (by rfl) ⟨455273, by rfl⟩ : syracuseStep 607031 = 910547) B910547
theorem B510695 : Blo 267823 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B3886163 : Blo 267823 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B609371 : Blo 267823 609371 := bstep (se 1 (by rfl) ⟨457028, by rfl⟩ : syracuseStep 609371 = 914057) B914057
theorem B905363 : Blo 267823 905363 := bstep (se 1 (by rfl) ⟨679022, by rfl⟩ : syracuseStep 905363 = 1358045) B1358045
theorem B1364363 : Blo 267823 1364363 := bstep (se 1 (by rfl) ⟨1023272, by rfl⟩ : syracuseStep 1364363 = 2046545) B2046545
theorem B1529603 : Blo 267823 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B5856923 : Blo 267823 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B681007 : Blo 267823 681007 := bstep (se 1 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 681007 = 1021511) B1021511
theorem B4614569 : Blo 267823 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B453991 : Blo 267823 453991 := bstep (se 1 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 453991 = 680987) B680987
theorem B454079 : Blo 267823 454079 := bstep (se 1 (by rfl) ⟨340559, by rfl⟩ : syracuseStep 454079 = 681119) B681119
theorem B1371815 : Blo 267823 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B14741261 : Blo 267823 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B456475 : Blo 267823 456475 := bstep (se 1 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 456475 = 684713) B684713
theorem B522067 : Blo 267823 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B2590775 : Blo 267823 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B3245837417 : Blo 267823 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B1019735 : Blo 267823 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B3904615 : Blo 267823 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B267935 : Blo 267823 267935 := bstep (se 1 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 267935 = 401903) B401903
theorem B268031 : Blo 267823 268031 := bstep (se 1 (by rfl) ⟨201023, by rfl⟩ : syracuseStep 268031 = 402047) B402047
theorem B268767 : Blo 267823 268767 := bstep (se 1 (by rfl) ⟨201575, by rfl⟩ : syracuseStep 268767 = 403151) B403151
theorem B269055 : Blo 267823 269055 := bstep (se 1 (by rfl) ⟨201791, by rfl⟩ : syracuseStep 269055 = 403583) B403583
theorem B269279 : Blo 267823 269279 := bstep (se 1 (by rfl) ⟨201959, by rfl⟩ : syracuseStep 269279 = 403919) B403919
theorem B269551 : Blo 267823 269551 := bstep (se 1 (by rfl) ⟨202163, by rfl⟩ : syracuseStep 269551 = 404327) B404327
theorem B269823 : Blo 267823 269823 := bstep (se 1 (by rfl) ⟨202367, by rfl⟩ : syracuseStep 269823 = 404735) B404735
theorem B302719 : Blo 267823 302719 := bstep (se 1 (by rfl) ⟨227039, by rfl⟩ : syracuseStep 302719 = 454079) B454079
theorem B696089 : Blo 267823 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B270447 : Blo 267823 270447 := bstep (se 1 (by rfl) ⟨202835, by rfl⟩ : syracuseStep 270447 = 405671) B405671
theorem B7152083 : Blo 267823 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B271039 : Blo 267823 271039 := bstep (se 1 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 271039 = 406559) B406559
theorem B271131 : Blo 267823 271131 := bstep (se 1 (by rfl) ⟨203348, by rfl⟩ : syracuseStep 271131 = 406697) B406697
theorem B10495655 : Blo 267823 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B862055 : Blo 267823 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B1157915 : Blo 267823 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B404687 : Blo 267823 404687 := bstep (se 1 (by rfl) ⟨303515, by rfl⟩ : syracuseStep 404687 = 607031) B607031
theorem B4369859 : Blo 267823 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B4992641 : Blo 267823 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B19837183 : Blo 267823 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B1552763 : Blo 267823 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B340463 : Blo 267823 340463 := bstep (se 1 (by rfl) ⟨255347, by rfl⟩ : syracuseStep 340463 = 510695) B510695
theorem B406247 : Blo 267823 406247 := bstep (se 1 (by rfl) ⟨304685, by rfl⟩ : syracuseStep 406247 = 609371) B609371
theorem B603575 : Blo 267823 603575 := bstep (se 1 (by rfl) ⟨452681, by rfl⟩ : syracuseStep 603575 = 905363) B905363
theorem B407177 : Blo 267823 407177 := bstep (se 2 (by rfl) ⟨152691, by rfl⟩ : syracuseStep 407177 = 305383) B305383
theorem B6928415 : Blo 267823 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B605321 : Blo 267823 605321 := bstep (se 2 (by rfl) ⟨226995, by rfl⟩ : syracuseStep 605321 = 453991) B453991
theorem B23708173 : Blo 267823 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B509419 : Blo 267823 509419 := bstep (se 1 (by rfl) ⟨382064, by rfl⟩ : syracuseStep 509419 = 764129) B764129
theorem B608633 : Blo 267823 608633 := bstep (se 2 (by rfl) ⟨228237, by rfl⟩ : syracuseStep 608633 = 456475) B456475
theorem B10472075 : Blo 267823 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B512639 : Blo 267823 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B5166787 : Blo 267823 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B908009 : Blo 267823 908009 := bstep (se 2 (by rfl) ⟨340503, by rfl⟩ : syracuseStep 908009 = 681007) B681007
theorem B909575 : Blo 267823 909575 := bstep (se 1 (by rfl) ⟨682181, by rfl⟩ : syracuseStep 909575 = 1364363) B1364363
theorem B2581631 : Blo 267823 2581631 := bstep (se 1 (by rfl) ⟨1936223, by rfl⟩ : syracuseStep 2581631 = 3872447) B3872447
theorem B3076379 : Blo 267823 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B4354559 : Blo 267823 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B1733723 : Blo 267823 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B914543 : Blo 267823 914543 := bstep (se 1 (by rfl) ⟨685907, by rfl⟩ : syracuseStep 914543 = 1371815) B1371815
theorem B9827507 : Blo 267823 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B457609 : Blo 267823 457609 := bstep (se 2 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 457609 = 343207) B343207
theorem B2817017 : Blo 267823 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B6981383 : Blo 267823 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B464059 : Blo 267823 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B26449577 : Blo 267823 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B269791 : Blo 267823 269791 := bstep (se 1 (by rfl) ⟨202343, by rfl⟩ : syracuseStep 269791 = 404687) B404687
theorem B6889049 : Blo 267823 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B270831 : Blo 267823 270831 := bstep (se 1 (by rfl) ⟨203123, by rfl⟩ : syracuseStep 270831 = 406247) B406247
theorem B1155815 : Blo 267823 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B402383 : Blo 267823 402383 := bstep (se 1 (by rfl) ⟨301787, by rfl⟩ : syracuseStep 402383 = 603575) B603575
theorem B271451 : Blo 267823 271451 := bstep (se 1 (by rfl) ⟨203588, by rfl⟩ : syracuseStep 271451 = 407177) B407177
theorem B1878011 : Blo 267823 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B403547 : Blo 267823 403547 := bstep (se 1 (by rfl) ⟨302660, by rfl⟩ : syracuseStep 403547 = 605321) B605321
theorem B403625 : Blo 267823 403625 := bstep (se 2 (by rfl) ⟨151359, by rfl⟩ : syracuseStep 403625 = 302719) B302719
theorem B405755 : Blo 267823 405755 := bstep (se 1 (by rfl) ⟨304316, by rfl⟩ : syracuseStep 405755 = 608633) B608633
theorem B341759 : Blo 267823 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B605339 : Blo 267823 605339 := bstep (se 1 (by rfl) ⟨454004, by rfl⟩ : syracuseStep 605339 = 908009) B908009
theorem B606383 : Blo 267823 606383 := bstep (se 1 (by rfl) ⟨454787, by rfl⟩ : syracuseStep 606383 = 909575) B909575
theorem B4768055 : Blo 267823 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B1721087 : Blo 267823 1721087 := bstep (se 1 (by rfl) ⟨1290815, by rfl⟩ : syracuseStep 1721087 = 2581631) B2581631
theorem B6997103 : Blo 267823 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B574703 : Blo 267823 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B771943 : Blo 267823 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B3328427 : Blo 267823 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B2050919 : Blo 267823 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B1035175 : Blo 267823 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B2903039 : Blo 267823 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B609695 : Blo 267823 609695 := bstep (se 1 (by rfl) ⟨457271, by rfl⟩ : syracuseStep 609695 = 914543) B914543
theorem B610145 : Blo 267823 610145 := bstep (se 2 (by rfl) ⟨228804, by rfl⟩ : syracuseStep 610145 = 457609) B457609
theorem B31610897 : Blo 267823 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B907901 : Blo 267823 907901 := bstep (se 3 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 907901 = 340463) B340463
theorem B1727183 : Blo 267823 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B679225 : Blo 267823 679225 := bstep (se 2 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 679225 = 509419) B509419
theorem B2163891611 : Blo 267823 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B679823 : Blo 267823 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B26206685 : Blo 267823 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B5206153 : Blo 267823 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B2913239 : Blo 267823 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B4618943 : Blo 267823 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B3178703 : Blo 267823 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B1147391 : Blo 267823 1147391 := bstep (se 1 (by rfl) ⟨860543, by rfl⟩ : syracuseStep 1147391 = 1721087) B1721087
theorem B4654255 : Blo 267823 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B1935359 : Blo 267823 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B17633051 : Blo 267823 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B1380233 : Blo 267823 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B21073931 : Blo 267823 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B4592699 : Blo 267823 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B17471123 : Blo 267823 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B268255 : Blo 267823 268255 := bstep (se 1 (by rfl) ⟨201191, by rfl⟩ : syracuseStep 268255 = 402383) B402383
theorem B1252007 : Blo 267823 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B269031 : Blo 267823 269031 := bstep (se 1 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 269031 = 403547) B403547
theorem B269083 : Blo 267823 269083 := bstep (se 1 (by rfl) ⟨201812, by rfl⟩ : syracuseStep 269083 = 403625) B403625
theorem B270503 : Blo 267823 270503 := bstep (se 1 (by rfl) ⟨202877, by rfl⟩ : syracuseStep 270503 = 405755) B405755
theorem B1942159 : Blo 267823 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B403559 : Blo 267823 403559 := bstep (se 1 (by rfl) ⟨302669, by rfl⟩ : syracuseStep 403559 = 605339) B605339
theorem B404255 : Blo 267823 404255 := bstep (se 1 (by rfl) ⟨303191, by rfl⟩ : syracuseStep 404255 = 606383) B606383
theorem B4664735 : Blo 267823 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B406463 : Blo 267823 406463 := bstep (se 1 (by rfl) ⟨304847, by rfl⟩ : syracuseStep 406463 = 609695) B609695
theorem B1029257 : Blo 267823 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B406763 : Blo 267823 406763 := bstep (se 1 (by rfl) ⟨305072, by rfl⟩ : syracuseStep 406763 = 610145) B610145
theorem B605267 : Blo 267823 605267 := bstep (se 1 (by rfl) ⟨453950, by rfl⟩ : syracuseStep 605267 = 907901) B907901
theorem B1442594407 : Blo 267823 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B770543 : Blo 267823 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B4605821 : Blo 267823 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B905633 : Blo 267823 905633 := bstep (se 2 (by rfl) ⟨339612, by rfl⟩ : syracuseStep 905633 = 679225) B679225
theorem B383135 : Blo 267823 383135 := bstep (se 1 (by rfl) ⟨287351, by rfl⟩ : syracuseStep 383135 = 574703) B574703
theorem B2218951 : Blo 267823 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1367279 : Blo 267823 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B911357 : Blo 267823 911357 := bstep (se 3 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 911357 = 341759) B341759
theorem B453215 : Blo 267823 453215 := bstep (se 1 (by rfl) ⟨339911, by rfl⟩ : syracuseStep 453215 = 679823) B679823
theorem B6941537 : Blo 267823 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B618745 : Blo 267823 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B3079295 : Blo 267823 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B2589545 : Blo 267823 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B920155 : Blo 267823 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B824993 : Blo 267823 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B1021693 : Blo 267823 1021693 := bstep (se 3 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 1021693 = 383135) B383135
theorem B269039 : Blo 267823 269039 := bstep (se 1 (by rfl) ⟨201779, by rfl⟩ : syracuseStep 269039 = 403559) B403559
theorem B302143 : Blo 267823 302143 := bstep (se 1 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 302143 = 453215) B453215
theorem B269503 : Blo 267823 269503 := bstep (se 1 (by rfl) ⟨202127, by rfl⟩ : syracuseStep 269503 = 404255) B404255
theorem B4627691 : Blo 267823 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B270975 : Blo 267823 270975 := bstep (se 1 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 270975 = 406463) B406463
theorem B271175 : Blo 267823 271175 := bstep (se 1 (by rfl) ⟨203381, by rfl⟩ : syracuseStep 271175 = 406763) B406763
theorem B2958601 : Blo 267823 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B403511 : Blo 267823 403511 := bstep (se 1 (by rfl) ⟨302633, by rfl⟩ : syracuseStep 403511 = 605267) B605267
theorem B1923459209 : Blo 267823 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B764927 : Blo 267823 764927 := bstep (se 1 (by rfl) ⟨573695, by rfl⟩ : syracuseStep 764927 = 1147391) B1147391
theorem B1290239 : Blo 267823 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B6205673 : Blo 267823 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B603755 : Blo 267823 603755 := bstep (se 1 (by rfl) ⟨452816, by rfl⟩ : syracuseStep 603755 = 905633) B905633
theorem B3061799 : Blo 267823 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B11647415 : Blo 267823 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B834671 : Blo 267823 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B607571 : Blo 267823 607571 := bstep (se 1 (by rfl) ⟨455678, by rfl⟩ : syracuseStep 607571 = 911357) B911357
theorem B2052863 : Blo 267823 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B2119135 : Blo 267823 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B513695 : Blo 267823 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B3070547 : Blo 267823 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B11755367 : Blo 267823 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B14049287 : Blo 267823 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B911519 : Blo 267823 911519 := bstep (se 1 (by rfl) ⟨683639, by rfl⟩ : syracuseStep 911519 = 1367279) B1367279
theorem B3109823 : Blo 267823 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B686171 : Blo 267823 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B16548461 : Blo 267823 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B3085127 : Blo 267823 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B7836911 : Blo 267823 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B269007 : Blo 267823 269007 := bstep (se 1 (by rfl) ⟨201755, by rfl⟩ : syracuseStep 269007 = 403511) B403511
theorem B2825513 : Blo 267823 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B860159 : Blo 267823 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B2073215 : Blo 267823 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B402503 : Blo 267823 402503 := bstep (se 1 (by rfl) ⟨301877, by rfl⟩ : syracuseStep 402503 = 603755) B603755
theorem B2041199 : Blo 267823 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B402857 : Blo 267823 402857 := bstep (se 2 (by rfl) ⟨151071, by rfl⟩ : syracuseStep 402857 = 302143) B302143
theorem B405047 : Blo 267823 405047 := bstep (se 1 (by rfl) ⟨303785, by rfl⟩ : syracuseStep 405047 = 607571) B607571
theorem B3944801 : Blo 267823 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B1226873 : Blo 267823 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B342463 : Blo 267823 342463 := bstep (se 1 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 342463 = 513695) B513695
theorem B2047031 : Blo 267823 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B607679 : Blo 267823 607679 := bstep (se 1 (by rfl) ⟨455759, by rfl⟩ : syracuseStep 607679 = 911519) B911519
theorem B509951 : Blo 267823 509951 := bstep (se 1 (by rfl) ⟨382463, by rfl⟩ : syracuseStep 509951 = 764927) B764927
theorem B1362257 : Blo 267823 1362257 := bstep (se 2 (by rfl) ⟨510846, by rfl⟩ : syracuseStep 1362257 = 1021693) B1021693
theorem B1726363 : Blo 267823 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1368575 : Blo 267823 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B549995 : Blo 267823 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B9366191 : Blo 267823 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B1282306139 : Blo 267823 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B457447 : Blo 267823 457447 := bstep (se 1 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 457447 = 686171) B686171
theorem B7764943 : Blo 267823 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B556447 : Blo 267823 556447 := bstep (se 1 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 556447 = 834671) B834671
theorem B10519469 : Blo 267823 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B5866613 : Blo 267823 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B1382143 : Blo 267823 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B268335 : Blo 267823 268335 := bstep (se 1 (by rfl) ⟨201251, by rfl⟩ : syracuseStep 268335 = 402503) B402503
theorem B268571 : Blo 267823 268571 := bstep (se 1 (by rfl) ⟨201428, by rfl⟩ : syracuseStep 268571 = 402857) B402857
theorem B270031 : Blo 267823 270031 := bstep (se 1 (by rfl) ⟨202523, by rfl⟩ : syracuseStep 270031 = 405047) B405047
theorem B2301817 : Blo 267823 2301817 := bstep (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) B1726363
theorem B11870869 : Blo 267823 11870869 := bstep (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) B556447
theorem B405119 : Blo 267823 405119 := bstep (se 1 (by rfl) ⟨303839, by rfl⟩ : syracuseStep 405119 = 607679) B607679
theorem B339967 : Blo 267823 339967 := bstep (se 1 (by rfl) ⟨254975, by rfl⟩ : syracuseStep 339967 = 509951) B509951
theorem B5224607 : Blo 267823 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B1883675 : Blo 267823 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B573439 : Blo 267823 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B1360799 : Blo 267823 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B6244127 : Blo 267823 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B854870759 : Blo 267823 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B609929 : Blo 267823 609929 := bstep (se 2 (by rfl) ⟨228723, by rfl⟩ : syracuseStep 609929 = 457447) B457447
theorem B1364687 : Blo 267823 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B11032307 : Blo 267823 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B908171 : Blo 267823 908171 := bstep (se 1 (by rfl) ⟨681128, by rfl⟩ : syracuseStep 908171 = 1362257) B1362257
theorem B2056751 : Blo 267823 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B3271661 : Blo 267823 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B912383 : Blo 267823 912383 := bstep (se 1 (by rfl) ⟨684287, by rfl⟩ : syracuseStep 912383 = 1368575) B1368575
theorem B456617 : Blo 267823 456617 := bstep (se 2 (by rfl) ⟨171231, by rfl⟩ : syracuseStep 456617 = 342463) B342463
theorem B10353257 : Blo 267823 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B7012979 : Blo 267823 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B15827825 : Blo 267823 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B4162751 : Blo 267823 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B1842857 : Blo 267823 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B270079 : Blo 267823 270079 := bstep (se 1 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 270079 = 405119) B405119
theorem B304411 : Blo 267823 304411 := bstep (se 1 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 304411 = 456617) B456617
theorem B3483071 : Blo 267823 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B1255783 : Blo 267823 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B764585 : Blo 267823 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B3911075 : Blo 267823 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B569913839 : Blo 267823 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B406619 : Blo 267823 406619 := bstep (se 1 (by rfl) ⟨304964, by rfl⟩ : syracuseStep 406619 = 609929) B609929
theorem B7354871 : Blo 267823 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B605447 : Blo 267823 605447 := bstep (se 1 (by rfl) ⟨454085, by rfl⟩ : syracuseStep 605447 = 908171) B908171
theorem B2181107 : Blo 267823 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B608255 : Blo 267823 608255 := bstep (se 1 (by rfl) ⟨456191, by rfl⟩ : syracuseStep 608255 = 912383) B912383
theorem B6902171 : Blo 267823 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B3069089 : Blo 267823 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B907199 : Blo 267823 907199 := bstep (se 1 (by rfl) ⟨680399, by rfl⟩ : syracuseStep 907199 = 1360799) B1360799
theorem B909791 : Blo 267823 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B453289 : Blo 267823 453289 := bstep (se 2 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 453289 = 339967) B339967
theorem B1371167 : Blo 267823 1371167 := bstep (se 1 (by rfl) ⟨1028375, by rfl⟩ : syracuseStep 1371167 = 2056751) B2056751
theorem B10551883 : Blo 267823 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B1674377 : Blo 267823 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B271079 : Blo 267823 271079 := bstep (se 1 (by rfl) ⟨203309, by rfl⟩ : syracuseStep 271079 = 406619) B406619
theorem B403631 : Blo 267823 403631 := bstep (se 1 (by rfl) ⟨302723, by rfl⟩ : syracuseStep 403631 = 605447) B605447
theorem B1454071 : Blo 267823 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B405503 : Blo 267823 405503 := bstep (se 1 (by rfl) ⟨304127, by rfl⟩ : syracuseStep 405503 = 608255) B608255
theorem B405881 : Blo 267823 405881 := bstep (se 2 (by rfl) ⟨152205, by rfl⟩ : syracuseStep 405881 = 304411) B304411
theorem B4601447 : Blo 267823 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B2046059 : Blo 267823 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B604385 : Blo 267823 604385 := bstep (se 2 (by rfl) ⟨226644, by rfl⟩ : syracuseStep 604385 = 453289) B453289
theorem B604799 : Blo 267823 604799 := bstep (se 1 (by rfl) ⟨453599, by rfl⟩ : syracuseStep 604799 = 907199) B907199
theorem B1228571 : Blo 267823 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B606527 : Blo 267823 606527 := bstep (se 1 (by rfl) ⟨454895, by rfl⟩ : syracuseStep 606527 = 909791) B909791
theorem B509723 : Blo 267823 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B2607383 : Blo 267823 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B4903247 : Blo 267823 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B4675319 : Blo 267823 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B2775167 : Blo 267823 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B2322047 : Blo 267823 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B914111 : Blo 267823 914111 := bstep (se 1 (by rfl) ⟨685583, by rfl⟩ : syracuseStep 914111 = 1371167) B1371167
theorem B379942559 : Blo 267823 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B1738255 : Blo 267823 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B1116251 : Blo 267823 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B3116879 : Blo 267823 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B1938761 : Blo 267823 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B269087 : Blo 267823 269087 := bstep (se 1 (by rfl) ⟨201815, by rfl⟩ : syracuseStep 269087 = 403631) B403631
theorem B1548031 : Blo 267823 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B270335 : Blo 267823 270335 := bstep (se 1 (by rfl) ⟨202751, by rfl⟩ : syracuseStep 270335 = 405503) B405503
theorem B270587 : Blo 267823 270587 := bstep (se 1 (by rfl) ⟨202940, by rfl⟩ : syracuseStep 270587 = 405881) B405881
theorem B402923 : Blo 267823 402923 := bstep (se 1 (by rfl) ⟨302192, by rfl⟩ : syracuseStep 402923 = 604385) B604385
theorem B403199 : Blo 267823 403199 := bstep (se 1 (by rfl) ⟨302399, by rfl⟩ : syracuseStep 403199 = 604799) B604799
theorem B404351 : Blo 267823 404351 := bstep (se 1 (by rfl) ⟨303263, by rfl⟩ : syracuseStep 404351 = 606527) B606527
theorem B14069177 : Blo 267823 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B339815 : Blo 267823 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B1850111 : Blo 267823 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B609407 : Blo 267823 609407 := bstep (se 1 (by rfl) ⟨457055, by rfl⟩ : syracuseStep 609407 = 914111) B914111
theorem B3067631 : Blo 267823 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B1364039 : Blo 267823 1364039 := bstep (se 1 (by rfl) ⟨1023029, by rfl⟩ : syracuseStep 1364039 = 2046059) B2046059
theorem B3268831 : Blo 267823 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B253295039 : Blo 267823 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B819047 : Blo 267823 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B4358441 : Blo 267823 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B268615 : Blo 267823 268615 := bstep (se 1 (by rfl) ⟨201461, by rfl⟩ : syracuseStep 268615 = 402923) B402923
theorem B268799 : Blo 267823 268799 := bstep (se 1 (by rfl) ⟨201599, by rfl⟩ : syracuseStep 268799 = 403199) B403199
theorem B269567 : Blo 267823 269567 := bstep (se 1 (by rfl) ⟨202175, by rfl⟩ : syracuseStep 269567 = 404351) B404351
theorem B9379451 : Blo 267823 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B168863359 : Blo 267823 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B406271 : Blo 267823 406271 := bstep (se 1 (by rfl) ⟨304703, by rfl⟩ : syracuseStep 406271 = 609407) B609407
theorem B2045087 : Blo 267823 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B2077919 : Blo 267823 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B1292507 : Blo 267823 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B1233407 : Blo 267823 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B906173 : Blo 267823 906173 := bstep (se 3 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 906173 = 339815) B339815
theorem B546031 : Blo 267823 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B744167 : Blo 267823 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B2317673 : Blo 267823 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B909359 : Blo 267823 909359 := bstep (se 1 (by rfl) ⟨682019, by rfl⟩ : syracuseStep 909359 = 1364039) B1364039
theorem B2064041 : Blo 267823 2064041 := bstep (se 2 (by rfl) ⟨774015, by rfl⟩ : syracuseStep 2064041 = 1548031) B1548031
theorem B225151145 : Blo 267823 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B822271 : Blo 267823 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B1545115 : Blo 267823 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B728041 : Blo 267823 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B270847 : Blo 267823 270847 := bstep (se 1 (by rfl) ⟨203135, by rfl⟩ : syracuseStep 270847 = 406271) B406271
theorem B1385279 : Blo 267823 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B861671 : Blo 267823 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B604115 : Blo 267823 604115 := bstep (se 1 (by rfl) ⟨453086, by rfl⟩ : syracuseStep 604115 = 906173) B906173
theorem B606239 : Blo 267823 606239 := bstep (se 1 (by rfl) ⟨454679, by rfl⟩ : syracuseStep 606239 = 909359) B909359
theorem B1984445 : Blo 267823 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B1363391 : Blo 267823 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B2905627 : Blo 267823 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B6252967 : Blo 267823 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B1376027 : Blo 267823 1376027 := bstep (se 1 (by rfl) ⟨1032020, by rfl⟩ : syracuseStep 1376027 = 2064041) B2064041
theorem B923519 : Blo 267823 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B3874169 : Blo 267823 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B402743 : Blo 267823 402743 := bstep (se 1 (by rfl) ⟨302057, by rfl⟩ : syracuseStep 402743 = 604115) B604115
theorem B404159 : Blo 267823 404159 := bstep (se 1 (by rfl) ⟨303119, by rfl⟩ : syracuseStep 404159 = 606239) B606239
theorem B1322963 : Blo 267823 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B2401612213 : Blo 267823 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B8337289 : Blo 267823 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B1096361 : Blo 267823 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B574447 : Blo 267823 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B970721 : Blo 267823 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B908927 : Blo 267823 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B2060153 : Blo 267823 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B917351 : Blo 267823 917351 := bstep (se 1 (by rfl) ⟨688013, by rfl⟩ : syracuseStep 917351 = 1376027) B1376027
theorem B2462717 : Blo 267823 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B268495 : Blo 267823 268495 := bstep (se 1 (by rfl) ⟨201371, by rfl⟩ : syracuseStep 268495 = 402743) B402743
theorem B269439 : Blo 267823 269439 := bstep (se 1 (by rfl) ⟨202079, by rfl⟩ : syracuseStep 269439 = 404159) B404159
theorem B11116385 : Blo 267823 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B730907 : Blo 267823 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B765929 : Blo 267823 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B605951 : Blo 267823 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B611567 : Blo 267823 611567 := bstep (se 1 (by rfl) ⟨458675, by rfl⟩ : syracuseStep 611567 = 917351) B917351
theorem B647147 : Blo 267823 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B2582779 : Blo 267823 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B3202149617 : Blo 267823 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B1373435 : Blo 267823 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B881975 : Blo 267823 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B3443705 : Blo 267823 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B1641811 : Blo 267823 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B7410923 : Blo 267823 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B403967 : Blo 267823 403967 := bstep (se 1 (by rfl) ⟨302975, by rfl⟩ : syracuseStep 403967 = 605951) B605951
theorem B407711 : Blo 267823 407711 := bstep (se 1 (by rfl) ⟨305783, by rfl⟩ : syracuseStep 407711 = 611567) B611567
theorem B510619 : Blo 267823 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B1725725 : Blo 267823 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B487271 : Blo 267823 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B2134766411 : Blo 267823 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B915623 : Blo 267823 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B587983 : Blo 267823 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B2295803 : Blo 267823 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B1150483 : Blo 267823 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B269311 : Blo 267823 269311 := bstep (se 1 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 269311 = 403967) B403967
theorem B271807 : Blo 267823 271807 := bstep (se 1 (by rfl) ⟨203855, by rfl⟩ : syracuseStep 271807 = 407711) B407711
theorem B610415 : Blo 267823 610415 := bstep (se 1 (by rfl) ⟨457811, by rfl⟩ : syracuseStep 610415 = 915623) B915623
theorem B4940615 : Blo 267823 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B680825 : Blo 267823 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B2189081 : Blo 267823 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B324847 : Blo 267823 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B783977 : Blo 267823 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B1423177607 : Blo 267823 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B433129 : Blo 267823 433129 := bstep (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) B324847
theorem B406943 : Blo 267823 406943 := bstep (se 1 (by rfl) ⟨305207, by rfl⟩ : syracuseStep 406943 = 610415) B610415
theorem B3293743 : Blo 267823 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B1459387 : Blo 267823 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B948785071 : Blo 267823 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B1530535 : Blo 267823 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B2090605 : Blo 267823 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B1533977 : Blo 267823 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B453883 : Blo 267823 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B4391657 : Blo 267823 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B2787473 : Blo 267823 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B1265046761 : Blo 267823 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B1022651 : Blo 267823 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B2040713 : Blo 267823 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B271295 : Blo 267823 271295 := bstep (se 1 (by rfl) ⟨203471, by rfl⟩ : syracuseStep 271295 = 406943) B406943
theorem B605177 : Blo 267823 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B7783397 : Blo 267823 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B577505 : Blo 267823 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B403451 : Blo 267823 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B2927771 : Blo 267823 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B5188931 : Blo 267823 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B843364507 : Blo 267823 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B1360475 : Blo 267823 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B1858315 : Blo 267823 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B385003 : Blo 267823 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B681767 : Blo 267823 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B268967 : Blo 267823 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B1951847 : Blo 267823 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B3459287 : Blo 267823 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B1124486009 : Blo 267823 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B2477753 : Blo 267823 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2053349 : Blo 267823 2053349 := bstep (se 4 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 2053349 = 385003) B385003
theorem B906983 : Blo 267823 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B454511 : Blo 267823 454511 := bstep (se 1 (by rfl) ⟨340883, by rfl⟩ : syracuseStep 454511 = 681767) B681767
theorem B303007 : Blo 267823 303007 := bstep (se 1 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 303007 = 454511) B454511
theorem B2306191 : Blo 267823 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B1651835 : Blo 267823 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B604655 : Blo 267823 604655 := bstep (se 1 (by rfl) ⟨453491, by rfl⟩ : syracuseStep 604655 = 906983) B906983
theorem B1301231 : Blo 267823 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B749657339 : Blo 267823 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B1368899 : Blo 267823 1368899 := bstep (se 1 (by rfl) ⟨1026674, by rfl⟩ : syracuseStep 1368899 = 2053349) B2053349
theorem B403103 : Blo 267823 403103 := bstep (se 1 (by rfl) ⟨302327, by rfl⟩ : syracuseStep 403103 = 604655) B604655
theorem B404009 : Blo 267823 404009 := bstep (se 2 (by rfl) ⟨151503, by rfl⟩ : syracuseStep 404009 = 303007) B303007
theorem B1101223 : Blo 267823 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B499771559 : Blo 267823 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B3074921 : Blo 267823 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B912599 : Blo 267823 912599 := bstep (se 1 (by rfl) ⟨684449, by rfl⟩ : syracuseStep 912599 = 1368899) B1368899
theorem B3469949 : Blo 267823 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B268735 : Blo 267823 268735 := bstep (se 1 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 268735 = 403103) B403103
theorem B269339 : Blo 267823 269339 := bstep (se 1 (by rfl) ⟨202004, by rfl⟩ : syracuseStep 269339 = 404009) B404009
theorem B2049947 : Blo 267823 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B608399 : Blo 267823 608399 := bstep (se 1 (by rfl) ⟨456299, by rfl⟩ : syracuseStep 608399 = 912599) B912599
theorem B2313299 : Blo 267823 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B1468297 : Blo 267823 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B333181039 : Blo 267823 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B1542199 : Blo 267823 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B444241385 : Blo 267823 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B405599 : Blo 267823 405599 := bstep (se 1 (by rfl) ⟨304199, by rfl⟩ : syracuseStep 405599 = 608399) B608399
theorem B1366631 : Blo 267823 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B7830917 : Blo 267823 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B296160923 : Blo 267823 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B270399 : Blo 267823 270399 := bstep (se 1 (by rfl) ⟨202799, by rfl⟩ : syracuseStep 270399 = 405599) B405599
theorem B5220611 : Blo 267823 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B2056265 : Blo 267823 2056265 := bstep (se 2 (by rfl) ⟨771099, by rfl⟩ : syracuseStep 2056265 = 1542199) B1542199
theorem B911087 : Blo 267823 911087 := bstep (se 1 (by rfl) ⟨683315, by rfl⟩ : syracuseStep 911087 = 1366631) B1366631
theorem B3480407 : Blo 267823 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B197440615 : Blo 267823 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B607391 : Blo 267823 607391 := bstep (se 1 (by rfl) ⟨455543, by rfl⟩ : syracuseStep 607391 = 911087) B911087
theorem B1370843 : Blo 267823 1370843 := bstep (se 1 (by rfl) ⟨1028132, by rfl⟩ : syracuseStep 1370843 = 2056265) B2056265
theorem B404927 : Blo 267823 404927 := bstep (se 1 (by rfl) ⟨303695, by rfl⟩ : syracuseStep 404927 = 607391) B607391
theorem B2320271 : Blo 267823 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B263254153 : Blo 267823 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B913895 : Blo 267823 913895 := bstep (se 1 (by rfl) ⟨685421, by rfl⟩ : syracuseStep 913895 = 1370843) B1370843
theorem B1546847 : Blo 267823 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B269951 : Blo 267823 269951 := bstep (se 1 (by rfl) ⟨202463, by rfl⟩ : syracuseStep 269951 = 404927) B404927
theorem B609263 : Blo 267823 609263 := bstep (se 1 (by rfl) ⟨456947, by rfl⟩ : syracuseStep 609263 = 913895) B913895
theorem B351005537 : Blo 267823 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B234003691 : Blo 267823 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B406175 : Blo 267823 406175 := bstep (se 1 (by rfl) ⟨304631, by rfl⟩ : syracuseStep 406175 = 609263) B609263
theorem B1031231 : Blo 267823 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B270783 : Blo 267823 270783 := bstep (se 1 (by rfl) ⟨203087, by rfl⟩ : syracuseStep 270783 = 406175) B406175
theorem B312004921 : Blo 267823 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B687487 : Blo 267823 687487 := bstep (se 1 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 687487 = 1031231) B1031231
theorem B416006561 : Blo 267823 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B916649 : Blo 267823 916649 := bstep (se 2 (by rfl) ⟨343743, by rfl⟩ : syracuseStep 916649 = 687487) B687487
theorem B611099 : Blo 267823 611099 := bstep (se 1 (by rfl) ⟨458324, by rfl⟩ : syracuseStep 611099 = 916649) B916649
theorem B1109350829 : Blo 267823 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B407399 : Blo 267823 407399 := bstep (se 1 (by rfl) ⟨305549, by rfl⟩ : syracuseStep 407399 = 611099) B611099
theorem B739567219 : Blo 267823 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 267823 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B271599 : Blo 267823 271599 := bstep (se 1 (by rfl) ⟨203699, by rfl⟩ : syracuseStep 271599 = 407399) B407399
theorem B657393083 : Blo 267823 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B438262055 : Blo 267823 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B292174703 : Blo 267823 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 267823 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B519421693 : Blo 267823 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 267823 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B461708171 : Blo 267823 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B307805447 : Blo 267823 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B205203631 : Blo 267823 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B273604841 : Blo 267823 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B182403227 : Blo 267823 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 267823 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B648544805 : Blo 267823 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B432363203 : Blo 267823 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 267823 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 267823 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 267823 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 267823 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 267823 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 267823 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 267823 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 267823 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 267823 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 267823 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 267823 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 267823 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 267823 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 267823 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 267823 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 267823 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 267823 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 267823 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 267823 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 267823 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 267823 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 267823 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 267823 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 267823 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 267823 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 267823 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B1948157 : Blo 267823 1948157 := bstep (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) B730559
theorem B1298771 : Blo 267823 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B865847 : Blo 267823 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B2308925 : Blo 267823 2308925 := bstep (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) B865847
theorem B1539283 : Blo 267823 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B2052377 : Blo 267823 2052377 := bstep (se 2 (by rfl) ⟨769641, by rfl⟩ : syracuseStep 2052377 = 1539283) B1539283
theorem B1368251 : Blo 267823 1368251 := bstep (se 1 (by rfl) ⟨1026188, by rfl⟩ : syracuseStep 1368251 = 2052377) B2052377
theorem B912167 : Blo 267823 912167 := bstep (se 1 (by rfl) ⟨684125, by rfl⟩ : syracuseStep 912167 = 1368251) B1368251
theorem B608111 : Blo 267823 608111 := bstep (se 1 (by rfl) ⟨456083, by rfl⟩ : syracuseStep 608111 = 912167) B912167
theorem B405407 : Blo 267823 405407 := bstep (se 1 (by rfl) ⟨304055, by rfl⟩ : syracuseStep 405407 = 608111) B608111
theorem B270271 : Blo 267823 270271 := bstep (se 1 (by rfl) ⟨202703, by rfl⟩ : syracuseStep 270271 = 405407) B405407

theorem C0 (j : ℕ) (h1 : 66955 ≤ j) (h2 : j ≤ 67654) : Blo 267823 (4 * j + 3) := by
  interval_cases j
  · exact B267823
  · exact B267827
  · exact B267831
  · exact B267835
  · exact B267839
  · exact B267843
  · exact B267847
  · exact B267851
  · exact B267855
  · exact B267859
  · exact B267863
  · exact B267867
  · exact B267871
  · exact B267875
  · exact B267879
  · exact B267883
  · exact B267887
  · exact B267891
  · exact B267895
  · exact B267899
  · exact B267903
  · exact B267907
  · exact B267911
  · exact B267915
  · exact B267919
  · exact B267923
  · exact B267927
  · exact B267931
  · exact B267935
  · exact B267939
  · exact B267943
  · exact B267947
  · exact B267951
  · exact B267955
  · exact B267959
  · exact B267963
  · exact B267967
  · exact B267971
  · exact B267975
  · exact B267979
  · exact B267983
  · exact B267987
  · exact B267991
  · exact B267995
  · exact B267999
  · exact B268003
  · exact B268007
  · exact B268011
  · exact B268015
  · exact B268019
  · exact B268023
  · exact B268027
  · exact B268031
  · exact B268035
  · exact B268039
  · exact B268043
  · exact B268047
  · exact B268051
  · exact B268055
  · exact B268059
  · exact B268063
  · exact B268067
  · exact B268071
  · exact B268075
  · exact B268079
  · exact B268083
  · exact B268087
  · exact B268091
  · exact B268095
  · exact B268099
  · exact B268103
  · exact B268107
  · exact B268111
  · exact B268115
  · exact B268119
  · exact B268123
  · exact B268127
  · exact B268131
  · exact B268135
  · exact B268139
  · exact B268143
  · exact B268147
  · exact B268151
  · exact B268155
  · exact B268159
  · exact B268163
  · exact B268167
  · exact B268171
  · exact B268175
  · exact B268179
  · exact B268183
  · exact B268187
  · exact B268191
  · exact B268195
  · exact B268199
  · exact B268203
  · exact B268207
  · exact B268211
  · exact B268215
  · exact B268219
  · exact B268223
  · exact B268227
  · exact B268231
  · exact B268235
  · exact B268239
  · exact B268243
  · exact B268247
  · exact B268251
  · exact B268255
  · exact B268259
  · exact B268263
  · exact B268267
  · exact B268271
  · exact B268275
  · exact B268279
  · exact B268283
  · exact B268287
  · exact B268291
  · exact B268295
  · exact B268299
  · exact B268303
  · exact B268307
  · exact B268311
  · exact B268315
  · exact B268319
  · exact B268323
  · exact B268327
  · exact B268331
  · exact B268335
  · exact B268339
  · exact B268343
  · exact B268347
  · exact B268351
  · exact B268355
  · exact B268359
  · exact B268363
  · exact B268367
  · exact B268371
  · exact B268375
  · exact B268379
  · exact B268383
  · exact B268387
  · exact B268391
  · exact B268395
  · exact B268399
  · exact B268403
  · exact B268407
  · exact B268411
  · exact B268415
  · exact B268419
  · exact B268423
  · exact B268427
  · exact B268431
  · exact B268435
  · exact B268439
  · exact B268443
  · exact B268447
  · exact B268451
  · exact B268455
  · exact B268459
  · exact B268463
  · exact B268467
  · exact B268471
  · exact B268475
  · exact B268479
  · exact B268483
  · exact B268487
  · exact B268491
  · exact B268495
  · exact B268499
  · exact B268503
  · exact B268507
  · exact B268511
  · exact B268515
  · exact B268519
  · exact B268523
  · exact B268527
  · exact B268531
  · exact B268535
  · exact B268539
  · exact B268543
  · exact B268547
  · exact B268551
  · exact B268555
  · exact B268559
  · exact B268563
  · exact B268567
  · exact B268571
  · exact B268575
  · exact B268579
  · exact B268583
  · exact B268587
  · exact B268591
  · exact B268595
  · exact B268599
  · exact B268603
  · exact B268607
  · exact B268611
  · exact B268615
  · exact B268619
  · exact B268623
  · exact B268627
  · exact B268631
  · exact B268635
  · exact B268639
  · exact B268643
  · exact B268647
  · exact B268651
  · exact B268655
  · exact B268659
  · exact B268663
  · exact B268667
  · exact B268671
  · exact B268675
  · exact B268679
  · exact B268683
  · exact B268687
  · exact B268691
  · exact B268695
  · exact B268699
  · exact B268703
  · exact B268707
  · exact B268711
  · exact B268715
  · exact B268719
  · exact B268723
  · exact B268727
  · exact B268731
  · exact B268735
  · exact B268739
  · exact B268743
  · exact B268747
  · exact B268751
  · exact B268755
  · exact B268759
  · exact B268763
  · exact B268767
  · exact B268771
  · exact B268775
  · exact B268779
  · exact B268783
  · exact B268787
  · exact B268791
  · exact B268795
  · exact B268799
  · exact B268803
  · exact B268807
  · exact B268811
  · exact B268815
  · exact B268819
  · exact B268823
  · exact B268827
  · exact B268831
  · exact B268835
  · exact B268839
  · exact B268843
  · exact B268847
  · exact B268851
  · exact B268855
  · exact B268859
  · exact B268863
  · exact B268867
  · exact B268871
  · exact B268875
  · exact B268879
  · exact B268883
  · exact B268887
  · exact B268891
  · exact B268895
  · exact B268899
  · exact B268903
  · exact B268907
  · exact B268911
  · exact B268915
  · exact B268919
  · exact B268923
  · exact B268927
  · exact B268931
  · exact B268935
  · exact B268939
  · exact B268943
  · exact B268947
  · exact B268951
  · exact B268955
  · exact B268959
  · exact B268963
  · exact B268967
  · exact B268971
  · exact B268975
  · exact B268979
  · exact B268983
  · exact B268987
  · exact B268991
  · exact B268995
  · exact B268999
  · exact B269003
  · exact B269007
  · exact B269011
  · exact B269015
  · exact B269019
  · exact B269023
  · exact B269027
  · exact B269031
  · exact B269035
  · exact B269039
  · exact B269043
  · exact B269047
  · exact B269051
  · exact B269055
  · exact B269059
  · exact B269063
  · exact B269067
  · exact B269071
  · exact B269075
  · exact B269079
  · exact B269083
  · exact B269087
  · exact B269091
  · exact B269095
  · exact B269099
  · exact B269103
  · exact B269107
  · exact B269111
  · exact B269115
  · exact B269119
  · exact B269123
  · exact B269127
  · exact B269131
  · exact B269135
  · exact B269139
  · exact B269143
  · exact B269147
  · exact B269151
  · exact B269155
  · exact B269159
  · exact B269163
  · exact B269167
  · exact B269171
  · exact B269175
  · exact B269179
  · exact B269183
  · exact B269187
  · exact B269191
  · exact B269195
  · exact B269199
  · exact B269203
  · exact B269207
  · exact B269211
  · exact B269215
  · exact B269219
  · exact B269223
  · exact B269227
  · exact B269231
  · exact B269235
  · exact B269239
  · exact B269243
  · exact B269247
  · exact B269251
  · exact B269255
  · exact B269259
  · exact B269263
  · exact B269267
  · exact B269271
  · exact B269275
  · exact B269279
  · exact B269283
  · exact B269287
  · exact B269291
  · exact B269295
  · exact B269299
  · exact B269303
  · exact B269307
  · exact B269311
  · exact B269315
  · exact B269319
  · exact B269323
  · exact B269327
  · exact B269331
  · exact B269335
  · exact B269339
  · exact B269343
  · exact B269347
  · exact B269351
  · exact B269355
  · exact B269359
  · exact B269363
  · exact B269367
  · exact B269371
  · exact B269375
  · exact B269379
  · exact B269383
  · exact B269387
  · exact B269391
  · exact B269395
  · exact B269399
  · exact B269403
  · exact B269407
  · exact B269411
  · exact B269415
  · exact B269419
  · exact B269423
  · exact B269427
  · exact B269431
  · exact B269435
  · exact B269439
  · exact B269443
  · exact B269447
  · exact B269451
  · exact B269455
  · exact B269459
  · exact B269463
  · exact B269467
  · exact B269471
  · exact B269475
  · exact B269479
  · exact B269483
  · exact B269487
  · exact B269491
  · exact B269495
  · exact B269499
  · exact B269503
  · exact B269507
  · exact B269511
  · exact B269515
  · exact B269519
  · exact B269523
  · exact B269527
  · exact B269531
  · exact B269535
  · exact B269539
  · exact B269543
  · exact B269547
  · exact B269551
  · exact B269555
  · exact B269559
  · exact B269563
  · exact B269567
  · exact B269571
  · exact B269575
  · exact B269579
  · exact B269583
  · exact B269587
  · exact B269591
  · exact B269595
  · exact B269599
  · exact B269603
  · exact B269607
  · exact B269611
  · exact B269615
  · exact B269619
  · exact B269623
  · exact B269627
  · exact B269631
  · exact B269635
  · exact B269639
  · exact B269643
  · exact B269647
  · exact B269651
  · exact B269655
  · exact B269659
  · exact B269663
  · exact B269667
  · exact B269671
  · exact B269675
  · exact B269679
  · exact B269683
  · exact B269687
  · exact B269691
  · exact B269695
  · exact B269699
  · exact B269703
  · exact B269707
  · exact B269711
  · exact B269715
  · exact B269719
  · exact B269723
  · exact B269727
  · exact B269731
  · exact B269735
  · exact B269739
  · exact B269743
  · exact B269747
  · exact B269751
  · exact B269755
  · exact B269759
  · exact B269763
  · exact B269767
  · exact B269771
  · exact B269775
  · exact B269779
  · exact B269783
  · exact B269787
  · exact B269791
  · exact B269795
  · exact B269799
  · exact B269803
  · exact B269807
  · exact B269811
  · exact B269815
  · exact B269819
  · exact B269823
  · exact B269827
  · exact B269831
  · exact B269835
  · exact B269839
  · exact B269843
  · exact B269847
  · exact B269851
  · exact B269855
  · exact B269859
  · exact B269863
  · exact B269867
  · exact B269871
  · exact B269875
  · exact B269879
  · exact B269883
  · exact B269887
  · exact B269891
  · exact B269895
  · exact B269899
  · exact B269903
  · exact B269907
  · exact B269911
  · exact B269915
  · exact B269919
  · exact B269923
  · exact B269927
  · exact B269931
  · exact B269935
  · exact B269939
  · exact B269943
  · exact B269947
  · exact B269951
  · exact B269955
  · exact B269959
  · exact B269963
  · exact B269967
  · exact B269971
  · exact B269975
  · exact B269979
  · exact B269983
  · exact B269987
  · exact B269991
  · exact B269995
  · exact B269999
  · exact B270003
  · exact B270007
  · exact B270011
  · exact B270015
  · exact B270019
  · exact B270023
  · exact B270027
  · exact B270031
  · exact B270035
  · exact B270039
  · exact B270043
  · exact B270047
  · exact B270051
  · exact B270055
  · exact B270059
  · exact B270063
  · exact B270067
  · exact B270071
  · exact B270075
  · exact B270079
  · exact B270083
  · exact B270087
  · exact B270091
  · exact B270095
  · exact B270099
  · exact B270103
  · exact B270107
  · exact B270111
  · exact B270115
  · exact B270119
  · exact B270123
  · exact B270127
  · exact B270131
  · exact B270135
  · exact B270139
  · exact B270143
  · exact B270147
  · exact B270151
  · exact B270155
  · exact B270159
  · exact B270163
  · exact B270167
  · exact B270171
  · exact B270175
  · exact B270179
  · exact B270183
  · exact B270187
  · exact B270191
  · exact B270195
  · exact B270199
  · exact B270203
  · exact B270207
  · exact B270211
  · exact B270215
  · exact B270219
  · exact B270223
  · exact B270227
  · exact B270231
  · exact B270235
  · exact B270239
  · exact B270243
  · exact B270247
  · exact B270251
  · exact B270255
  · exact B270259
  · exact B270263
  · exact B270267
  · exact B270271
  · exact B270275
  · exact B270279
  · exact B270283
  · exact B270287
  · exact B270291
  · exact B270295
  · exact B270299
  · exact B270303
  · exact B270307
  · exact B270311
  · exact B270315
  · exact B270319
  · exact B270323
  · exact B270327
  · exact B270331
  · exact B270335
  · exact B270339
  · exact B270343
  · exact B270347
  · exact B270351
  · exact B270355
  · exact B270359
  · exact B270363
  · exact B270367
  · exact B270371
  · exact B270375
  · exact B270379
  · exact B270383
  · exact B270387
  · exact B270391
  · exact B270395
  · exact B270399
  · exact B270403
  · exact B270407
  · exact B270411
  · exact B270415
  · exact B270419
  · exact B270423
  · exact B270427
  · exact B270431
  · exact B270435
  · exact B270439
  · exact B270443
  · exact B270447
  · exact B270451
  · exact B270455
  · exact B270459
  · exact B270463
  · exact B270467
  · exact B270471
  · exact B270475
  · exact B270479
  · exact B270483
  · exact B270487
  · exact B270491
  · exact B270495
  · exact B270499
  · exact B270503
  · exact B270507
  · exact B270511
  · exact B270515
  · exact B270519
  · exact B270523
  · exact B270527
  · exact B270531
  · exact B270535
  · exact B270539
  · exact B270543
  · exact B270547
  · exact B270551
  · exact B270555
  · exact B270559
  · exact B270563
  · exact B270567
  · exact B270571
  · exact B270575
  · exact B270579
  · exact B270583
  · exact B270587
  · exact B270591
  · exact B270595
  · exact B270599
  · exact B270603
  · exact B270607
  · exact B270611
  · exact B270615
  · exact B270619

theorem C1 (j : ℕ) (h1 : 67655 ≤ j) (h2 : j ≤ 67955) : Blo 267823 (4 * j + 3) := by
  interval_cases j
  · exact B270623
  · exact B270627
  · exact B270631
  · exact B270635
  · exact B270639
  · exact B270643
  · exact B270647
  · exact B270651
  · exact B270655
  · exact B270659
  · exact B270663
  · exact B270667
  · exact B270671
  · exact B270675
  · exact B270679
  · exact B270683
  · exact B270687
  · exact B270691
  · exact B270695
  · exact B270699
  · exact B270703
  · exact B270707
  · exact B270711
  · exact B270715
  · exact B270719
  · exact B270723
  · exact B270727
  · exact B270731
  · exact B270735
  · exact B270739
  · exact B270743
  · exact B270747
  · exact B270751
  · exact B270755
  · exact B270759
  · exact B270763
  · exact B270767
  · exact B270771
  · exact B270775
  · exact B270779
  · exact B270783
  · exact B270787
  · exact B270791
  · exact B270795
  · exact B270799
  · exact B270803
  · exact B270807
  · exact B270811
  · exact B270815
  · exact B270819
  · exact B270823
  · exact B270827
  · exact B270831
  · exact B270835
  · exact B270839
  · exact B270843
  · exact B270847
  · exact B270851
  · exact B270855
  · exact B270859
  · exact B270863
  · exact B270867
  · exact B270871
  · exact B270875
  · exact B270879
  · exact B270883
  · exact B270887
  · exact B270891
  · exact B270895
  · exact B270899
  · exact B270903
  · exact B270907
  · exact B270911
  · exact B270915
  · exact B270919
  · exact B270923
  · exact B270927
  · exact B270931
  · exact B270935
  · exact B270939
  · exact B270943
  · exact B270947
  · exact B270951
  · exact B270955
  · exact B270959
  · exact B270963
  · exact B270967
  · exact B270971
  · exact B270975
  · exact B270979
  · exact B270983
  · exact B270987
  · exact B270991
  · exact B270995
  · exact B270999
  · exact B271003
  · exact B271007
  · exact B271011
  · exact B271015
  · exact B271019
  · exact B271023
  · exact B271027
  · exact B271031
  · exact B271035
  · exact B271039
  · exact B271043
  · exact B271047
  · exact B271051
  · exact B271055
  · exact B271059
  · exact B271063
  · exact B271067
  · exact B271071
  · exact B271075
  · exact B271079
  · exact B271083
  · exact B271087
  · exact B271091
  · exact B271095
  · exact B271099
  · exact B271103
  · exact B271107
  · exact B271111
  · exact B271115
  · exact B271119
  · exact B271123
  · exact B271127
  · exact B271131
  · exact B271135
  · exact B271139
  · exact B271143
  · exact B271147
  · exact B271151
  · exact B271155
  · exact B271159
  · exact B271163
  · exact B271167
  · exact B271171
  · exact B271175
  · exact B271179
  · exact B271183
  · exact B271187
  · exact B271191
  · exact B271195
  · exact B271199
  · exact B271203
  · exact B271207
  · exact B271211
  · exact B271215
  · exact B271219
  · exact B271223
  · exact B271227
  · exact B271231
  · exact B271235
  · exact B271239
  · exact B271243
  · exact B271247
  · exact B271251
  · exact B271255
  · exact B271259
  · exact B271263
  · exact B271267
  · exact B271271
  · exact B271275
  · exact B271279
  · exact B271283
  · exact B271287
  · exact B271291
  · exact B271295
  · exact B271299
  · exact B271303
  · exact B271307
  · exact B271311
  · exact B271315
  · exact B271319
  · exact B271323
  · exact B271327
  · exact B271331
  · exact B271335
  · exact B271339
  · exact B271343
  · exact B271347
  · exact B271351
  · exact B271355
  · exact B271359
  · exact B271363
  · exact B271367
  · exact B271371
  · exact B271375
  · exact B271379
  · exact B271383
  · exact B271387
  · exact B271391
  · exact B271395
  · exact B271399
  · exact B271403
  · exact B271407
  · exact B271411
  · exact B271415
  · exact B271419
  · exact B271423
  · exact B271427
  · exact B271431
  · exact B271435
  · exact B271439
  · exact B271443
  · exact B271447
  · exact B271451
  · exact B271455
  · exact B271459
  · exact B271463
  · exact B271467
  · exact B271471
  · exact B271475
  · exact B271479
  · exact B271483
  · exact B271487
  · exact B271491
  · exact B271495
  · exact B271499
  · exact B271503
  · exact B271507
  · exact B271511
  · exact B271515
  · exact B271519
  · exact B271523
  · exact B271527
  · exact B271531
  · exact B271535
  · exact B271539
  · exact B271543
  · exact B271547
  · exact B271551
  · exact B271555
  · exact B271559
  · exact B271563
  · exact B271567
  · exact B271571
  · exact B271575
  · exact B271579
  · exact B271583
  · exact B271587
  · exact B271591
  · exact B271595
  · exact B271599
  · exact B271603
  · exact B271607
  · exact B271611
  · exact B271615
  · exact B271619
  · exact B271623
  · exact B271627
  · exact B271631
  · exact B271635
  · exact B271639
  · exact B271643
  · exact B271647
  · exact B271651
  · exact B271655
  · exact B271659
  · exact B271663
  · exact B271667
  · exact B271671
  · exact B271675
  · exact B271679
  · exact B271683
  · exact B271687
  · exact B271691
  · exact B271695
  · exact B271699
  · exact B271703
  · exact B271707
  · exact B271711
  · exact B271715
  · exact B271719
  · exact B271723
  · exact B271727
  · exact B271731
  · exact B271735
  · exact B271739
  · exact B271743
  · exact B271747
  · exact B271751
  · exact B271755
  · exact B271759
  · exact B271763
  · exact B271767
  · exact B271771
  · exact B271775
  · exact B271779
  · exact B271783
  · exact B271787
  · exact B271791
  · exact B271795
  · exact B271799
  · exact B271803
  · exact B271807
  · exact B271811
  · exact B271815
  · exact B271819
  · exact B271823

theorem solution (m : ℕ) (hlo : 267823 ≤ m) (hhi : m ≤ 271823) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 66955 ≤ j := by omega
    have hj2 : j ≤ 67955 := by omega
    have hb : Blo 267823 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 67655 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
