-- Prove2me | solution 1 for syracuse_descends_range_1289963_1291963
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:22.748771+00:00
-- url     : https://prove2.me/submissions/f7d20088-62e7-47d7-aad5-64b39dfad2b6

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


theorem B2015237 : Blo 1289963 2015237 := bbase (se 4 (by rfl) ⟨188928, by rfl⟩ : syracuseStep 2015237 = 377857) (by norm_num)
theorem B3268613 : Blo 1289963 3268613 := bbase (se 4 (by rfl) ⟨306432, by rfl⟩ : syracuseStep 3268613 = 612865) (by norm_num)
theorem B2179109 : Blo 1289963 2179109 := bbase (se 4 (by rfl) ⟨204291, by rfl⟩ : syracuseStep 2179109 = 408583) (by norm_num)
theorem B2179237 : Blo 1289963 2179237 := bbase (se 4 (by rfl) ⟨204303, by rfl⟩ : syracuseStep 2179237 = 408607) (by norm_num)
theorem B2179325 : Blo 1289963 2179325 := bbase (se 3 (by rfl) ⟨408623, by rfl⟩ : syracuseStep 2179325 = 817247) (by norm_num)
theorem B6537509 : Blo 1289963 6537509 := bbase (se 4 (by rfl) ⟨612891, by rfl⟩ : syracuseStep 6537509 = 1225783) (by norm_num)
theorem B3268957 : Blo 1289963 3268957 := bbase (se 3 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 3268957 = 1225859) (by norm_num)
theorem B4358501 : Blo 1289963 4358501 := bbase (se 4 (by rfl) ⟨408609, by rfl⟩ : syracuseStep 4358501 = 817219) (by norm_num)
theorem B2179453 : Blo 1289963 2179453 := bbase (se 3 (by rfl) ⟨408647, by rfl⟩ : syracuseStep 2179453 = 817295) (by norm_num)
theorem B3269069 : Blo 1289963 3269069 := bbase (se 3 (by rfl) ⟨612950, by rfl⟩ : syracuseStep 3269069 = 1225901) (by norm_num)
theorem B2179541 : Blo 1289963 2179541 := bbase (se 7 (by rfl) ⟨25541, by rfl⟩ : syracuseStep 2179541 = 51083) (by norm_num)
theorem B9306677 : Blo 1289963 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B5972549 : Blo 1289963 5972549 := bbase (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) (by norm_num)
theorem B2179669 : Blo 1289963 2179669 := bbase (se 8 (by rfl) ⟨12771, by rfl⟩ : syracuseStep 2179669 = 25543) (by norm_num)
theorem B3678853 : Blo 1289963 3678853 := bbase (se 4 (by rfl) ⟨344892, by rfl⟩ : syracuseStep 3678853 = 689785) (by norm_num)
theorem B3269261 : Blo 1289963 3269261 := bbase (se 3 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 3269261 = 1225973) (by norm_num)
theorem B2179757 : Blo 1289963 2179757 := bbase (se 3 (by rfl) ⟨408704, by rfl⟩ : syracuseStep 2179757 = 817409) (by norm_num)
theorem B2450101 : Blo 1289963 2450101 := bbase (se 5 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 2450101 = 229697) (by norm_num)
theorem B4358933 : Blo 1289963 4358933 := bbase (se 6 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 4358933 = 204325) (by norm_num)
theorem B3679013 : Blo 1289963 3679013 := bbase (se 4 (by rfl) ⟨344907, by rfl⟩ : syracuseStep 3679013 = 689815) (by norm_num)
theorem B2179885 : Blo 1289963 2179885 := bbase (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) (by norm_num)
theorem B2450245 : Blo 1289963 2450245 := bbase (se 4 (by rfl) ⟨229710, by rfl⟩ : syracuseStep 2450245 = 459421) (by norm_num)
theorem B2179973 : Blo 1289963 2179973 := bbase (se 4 (by rfl) ⟨204372, by rfl⟩ : syracuseStep 2179973 = 408745) (by norm_num)
theorem B4137941 : Blo 1289963 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B2450405 : Blo 1289963 2450405 := bbase (se 4 (by rfl) ⟨229725, by rfl⟩ : syracuseStep 2450405 = 459451) (by norm_num)
theorem B3269605 : Blo 1289963 3269605 := bbase (se 4 (by rfl) ⟨306525, by rfl⟩ : syracuseStep 3269605 = 613051) (by norm_num)
theorem B2327549 : Blo 1289963 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B2180101 : Blo 1289963 2180101 := bbase (se 4 (by rfl) ⟨204384, by rfl⟩ : syracuseStep 2180101 = 408769) (by norm_num)
theorem B10462229 : Blo 1289963 10462229 := bbase (se 6 (by rfl) ⟨245208, by rfl⟩ : syracuseStep 10462229 = 490417) (by norm_num)
theorem B6202453 : Blo 1289963 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B3269717 : Blo 1289963 3269717 := bbase (se 8 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 3269717 = 38317) (by norm_num)
theorem B2180189 : Blo 1289963 2180189 := bbase (se 3 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 2180189 = 817571) (by norm_num)
theorem B2450549 : Blo 1289963 2450549 := bbase (se 5 (by rfl) ⟨114869, by rfl⟩ : syracuseStep 2450549 = 229739) (by norm_num)
theorem B8275061 : Blo 1289963 8275061 := bbase (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) (by norm_num)
theorem B4899973 : Blo 1289963 4899973 := bbase (se 4 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 4899973 = 918745) (by norm_num)
theorem B4654261 : Blo 1289963 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B4359365 : Blo 1289963 4359365 := bbase (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) (by norm_num)
theorem B1451209 : Blo 1289963 1451209 := bbase (se 2 (by rfl) ⟨544203, by rfl⟩ : syracuseStep 1451209 = 1088407) (by norm_num)
theorem B1451245 : Blo 1289963 1451245 := bbase (se 3 (by rfl) ⟨272108, by rfl⟩ : syracuseStep 1451245 = 544217) (by norm_num)
theorem B1377533 : Blo 1289963 1377533 := bbase (se 3 (by rfl) ⟨258287, by rfl⟩ : syracuseStep 1377533 = 516575) (by norm_num)
theorem B1451281 : Blo 1289963 1451281 := bbase (se 2 (by rfl) ⟨544230, by rfl⟩ : syracuseStep 1451281 = 1088461) (by norm_num)
theorem B3269909 : Blo 1289963 3269909 := bbase (se 6 (by rfl) ⟨76638, by rfl⟩ : syracuseStep 3269909 = 153277) (by norm_num)
theorem B1451317 : Blo 1289963 1451317 := bbase (se 5 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 1451317 = 136061) (by norm_num)
theorem B1377605 : Blo 1289963 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B1451353 : Blo 1289963 1451353 := bbase (se 2 (by rfl) ⟨544257, by rfl⟩ : syracuseStep 1451353 = 1088515) (by norm_num)
theorem B1451389 : Blo 1289963 1451389 := bbase (se 3 (by rfl) ⟨272135, by rfl⟩ : syracuseStep 1451389 = 544271) (by norm_num)
theorem B2450837 : Blo 1289963 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B1451425 : Blo 1289963 1451425 := bbase (se 2 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 1451425 = 1088569) (by norm_num)
theorem B4900277 : Blo 1289963 4900277 := bbase (se 5 (by rfl) ⟨229700, by rfl⟩ : syracuseStep 4900277 = 459401) (by norm_num)
theorem B1451461 : Blo 1289963 1451461 := bbase (se 4 (by rfl) ⟨136074, by rfl⟩ : syracuseStep 1451461 = 272149) (by norm_num)
theorem B2516437 : Blo 1289963 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B1451497 : Blo 1289963 1451497 := bbase (se 2 (by rfl) ⟨544311, by rfl⟩ : syracuseStep 1451497 = 1088623) (by norm_num)
theorem B2328053 : Blo 1289963 2328053 := bbase (se 5 (by rfl) ⟨109127, by rfl⟩ : syracuseStep 2328053 = 218255) (by norm_num)
theorem B1377793 : Blo 1289963 1377793 := bbase (se 2 (by rfl) ⟨516672, by rfl⟩ : syracuseStep 1377793 = 1033345) (by norm_num)
theorem B1451533 : Blo 1289963 1451533 := bbase (se 3 (by rfl) ⟨272162, by rfl⟩ : syracuseStep 1451533 = 544325) (by norm_num)
theorem B2450989 : Blo 1289963 2450989 := bbase (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) (by norm_num)
theorem B1451569 : Blo 1289963 1451569 := bbase (se 2 (by rfl) ⟨544338, by rfl⟩ : syracuseStep 1451569 = 1088677) (by norm_num)
theorem B6538805 : Blo 1289963 6538805 := bbase (se 5 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 6538805 = 613013) (by norm_num)
theorem B1451605 : Blo 1289963 1451605 := bbase (se 8 (by rfl) ⟨8505, by rfl⟩ : syracuseStep 1451605 = 17011) (by norm_num)
theorem B23881301 : Blo 1289963 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B1934957 : Blo 1289963 1934957 := bbase (se 3 (by rfl) ⟨362804, by rfl⟩ : syracuseStep 1934957 = 725609) (by norm_num)
theorem B3270253 : Blo 1289963 3270253 := bbase (se 3 (by rfl) ⟨613172, by rfl⟩ : syracuseStep 3270253 = 1226345) (by norm_num)
theorem B4359797 : Blo 1289963 4359797 := bbase (se 5 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 4359797 = 408731) (by norm_num)
theorem B1451641 : Blo 1289963 1451641 := bbase (se 2 (by rfl) ⟨544365, by rfl⟩ : syracuseStep 1451641 = 1088731) (by norm_num)
theorem B1934981 : Blo 1289963 1934981 := bbase (se 4 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 1934981 = 362809) (by norm_num)
theorem B1935005 : Blo 1289963 1935005 := bbase (se 3 (by rfl) ⟨362813, by rfl⟩ : syracuseStep 1935005 = 725627) (by norm_num)
theorem B1451677 : Blo 1289963 1451677 := bbase (se 3 (by rfl) ⟨272189, by rfl⟩ : syracuseStep 1451677 = 544379) (by norm_num)
theorem B1935029 : Blo 1289963 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B1377977 : Blo 1289963 1377977 := bbase (se 2 (by rfl) ⟨516741, by rfl⟩ : syracuseStep 1377977 = 1033483) (by norm_num)
theorem B1451713 : Blo 1289963 1451713 := bbase (se 2 (by rfl) ⟨544392, by rfl⟩ : syracuseStep 1451713 = 1088785) (by norm_num)
theorem B1935053 : Blo 1289963 1935053 := bbase (se 3 (by rfl) ⟨362822, by rfl⟩ : syracuseStep 1935053 = 725645) (by norm_num)
theorem B11175637 : Blo 1289963 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B1935077 : Blo 1289963 1935077 := bbase (se 4 (by rfl) ⟨181413, by rfl⟩ : syracuseStep 1935077 = 362827) (by norm_num)
theorem B1451749 : Blo 1289963 1451749 := bbase (se 4 (by rfl) ⟨136101, by rfl⟩ : syracuseStep 1451749 = 272203) (by norm_num)
theorem B1935101 : Blo 1289963 1935101 := bbase (se 3 (by rfl) ⟨362831, by rfl⟩ : syracuseStep 1935101 = 725663) (by norm_num)
theorem B1451785 : Blo 1289963 1451785 := bbase (se 2 (by rfl) ⟨544419, by rfl⟩ : syracuseStep 1451785 = 1088839) (by norm_num)
theorem B1935125 : Blo 1289963 1935125 := bbase (se 6 (by rfl) ⟨45354, by rfl⟩ : syracuseStep 1935125 = 90709) (by norm_num)
theorem B1935149 : Blo 1289963 1935149 := bbase (se 3 (by rfl) ⟨362840, by rfl⟩ : syracuseStep 1935149 = 725681) (by norm_num)
theorem B1451821 : Blo 1289963 1451821 := bbase (se 3 (by rfl) ⟨272216, by rfl⟩ : syracuseStep 1451821 = 544433) (by norm_num)
theorem B1935173 : Blo 1289963 1935173 := bbase (se 4 (by rfl) ⟨181422, by rfl⟩ : syracuseStep 1935173 = 362845) (by norm_num)
theorem B1451857 : Blo 1289963 1451857 := bbase (se 2 (by rfl) ⟨544446, by rfl⟩ : syracuseStep 1451857 = 1088893) (by norm_num)
theorem B1935197 : Blo 1289963 1935197 := bbase (se 3 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 1935197 = 725699) (by norm_num)
theorem B2451293 : Blo 1289963 2451293 := bbase (se 3 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 2451293 = 919235) (by norm_num)
theorem B1451893 : Blo 1289963 1451893 := bbase (se 5 (by rfl) ⟨68057, by rfl⟩ : syracuseStep 1451893 = 136115) (by norm_num)
theorem B1935221 : Blo 1289963 1935221 := bbase (se 5 (by rfl) ⟨90713, by rfl⟩ : syracuseStep 1935221 = 181427) (by norm_num)
theorem B1935245 : Blo 1289963 1935245 := bbase (se 3 (by rfl) ⟨362858, by rfl⟩ : syracuseStep 1935245 = 725717) (by norm_num)
theorem B1451929 : Blo 1289963 1451929 := bbase (se 2 (by rfl) ⟨544473, by rfl⟩ : syracuseStep 1451929 = 1088947) (by norm_num)
theorem B1935269 : Blo 1289963 1935269 := bbase (se 4 (by rfl) ⟨181431, by rfl⟩ : syracuseStep 1935269 = 362863) (by norm_num)
theorem B2066357 : Blo 1289963 2066357 := bbase (se 5 (by rfl) ⟨96860, by rfl⟩ : syracuseStep 2066357 = 193721) (by norm_num)
theorem B1935293 : Blo 1289963 1935293 := bbase (se 3 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 1935293 = 725735) (by norm_num)
theorem B1451965 : Blo 1289963 1451965 := bbase (se 3 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 1451965 = 544487) (by norm_num)
theorem B6531029 : Blo 1289963 6531029 := bbase (se 7 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 6531029 = 153071) (by norm_num)
theorem B1935317 : Blo 1289963 1935317 := bbase (se 7 (by rfl) ⟨22679, by rfl⟩ : syracuseStep 1935317 = 45359) (by norm_num)
theorem B1452001 : Blo 1289963 1452001 := bbase (se 2 (by rfl) ⟨544500, by rfl⟩ : syracuseStep 1452001 = 1089001) (by norm_num)
theorem B1935341 : Blo 1289963 1935341 := bbase (se 3 (by rfl) ⟨362876, by rfl⟩ : syracuseStep 1935341 = 725753) (by norm_num)
theorem B1935365 : Blo 1289963 1935365 := bbase (se 4 (by rfl) ⟨181440, by rfl⟩ : syracuseStep 1935365 = 362881) (by norm_num)
theorem B1452037 : Blo 1289963 1452037 := bbase (se 4 (by rfl) ⟨136128, by rfl⟩ : syracuseStep 1452037 = 272257) (by norm_num)
theorem B1935389 : Blo 1289963 1935389 := bbase (se 3 (by rfl) ⟨362885, by rfl⟩ : syracuseStep 1935389 = 725771) (by norm_num)
theorem B4417573 : Blo 1289963 4417573 := bbase (se 4 (by rfl) ⟨414147, by rfl⟩ : syracuseStep 4417573 = 828295) (by norm_num)
theorem B4360229 : Blo 1289963 4360229 := bbase (se 4 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 4360229 = 817543) (by norm_num)
theorem B1452073 : Blo 1289963 1452073 := bbase (se 2 (by rfl) ⟨544527, by rfl⟩ : syracuseStep 1452073 = 1089055) (by norm_num)
theorem B2066485 : Blo 1289963 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1935413 : Blo 1289963 1935413 := bbase (se 5 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 1935413 = 181445) (by norm_num)
theorem B1935437 : Blo 1289963 1935437 := bbase (se 3 (by rfl) ⟨362894, by rfl⟩ : syracuseStep 1935437 = 725789) (by norm_num)
theorem B1452109 : Blo 1289963 1452109 := bbase (se 3 (by rfl) ⟨272270, by rfl⟩ : syracuseStep 1452109 = 544541) (by norm_num)
theorem B1935461 : Blo 1289963 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1452145 : Blo 1289963 1452145 := bbase (se 2 (by rfl) ⟨544554, by rfl⟩ : syracuseStep 1452145 = 1089109) (by norm_num)
theorem B1935485 : Blo 1289963 1935485 := bbase (se 3 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 1935485 = 725807) (by norm_num)
theorem B1935509 : Blo 1289963 1935509 := bbase (se 6 (by rfl) ⟨45363, by rfl⟩ : syracuseStep 1935509 = 90727) (by norm_num)
theorem B2943125 : Blo 1289963 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B5376149 : Blo 1289963 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1452181 : Blo 1289963 1452181 := bbase (se 6 (by rfl) ⟨34035, by rfl⟩ : syracuseStep 1452181 = 68071) (by norm_num)
theorem B1935533 : Blo 1289963 1935533 := bbase (se 3 (by rfl) ⟨362912, by rfl⟩ : syracuseStep 1935533 = 725825) (by norm_num)
theorem B1452217 : Blo 1289963 1452217 := bbase (se 2 (by rfl) ⟨544581, by rfl⟩ : syracuseStep 1452217 = 1089163) (by norm_num)
theorem B1935557 : Blo 1289963 1935557 := bbase (se 4 (by rfl) ⟨181458, by rfl⟩ : syracuseStep 1935557 = 362917) (by norm_num)
theorem B1935581 : Blo 1289963 1935581 := bbase (se 3 (by rfl) ⟨362921, by rfl⟩ : syracuseStep 1935581 = 725843) (by norm_num)
theorem B1452253 : Blo 1289963 1452253 := bbase (se 3 (by rfl) ⟨272297, by rfl⟩ : syracuseStep 1452253 = 544595) (by norm_num)
theorem B1935605 : Blo 1289963 1935605 := bbase (se 5 (by rfl) ⟨90731, by rfl⟩ : syracuseStep 1935605 = 181463) (by norm_num)
theorem B1452289 : Blo 1289963 1452289 := bbase (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) (by norm_num)
theorem B1935629 : Blo 1289963 1935629 := bbase (se 3 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 1935629 = 725861) (by norm_num)
theorem B1935653 : Blo 1289963 1935653 := bbase (se 4 (by rfl) ⟨181467, by rfl⟩ : syracuseStep 1935653 = 362935) (by norm_num)
theorem B1452325 : Blo 1289963 1452325 := bbase (se 4 (by rfl) ⟨136155, by rfl⟩ : syracuseStep 1452325 = 272311) (by norm_num)
theorem B1935677 : Blo 1289963 1935677 := bbase (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) (by norm_num)
theorem B4417861 : Blo 1289963 4417861 := bbase (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) (by norm_num)
theorem B1452361 : Blo 1289963 1452361 := bbase (se 2 (by rfl) ⟨544635, by rfl⟩ : syracuseStep 1452361 = 1089271) (by norm_num)
theorem B1935701 : Blo 1289963 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1935725 : Blo 1289963 1935725 := bbase (se 3 (by rfl) ⟨362948, by rfl⟩ : syracuseStep 1935725 = 725897) (by norm_num)
theorem B1452397 : Blo 1289963 1452397 := bbase (se 3 (by rfl) ⟨272324, by rfl⟩ : syracuseStep 1452397 = 544649) (by norm_num)
theorem B1935749 : Blo 1289963 1935749 := bbase (se 4 (by rfl) ⟨181476, by rfl⟩ : syracuseStep 1935749 = 362953) (by norm_num)
theorem B1452433 : Blo 1289963 1452433 := bbase (se 2 (by rfl) ⟨544662, by rfl⟩ : syracuseStep 1452433 = 1089325) (by norm_num)
theorem B1935773 : Blo 1289963 1935773 := bbase (se 3 (by rfl) ⟨362957, by rfl⟩ : syracuseStep 1935773 = 725915) (by norm_num)
theorem B1378729 : Blo 1289963 1378729 := bbase (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) (by norm_num)
theorem B2902445 : Blo 1289963 2902445 := bbase (se 3 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 2902445 = 1088417) (by norm_num)
theorem B1935797 : Blo 1289963 1935797 := bbase (se 5 (by rfl) ⟨90740, by rfl⟩ : syracuseStep 1935797 = 181481) (by norm_num)
theorem B1452469 : Blo 1289963 1452469 := bbase (se 5 (by rfl) ⟨68084, by rfl⟩ : syracuseStep 1452469 = 136169) (by norm_num)
theorem B1935821 : Blo 1289963 1935821 := bbase (se 3 (by rfl) ⟨362966, by rfl⟩ : syracuseStep 1935821 = 725933) (by norm_num)
theorem B1452505 : Blo 1289963 1452505 := bbase (se 2 (by rfl) ⟨544689, by rfl⟩ : syracuseStep 1452505 = 1089379) (by norm_num)
theorem B1632737 : Blo 1289963 1632737 := bbase (se 2 (by rfl) ⟨612276, by rfl⟩ : syracuseStep 1632737 = 1224553) (by norm_num)
theorem B1935845 : Blo 1289963 1935845 := bbase (se 4 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 1935845 = 362971) (by norm_num)
theorem B1378801 : Blo 1289963 1378801 := bbase (se 2 (by rfl) ⟨517050, by rfl⟩ : syracuseStep 1378801 = 1034101) (by norm_num)
theorem B2902517 : Blo 1289963 2902517 := bbase (se 5 (by rfl) ⟨136055, by rfl⟩ : syracuseStep 2902517 = 272111) (by norm_num)
theorem B1935869 : Blo 1289963 1935869 := bbase (se 3 (by rfl) ⟨362975, by rfl⟩ : syracuseStep 1935869 = 725951) (by norm_num)
theorem B1452541 : Blo 1289963 1452541 := bbase (se 3 (by rfl) ⟨272351, by rfl⟩ : syracuseStep 1452541 = 544703) (by norm_num)
theorem B1935893 : Blo 1289963 1935893 := bbase (se 6 (by rfl) ⟨45372, by rfl⟩ : syracuseStep 1935893 = 90745) (by norm_num)
theorem B3926549 : Blo 1289963 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B1632793 : Blo 1289963 1632793 := bbase (se 2 (by rfl) ⟨612297, by rfl⟩ : syracuseStep 1632793 = 1224595) (by norm_num)
theorem B1452577 : Blo 1289963 1452577 := bbase (se 2 (by rfl) ⟨544716, by rfl⟩ : syracuseStep 1452577 = 1089433) (by norm_num)
theorem B1935917 : Blo 1289963 1935917 := bbase (se 3 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 1935917 = 725969) (by norm_num)
theorem B2902589 : Blo 1289963 2902589 := bbase (se 3 (by rfl) ⟨544235, by rfl⟩ : syracuseStep 2902589 = 1088471) (by norm_num)
theorem B1935941 : Blo 1289963 1935941 := bbase (se 4 (by rfl) ⟨181494, by rfl⟩ : syracuseStep 1935941 = 362989) (by norm_num)
theorem B1452613 : Blo 1289963 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B2452045 : Blo 1289963 2452045 := bbase (se 3 (by rfl) ⟨459758, by rfl⟩ : syracuseStep 2452045 = 919517) (by norm_num)
theorem B1935965 : Blo 1289963 1935965 := bbase (se 3 (by rfl) ⟨362993, by rfl⟩ : syracuseStep 1935965 = 725987) (by norm_num)
theorem B1452649 : Blo 1289963 1452649 := bbase (se 2 (by rfl) ⟨544743, by rfl⟩ : syracuseStep 1452649 = 1089487) (by norm_num)
theorem B1935989 : Blo 1289963 1935989 := bbase (se 5 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 1935989 = 181499) (by norm_num)
theorem B1632889 : Blo 1289963 1632889 := bbase (se 2 (by rfl) ⟨612333, by rfl⟩ : syracuseStep 1632889 = 1224667) (by norm_num)
theorem B2902661 : Blo 1289963 2902661 := bbase (se 4 (by rfl) ⟨272124, by rfl⟩ : syracuseStep 2902661 = 544249) (by norm_num)
theorem B1936013 : Blo 1289963 1936013 := bbase (se 3 (by rfl) ⟨363002, by rfl⟩ : syracuseStep 1936013 = 726005) (by norm_num)
theorem B1452685 : Blo 1289963 1452685 := bbase (se 3 (by rfl) ⟨272378, by rfl⟩ : syracuseStep 1452685 = 544757) (by norm_num)
theorem B1550993 : Blo 1289963 1550993 := bbase (se 2 (by rfl) ⟨581622, by rfl⟩ : syracuseStep 1550993 = 1163245) (by norm_num)
theorem B1936037 : Blo 1289963 1936037 := bbase (se 4 (by rfl) ⟨181503, by rfl⟩ : syracuseStep 1936037 = 363007) (by norm_num)
theorem B1378981 : Blo 1289963 1378981 := bbase (se 4 (by rfl) ⟨129279, by rfl⟩ : syracuseStep 1378981 = 258559) (by norm_num)
theorem B1837741 : Blo 1289963 1837741 := bbase (se 3 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 1837741 = 689153) (by norm_num)
theorem B1452721 : Blo 1289963 1452721 := bbase (se 2 (by rfl) ⟨544770, by rfl⟩ : syracuseStep 1452721 = 1089541) (by norm_num)
theorem B2067125 : Blo 1289963 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B1936061 : Blo 1289963 1936061 := bbase (se 3 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 1936061 = 726023) (by norm_num)
theorem B2902733 : Blo 1289963 2902733 := bbase (se 3 (by rfl) ⟨544262, by rfl⟩ : syracuseStep 2902733 = 1088525) (by norm_num)
theorem B1936085 : Blo 1289963 1936085 := bbase (se 7 (by rfl) ⟨22688, by rfl⟩ : syracuseStep 1936085 = 45377) (by norm_num)
theorem B1452757 : Blo 1289963 1452757 := bbase (se 7 (by rfl) ⟨17024, by rfl⟩ : syracuseStep 1452757 = 34049) (by norm_num)
theorem B2452189 : Blo 1289963 2452189 := bbase (se 3 (by rfl) ⟨459785, by rfl⟩ : syracuseStep 2452189 = 919571) (by norm_num)
theorem B1936109 : Blo 1289963 1936109 := bbase (se 3 (by rfl) ⟨363020, by rfl⟩ : syracuseStep 1936109 = 726041) (by norm_num)
theorem B1452793 : Blo 1289963 1452793 := bbase (se 2 (by rfl) ⟨544797, by rfl⟩ : syracuseStep 1452793 = 1089595) (by norm_num)
theorem B1936133 : Blo 1289963 1936133 := bbase (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) (by norm_num)
theorem B2616077 : Blo 1289963 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B2902805 : Blo 1289963 2902805 := bbase (se 6 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 2902805 = 136069) (by norm_num)
theorem B1936157 : Blo 1289963 1936157 := bbase (se 3 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 1936157 = 726059) (by norm_num)
theorem B1452829 : Blo 1289963 1452829 := bbase (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) (by norm_num)
theorem B1633061 : Blo 1289963 1633061 := bbase (se 4 (by rfl) ⟨153099, by rfl⟩ : syracuseStep 1633061 = 306199) (by norm_num)
theorem B1936181 : Blo 1289963 1936181 := bbase (se 5 (by rfl) ⟨90758, by rfl⟩ : syracuseStep 1936181 = 181517) (by norm_num)
theorem B1452865 : Blo 1289963 1452865 := bbase (se 2 (by rfl) ⟨544824, by rfl⟩ : syracuseStep 1452865 = 1089649) (by norm_num)
theorem B6540101 : Blo 1289963 6540101 := bbase (se 4 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 6540101 = 1226269) (by norm_num)
theorem B1936205 : Blo 1289963 1936205 := bbase (se 3 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 1936205 = 726077) (by norm_num)
theorem B23554901 : Blo 1289963 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B2902877 : Blo 1289963 2902877 := bbase (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) (by norm_num)
theorem B1633117 : Blo 1289963 1633117 := bbase (se 3 (by rfl) ⟨306209, by rfl⟩ : syracuseStep 1633117 = 612419) (by norm_num)
theorem B1936229 : Blo 1289963 1936229 := bbase (se 4 (by rfl) ⟨181521, by rfl⟩ : syracuseStep 1936229 = 363043) (by norm_num)
theorem B1452901 : Blo 1289963 1452901 := bbase (se 4 (by rfl) ⟨136209, by rfl⟩ : syracuseStep 1452901 = 272419) (by norm_num)
theorem B1936253 : Blo 1289963 1936253 := bbase (se 3 (by rfl) ⟨363047, by rfl⟩ : syracuseStep 1936253 = 726095) (by norm_num)
theorem B2452349 : Blo 1289963 2452349 := bbase (se 3 (by rfl) ⟨459815, by rfl⟩ : syracuseStep 2452349 = 919631) (by norm_num)
theorem B2206597 : Blo 1289963 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B1452937 : Blo 1289963 1452937 := bbase (se 2 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 1452937 = 1089703) (by norm_num)
theorem B1936277 : Blo 1289963 1936277 := bbase (se 6 (by rfl) ⟨45381, by rfl⟩ : syracuseStep 1936277 = 90763) (by norm_num)
theorem B2902949 : Blo 1289963 2902949 := bbase (se 4 (by rfl) ⟨272151, by rfl⟩ : syracuseStep 2902949 = 544303) (by norm_num)
theorem B1936301 : Blo 1289963 1936301 := bbase (se 3 (by rfl) ⟨363056, by rfl⟩ : syracuseStep 1936301 = 726113) (by norm_num)
theorem B1452973 : Blo 1289963 1452973 := bbase (se 3 (by rfl) ⟨272432, by rfl⟩ : syracuseStep 1452973 = 544865) (by norm_num)
theorem B1633213 : Blo 1289963 1633213 := bbase (se 3 (by rfl) ⟨306227, by rfl⟩ : syracuseStep 1633213 = 612455) (by norm_num)
theorem B1936325 : Blo 1289963 1936325 := bbase (se 4 (by rfl) ⟨181530, by rfl⟩ : syracuseStep 1936325 = 363061) (by norm_num)
theorem B1453009 : Blo 1289963 1453009 := bbase (se 2 (by rfl) ⟨544878, by rfl⟩ : syracuseStep 1453009 = 1089757) (by norm_num)
theorem B1936349 : Blo 1289963 1936349 := bbase (se 3 (by rfl) ⟨363065, by rfl⟩ : syracuseStep 1936349 = 726131) (by norm_num)
theorem B1551325 : Blo 1289963 1551325 := bbase (se 3 (by rfl) ⟨290873, by rfl⟩ : syracuseStep 1551325 = 581747) (by norm_num)
theorem B2903021 : Blo 1289963 2903021 := bbase (se 3 (by rfl) ⟨544316, by rfl⟩ : syracuseStep 2903021 = 1088633) (by norm_num)
theorem B1936373 : Blo 1289963 1936373 := bbase (se 5 (by rfl) ⟨90767, by rfl⟩ : syracuseStep 1936373 = 181535) (by norm_num)
theorem B1453045 : Blo 1289963 1453045 := bbase (se 5 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 1453045 = 136223) (by norm_num)
theorem B1936397 : Blo 1289963 1936397 := bbase (se 3 (by rfl) ⟨363074, by rfl⟩ : syracuseStep 1936397 = 726149) (by norm_num)
theorem B2452493 : Blo 1289963 2452493 := bbase (se 3 (by rfl) ⟨459842, by rfl⟩ : syracuseStep 2452493 = 919685) (by norm_num)
theorem B1453081 : Blo 1289963 1453081 := bbase (se 2 (by rfl) ⟨544905, by rfl⟩ : syracuseStep 1453081 = 1089811) (by norm_num)
theorem B2755613 : Blo 1289963 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B1936421 : Blo 1289963 1936421 := bbase (se 4 (by rfl) ⟨181539, by rfl⟩ : syracuseStep 1936421 = 363079) (by norm_num)
theorem B5237797 : Blo 1289963 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B2903093 : Blo 1289963 2903093 := bbase (se 5 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 2903093 = 272165) (by norm_num)
theorem B1936445 : Blo 1289963 1936445 := bbase (se 3 (by rfl) ⟨363083, by rfl⟩ : syracuseStep 1936445 = 726167) (by norm_num)
theorem B1453117 : Blo 1289963 1453117 := bbase (se 3 (by rfl) ⟨272459, by rfl⟩ : syracuseStep 1453117 = 544919) (by norm_num)
theorem B1936469 : Blo 1289963 1936469 := bbase (se 8 (by rfl) ⟨11346, by rfl⟩ : syracuseStep 1936469 = 22693) (by norm_num)
theorem B1453153 : Blo 1289963 1453153 := bbase (se 2 (by rfl) ⟨544932, by rfl⟩ : syracuseStep 1453153 = 1089865) (by norm_num)
theorem B1379425 : Blo 1289963 1379425 := bbase (se 2 (by rfl) ⟨517284, by rfl⟩ : syracuseStep 1379425 = 1034569) (by norm_num)
theorem B1633385 : Blo 1289963 1633385 := bbase (se 2 (by rfl) ⟨612519, by rfl⟩ : syracuseStep 1633385 = 1225039) (by norm_num)
theorem B1936493 : Blo 1289963 1936493 := bbase (se 3 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 1936493 = 726185) (by norm_num)
theorem B1551469 : Blo 1289963 1551469 := bbase (se 3 (by rfl) ⟨290900, by rfl⟩ : syracuseStep 1551469 = 581801) (by norm_num)
theorem B7851125 : Blo 1289963 7851125 := bbase (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) (by norm_num)
theorem B2903165 : Blo 1289963 2903165 := bbase (se 3 (by rfl) ⟨544343, by rfl⟩ : syracuseStep 2903165 = 1088687) (by norm_num)
theorem B2067581 : Blo 1289963 2067581 := bbase (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) (by norm_num)
theorem B1936517 : Blo 1289963 1936517 := bbase (se 4 (by rfl) ⟨181548, by rfl⟩ : syracuseStep 1936517 = 363097) (by norm_num)
theorem B1453189 : Blo 1289963 1453189 := bbase (se 4 (by rfl) ⟨136236, by rfl⟩ : syracuseStep 1453189 = 272473) (by norm_num)
theorem B1936541 : Blo 1289963 1936541 := bbase (se 3 (by rfl) ⟨363101, by rfl⟩ : syracuseStep 1936541 = 726203) (by norm_num)
theorem B1633441 : Blo 1289963 1633441 := bbase (se 2 (by rfl) ⟨612540, by rfl⟩ : syracuseStep 1633441 = 1225081) (by norm_num)
theorem B1453225 : Blo 1289963 1453225 := bbase (se 2 (by rfl) ⟨544959, by rfl⟩ : syracuseStep 1453225 = 1089919) (by norm_num)
theorem B2755757 : Blo 1289963 2755757 := bbase (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) (by norm_num)
theorem B1936565 : Blo 1289963 1936565 := bbase (se 5 (by rfl) ⟨90776, by rfl⟩ : syracuseStep 1936565 = 181553) (by norm_num)
theorem B2903237 : Blo 1289963 2903237 := bbase (se 4 (by rfl) ⟨272178, by rfl⟩ : syracuseStep 2903237 = 544357) (by norm_num)
theorem B1936589 : Blo 1289963 1936589 := bbase (se 3 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 1936589 = 726221) (by norm_num)
theorem B1453261 : Blo 1289963 1453261 := bbase (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) (by norm_num)
theorem B1379549 : Blo 1289963 1379549 := bbase (se 3 (by rfl) ⟨258665, by rfl⟩ : syracuseStep 1379549 = 517331) (by norm_num)
theorem B6532325 : Blo 1289963 6532325 := bbase (se 4 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 6532325 = 1224811) (by norm_num)
theorem B1936613 : Blo 1289963 1936613 := bbase (se 4 (by rfl) ⟨181557, by rfl⟩ : syracuseStep 1936613 = 363115) (by norm_num)
theorem B1453297 : Blo 1289963 1453297 := bbase (se 2 (by rfl) ⟨544986, by rfl⟩ : syracuseStep 1453297 = 1089973) (by norm_num)
theorem B1936637 : Blo 1289963 1936637 := bbase (se 3 (by rfl) ⟨363119, by rfl⟩ : syracuseStep 1936637 = 726239) (by norm_num)
theorem B1838333 : Blo 1289963 1838333 := bbase (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) (by norm_num)
theorem B1633537 : Blo 1289963 1633537 := bbase (se 2 (by rfl) ⟨612576, by rfl⟩ : syracuseStep 1633537 = 1225153) (by norm_num)
theorem B2903309 : Blo 1289963 2903309 := bbase (se 3 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 2903309 = 1088741) (by norm_num)
theorem B1936661 : Blo 1289963 1936661 := bbase (se 6 (by rfl) ⟨45390, by rfl⟩ : syracuseStep 1936661 = 90781) (by norm_num)
theorem B1453333 : Blo 1289963 1453333 := bbase (se 6 (by rfl) ⟨34062, by rfl⟩ : syracuseStep 1453333 = 68125) (by norm_num)
theorem B1936685 : Blo 1289963 1936685 := bbase (se 3 (by rfl) ⟨363128, by rfl⟩ : syracuseStep 1936685 = 726257) (by norm_num)
theorem B1453369 : Blo 1289963 1453369 := bbase (se 2 (by rfl) ⟨545013, by rfl⟩ : syracuseStep 1453369 = 1090027) (by norm_num)
theorem B1936709 : Blo 1289963 1936709 := bbase (se 4 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 1936709 = 363133) (by norm_num)
theorem B1838413 : Blo 1289963 1838413 := bbase (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) (by norm_num)
theorem B2903381 : Blo 1289963 2903381 := bbase (se 11 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 2903381 = 4253) (by norm_num)
theorem B2067805 : Blo 1289963 2067805 := bbase (se 3 (by rfl) ⟨387713, by rfl⟩ : syracuseStep 2067805 = 775427) (by norm_num)
theorem B1936733 : Blo 1289963 1936733 := bbase (se 3 (by rfl) ⟨363137, by rfl⟩ : syracuseStep 1936733 = 726275) (by norm_num)
theorem B1453405 : Blo 1289963 1453405 := bbase (se 3 (by rfl) ⟨272513, by rfl⟩ : syracuseStep 1453405 = 545027) (by norm_num)
theorem B1936757 : Blo 1289963 1936757 := bbase (se 5 (by rfl) ⟨90785, by rfl⟩ : syracuseStep 1936757 = 181571) (by norm_num)
theorem B1453441 : Blo 1289963 1453441 := bbase (se 2 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 1453441 = 1090081) (by norm_num)
theorem B4476293 : Blo 1289963 4476293 := bbase (se 4 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 4476293 = 839305) (by norm_num)
theorem B1936781 : Blo 1289963 1936781 := bbase (se 3 (by rfl) ⟨363146, by rfl⟩ : syracuseStep 1936781 = 726293) (by norm_num)
theorem B2616725 : Blo 1289963 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B5516693 : Blo 1289963 5516693 := bbase (se 6 (by rfl) ⟨129297, by rfl⟩ : syracuseStep 5516693 = 258595) (by norm_num)
theorem B2903453 : Blo 1289963 2903453 := bbase (se 3 (by rfl) ⟨544397, by rfl⟩ : syracuseStep 2903453 = 1088795) (by norm_num)
theorem B2067869 : Blo 1289963 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B1936805 : Blo 1289963 1936805 := bbase (se 4 (by rfl) ⟨181575, by rfl⟩ : syracuseStep 1936805 = 363151) (by norm_num)
theorem B1633709 : Blo 1289963 1633709 := bbase (se 3 (by rfl) ⟨306320, by rfl⟩ : syracuseStep 1633709 = 612641) (by norm_num)
theorem B1936829 : Blo 1289963 1936829 := bbase (se 3 (by rfl) ⟨363155, by rfl⟩ : syracuseStep 1936829 = 726311) (by norm_num)
theorem B1838533 : Blo 1289963 1838533 := bbase (se 4 (by rfl) ⟨172362, by rfl⟩ : syracuseStep 1838533 = 344725) (by norm_num)
theorem B1936853 : Blo 1289963 1936853 := bbase (se 7 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 1936853 = 45395) (by norm_num)
theorem B53013973 : Blo 1289963 53013973 := bbase (se 7 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 53013973 = 1242515) (by norm_num)
theorem B3927509 : Blo 1289963 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2903525 : Blo 1289963 2903525 := bbase (se 4 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 2903525 = 544411) (by norm_num)
theorem B1633765 : Blo 1289963 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B3100141 : Blo 1289963 3100141 := bbase (se 3 (by rfl) ⟨581276, by rfl⟩ : syracuseStep 3100141 = 1162553) (by norm_num)
theorem B1936877 : Blo 1289963 1936877 := bbase (se 3 (by rfl) ⟨363164, by rfl⟩ : syracuseStep 1936877 = 726329) (by norm_num)
theorem B4902389 : Blo 1289963 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B1936901 : Blo 1289963 1936901 := bbase (se 4 (by rfl) ⟨181584, by rfl⟩ : syracuseStep 1936901 = 363169) (by norm_num)
theorem B7351829 : Blo 1289963 7351829 := bbase (se 6 (by rfl) ⟨172308, by rfl⟩ : syracuseStep 7351829 = 344617) (by norm_num)
theorem B3100189 : Blo 1289963 3100189 := bbase (se 3 (by rfl) ⟨581285, by rfl⟩ : syracuseStep 3100189 = 1162571) (by norm_num)
theorem B2067997 : Blo 1289963 2067997 := bbase (se 3 (by rfl) ⟨387749, by rfl⟩ : syracuseStep 2067997 = 775499) (by norm_num)
theorem B1936925 : Blo 1289963 1936925 := bbase (se 3 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 1936925 = 726347) (by norm_num)
theorem B3673637 : Blo 1289963 3673637 := bbase (se 4 (by rfl) ⟨344403, by rfl⟩ : syracuseStep 3673637 = 688807) (by norm_num)
theorem B1838629 : Blo 1289963 1838629 := bbase (se 4 (by rfl) ⟨172371, by rfl⟩ : syracuseStep 1838629 = 344743) (by norm_num)
theorem B2903597 : Blo 1289963 2903597 := bbase (se 3 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 2903597 = 1088849) (by norm_num)
theorem B1936949 : Blo 1289963 1936949 := bbase (se 5 (by rfl) ⟨90794, by rfl⟩ : syracuseStep 1936949 = 181589) (by norm_num)
theorem B1633861 : Blo 1289963 1633861 := bbase (se 4 (by rfl) ⟨153174, by rfl⟩ : syracuseStep 1633861 = 306349) (by norm_num)
theorem B1936973 : Blo 1289963 1936973 := bbase (se 3 (by rfl) ⟨363182, by rfl⟩ : syracuseStep 1936973 = 726365) (by norm_num)
theorem B1863253 : Blo 1289963 1863253 := bbase (se 8 (by rfl) ⟨10917, by rfl⟩ : syracuseStep 1863253 = 21835) (by norm_num)
theorem B1936997 : Blo 1289963 1936997 := bbase (se 4 (by rfl) ⟨181593, by rfl⟩ : syracuseStep 1936997 = 363187) (by norm_num)
theorem B2903669 : Blo 1289963 2903669 := bbase (se 5 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 2903669 = 272219) (by norm_num)
theorem B1937021 : Blo 1289963 1937021 := bbase (se 3 (by rfl) ⟨363191, by rfl⟩ : syracuseStep 1937021 = 726383) (by norm_num)
theorem B1937045 : Blo 1289963 1937045 := bbase (se 6 (by rfl) ⟨45399, by rfl⟩ : syracuseStep 1937045 = 90799) (by norm_num)
theorem B1937069 : Blo 1289963 1937069 := bbase (se 3 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 1937069 = 726401) (by norm_num)
theorem B5516981 : Blo 1289963 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B2903741 : Blo 1289963 2903741 := bbase (se 3 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 2903741 = 1088903) (by norm_num)
theorem B1937093 : Blo 1289963 1937093 := bbase (se 4 (by rfl) ⟨181602, by rfl⟩ : syracuseStep 1937093 = 363205) (by norm_num)
theorem B4353749 : Blo 1289963 4353749 := bbase (se 7 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 4353749 = 102041) (by norm_num)
theorem B1937117 : Blo 1289963 1937117 := bbase (se 3 (by rfl) ⟨363209, by rfl⟩ : syracuseStep 1937117 = 726419) (by norm_num)
theorem B1634033 : Blo 1289963 1634033 := bbase (se 2 (by rfl) ⟨612762, by rfl⟩ : syracuseStep 1634033 = 1225525) (by norm_num)
theorem B1937141 : Blo 1289963 1937141 := bbase (se 5 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 1937141 = 181607) (by norm_num)
theorem B2903813 : Blo 1289963 2903813 := bbase (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) (by norm_num)
theorem B1937165 : Blo 1289963 1937165 := bbase (se 3 (by rfl) ⟨363218, by rfl⟩ : syracuseStep 1937165 = 726437) (by norm_num)
theorem B4902677 : Blo 1289963 4902677 := bbase (se 6 (by rfl) ⟨114906, by rfl⟩ : syracuseStep 4902677 = 229813) (by norm_num)
theorem B1937189 : Blo 1289963 1937189 := bbase (se 4 (by rfl) ⟨181611, by rfl⟩ : syracuseStep 1937189 = 363223) (by norm_num)
theorem B1634089 : Blo 1289963 1634089 := bbase (se 2 (by rfl) ⟨612783, by rfl⟩ : syracuseStep 1634089 = 1225567) (by norm_num)
theorem B2207549 : Blo 1289963 2207549 := bbase (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) (by norm_num)
theorem B1937213 : Blo 1289963 1937213 := bbase (se 3 (by rfl) ⟨363227, by rfl⟩ : syracuseStep 1937213 = 726455) (by norm_num)
theorem B2903885 : Blo 1289963 2903885 := bbase (se 3 (by rfl) ⟨544478, by rfl⟩ : syracuseStep 2903885 = 1088957) (by norm_num)
theorem B1937237 : Blo 1289963 1937237 := bbase (se 9 (by rfl) ⟨5675, by rfl⟩ : syracuseStep 1937237 = 11351) (by norm_num)
theorem B1937261 : Blo 1289963 1937261 := bbase (se 3 (by rfl) ⟨363236, by rfl⟩ : syracuseStep 1937261 = 726473) (by norm_num)
theorem B1937285 : Blo 1289963 1937285 := bbase (se 4 (by rfl) ⟨181620, by rfl⟩ : syracuseStep 1937285 = 363241) (by norm_num)
theorem B1634185 : Blo 1289963 1634185 := bbase (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) (by norm_num)
theorem B2903957 : Blo 1289963 2903957 := bbase (se 6 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 2903957 = 136123) (by norm_num)
theorem B2756501 : Blo 1289963 2756501 := bbase (se 6 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 2756501 = 129211) (by norm_num)
theorem B1937309 : Blo 1289963 1937309 := bbase (se 3 (by rfl) ⟨363245, by rfl⟩ : syracuseStep 1937309 = 726491) (by norm_num)
theorem B1937333 : Blo 1289963 1937333 := bbase (se 5 (by rfl) ⟨90812, by rfl⟩ : syracuseStep 1937333 = 181625) (by norm_num)
theorem B1937357 : Blo 1289963 1937357 := bbase (se 3 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 1937357 = 726509) (by norm_num)
theorem B3674069 : Blo 1289963 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B2904029 : Blo 1289963 2904029 := bbase (se 3 (by rfl) ⟨544505, by rfl⟩ : syracuseStep 2904029 = 1089011) (by norm_num)
theorem B1937381 : Blo 1289963 1937381 := bbase (se 4 (by rfl) ⟨181629, by rfl⟩ : syracuseStep 1937381 = 363259) (by norm_num)
theorem B9809909 : Blo 1289963 9809909 := bbase (se 5 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 9809909 = 919679) (by norm_num)
theorem B1937405 : Blo 1289963 1937405 := bbase (se 3 (by rfl) ⟨363263, by rfl⟩ : syracuseStep 1937405 = 726527) (by norm_num)
theorem B3313685 : Blo 1289963 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B1937429 : Blo 1289963 1937429 := bbase (se 6 (by rfl) ⟨45408, by rfl⟩ : syracuseStep 1937429 = 90817) (by norm_num)
theorem B1839125 : Blo 1289963 1839125 := bbase (se 6 (by rfl) ⟨43104, by rfl⟩ : syracuseStep 1839125 = 86209) (by norm_num)
theorem B2904101 : Blo 1289963 2904101 := bbase (se 4 (by rfl) ⟨272259, by rfl⟩ : syracuseStep 2904101 = 544519) (by norm_num)
theorem B1937453 : Blo 1289963 1937453 := bbase (se 3 (by rfl) ⟨363272, by rfl⟩ : syracuseStep 1937453 = 726545) (by norm_num)
theorem B1634357 : Blo 1289963 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B1937477 : Blo 1289963 1937477 := bbase (se 4 (by rfl) ⟨181638, by rfl⟩ : syracuseStep 1937477 = 363277) (by norm_num)
theorem B1937501 : Blo 1289963 1937501 := bbase (se 3 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 1937501 = 726563) (by norm_num)
theorem B2904173 : Blo 1289963 2904173 := bbase (se 3 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 2904173 = 1089065) (by norm_num)
theorem B1634413 : Blo 1289963 1634413 := bbase (se 3 (by rfl) ⟨306452, by rfl⟩ : syracuseStep 1634413 = 612905) (by norm_num)
theorem B1937525 : Blo 1289963 1937525 := bbase (se 5 (by rfl) ⟨90821, by rfl⟩ : syracuseStep 1937525 = 181643) (by norm_num)
theorem B4354181 : Blo 1289963 4354181 := bbase (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) (by norm_num)
theorem B3100805 : Blo 1289963 3100805 := bbase (se 4 (by rfl) ⟨290700, by rfl⟩ : syracuseStep 3100805 = 581401) (by norm_num)
theorem B1937549 : Blo 1289963 1937549 := bbase (se 3 (by rfl) ⟨363290, by rfl⟩ : syracuseStep 1937549 = 726581) (by norm_num)
theorem B1937573 : Blo 1289963 1937573 := bbase (se 4 (by rfl) ⟨181647, by rfl⟩ : syracuseStep 1937573 = 363295) (by norm_num)
theorem B2904245 : Blo 1289963 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B1937597 : Blo 1289963 1937597 := bbase (se 3 (by rfl) ⟨363299, by rfl⟩ : syracuseStep 1937597 = 726599) (by norm_num)
theorem B1634509 : Blo 1289963 1634509 := bbase (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) (by norm_num)
theorem B1937621 : Blo 1289963 1937621 := bbase (se 7 (by rfl) ⟨22706, by rfl⟩ : syracuseStep 1937621 = 45413) (by norm_num)
theorem B1863901 : Blo 1289963 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B1937645 : Blo 1289963 1937645 := bbase (se 3 (by rfl) ⟨363308, by rfl⟩ : syracuseStep 1937645 = 726617) (by norm_num)
theorem B2904317 : Blo 1289963 2904317 := bbase (se 3 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 2904317 = 1089119) (by norm_num)
theorem B1937669 : Blo 1289963 1937669 := bbase (se 4 (by rfl) ⟨181656, by rfl⟩ : syracuseStep 1937669 = 363313) (by norm_num)
theorem B1937693 : Blo 1289963 1937693 := bbase (se 3 (by rfl) ⟨363317, by rfl⟩ : syracuseStep 1937693 = 726635) (by norm_num)
theorem B1937717 : Blo 1289963 1937717 := bbase (se 5 (by rfl) ⟨90830, by rfl⟩ : syracuseStep 1937717 = 181661) (by norm_num)
theorem B2904389 : Blo 1289963 2904389 := bbase (se 4 (by rfl) ⟨272286, by rfl⟩ : syracuseStep 2904389 = 544573) (by norm_num)
theorem B1937741 : Blo 1289963 1937741 := bbase (se 3 (by rfl) ⟨363326, by rfl⟩ : syracuseStep 1937741 = 726653) (by norm_num)
theorem B1937765 : Blo 1289963 1937765 := bbase (se 4 (by rfl) ⟨181665, by rfl⟩ : syracuseStep 1937765 = 363331) (by norm_num)
theorem B1634681 : Blo 1289963 1634681 := bbase (se 2 (by rfl) ⟨613005, by rfl⟩ : syracuseStep 1634681 = 1226011) (by norm_num)
theorem B1937789 : Blo 1289963 1937789 := bbase (se 3 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 1937789 = 726671) (by norm_num)
theorem B2904461 : Blo 1289963 2904461 := bbase (se 3 (by rfl) ⟨544586, by rfl⟩ : syracuseStep 2904461 = 1089173) (by norm_num)
theorem B9802133 : Blo 1289963 9802133 := bbase (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) (by norm_num)
theorem B1937813 : Blo 1289963 1937813 := bbase (se 6 (by rfl) ⟨45417, by rfl⟩ : syracuseStep 1937813 = 90835) (by norm_num)
theorem B5517733 : Blo 1289963 5517733 := bbase (se 4 (by rfl) ⟨517287, by rfl⟩ : syracuseStep 5517733 = 1034575) (by norm_num)
theorem B1937837 : Blo 1289963 1937837 := bbase (se 3 (by rfl) ⟨363344, by rfl⟩ : syracuseStep 1937837 = 726689) (by norm_num)
theorem B1634737 : Blo 1289963 1634737 := bbase (se 2 (by rfl) ⟨613026, by rfl⟩ : syracuseStep 1634737 = 1226053) (by norm_num)
theorem B1937861 : Blo 1289963 1937861 := bbase (se 4 (by rfl) ⟨181674, by rfl⟩ : syracuseStep 1937861 = 363349) (by norm_num)
theorem B14701013 : Blo 1289963 14701013 := bbase (se 7 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 14701013 = 344555) (by norm_num)
theorem B2904533 : Blo 1289963 2904533 := bbase (se 7 (by rfl) ⟨34037, by rfl⟩ : syracuseStep 2904533 = 68075) (by norm_num)
theorem B3101149 : Blo 1289963 3101149 := bbase (se 3 (by rfl) ⟨581465, by rfl⟩ : syracuseStep 3101149 = 1162931) (by norm_num)
theorem B1937885 : Blo 1289963 1937885 := bbase (se 3 (by rfl) ⟨363353, by rfl⟩ : syracuseStep 1937885 = 726707) (by norm_num)
theorem B6533621 : Blo 1289963 6533621 := bbase (se 5 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 6533621 = 612527) (by norm_num)
theorem B1937909 : Blo 1289963 1937909 := bbase (se 5 (by rfl) ⟨90839, by rfl⟩ : syracuseStep 1937909 = 181679) (by norm_num)
theorem B1937933 : Blo 1289963 1937933 := bbase (se 3 (by rfl) ⟨363362, by rfl⟩ : syracuseStep 1937933 = 726725) (by norm_num)
theorem B1634833 : Blo 1289963 1634833 := bbase (se 2 (by rfl) ⟨613062, by rfl⟩ : syracuseStep 1634833 = 1226125) (by norm_num)
theorem B2904605 : Blo 1289963 2904605 := bbase (se 3 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 2904605 = 1089227) (by norm_num)
theorem B4354613 : Blo 1289963 4354613 := bbase (se 5 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 4354613 = 408245) (by norm_num)
theorem B2904677 : Blo 1289963 2904677 := bbase (se 4 (by rfl) ⟨272313, by rfl⟩ : syracuseStep 2904677 = 544627) (by norm_num)
theorem B2757253 : Blo 1289963 2757253 := bbase (se 4 (by rfl) ⟨258492, by rfl⟩ : syracuseStep 2757253 = 516985) (by norm_num)
theorem B5968549 : Blo 1289963 5968549 := bbase (se 4 (by rfl) ⟨559551, by rfl⟩ : syracuseStep 5968549 = 1119103) (by norm_num)
theorem B2904749 : Blo 1289963 2904749 := bbase (se 3 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 2904749 = 1089281) (by norm_num)
theorem B1635005 : Blo 1289963 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B3674821 : Blo 1289963 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B3101381 : Blo 1289963 3101381 := bbase (se 4 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 3101381 = 581509) (by norm_num)
theorem B2986717 : Blo 1289963 2986717 := bbase (se 3 (by rfl) ⟨560009, by rfl⟩ : syracuseStep 2986717 = 1120019) (by norm_num)
theorem B2069221 : Blo 1289963 2069221 := bbase (se 4 (by rfl) ⟨193989, by rfl⟩ : syracuseStep 2069221 = 387979) (by norm_num)
theorem B2904821 : Blo 1289963 2904821 := bbase (se 5 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 2904821 = 272327) (by norm_num)
theorem B1635061 : Blo 1289963 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B1471225 : Blo 1289963 1471225 := bbase (se 2 (by rfl) ⟨551709, by rfl⟩ : syracuseStep 1471225 = 1103419) (by norm_num)
theorem B2757397 : Blo 1289963 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B2904893 : Blo 1289963 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B3265373 : Blo 1289963 3265373 := bbase (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) (by norm_num)
theorem B2208629 : Blo 1289963 2208629 := bbase (se 5 (by rfl) ⟨103529, by rfl⟩ : syracuseStep 2208629 = 207059) (by norm_num)
theorem B3101573 : Blo 1289963 3101573 := bbase (se 4 (by rfl) ⟨290772, by rfl⟩ : syracuseStep 3101573 = 581545) (by norm_num)
theorem B2904965 : Blo 1289963 2904965 := bbase (se 4 (by rfl) ⟨272340, by rfl⟩ : syracuseStep 2904965 = 544681) (by norm_num)
theorem B2945933 : Blo 1289963 2945933 := bbase (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) (by norm_num)
theorem B4903861 : Blo 1289963 4903861 := bbase (se 5 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 4903861 = 459737) (by norm_num)
theorem B2905037 : Blo 1289963 2905037 := bbase (se 3 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 2905037 = 1089389) (by norm_num)
theorem B2946005 : Blo 1289963 2946005 := bbase (se 7 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 2946005 = 69047) (by norm_num)
theorem B4355045 : Blo 1289963 4355045 := bbase (se 4 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 4355045 = 816571) (by norm_num)
theorem B2618381 : Blo 1289963 2618381 := bbase (se 3 (by rfl) ⟨490946, by rfl⟩ : syracuseStep 2618381 = 981893) (by norm_num)
theorem B2905109 : Blo 1289963 2905109 := bbase (se 6 (by rfl) ⟨68088, by rfl⟩ : syracuseStep 2905109 = 136177) (by norm_num)
theorem B2356309 : Blo 1289963 2356309 := bbase (se 8 (by rfl) ⟨13806, by rfl⟩ : syracuseStep 2356309 = 27613) (by norm_num)
theorem B2905181 : Blo 1289963 2905181 := bbase (se 3 (by rfl) ⟨544721, by rfl⟩ : syracuseStep 2905181 = 1089443) (by norm_num)
theorem B5231749 : Blo 1289963 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B5518469 : Blo 1289963 5518469 := bbase (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) (by norm_num)
theorem B2757773 : Blo 1289963 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B3101861 : Blo 1289963 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B2905253 : Blo 1289963 2905253 := bbase (se 4 (by rfl) ⟨272367, by rfl⟩ : syracuseStep 2905253 = 544735) (by norm_num)
theorem B3265717 : Blo 1289963 3265717 := bbase (se 5 (by rfl) ⟨153080, by rfl⟩ : syracuseStep 3265717 = 306161) (by norm_num)
theorem B6206645 : Blo 1289963 6206645 := bbase (se 5 (by rfl) ⟨290936, by rfl⟩ : syracuseStep 6206645 = 581873) (by norm_num)
theorem B11023573 : Blo 1289963 11023573 := bbase (se 7 (by rfl) ⟨129182, by rfl⟩ : syracuseStep 11023573 = 258365) (by norm_num)
theorem B4904165 : Blo 1289963 4904165 := bbase (se 4 (by rfl) ⟨459765, by rfl⟩ : syracuseStep 4904165 = 919531) (by norm_num)
theorem B2389229 : Blo 1289963 2389229 := bbase (se 3 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 2389229 = 895961) (by norm_num)
theorem B2905325 : Blo 1289963 2905325 := bbase (se 3 (by rfl) ⟨544748, by rfl⟩ : syracuseStep 2905325 = 1089497) (by norm_num)
theorem B4134149 : Blo 1289963 4134149 := bbase (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) (by norm_num)
theorem B3265829 : Blo 1289963 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B1307957 : Blo 1289963 1307957 := bbase (se 5 (by rfl) ⟨61310, by rfl⟩ : syracuseStep 1307957 = 122621) (by norm_num)
theorem B2905397 : Blo 1289963 2905397 := bbase (se 5 (by rfl) ⟨136190, by rfl⟩ : syracuseStep 2905397 = 272381) (by norm_num)
theorem B2905469 : Blo 1289963 2905469 := bbase (se 3 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 2905469 = 1089551) (by norm_num)
theorem B2651525 : Blo 1289963 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B4355477 : Blo 1289963 4355477 := bbase (se 6 (by rfl) ⟨102081, by rfl⟩ : syracuseStep 4355477 = 204163) (by norm_num)
theorem B3487141 : Blo 1289963 3487141 := bbase (se 4 (by rfl) ⟨326919, by rfl⟩ : syracuseStep 3487141 = 653839) (by norm_num)
theorem B4134341 : Blo 1289963 4134341 := bbase (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) (by norm_num)
theorem B2905541 : Blo 1289963 2905541 := bbase (se 4 (by rfl) ⟨272394, by rfl⟩ : syracuseStep 2905541 = 544789) (by norm_num)
theorem B3266021 : Blo 1289963 3266021 := bbase (se 4 (by rfl) ⟨306189, by rfl⟩ : syracuseStep 3266021 = 612379) (by norm_num)
theorem B2758141 : Blo 1289963 2758141 := bbase (se 3 (by rfl) ⟨517151, by rfl⟩ : syracuseStep 2758141 = 1034303) (by norm_num)
theorem B2905613 : Blo 1289963 2905613 := bbase (se 3 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 2905613 = 1089605) (by norm_num)
theorem B5510693 : Blo 1289963 5510693 := bbase (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) (by norm_num)
theorem B5887525 : Blo 1289963 5887525 := bbase (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) (by norm_num)
theorem B2905685 : Blo 1289963 2905685 := bbase (se 8 (by rfl) ⟨17025, by rfl⟩ : syracuseStep 2905685 = 34051) (by norm_num)
theorem B2619013 : Blo 1289963 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B2905757 : Blo 1289963 2905757 := bbase (se 3 (by rfl) ⟨544829, by rfl⟩ : syracuseStep 2905757 = 1089659) (by norm_num)
theorem B2651869 : Blo 1289963 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B2905829 : Blo 1289963 2905829 := bbase (se 4 (by rfl) ⟨272421, by rfl⟩ : syracuseStep 2905829 = 544843) (by norm_num)
theorem B6534917 : Blo 1289963 6534917 := bbase (se 4 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 6534917 = 1225297) (by norm_num)
theorem B2905901 : Blo 1289963 2905901 := bbase (se 3 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 2905901 = 1089713) (by norm_num)
theorem B3266365 : Blo 1289963 3266365 := bbase (se 3 (by rfl) ⟨612443, by rfl⟩ : syracuseStep 3266365 = 1224887) (by norm_num)
theorem B4355909 : Blo 1289963 4355909 := bbase (se 4 (by rfl) ⟨408366, by rfl⟩ : syracuseStep 4355909 = 816733) (by norm_num)
theorem B2176861 : Blo 1289963 2176861 := bbase (se 3 (by rfl) ⟨408161, by rfl⟩ : syracuseStep 2176861 = 816323) (by norm_num)
theorem B2905973 : Blo 1289963 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B1308557 : Blo 1289963 1308557 := bbase (se 3 (by rfl) ⟨245354, by rfl⟩ : syracuseStep 1308557 = 490709) (by norm_num)
theorem B3266477 : Blo 1289963 3266477 := bbase (se 3 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 3266477 = 1224929) (by norm_num)
theorem B2176949 : Blo 1289963 2176949 := bbase (se 5 (by rfl) ⟨102044, by rfl⟩ : syracuseStep 2176949 = 204089) (by norm_num)
theorem B2906045 : Blo 1289963 2906045 := bbase (se 3 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 2906045 = 1089767) (by norm_num)
theorem B1964029 : Blo 1289963 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2906117 : Blo 1289963 2906117 := bbase (se 4 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 2906117 = 544897) (by norm_num)
theorem B2177077 : Blo 1289963 2177077 := bbase (se 5 (by rfl) ⟨102050, by rfl⟩ : syracuseStep 2177077 = 204101) (by norm_num)
theorem B1964101 : Blo 1289963 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B2906189 : Blo 1289963 2906189 := bbase (se 3 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 2906189 = 1089821) (by norm_num)
theorem B3266669 : Blo 1289963 3266669 := bbase (se 3 (by rfl) ⟨612500, by rfl⟩ : syracuseStep 3266669 = 1225001) (by norm_num)
theorem B2177165 : Blo 1289963 2177165 := bbase (se 3 (by rfl) ⟨408218, by rfl⟩ : syracuseStep 2177165 = 816437) (by norm_num)
theorem B2906261 : Blo 1289963 2906261 := bbase (se 6 (by rfl) ⟨68115, by rfl⟩ : syracuseStep 2906261 = 136231) (by norm_num)
theorem B2906333 : Blo 1289963 2906333 := bbase (se 3 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 2906333 = 1089875) (by norm_num)
theorem B4356341 : Blo 1289963 4356341 := bbase (se 5 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 4356341 = 408407) (by norm_num)
theorem B2177293 : Blo 1289963 2177293 := bbase (se 3 (by rfl) ⟨408242, by rfl⟩ : syracuseStep 2177293 = 816485) (by norm_num)
theorem B6715669 : Blo 1289963 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B2906405 : Blo 1289963 2906405 := bbase (se 4 (by rfl) ⟨272475, by rfl⟩ : syracuseStep 2906405 = 544951) (by norm_num)
theorem B2177381 : Blo 1289963 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B2906477 : Blo 1289963 2906477 := bbase (se 3 (by rfl) ⟨544964, by rfl⟩ : syracuseStep 2906477 = 1089929) (by norm_num)
theorem B1571185 : Blo 1289963 1571185 := bbase (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) (by norm_num)
theorem B6199685 : Blo 1289963 6199685 := bbase (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) (by norm_num)
theorem B5233061 : Blo 1289963 5233061 := bbase (se 4 (by rfl) ⟨490599, by rfl⟩ : syracuseStep 5233061 = 981199) (by norm_num)
theorem B2906549 : Blo 1289963 2906549 := bbase (se 5 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 2906549 = 272489) (by norm_num)
theorem B3267013 : Blo 1289963 3267013 := bbase (se 4 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 3267013 = 612565) (by norm_num)
theorem B2177509 : Blo 1289963 2177509 := bbase (se 4 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 2177509 = 408283) (by norm_num)
theorem B2906621 : Blo 1289963 2906621 := bbase (se 3 (by rfl) ⟨544991, by rfl⟩ : syracuseStep 2906621 = 1089983) (by norm_num)
theorem B5511685 : Blo 1289963 5511685 := bbase (se 4 (by rfl) ⟨516720, by rfl⟩ : syracuseStep 5511685 = 1033441) (by norm_num)
theorem B3267125 : Blo 1289963 3267125 := bbase (se 5 (by rfl) ⟨153146, by rfl⟩ : syracuseStep 3267125 = 306293) (by norm_num)
theorem B2177597 : Blo 1289963 2177597 := bbase (se 3 (by rfl) ⟨408299, by rfl⟩ : syracuseStep 2177597 = 816599) (by norm_num)
theorem B2906693 : Blo 1289963 2906693 := bbase (se 4 (by rfl) ⟨272502, by rfl⟩ : syracuseStep 2906693 = 545005) (by norm_num)
theorem B3725909 : Blo 1289963 3725909 := bbase (se 8 (by rfl) ⟨21831, by rfl⟩ : syracuseStep 3725909 = 43663) (by norm_num)
theorem B1473113 : Blo 1289963 1473113 := bbase (se 2 (by rfl) ⟨552417, by rfl⟩ : syracuseStep 1473113 = 1104835) (by norm_num)
theorem B4414085 : Blo 1289963 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B2906765 : Blo 1289963 2906765 := bbase (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) (by norm_num)
theorem B3537557 : Blo 1289963 3537557 := bbase (se 6 (by rfl) ⟨82911, by rfl⟩ : syracuseStep 3537557 = 165823) (by norm_num)
theorem B4356773 : Blo 1289963 4356773 := bbase (se 4 (by rfl) ⟨408447, by rfl⟩ : syracuseStep 4356773 = 816895) (by norm_num)
theorem B2177725 : Blo 1289963 2177725 := bbase (se 3 (by rfl) ⟨408323, by rfl⟩ : syracuseStep 2177725 = 816647) (by norm_num)
theorem B2906837 : Blo 1289963 2906837 := bbase (se 7 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 2906837 = 68129) (by norm_num)
theorem B3267317 : Blo 1289963 3267317 := bbase (se 5 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 3267317 = 306311) (by norm_num)
theorem B2177813 : Blo 1289963 2177813 := bbase (se 6 (by rfl) ⟨51042, by rfl⟩ : syracuseStep 2177813 = 102085) (by norm_num)
theorem B2906909 : Blo 1289963 2906909 := bbase (se 3 (by rfl) ⟨545045, by rfl⟩ : syracuseStep 2906909 = 1090091) (by norm_num)
theorem B2177941 : Blo 1289963 2177941 := bbase (se 6 (by rfl) ⟨51045, by rfl⟩ : syracuseStep 2177941 = 102091) (by norm_num)
theorem B3726229 : Blo 1289963 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B1571789 : Blo 1289963 1571789 := bbase (se 3 (by rfl) ⟨294710, by rfl⟩ : syracuseStep 1571789 = 589421) (by norm_num)
theorem B7076821 : Blo 1289963 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B2178029 : Blo 1289963 2178029 := bbase (se 3 (by rfl) ⟨408380, by rfl⟩ : syracuseStep 2178029 = 816761) (by norm_num)
theorem B6536213 : Blo 1289963 6536213 := bbase (se 6 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 6536213 = 306385) (by norm_num)
theorem B3267661 : Blo 1289963 3267661 := bbase (se 3 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 3267661 = 1225373) (by norm_num)
theorem B4357205 : Blo 1289963 4357205 := bbase (se 8 (by rfl) ⟨25530, by rfl⟩ : syracuseStep 4357205 = 51061) (by norm_num)
theorem B2178157 : Blo 1289963 2178157 := bbase (se 3 (by rfl) ⟨408404, by rfl⟩ : syracuseStep 2178157 = 816809) (by norm_num)
theorem B11025557 : Blo 1289963 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B3267773 : Blo 1289963 3267773 := bbase (se 3 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 3267773 = 1225415) (by norm_num)
theorem B2178245 : Blo 1289963 2178245 := bbase (se 4 (by rfl) ⟨204210, by rfl⟩ : syracuseStep 2178245 = 408421) (by norm_num)
theorem B12401909 : Blo 1289963 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B2178373 : Blo 1289963 2178373 := bbase (se 4 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 2178373 = 408445) (by norm_num)
theorem B3267965 : Blo 1289963 3267965 := bbase (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) (by norm_num)
theorem B2178461 : Blo 1289963 2178461 := bbase (se 3 (by rfl) ⟨408461, by rfl⟩ : syracuseStep 2178461 = 816923) (by norm_num)
theorem B3677669 : Blo 1289963 3677669 := bbase (se 4 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 3677669 = 689563) (by norm_num)
theorem B4357637 : Blo 1289963 4357637 := bbase (se 4 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 4357637 = 817057) (by norm_num)
theorem B2178589 : Blo 1289963 2178589 := bbase (se 3 (by rfl) ⟨408485, by rfl⟩ : syracuseStep 2178589 = 816971) (by norm_num)
theorem B2178677 : Blo 1289963 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B2449045 : Blo 1289963 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B4898501 : Blo 1289963 4898501 := bbase (se 4 (by rfl) ⟨459234, by rfl⟩ : syracuseStep 4898501 = 918469) (by norm_num)
theorem B3268309 : Blo 1289963 3268309 := bbase (se 7 (by rfl) ⟨38300, by rfl⟩ : syracuseStep 3268309 = 76601) (by norm_num)
theorem B3145429 : Blo 1289963 3145429 := bbase (se 7 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 3145429 = 73721) (by norm_num)
theorem B2178805 : Blo 1289963 2178805 := bbase (se 5 (by rfl) ⟨102131, by rfl⟩ : syracuseStep 2178805 = 204263) (by norm_num)
theorem B3268421 : Blo 1289963 3268421 := bbase (se 4 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 3268421 = 612829) (by norm_num)
theorem B2096965 : Blo 1289963 2096965 := bbase (se 4 (by rfl) ⟨196590, by rfl⟩ : syracuseStep 2096965 = 393181) (by norm_num)
theorem B2178893 : Blo 1289963 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B3358549 : Blo 1289963 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1679197 : Blo 1289963 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B4358069 : Blo 1289963 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B2449349 : Blo 1289963 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B2179021 : Blo 1289963 2179021 := bbase (se 3 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 2179021 = 817133) (by norm_num)
theorem B4898789 : Blo 1289963 4898789 := bbase (se 4 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 4898789 = 918523) (by norm_num)
theorem B1343491 : Blo 1289963 1343491 := bstep (se 1 (by rfl) ⟨1007618, by rfl⟩ : syracuseStep 1343491 = 2015237) B2015237
theorem B7348229 : Blo 1289963 7348229 := bstep (se 4 (by rfl) ⟨688896, by rfl⟩ : syracuseStep 7348229 = 1377793) B1377793
theorem B2179075 : Blo 1289963 2179075 := bstep (se 1 (by rfl) ⟨1634306, by rfl⟩ : syracuseStep 2179075 = 3268613) B3268613
theorem B5890097 : Blo 1289963 5890097 := bstep (se 2 (by rfl) ⟨2208786, by rfl⟩ : syracuseStep 5890097 = 4417573) B4417573
theorem B4358285 : Blo 1289963 4358285 := bstep (se 3 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 4358285 = 1634357) B1634357
theorem B2179217 : Blo 1289963 2179217 := bstep (se 2 (by rfl) ⟨817206, by rfl⟩ : syracuseStep 2179217 = 1634413) B1634413
theorem B4358339 : Blo 1289963 4358339 := bstep (se 1 (by rfl) ⟨3268754, by rfl⟩ : syracuseStep 4358339 = 6537509) B6537509
theorem B9806021 : Blo 1289963 9806021 := bstep (se 4 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 9806021 = 1838629) B1838629
theorem B2179345 : Blo 1289963 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B2179379 : Blo 1289963 2179379 := bstep (se 1 (by rfl) ⟨1634534, by rfl⟩ : syracuseStep 2179379 = 3269069) B3269069
theorem B8954225 : Blo 1289963 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B5890481 : Blo 1289963 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B2179507 : Blo 1289963 2179507 := bstep (se 1 (by rfl) ⟨1634630, by rfl⟩ : syracuseStep 2179507 = 3269261) B3269261
theorem B12566981 : Blo 1289963 12566981 := bstep (se 4 (by rfl) ⟨1178154, by rfl⟩ : syracuseStep 12566981 = 2356309) B2356309
theorem B9937349 : Blo 1289963 9937349 := bstep (se 4 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 9937349 = 1863253) B1863253
theorem B4358609 : Blo 1289963 4358609 := bstep (se 2 (by rfl) ⟨1634478, by rfl⟩ : syracuseStep 4358609 = 3268957) B3268957
theorem B7356977 : Blo 1289963 7356977 := bstep (se 2 (by rfl) ⟨2758866, by rfl⟩ : syracuseStep 7356977 = 5517733) B5517733
theorem B13951541 : Blo 1289963 13951541 := bstep (se 5 (by rfl) ⟨653978, by rfl⟩ : syracuseStep 13951541 = 1307957) B1307957
theorem B2179649 : Blo 1289963 2179649 := bstep (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) B1634737
theorem B3678797 : Blo 1289963 3678797 := bstep (se 3 (by rfl) ⟨689774, by rfl⟩ : syracuseStep 3678797 = 1379549) B1379549
theorem B7348913 : Blo 1289963 7348913 := bstep (se 2 (by rfl) ⟨2755842, by rfl⟩ : syracuseStep 7348913 = 5511685) B5511685
theorem B1745587 : Blo 1289963 1745587 := bstep (se 1 (by rfl) ⟨1309190, by rfl⟩ : syracuseStep 1745587 = 2618381) B2618381
theorem B2179777 : Blo 1289963 2179777 := bstep (se 2 (by rfl) ⟨817416, by rfl⟩ : syracuseStep 2179777 = 1634833) B1634833
theorem B2179811 : Blo 1289963 2179811 := bstep (se 1 (by rfl) ⟨1634858, by rfl⟩ : syracuseStep 2179811 = 3269717) B3269717
theorem B3678979 : Blo 1289963 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B3269393 : Blo 1289963 3269393 := bstep (se 2 (by rfl) ⟨1226022, by rfl⟩ : syracuseStep 3269393 = 2452045) B2452045
theorem B4137763 : Blo 1289963 4137763 := bstep (se 1 (by rfl) ⟨3103322, by rfl⟩ : syracuseStep 4137763 = 6206645) B6206645
theorem B3269443 : Blo 1289963 3269443 := bstep (se 1 (by rfl) ⟨2452082, by rfl⟩ : syracuseStep 3269443 = 4904165) B4904165
theorem B2179939 : Blo 1289963 2179939 := bstep (se 1 (by rfl) ⟨1634954, by rfl⟩ : syracuseStep 2179939 = 3269909) B3269909
theorem B2450321 : Blo 1289963 2450321 := bstep (se 2 (by rfl) ⟨918870, by rfl⟩ : syracuseStep 2450321 = 1837741) B1837741
theorem B4899761 : Blo 1289963 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B3269585 : Blo 1289963 3269585 := bstep (se 2 (by rfl) ⟨1226094, by rfl⟩ : syracuseStep 3269585 = 2452189) B2452189
theorem B3982289 : Blo 1289963 3982289 := bstep (se 2 (by rfl) ⟨1493358, by rfl⟩ : syracuseStep 3982289 = 2986717) B2986717
theorem B4359149 : Blo 1289963 4359149 := bstep (se 3 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 4359149 = 1634681) B1634681
theorem B2180081 : Blo 1289963 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B4359203 : Blo 1289963 4359203 := bstep (se 1 (by rfl) ⟨3269402, by rfl⟩ : syracuseStep 4359203 = 6538805) B6538805
theorem B5514317 : Blo 1289963 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B2942129 : Blo 1289963 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B6538481 : Blo 1289963 6538481 := bstep (se 2 (by rfl) ⟨2451930, by rfl⟩ : syracuseStep 6538481 = 4903861) B4903861
theorem B1377571 : Blo 1289963 1377571 := bstep (se 1 (by rfl) ⟨1033178, by rfl⟩ : syracuseStep 1377571 = 2066357) B2066357
theorem B1451299 : Blo 1289963 1451299 := bstep (se 1 (by rfl) ⟨1088474, by rfl⟩ : syracuseStep 1451299 = 2176949) B2176949
theorem B4359473 : Blo 1289963 4359473 := bstep (se 2 (by rfl) ⟨1634802, by rfl⟩ : syracuseStep 4359473 = 3269605) B3269605
theorem B1451443 : Blo 1289963 1451443 := bstep (se 1 (by rfl) ⟨1088582, by rfl⟩ : syracuseStep 1451443 = 2177165) B2177165
theorem B15926797 : Blo 1289963 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B1451587 : Blo 1289963 1451587 := bstep (se 1 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 1451587 = 2177381) B2177381
theorem B1934945 : Blo 1289963 1934945 := bstep (se 2 (by rfl) ⟨725604, by rfl⟩ : syracuseStep 1934945 = 1451209) B1451209
theorem B14698097 : Blo 1289963 14698097 := bstep (se 2 (by rfl) ⟨5511786, by rfl⟩ : syracuseStep 14698097 = 11023573) B11023573
theorem B1934963 : Blo 1289963 1934963 := bstep (se 1 (by rfl) ⟨1451222, by rfl⟩ : syracuseStep 1934963 = 2902445) B2902445
theorem B1934993 : Blo 1289963 1934993 := bstep (se 2 (by rfl) ⟨725622, by rfl⟩ : syracuseStep 1934993 = 1451245) B1451245
theorem B1935011 : Blo 1289963 1935011 := bstep (se 1 (by rfl) ⟨1451258, by rfl⟩ : syracuseStep 1935011 = 2902517) B2902517
theorem B1935041 : Blo 1289963 1935041 := bstep (se 2 (by rfl) ⟨725640, by rfl⟩ : syracuseStep 1935041 = 1451281) B1451281
theorem B1935059 : Blo 1289963 1935059 := bstep (se 1 (by rfl) ⟨1451294, by rfl⟩ : syracuseStep 1935059 = 2902589) B2902589
theorem B1451731 : Blo 1289963 1451731 := bstep (se 1 (by rfl) ⟨1088798, by rfl⟩ : syracuseStep 1451731 = 2177597) B2177597
theorem B2483939 : Blo 1289963 2483939 := bstep (se 1 (by rfl) ⟨1862954, by rfl⟩ : syracuseStep 2483939 = 3725909) B3725909
theorem B1935089 : Blo 1289963 1935089 := bstep (se 2 (by rfl) ⟨725658, by rfl⟩ : syracuseStep 1935089 = 1451317) B1451317
theorem B1935107 : Blo 1289963 1935107 := bstep (se 1 (by rfl) ⟨1451330, by rfl⟩ : syracuseStep 1935107 = 2902661) B2902661
theorem B2942723 : Blo 1289963 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B2451217 : Blo 1289963 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B1935137 : Blo 1289963 1935137 := bstep (se 2 (by rfl) ⟨725676, by rfl⟩ : syracuseStep 1935137 = 1451353) B1451353
theorem B1935155 : Blo 1289963 1935155 := bstep (se 1 (by rfl) ⟨1451366, by rfl⟩ : syracuseStep 1935155 = 2902733) B2902733
theorem B4360013 : Blo 1289963 4360013 := bstep (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) B1635005
theorem B1935185 : Blo 1289963 1935185 := bstep (se 2 (by rfl) ⟨725694, by rfl⟩ : syracuseStep 1935185 = 1451389) B1451389
theorem B1935203 : Blo 1289963 1935203 := bstep (se 1 (by rfl) ⟨1451402, by rfl⟩ : syracuseStep 1935203 = 2902805) B2902805
theorem B1451875 : Blo 1289963 1451875 := bstep (se 1 (by rfl) ⟨1088906, by rfl⟩ : syracuseStep 1451875 = 2177813) B2177813
theorem B1935233 : Blo 1289963 1935233 := bstep (se 2 (by rfl) ⟨725712, by rfl⟩ : syracuseStep 1935233 = 1451425) B1451425
theorem B4360067 : Blo 1289963 4360067 := bstep (se 1 (by rfl) ⟨3270050, by rfl⟩ : syracuseStep 4360067 = 6540101) B6540101
theorem B1935251 : Blo 1289963 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B1935281 : Blo 1289963 1935281 := bstep (se 2 (by rfl) ⟨725730, by rfl⟩ : syracuseStep 1935281 = 1451461) B1451461
theorem B2451377 : Blo 1289963 2451377 := bstep (se 2 (by rfl) ⟨919266, by rfl⟩ : syracuseStep 2451377 = 1838533) B1838533
theorem B1935299 : Blo 1289963 1935299 := bstep (se 1 (by rfl) ⟨1451474, by rfl⟩ : syracuseStep 1935299 = 2902949) B2902949
theorem B1935329 : Blo 1289963 1935329 := bstep (se 2 (by rfl) ⟨725748, by rfl⟩ : syracuseStep 1935329 = 1451497) B1451497
theorem B1935347 : Blo 1289963 1935347 := bstep (se 1 (by rfl) ⟨1451510, by rfl⟩ : syracuseStep 1935347 = 2903021) B2903021
theorem B1452019 : Blo 1289963 1452019 := bstep (se 1 (by rfl) ⟨1089014, by rfl⟩ : syracuseStep 1452019 = 2178029) B2178029
theorem B1935377 : Blo 1289963 1935377 := bstep (se 2 (by rfl) ⟨725766, by rfl⟩ : syracuseStep 1935377 = 1451533) B1451533
theorem B1837075 : Blo 1289963 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B1935395 : Blo 1289963 1935395 := bstep (se 1 (by rfl) ⟨1451546, by rfl⟩ : syracuseStep 1935395 = 2903093) B2903093
theorem B7850033 : Blo 1289963 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B1935425 : Blo 1289963 1935425 := bstep (se 2 (by rfl) ⟨725784, by rfl⟩ : syracuseStep 1935425 = 1451569) B1451569
theorem B1935443 : Blo 1289963 1935443 := bstep (se 1 (by rfl) ⟨1451582, by rfl⟩ : syracuseStep 1935443 = 2903165) B2903165
theorem B1378387 : Blo 1289963 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B7350371 : Blo 1289963 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B1935473 : Blo 1289963 1935473 := bstep (se 2 (by rfl) ⟨725802, by rfl⟩ : syracuseStep 1935473 = 1451605) B1451605
theorem B1837171 : Blo 1289963 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B1935491 : Blo 1289963 1935491 := bstep (se 1 (by rfl) ⟨1451618, by rfl⟩ : syracuseStep 1935491 = 2903237) B2903237
theorem B1452163 : Blo 1289963 1452163 := bstep (se 1 (by rfl) ⟨1089122, by rfl⟩ : syracuseStep 1452163 = 2178245) B2178245
theorem B4360337 : Blo 1289963 4360337 := bstep (se 2 (by rfl) ⟨1635126, by rfl⟩ : syracuseStep 4360337 = 3270253) B3270253
theorem B1935521 : Blo 1289963 1935521 := bstep (se 2 (by rfl) ⟨725820, by rfl⟩ : syracuseStep 1935521 = 1451641) B1451641
theorem B8267939 : Blo 1289963 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B3492017 : Blo 1289963 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B1935539 : Blo 1289963 1935539 := bstep (se 1 (by rfl) ⟨1451654, by rfl⟩ : syracuseStep 1935539 = 2903309) B2903309
theorem B1935569 : Blo 1289963 1935569 := bstep (se 2 (by rfl) ⟨725838, by rfl⟩ : syracuseStep 1935569 = 1451677) B1451677
theorem B1935587 : Blo 1289963 1935587 := bstep (se 1 (by rfl) ⟨1451690, by rfl⟩ : syracuseStep 1935587 = 2903381) B2903381
theorem B1935617 : Blo 1289963 1935617 := bstep (se 2 (by rfl) ⟨725856, by rfl⟩ : syracuseStep 1935617 = 1451713) B1451713
theorem B2984195 : Blo 1289963 2984195 := bstep (se 1 (by rfl) ⟨2238146, by rfl⟩ : syracuseStep 2984195 = 4476293) B4476293
theorem B1935635 : Blo 1289963 1935635 := bstep (se 1 (by rfl) ⟨1451726, by rfl⟩ : syracuseStep 1935635 = 2903453) B2903453
theorem B1452307 : Blo 1289963 1452307 := bstep (se 1 (by rfl) ⟨1089230, by rfl⟩ : syracuseStep 1452307 = 2178461) B2178461
theorem B1935665 : Blo 1289963 1935665 := bstep (se 2 (by rfl) ⟨725874, by rfl⟩ : syracuseStep 1935665 = 1451749) B1451749
theorem B1935683 : Blo 1289963 1935683 := bstep (se 1 (by rfl) ⟨1451762, by rfl⟩ : syracuseStep 1935683 = 2903525) B2903525
theorem B2451779 : Blo 1289963 2451779 := bstep (se 1 (by rfl) ⟨1838834, by rfl⟩ : syracuseStep 2451779 = 3677669) B3677669
theorem B1935713 : Blo 1289963 1935713 := bstep (se 2 (by rfl) ⟨725892, by rfl⟩ : syracuseStep 1935713 = 1451785) B1451785
theorem B4901219 : Blo 1289963 4901219 := bstep (se 1 (by rfl) ⟨3675914, by rfl⟩ : syracuseStep 4901219 = 7351829) B7351829
theorem B1935731 : Blo 1289963 1935731 := bstep (se 1 (by rfl) ⟨1451798, by rfl⟩ : syracuseStep 1935731 = 2903597) B2903597
theorem B1935761 : Blo 1289963 1935761 := bstep (se 2 (by rfl) ⟨725910, by rfl⟩ : syracuseStep 1935761 = 1451821) B1451821
theorem B1935779 : Blo 1289963 1935779 := bstep (se 1 (by rfl) ⟨1451834, by rfl⟩ : syracuseStep 1935779 = 2903669) B2903669
theorem B1452451 : Blo 1289963 1452451 := bstep (se 1 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 1452451 = 2178677) B2178677
theorem B2795953 : Blo 1289963 2795953 := bstep (se 2 (by rfl) ⟨1048482, by rfl⟩ : syracuseStep 2795953 = 2096965) B2096965
theorem B1935809 : Blo 1289963 1935809 := bstep (se 2 (by rfl) ⟨725928, by rfl⟩ : syracuseStep 1935809 = 1451857) B1451857
theorem B13420997 : Blo 1289963 13420997 := bstep (se 4 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 13420997 = 2516437) B2516437
theorem B2902481 : Blo 1289963 2902481 := bstep (se 2 (by rfl) ⟨1088430, by rfl⟩ : syracuseStep 2902481 = 2176861) B2176861
theorem B2238929 : Blo 1289963 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B1935827 : Blo 1289963 1935827 := bstep (se 1 (by rfl) ⟨1451870, by rfl⟩ : syracuseStep 1935827 = 2903741) B2903741
theorem B2902499 : Blo 1289963 2902499 := bstep (se 1 (by rfl) ⟨2176874, by rfl⟩ : syracuseStep 2902499 = 4353749) B4353749
theorem B1935857 : Blo 1289963 1935857 := bstep (se 2 (by rfl) ⟨725946, by rfl⟩ : syracuseStep 1935857 = 1451893) B1451893
theorem B1935875 : Blo 1289963 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B1935905 : Blo 1289963 1935905 := bstep (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) B1451929
theorem B1935923 : Blo 1289963 1935923 := bstep (se 1 (by rfl) ⟨1451942, by rfl⟩ : syracuseStep 1935923 = 2903885) B2903885
theorem B1452595 : Blo 1289963 1452595 := bstep (se 1 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 1452595 = 2178893) B2178893
theorem B24832565 : Blo 1289963 24832565 := bstep (se 5 (by rfl) ⟨1164026, by rfl⟩ : syracuseStep 24832565 = 2328053) B2328053
theorem B1935953 : Blo 1289963 1935953 := bstep (se 2 (by rfl) ⟨725982, by rfl⟩ : syracuseStep 1935953 = 1451965) B1451965
theorem B1935971 : Blo 1289963 1935971 := bstep (se 1 (by rfl) ⟨1451978, by rfl⟩ : syracuseStep 1935971 = 2903957) B2903957
theorem B1837667 : Blo 1289963 1837667 := bstep (se 1 (by rfl) ⟨1378250, by rfl⟩ : syracuseStep 1837667 = 2756501) B2756501
theorem B1936001 : Blo 1289963 1936001 := bstep (se 2 (by rfl) ⟨726000, by rfl⟩ : syracuseStep 1936001 = 1452001) B1452001
theorem B1632899 : Blo 1289963 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B1936019 : Blo 1289963 1936019 := bstep (se 1 (by rfl) ⟨1452014, by rfl⟩ : syracuseStep 1936019 = 2904029) B2904029
theorem B6539939 : Blo 1289963 6539939 := bstep (se 1 (by rfl) ⟨4904954, by rfl⟩ : syracuseStep 6539939 = 9809909) B9809909
theorem B1936049 : Blo 1289963 1936049 := bstep (se 2 (by rfl) ⟨726018, by rfl⟩ : syracuseStep 1936049 = 1452037) B1452037
theorem B1936067 : Blo 1289963 1936067 := bstep (se 1 (by rfl) ⟨1452050, by rfl⟩ : syracuseStep 1936067 = 2904101) B2904101
theorem B1452739 : Blo 1289963 1452739 := bstep (se 1 (by rfl) ⟨1089554, by rfl⟩ : syracuseStep 1452739 = 2179109) B2179109
theorem B1936097 : Blo 1289963 1936097 := bstep (se 2 (by rfl) ⟨726036, by rfl⟩ : syracuseStep 1936097 = 1452073) B1452073
theorem B2755313 : Blo 1289963 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2902769 : Blo 1289963 2902769 := bstep (se 2 (by rfl) ⟨1088538, by rfl⟩ : syracuseStep 2902769 = 2177077) B2177077
theorem B1936115 : Blo 1289963 1936115 := bstep (se 1 (by rfl) ⟨1452086, by rfl⟩ : syracuseStep 1936115 = 2904173) B2904173
theorem B2902787 : Blo 1289963 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B2067203 : Blo 1289963 2067203 := bstep (se 1 (by rfl) ⟨1550402, by rfl⟩ : syracuseStep 2067203 = 3100805) B3100805
theorem B1936145 : Blo 1289963 1936145 := bstep (se 2 (by rfl) ⟨726054, by rfl⟩ : syracuseStep 1936145 = 1452109) B1452109
theorem B1936163 : Blo 1289963 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1936193 : Blo 1289963 1936193 := bstep (se 2 (by rfl) ⟨726072, by rfl⟩ : syracuseStep 1936193 = 1452145) B1452145
theorem B1936211 : Blo 1289963 1936211 := bstep (se 1 (by rfl) ⟨1452158, by rfl⟩ : syracuseStep 1936211 = 2904317) B2904317
theorem B1452883 : Blo 1289963 1452883 := bstep (se 1 (by rfl) ⟨1089662, by rfl⟩ : syracuseStep 1452883 = 2179325) B2179325
theorem B1936241 : Blo 1289963 1936241 := bstep (se 2 (by rfl) ⟨726090, by rfl⟩ : syracuseStep 1936241 = 1452181) B1452181
theorem B1936259 : Blo 1289963 1936259 := bstep (se 1 (by rfl) ⟨1452194, by rfl⟩ : syracuseStep 1936259 = 2904389) B2904389
theorem B1936289 : Blo 1289963 1936289 := bstep (se 2 (by rfl) ⟨726108, by rfl⟩ : syracuseStep 1936289 = 1452217) B1452217
theorem B1936307 : Blo 1289963 1936307 := bstep (se 1 (by rfl) ⟨1452230, by rfl⟩ : syracuseStep 1936307 = 2904461) B2904461
theorem B1936337 : Blo 1289963 1936337 := bstep (se 2 (by rfl) ⟨726126, by rfl⟩ : syracuseStep 1936337 = 1452253) B1452253
theorem B9800675 : Blo 1289963 9800675 := bstep (se 1 (by rfl) ⟨7350506, by rfl⟩ : syracuseStep 9800675 = 14701013) B14701013
theorem B1936355 : Blo 1289963 1936355 := bstep (se 1 (by rfl) ⟨1452266, by rfl⟩ : syracuseStep 1936355 = 2904533) B2904533
theorem B1453027 : Blo 1289963 1453027 := bstep (se 1 (by rfl) ⟨1089770, by rfl⟩ : syracuseStep 1453027 = 2179541) B2179541
theorem B1936385 : Blo 1289963 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B2903057 : Blo 1289963 2903057 := bstep (se 2 (by rfl) ⟨1088646, by rfl⟩ : syracuseStep 2903057 = 2177293) B2177293
theorem B1936403 : Blo 1289963 1936403 := bstep (se 1 (by rfl) ⟨1452302, by rfl⟩ : syracuseStep 1936403 = 2904605) B2904605
theorem B2903075 : Blo 1289963 2903075 := bstep (se 1 (by rfl) ⟨2177306, by rfl⟩ : syracuseStep 2903075 = 4354613) B4354613
theorem B6204451 : Blo 1289963 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B1936433 : Blo 1289963 1936433 := bstep (se 2 (by rfl) ⟨726162, by rfl⟩ : syracuseStep 1936433 = 1452325) B1452325
theorem B1936451 : Blo 1289963 1936451 := bstep (se 1 (by rfl) ⟨1452338, by rfl⟩ : syracuseStep 1936451 = 2904677) B2904677
theorem B1936481 : Blo 1289963 1936481 := bstep (se 2 (by rfl) ⟨726180, by rfl⟩ : syracuseStep 1936481 = 1452361) B1452361
theorem B1936499 : Blo 1289963 1936499 := bstep (se 1 (by rfl) ⟨1452374, by rfl⟩ : syracuseStep 1936499 = 2904749) B2904749
theorem B1453171 : Blo 1289963 1453171 := bstep (se 1 (by rfl) ⟨1089878, by rfl⟩ : syracuseStep 1453171 = 2179757) B2179757
theorem B2067587 : Blo 1289963 2067587 := bstep (se 1 (by rfl) ⟨1550690, by rfl⟩ : syracuseStep 2067587 = 3101381) B3101381
theorem B1936529 : Blo 1289963 1936529 := bstep (se 2 (by rfl) ⟨726198, by rfl⟩ : syracuseStep 1936529 = 1452397) B1452397
theorem B1936547 : Blo 1289963 1936547 := bstep (se 1 (by rfl) ⟨1452410, by rfl⟩ : syracuseStep 1936547 = 2904821) B2904821
theorem B1936577 : Blo 1289963 1936577 := bstep (se 2 (by rfl) ⟨726216, by rfl⟩ : syracuseStep 1936577 = 1452433) B1452433
theorem B2452675 : Blo 1289963 2452675 := bstep (se 1 (by rfl) ⟨1839506, by rfl⟩ : syracuseStep 2452675 = 3679013) B3679013
theorem B1936595 : Blo 1289963 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1838305 : Blo 1289963 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B1936625 : Blo 1289963 1936625 := bstep (se 2 (by rfl) ⟨726234, by rfl⟩ : syracuseStep 1936625 = 1452469) B1452469
theorem B2067715 : Blo 1289963 2067715 := bstep (se 1 (by rfl) ⟨1550786, by rfl⟩ : syracuseStep 2067715 = 3101573) B3101573
theorem B1936643 : Blo 1289963 1936643 := bstep (se 1 (by rfl) ⟨1452482, by rfl⟩ : syracuseStep 1936643 = 2904965) B2904965
theorem B1453315 : Blo 1289963 1453315 := bstep (se 1 (by rfl) ⟨1089986, by rfl⟩ : syracuseStep 1453315 = 2179973) B2179973
theorem B1936673 : Blo 1289963 1936673 := bstep (se 2 (by rfl) ⟨726252, by rfl⟩ : syracuseStep 1936673 = 1452505) B1452505
theorem B2903345 : Blo 1289963 2903345 := bstep (se 2 (by rfl) ⟨1088754, by rfl⟩ : syracuseStep 2903345 = 2177509) B2177509
theorem B1936691 : Blo 1289963 1936691 := bstep (se 1 (by rfl) ⟨1452518, by rfl⟩ : syracuseStep 1936691 = 2905037) B2905037
theorem B2903363 : Blo 1289963 2903363 := bstep (se 1 (by rfl) ⟨2177522, by rfl⟩ : syracuseStep 2903363 = 4355045) B4355045
theorem B1633603 : Blo 1289963 1633603 := bstep (se 1 (by rfl) ⟨1225202, by rfl⟩ : syracuseStep 1633603 = 2450405) B2450405
theorem B3673421 : Blo 1289963 3673421 := bstep (se 3 (by rfl) ⟨688766, by rfl⟩ : syracuseStep 3673421 = 1377533) B1377533
theorem B4902221 : Blo 1289963 4902221 := bstep (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) B1838333
theorem B1936721 : Blo 1289963 1936721 := bstep (se 2 (by rfl) ⟨726270, by rfl⟩ : syracuseStep 1936721 = 1452541) B1452541
theorem B6974819 : Blo 1289963 6974819 := bstep (se 1 (by rfl) ⟨5231114, by rfl⟩ : syracuseStep 6974819 = 10462229) B10462229
theorem B1936739 : Blo 1289963 1936739 := bstep (se 1 (by rfl) ⟨1452554, by rfl⟩ : syracuseStep 1936739 = 2905109) B2905109
theorem B1936769 : Blo 1289963 1936769 := bstep (se 2 (by rfl) ⟨726288, by rfl⟩ : syracuseStep 1936769 = 1452577) B1452577
theorem B1936787 : Blo 1289963 1936787 := bstep (se 1 (by rfl) ⟨1452590, by rfl⟩ : syracuseStep 1936787 = 2905181) B2905181
theorem B1453459 : Blo 1289963 1453459 := bstep (se 1 (by rfl) ⟨1090094, by rfl⟩ : syracuseStep 1453459 = 2180189) B2180189
theorem B1633699 : Blo 1289963 1633699 := bstep (se 1 (by rfl) ⟨1225274, by rfl⟩ : syracuseStep 1633699 = 2450549) B2450549
theorem B1936817 : Blo 1289963 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B1936835 : Blo 1289963 1936835 := bstep (se 1 (by rfl) ⟨1452626, by rfl⟩ : syracuseStep 1936835 = 2905253) B2905253
theorem B1936865 : Blo 1289963 1936865 := bstep (se 2 (by rfl) ⟨726324, by rfl⟩ : syracuseStep 1936865 = 1452649) B1452649
theorem B1592819 : Blo 1289963 1592819 := bstep (se 1 (by rfl) ⟨1194614, by rfl⟩ : syracuseStep 1592819 = 2389229) B2389229
theorem B1936883 : Blo 1289963 1936883 := bstep (se 1 (by rfl) ⟨1452662, by rfl⟩ : syracuseStep 1936883 = 2905325) B2905325
theorem B2756099 : Blo 1289963 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B3673613 : Blo 1289963 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1936913 : Blo 1289963 1936913 := bstep (se 2 (by rfl) ⟨726342, by rfl⟩ : syracuseStep 1936913 = 1452685) B1452685
theorem B1936931 : Blo 1289963 1936931 := bstep (se 1 (by rfl) ⟨1452698, by rfl⟩ : syracuseStep 1936931 = 2905397) B2905397
theorem B1838641 : Blo 1289963 1838641 := bstep (se 2 (by rfl) ⟨689490, by rfl⟩ : syracuseStep 1838641 = 1378981) B1378981
theorem B1936961 : Blo 1289963 1936961 := bstep (se 2 (by rfl) ⟨726360, by rfl⟩ : syracuseStep 1936961 = 1452721) B1452721
theorem B2903633 : Blo 1289963 2903633 := bstep (se 2 (by rfl) ⟨1088862, by rfl⟩ : syracuseStep 2903633 = 2177725) B2177725
theorem B1936979 : Blo 1289963 1936979 := bstep (se 1 (by rfl) ⟨1452734, by rfl⟩ : syracuseStep 1936979 = 2905469) B2905469
theorem B2903651 : Blo 1289963 2903651 := bstep (se 1 (by rfl) ⟨2177738, by rfl⟩ : syracuseStep 2903651 = 4355477) B4355477
theorem B1937009 : Blo 1289963 1937009 := bstep (se 2 (by rfl) ⟨726378, by rfl⟩ : syracuseStep 1937009 = 1452757) B1452757
theorem B1937027 : Blo 1289963 1937027 := bstep (se 1 (by rfl) ⟨1452770, by rfl⟩ : syracuseStep 1937027 = 2905541) B2905541
theorem B1961633 : Blo 1289963 1961633 := bstep (se 2 (by rfl) ⟨735612, by rfl⟩ : syracuseStep 1961633 = 1471225) B1471225
theorem B1937057 : Blo 1289963 1937057 := bstep (se 2 (by rfl) ⟨726396, by rfl⟩ : syracuseStep 1937057 = 1452793) B1452793
theorem B1937075 : Blo 1289963 1937075 := bstep (se 1 (by rfl) ⟨1452806, by rfl⟩ : syracuseStep 1937075 = 2905613) B2905613
theorem B1937105 : Blo 1289963 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B15920867 : Blo 1289963 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B1937123 : Blo 1289963 1937123 := bstep (se 1 (by rfl) ⟨1452842, by rfl⟩ : syracuseStep 1937123 = 2905685) B2905685
theorem B1289971 : Blo 1289963 1289971 := bstep (se 1 (by rfl) ⟨967478, by rfl⟩ : syracuseStep 1289971 = 1934957) B1934957
theorem B1937153 : Blo 1289963 1937153 := bstep (se 2 (by rfl) ⟨726432, by rfl⟩ : syracuseStep 1937153 = 1452865) B1452865
theorem B1289987 : Blo 1289963 1289987 := bstep (se 1 (by rfl) ⟨967490, by rfl⟩ : syracuseStep 1289987 = 1934981) B1934981
theorem B1290003 : Blo 1289963 1290003 := bstep (se 1 (by rfl) ⟨967502, by rfl⟩ : syracuseStep 1290003 = 1935005) B1935005
theorem B1937171 : Blo 1289963 1937171 := bstep (se 1 (by rfl) ⟨1452878, by rfl⟩ : syracuseStep 1937171 = 2905757) B2905757
theorem B1290019 : Blo 1289963 1290019 := bstep (se 1 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 1290019 = 1935029) B1935029
theorem B1937201 : Blo 1289963 1937201 := bstep (se 2 (by rfl) ⟨726450, by rfl⟩ : syracuseStep 1937201 = 1452901) B1452901
theorem B1290035 : Blo 1289963 1290035 := bstep (se 1 (by rfl) ⟨967526, by rfl⟩ : syracuseStep 1290035 = 1935053) B1935053
theorem B1290051 : Blo 1289963 1290051 := bstep (se 1 (by rfl) ⟨967538, by rfl⟩ : syracuseStep 1290051 = 1935077) B1935077
theorem B1937219 : Blo 1289963 1937219 := bstep (se 1 (by rfl) ⟨1452914, by rfl⟩ : syracuseStep 1937219 = 2905829) B2905829
theorem B9940805 : Blo 1289963 9940805 := bstep (se 4 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 9940805 = 1863901) B1863901
theorem B1290067 : Blo 1289963 1290067 := bstep (se 1 (by rfl) ⟨967550, by rfl⟩ : syracuseStep 1290067 = 1935101) B1935101
theorem B1937249 : Blo 1289963 1937249 := bstep (se 2 (by rfl) ⟨726468, by rfl⟩ : syracuseStep 1937249 = 1452937) B1452937
theorem B1290083 : Blo 1289963 1290083 := bstep (se 1 (by rfl) ⟨967562, by rfl⟩ : syracuseStep 1290083 = 1935125) B1935125
theorem B2903921 : Blo 1289963 2903921 := bstep (se 2 (by rfl) ⟨1088970, by rfl⟩ : syracuseStep 2903921 = 2177941) B2177941
theorem B4968305 : Blo 1289963 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B1290099 : Blo 1289963 1290099 := bstep (se 1 (by rfl) ⟨967574, by rfl⟩ : syracuseStep 1290099 = 1935149) B1935149
theorem B1937267 : Blo 1289963 1937267 := bstep (se 1 (by rfl) ⟨1452950, by rfl⟩ : syracuseStep 1937267 = 2905901) B2905901
theorem B1290115 : Blo 1289963 1290115 := bstep (se 1 (by rfl) ⟨967586, by rfl⟩ : syracuseStep 1290115 = 1935173) B1935173
theorem B2903939 : Blo 1289963 2903939 := bstep (se 1 (by rfl) ⟨2177954, by rfl⟩ : syracuseStep 2903939 = 4355909) B4355909
theorem B1937297 : Blo 1289963 1937297 := bstep (se 2 (by rfl) ⟨726486, by rfl⟩ : syracuseStep 1937297 = 1452973) B1452973
theorem B1290131 : Blo 1289963 1290131 := bstep (se 1 (by rfl) ⟨967598, by rfl⟩ : syracuseStep 1290131 = 1935197) B1935197
theorem B1634195 : Blo 1289963 1634195 := bstep (se 1 (by rfl) ⟨1225646, by rfl⟩ : syracuseStep 1634195 = 2451293) B2451293
theorem B1290147 : Blo 1289963 1290147 := bstep (se 1 (by rfl) ⟨967610, by rfl⟩ : syracuseStep 1290147 = 1935221) B1935221
theorem B1937315 : Blo 1289963 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B4353965 : Blo 1289963 4353965 := bstep (se 3 (by rfl) ⟨816368, by rfl⟩ : syracuseStep 4353965 = 1632737) B1632737
theorem B1290163 : Blo 1289963 1290163 := bstep (se 1 (by rfl) ⟨967622, by rfl⟩ : syracuseStep 1290163 = 1935245) B1935245
theorem B1937345 : Blo 1289963 1937345 := bstep (se 2 (by rfl) ⟨726504, by rfl⟩ : syracuseStep 1937345 = 1453009) B1453009
theorem B1290179 : Blo 1289963 1290179 := bstep (se 1 (by rfl) ⟨967634, by rfl⟩ : syracuseStep 1290179 = 1935269) B1935269
theorem B2068433 : Blo 1289963 2068433 := bstep (se 2 (by rfl) ⟨775662, by rfl⟩ : syracuseStep 2068433 = 1551325) B1551325
theorem B1290195 : Blo 1289963 1290195 := bstep (se 1 (by rfl) ⟨967646, by rfl⟩ : syracuseStep 1290195 = 1935293) B1935293
theorem B1937363 : Blo 1289963 1937363 := bstep (se 1 (by rfl) ⟨1453022, by rfl⟩ : syracuseStep 1937363 = 2906045) B2906045
theorem B4354019 : Blo 1289963 4354019 := bstep (se 1 (by rfl) ⟨3265514, by rfl⟩ : syracuseStep 4354019 = 6531029) B6531029
theorem B1290211 : Blo 1289963 1290211 := bstep (se 1 (by rfl) ⟨967658, by rfl⟩ : syracuseStep 1290211 = 1935317) B1935317
theorem B1937393 : Blo 1289963 1937393 := bstep (se 2 (by rfl) ⟨726522, by rfl⟩ : syracuseStep 1937393 = 1453045) B1453045
theorem B1290227 : Blo 1289963 1290227 := bstep (se 1 (by rfl) ⟨967670, by rfl⟩ : syracuseStep 1290227 = 1935341) B1935341
theorem B1290243 : Blo 1289963 1290243 := bstep (se 1 (by rfl) ⟨967682, by rfl⟩ : syracuseStep 1290243 = 1935365) B1935365
theorem B1937411 : Blo 1289963 1937411 := bstep (se 1 (by rfl) ⟨1453058, by rfl⟩ : syracuseStep 1937411 = 2906117) B2906117
theorem B1290259 : Blo 1289963 1290259 := bstep (se 1 (by rfl) ⟨967694, by rfl⟩ : syracuseStep 1290259 = 1935389) B1935389
theorem B1937441 : Blo 1289963 1937441 := bstep (se 2 (by rfl) ⟨726540, by rfl⟩ : syracuseStep 1937441 = 1453081) B1453081
theorem B1290275 : Blo 1289963 1290275 := bstep (se 1 (by rfl) ⟨967706, by rfl⟩ : syracuseStep 1290275 = 1935413) B1935413
theorem B6983729 : Blo 1289963 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1290291 : Blo 1289963 1290291 := bstep (se 1 (by rfl) ⟨967718, by rfl⟩ : syracuseStep 1290291 = 1935437) B1935437
theorem B1937459 : Blo 1289963 1937459 := bstep (se 1 (by rfl) ⟨1453094, by rfl⟩ : syracuseStep 1937459 = 2906189) B2906189
theorem B1290307 : Blo 1289963 1290307 := bstep (se 1 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 1290307 = 1935461) B1935461
theorem B1937489 : Blo 1289963 1937489 := bstep (se 2 (by rfl) ⟨726558, by rfl⟩ : syracuseStep 1937489 = 1453117) B1453117
theorem B1290323 : Blo 1289963 1290323 := bstep (se 1 (by rfl) ⟨967742, by rfl⟩ : syracuseStep 1290323 = 1935485) B1935485
theorem B1290339 : Blo 1289963 1290339 := bstep (se 1 (by rfl) ⟨967754, by rfl⟩ : syracuseStep 1290339 = 1935509) B1935509
theorem B1962083 : Blo 1289963 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B3584099 : Blo 1289963 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B1937507 : Blo 1289963 1937507 := bstep (se 1 (by rfl) ⟨1453130, by rfl⟩ : syracuseStep 1937507 = 2906261) B2906261
theorem B8269937 : Blo 1289963 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B1290355 : Blo 1289963 1290355 := bstep (se 1 (by rfl) ⟨967766, by rfl⟩ : syracuseStep 1290355 = 1935533) B1935533
theorem B1937537 : Blo 1289963 1937537 := bstep (se 2 (by rfl) ⟨726576, by rfl⟩ : syracuseStep 1937537 = 1453153) B1453153
theorem B1290371 : Blo 1289963 1290371 := bstep (se 1 (by rfl) ⟨967778, by rfl⟩ : syracuseStep 1290371 = 1935557) B1935557
theorem B1839233 : Blo 1289963 1839233 := bstep (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) B1379425
theorem B2904209 : Blo 1289963 2904209 := bstep (se 2 (by rfl) ⟨1089078, by rfl⟩ : syracuseStep 2904209 = 2178157) B2178157
theorem B2068625 : Blo 1289963 2068625 := bstep (se 2 (by rfl) ⟨775734, by rfl⟩ : syracuseStep 2068625 = 1551469) B1551469
theorem B1290387 : Blo 1289963 1290387 := bstep (se 1 (by rfl) ⟨967790, by rfl⟩ : syracuseStep 1290387 = 1935581) B1935581
theorem B1937555 : Blo 1289963 1937555 := bstep (se 1 (by rfl) ⟨1453166, by rfl⟩ : syracuseStep 1937555 = 2906333) B2906333
theorem B1290403 : Blo 1289963 1290403 := bstep (se 1 (by rfl) ⟨967802, by rfl⟩ : syracuseStep 1290403 = 1935605) B1935605
theorem B2904227 : Blo 1289963 2904227 := bstep (se 1 (by rfl) ⟨2178170, by rfl⟩ : syracuseStep 2904227 = 4356341) B4356341
theorem B6975665 : Blo 1289963 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B6533297 : Blo 1289963 6533297 := bstep (se 2 (by rfl) ⟨2449986, by rfl⟩ : syracuseStep 6533297 = 4899973) B4899973
theorem B1290419 : Blo 1289963 1290419 := bstep (se 1 (by rfl) ⟨967814, by rfl⟩ : syracuseStep 1290419 = 1935629) B1935629
theorem B1937585 : Blo 1289963 1937585 := bstep (se 2 (by rfl) ⟨726594, by rfl⟩ : syracuseStep 1937585 = 1453189) B1453189
theorem B16543925 : Blo 1289963 16543925 := bstep (se 5 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 16543925 = 1550993) B1550993
theorem B1290435 : Blo 1289963 1290435 := bstep (se 1 (by rfl) ⟨967826, by rfl⟩ : syracuseStep 1290435 = 1935653) B1935653
theorem B1937603 : Blo 1289963 1937603 := bstep (se 1 (by rfl) ⟨1453202, by rfl⟩ : syracuseStep 1937603 = 2906405) B2906405
theorem B1290451 : Blo 1289963 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B1937633 : Blo 1289963 1937633 := bstep (se 2 (by rfl) ⟨726612, by rfl⟩ : syracuseStep 1937633 = 1453225) B1453225
theorem B1290467 : Blo 1289963 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B3928301 : Blo 1289963 3928301 := bstep (se 3 (by rfl) ⟨736556, by rfl⟩ : syracuseStep 3928301 = 1473113) B1473113
theorem B4354289 : Blo 1289963 4354289 := bstep (se 2 (by rfl) ⟨1632858, by rfl⟩ : syracuseStep 4354289 = 3265717) B3265717
theorem B6205681 : Blo 1289963 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B1290483 : Blo 1289963 1290483 := bstep (se 1 (by rfl) ⟨967862, by rfl⟩ : syracuseStep 1290483 = 1935725) B1935725
theorem B1937651 : Blo 1289963 1937651 := bstep (se 1 (by rfl) ⟨1453238, by rfl⟩ : syracuseStep 1937651 = 2906477) B2906477
theorem B4133123 : Blo 1289963 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B1290499 : Blo 1289963 1290499 := bstep (se 1 (by rfl) ⟨967874, by rfl⟩ : syracuseStep 1290499 = 1935749) B1935749
theorem B1290515 : Blo 1289963 1290515 := bstep (se 1 (by rfl) ⟨967886, by rfl⟩ : syracuseStep 1290515 = 1935773) B1935773
theorem B1937681 : Blo 1289963 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B1290531 : Blo 1289963 1290531 := bstep (se 1 (by rfl) ⟨967898, by rfl⟩ : syracuseStep 1290531 = 1935797) B1935797
theorem B1937699 : Blo 1289963 1937699 := bstep (se 1 (by rfl) ⟨1453274, by rfl⟩ : syracuseStep 1937699 = 2906549) B2906549
theorem B1290547 : Blo 1289963 1290547 := bstep (se 1 (by rfl) ⟨967910, by rfl⟩ : syracuseStep 1290547 = 1935821) B1935821
theorem B1937729 : Blo 1289963 1937729 := bstep (se 2 (by rfl) ⟨726648, by rfl⟩ : syracuseStep 1937729 = 1453297) B1453297
theorem B1290563 : Blo 1289963 1290563 := bstep (se 1 (by rfl) ⟨967922, by rfl⟩ : syracuseStep 1290563 = 1935845) B1935845
theorem B1290579 : Blo 1289963 1290579 := bstep (se 1 (by rfl) ⟨967934, by rfl⟩ : syracuseStep 1290579 = 1935869) B1935869
theorem B1937747 : Blo 1289963 1937747 := bstep (se 1 (by rfl) ⟨1453310, by rfl⟩ : syracuseStep 1937747 = 2906621) B2906621
theorem B1290595 : Blo 1289963 1290595 := bstep (se 1 (by rfl) ⟨967946, by rfl⟩ : syracuseStep 1290595 = 1935893) B1935893
theorem B2617699 : Blo 1289963 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B1937777 : Blo 1289963 1937777 := bstep (se 2 (by rfl) ⟨726666, by rfl⟩ : syracuseStep 1937777 = 1453333) B1453333
theorem B1290611 : Blo 1289963 1290611 := bstep (se 1 (by rfl) ⟨967958, by rfl⟩ : syracuseStep 1290611 = 1935917) B1935917
theorem B1290627 : Blo 1289963 1290627 := bstep (se 1 (by rfl) ⟨967970, by rfl⟩ : syracuseStep 1290627 = 1935941) B1935941
theorem B1937795 : Blo 1289963 1937795 := bstep (se 1 (by rfl) ⟨1453346, by rfl⟩ : syracuseStep 1937795 = 2906693) B2906693
theorem B1290643 : Blo 1289963 1290643 := bstep (se 1 (by rfl) ⟨967982, by rfl⟩ : syracuseStep 1290643 = 1935965) B1935965
theorem B1937825 : Blo 1289963 1937825 := bstep (se 2 (by rfl) ⟨726684, by rfl⟩ : syracuseStep 1937825 = 1453369) B1453369
theorem B1290659 : Blo 1289963 1290659 := bstep (se 1 (by rfl) ⟨967994, by rfl⟩ : syracuseStep 1290659 = 1935989) B1935989
theorem B2904497 : Blo 1289963 2904497 := bstep (se 2 (by rfl) ⟨1089186, by rfl⟩ : syracuseStep 2904497 = 2178373) B2178373
theorem B1290675 : Blo 1289963 1290675 := bstep (se 1 (by rfl) ⟨968006, by rfl⟩ : syracuseStep 1290675 = 1936013) B1936013
theorem B1937843 : Blo 1289963 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B1290691 : Blo 1289963 1290691 := bstep (se 1 (by rfl) ⟨968018, by rfl⟩ : syracuseStep 1290691 = 1936037) B1936037
theorem B2904515 : Blo 1289963 2904515 := bstep (se 1 (by rfl) ⟨2178386, by rfl⟩ : syracuseStep 2904515 = 4356773) B4356773
theorem B17912261 : Blo 1289963 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B2757073 : Blo 1289963 2757073 := bstep (se 2 (by rfl) ⟨1033902, by rfl⟩ : syracuseStep 2757073 = 2067805) B2067805
theorem B1937873 : Blo 1289963 1937873 := bstep (se 2 (by rfl) ⟨726702, by rfl⟩ : syracuseStep 1937873 = 1453405) B1453405
theorem B1290707 : Blo 1289963 1290707 := bstep (se 1 (by rfl) ⟨968030, by rfl⟩ : syracuseStep 1290707 = 1936061) B1936061
theorem B1290723 : Blo 1289963 1290723 := bstep (se 1 (by rfl) ⟨968042, by rfl⟩ : syracuseStep 1290723 = 1936085) B1936085
theorem B1937891 : Blo 1289963 1937891 := bstep (se 1 (by rfl) ⟨1453418, by rfl⟩ : syracuseStep 1937891 = 2906837) B2906837
theorem B3674605 : Blo 1289963 3674605 := bstep (se 3 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 3674605 = 1377977) B1377977
theorem B1290739 : Blo 1289963 1290739 := bstep (se 1 (by rfl) ⟨968054, by rfl⟩ : syracuseStep 1290739 = 1936109) B1936109
theorem B1937921 : Blo 1289963 1937921 := bstep (se 2 (by rfl) ⟨726720, by rfl⟩ : syracuseStep 1937921 = 1453441) B1453441
theorem B1290755 : Blo 1289963 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B1290771 : Blo 1289963 1290771 := bstep (se 1 (by rfl) ⟨968078, by rfl⟩ : syracuseStep 1290771 = 1936157) B1936157
theorem B1937939 : Blo 1289963 1937939 := bstep (se 1 (by rfl) ⟨1453454, by rfl⟩ : syracuseStep 1937939 = 2906909) B2906909
theorem B1290787 : Blo 1289963 1290787 := bstep (se 1 (by rfl) ⟨968090, by rfl⟩ : syracuseStep 1290787 = 1936181) B1936181
theorem B4649521 : Blo 1289963 4649521 := bstep (se 2 (by rfl) ⟨1743570, by rfl⟩ : syracuseStep 4649521 = 3487141) B3487141
theorem B1290803 : Blo 1289963 1290803 := bstep (se 1 (by rfl) ⟨968102, by rfl⟩ : syracuseStep 1290803 = 1936205) B1936205
theorem B22049333 : Blo 1289963 22049333 := bstep (se 5 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 22049333 = 2067125) B2067125
theorem B1290819 : Blo 1289963 1290819 := bstep (se 1 (by rfl) ⟨968114, by rfl⟩ : syracuseStep 1290819 = 1936229) B1936229
theorem B1290835 : Blo 1289963 1290835 := bstep (se 1 (by rfl) ⟨968126, by rfl⟩ : syracuseStep 1290835 = 1936253) B1936253
theorem B1634899 : Blo 1289963 1634899 := bstep (se 1 (by rfl) ⟨1226174, by rfl⟩ : syracuseStep 1634899 = 2452349) B2452349
theorem B1290851 : Blo 1289963 1290851 := bstep (se 1 (by rfl) ⟨968138, by rfl⟩ : syracuseStep 1290851 = 1936277) B1936277
theorem B70685297 : Blo 1289963 70685297 := bstep (se 2 (by rfl) ⟨26506986, by rfl⟩ : syracuseStep 70685297 = 53013973) B53013973
theorem B1290867 : Blo 1289963 1290867 := bstep (se 1 (by rfl) ⟨968150, by rfl⟩ : syracuseStep 1290867 = 1936301) B1936301
theorem B1290883 : Blo 1289963 1290883 := bstep (se 1 (by rfl) ⟨968162, by rfl⟩ : syracuseStep 1290883 = 1936325) B1936325
theorem B4133521 : Blo 1289963 4133521 := bstep (se 2 (by rfl) ⟨1550070, by rfl⟩ : syracuseStep 4133521 = 3100141) B3100141
theorem B1290899 : Blo 1289963 1290899 := bstep (se 1 (by rfl) ⟨968174, by rfl⟩ : syracuseStep 1290899 = 1936349) B1936349
theorem B1290915 : Blo 1289963 1290915 := bstep (se 1 (by rfl) ⟨968186, by rfl⟩ : syracuseStep 1290915 = 1936373) B1936373
theorem B1290931 : Blo 1289963 1290931 := bstep (se 1 (by rfl) ⟨968198, by rfl⟩ : syracuseStep 1290931 = 1936397) B1936397
theorem B1634995 : Blo 1289963 1634995 := bstep (se 1 (by rfl) ⟨1226246, by rfl⟩ : syracuseStep 1634995 = 2452493) B2452493
theorem B1290947 : Blo 1289963 1290947 := bstep (se 1 (by rfl) ⟨968210, by rfl⟩ : syracuseStep 1290947 = 1936421) B1936421
theorem B6976205 : Blo 1289963 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B4133585 : Blo 1289963 4133585 := bstep (se 2 (by rfl) ⟨1550094, by rfl⟩ : syracuseStep 4133585 = 3100189) B3100189
theorem B1290963 : Blo 1289963 1290963 := bstep (se 1 (by rfl) ⟨968222, by rfl⟩ : syracuseStep 1290963 = 1936445) B1936445
theorem B2904785 : Blo 1289963 2904785 := bstep (se 2 (by rfl) ⟨1089294, by rfl⟩ : syracuseStep 2904785 = 2178589) B2178589
theorem B2757329 : Blo 1289963 2757329 := bstep (se 2 (by rfl) ⟨1033998, by rfl⟩ : syracuseStep 2757329 = 2067997) B2067997
theorem B1290979 : Blo 1289963 1290979 := bstep (se 1 (by rfl) ⟨968234, by rfl⟩ : syracuseStep 1290979 = 1936469) B1936469
theorem B2904803 : Blo 1289963 2904803 := bstep (se 1 (by rfl) ⟨2178602, by rfl⟩ : syracuseStep 2904803 = 4357205) B4357205
theorem B1290995 : Blo 1289963 1290995 := bstep (se 1 (by rfl) ⟨968246, by rfl⟩ : syracuseStep 1290995 = 1936493) B1936493
theorem B1291011 : Blo 1289963 1291011 := bstep (se 1 (by rfl) ⟨968258, by rfl⟩ : syracuseStep 1291011 = 1936517) B1936517
theorem B4354829 : Blo 1289963 4354829 := bstep (se 3 (by rfl) ⟨816530, by rfl⟩ : syracuseStep 4354829 = 1633061) B1633061
theorem B1291027 : Blo 1289963 1291027 := bstep (se 1 (by rfl) ⟨968270, by rfl⟩ : syracuseStep 1291027 = 1936541) B1936541
theorem B1291043 : Blo 1289963 1291043 := bstep (se 1 (by rfl) ⟨968282, by rfl⟩ : syracuseStep 1291043 = 1936565) B1936565
theorem B1291059 : Blo 1289963 1291059 := bstep (se 1 (by rfl) ⟨968294, by rfl⟩ : syracuseStep 1291059 = 1936589) B1936589
theorem B4354883 : Blo 1289963 4354883 := bstep (se 1 (by rfl) ⟨3266162, by rfl⟩ : syracuseStep 4354883 = 6532325) B6532325
theorem B1291075 : Blo 1289963 1291075 := bstep (se 1 (by rfl) ⟨968306, by rfl⟩ : syracuseStep 1291075 = 1936613) B1936613
theorem B1291091 : Blo 1289963 1291091 := bstep (se 1 (by rfl) ⟨968318, by rfl⟩ : syracuseStep 1291091 = 1936637) B1936637
theorem B1291107 : Blo 1289963 1291107 := bstep (se 1 (by rfl) ⟨968330, by rfl⟩ : syracuseStep 1291107 = 1936661) B1936661
theorem B3265393 : Blo 1289963 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B1291123 : Blo 1289963 1291123 := bstep (se 1 (by rfl) ⟨968342, by rfl⟩ : syracuseStep 1291123 = 1936685) B1936685
theorem B1291139 : Blo 1289963 1291139 := bstep (se 1 (by rfl) ⟨968354, by rfl⟩ : syracuseStep 1291139 = 1936709) B1936709
theorem B62813069 : Blo 1289963 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B1291155 : Blo 1289963 1291155 := bstep (se 1 (by rfl) ⟨968366, by rfl⟩ : syracuseStep 1291155 = 1936733) B1936733
theorem B1291171 : Blo 1289963 1291171 := bstep (se 1 (by rfl) ⟨968378, by rfl⟩ : syracuseStep 1291171 = 1936757) B1936757
theorem B1291187 : Blo 1289963 1291187 := bstep (se 1 (by rfl) ⟨968390, by rfl⟩ : syracuseStep 1291187 = 1936781) B1936781
theorem B1291203 : Blo 1289963 1291203 := bstep (se 1 (by rfl) ⟨968402, by rfl⟩ : syracuseStep 1291203 = 1936805) B1936805
theorem B3535825 : Blo 1289963 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B1291219 : Blo 1289963 1291219 := bstep (se 1 (by rfl) ⟨968414, by rfl⟩ : syracuseStep 1291219 = 1936829) B1936829
theorem B1291235 : Blo 1289963 1291235 := bstep (se 1 (by rfl) ⟨968426, by rfl⟩ : syracuseStep 1291235 = 1936853) B1936853
theorem B2618339 : Blo 1289963 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B2905073 : Blo 1289963 2905073 := bstep (se 2 (by rfl) ⟨1089402, by rfl⟩ : syracuseStep 2905073 = 2178805) B2178805
theorem B1291251 : Blo 1289963 1291251 := bstep (se 1 (by rfl) ⟨968438, by rfl⟩ : syracuseStep 1291251 = 1936877) B1936877
theorem B2905091 : Blo 1289963 2905091 := bstep (se 1 (by rfl) ⟨2178818, by rfl⟩ : syracuseStep 2905091 = 4357637) B4357637
theorem B1291267 : Blo 1289963 1291267 := bstep (se 1 (by rfl) ⟨968450, by rfl⟩ : syracuseStep 1291267 = 1936901) B1936901
theorem B1291283 : Blo 1289963 1291283 := bstep (se 1 (by rfl) ⟨968462, by rfl⟩ : syracuseStep 1291283 = 1936925) B1936925
theorem B1291299 : Blo 1289963 1291299 := bstep (se 1 (by rfl) ⟨968474, by rfl⟩ : syracuseStep 1291299 = 1936949) B1936949
theorem B1291315 : Blo 1289963 1291315 := bstep (se 1 (by rfl) ⟨968486, by rfl⟩ : syracuseStep 1291315 = 1936973) B1936973
theorem B1291331 : Blo 1289963 1291331 := bstep (se 1 (by rfl) ⟨968498, by rfl⟩ : syracuseStep 1291331 = 1936997) B1936997
theorem B4355153 : Blo 1289963 4355153 := bstep (se 2 (by rfl) ⟨1633182, by rfl⟩ : syracuseStep 4355153 = 3266365) B3266365
theorem B1291347 : Blo 1289963 1291347 := bstep (se 1 (by rfl) ⟨968510, by rfl⟩ : syracuseStep 1291347 = 1937021) B1937021
theorem B1291363 : Blo 1289963 1291363 := bstep (se 1 (by rfl) ⟨968522, by rfl⟩ : syracuseStep 1291363 = 1937045) B1937045
theorem B1291379 : Blo 1289963 1291379 := bstep (se 1 (by rfl) ⟨968534, by rfl⟩ : syracuseStep 1291379 = 1937069) B1937069
theorem B3265667 : Blo 1289963 3265667 := bstep (se 1 (by rfl) ⟨2449250, by rfl⟩ : syracuseStep 3265667 = 4898501) B4898501
theorem B1291395 : Blo 1289963 1291395 := bstep (se 1 (by rfl) ⟨968546, by rfl⟩ : syracuseStep 1291395 = 1937093) B1937093
theorem B1291411 : Blo 1289963 1291411 := bstep (se 1 (by rfl) ⟨968558, by rfl⟩ : syracuseStep 1291411 = 1937117) B1937117
theorem B1291427 : Blo 1289963 1291427 := bstep (se 1 (by rfl) ⟨968570, by rfl⟩ : syracuseStep 1291427 = 1937141) B1937141
theorem B1291443 : Blo 1289963 1291443 := bstep (se 1 (by rfl) ⟨968582, by rfl⟩ : syracuseStep 1291443 = 1937165) B1937165
theorem B1291459 : Blo 1289963 1291459 := bstep (se 1 (by rfl) ⟨968594, by rfl⟩ : syracuseStep 1291459 = 1937189) B1937189
theorem B4191437 : Blo 1289963 4191437 := bstep (se 3 (by rfl) ⟨785894, by rfl⟩ : syracuseStep 4191437 = 1571789) B1571789
theorem B1471699 : Blo 1289963 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B1291475 : Blo 1289963 1291475 := bstep (se 1 (by rfl) ⟨968606, by rfl⟩ : syracuseStep 1291475 = 1937213) B1937213
theorem B1291491 : Blo 1289963 1291491 := bstep (se 1 (by rfl) ⟨968618, by rfl⟩ : syracuseStep 1291491 = 1937237) B1937237
theorem B1291507 : Blo 1289963 1291507 := bstep (se 1 (by rfl) ⟨968630, by rfl⟩ : syracuseStep 1291507 = 1937261) B1937261
theorem B1291523 : Blo 1289963 1291523 := bstep (se 1 (by rfl) ⟨968642, by rfl⟩ : syracuseStep 1291523 = 1937285) B1937285
theorem B7353605 : Blo 1289963 7353605 := bstep (se 4 (by rfl) ⟨689400, by rfl⟩ : syracuseStep 7353605 = 1378801) B1378801
theorem B2905361 : Blo 1289963 2905361 := bstep (se 2 (by rfl) ⟨1089510, by rfl⟩ : syracuseStep 2905361 = 2179021) B2179021
theorem B1291539 : Blo 1289963 1291539 := bstep (se 1 (by rfl) ⟨968654, by rfl⟩ : syracuseStep 1291539 = 1937309) B1937309
theorem B2905379 : Blo 1289963 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B1291555 : Blo 1289963 1291555 := bstep (se 1 (by rfl) ⟨968666, by rfl⟩ : syracuseStep 1291555 = 1937333) B1937333
theorem B1291571 : Blo 1289963 1291571 := bstep (se 1 (by rfl) ⟨968678, by rfl⟩ : syracuseStep 1291571 = 1937357) B1937357
theorem B3265859 : Blo 1289963 3265859 := bstep (se 1 (by rfl) ⟨2449394, by rfl⟩ : syracuseStep 3265859 = 4898789) B4898789
theorem B1291587 : Blo 1289963 1291587 := bstep (se 1 (by rfl) ⟨968690, by rfl⟩ : syracuseStep 1291587 = 1937381) B1937381
theorem B6206797 : Blo 1289963 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B2618705 : Blo 1289963 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B1291603 : Blo 1289963 1291603 := bstep (se 1 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 1291603 = 1937405) B1937405
theorem B2209123 : Blo 1289963 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B1291619 : Blo 1289963 1291619 := bstep (se 1 (by rfl) ⟨968714, by rfl⟩ : syracuseStep 1291619 = 1937429) B1937429
theorem B1291635 : Blo 1289963 1291635 := bstep (se 1 (by rfl) ⟨968726, by rfl⟩ : syracuseStep 1291635 = 1937453) B1937453
theorem B1291651 : Blo 1289963 1291651 := bstep (se 1 (by rfl) ⟨968738, by rfl⟩ : syracuseStep 1291651 = 1937477) B1937477
theorem B4904333 : Blo 1289963 4904333 := bstep (se 3 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 4904333 = 1839125) B1839125
theorem B1291667 : Blo 1289963 1291667 := bstep (se 1 (by rfl) ⟨968750, by rfl⟩ : syracuseStep 1291667 = 1937501) B1937501
theorem B1291683 : Blo 1289963 1291683 := bstep (se 1 (by rfl) ⟨968762, by rfl⟩ : syracuseStep 1291683 = 1937525) B1937525
theorem B2618801 : Blo 1289963 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B1291699 : Blo 1289963 1291699 := bstep (se 1 (by rfl) ⟨968774, by rfl⟩ : syracuseStep 1291699 = 1937549) B1937549
theorem B1291715 : Blo 1289963 1291715 := bstep (se 1 (by rfl) ⟨968786, by rfl⟩ : syracuseStep 1291715 = 1937573) B1937573
theorem B1291731 : Blo 1289963 1291731 := bstep (se 1 (by rfl) ⟨968798, by rfl⟩ : syracuseStep 1291731 = 1937597) B1937597
theorem B1291747 : Blo 1289963 1291747 := bstep (se 1 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 1291747 = 1937621) B1937621
theorem B1291763 : Blo 1289963 1291763 := bstep (se 1 (by rfl) ⟨968822, by rfl⟩ : syracuseStep 1291763 = 1937645) B1937645
theorem B1291779 : Blo 1289963 1291779 := bstep (se 1 (by rfl) ⟨968834, by rfl⟩ : syracuseStep 1291779 = 1937669) B1937669
theorem B1291795 : Blo 1289963 1291795 := bstep (se 1 (by rfl) ⟨968846, by rfl⟩ : syracuseStep 1291795 = 1937693) B1937693
theorem B1291811 : Blo 1289963 1291811 := bstep (se 1 (by rfl) ⟨968858, by rfl⟩ : syracuseStep 1291811 = 1937717) B1937717
theorem B2905649 : Blo 1289963 2905649 := bstep (se 2 (by rfl) ⟨1089618, by rfl⟩ : syracuseStep 2905649 = 2179237) B2179237
theorem B1291827 : Blo 1289963 1291827 := bstep (se 1 (by rfl) ⟨968870, by rfl⟩ : syracuseStep 1291827 = 1937741) B1937741
theorem B2905667 : Blo 1289963 2905667 := bstep (se 1 (by rfl) ⟨2179250, by rfl⟩ : syracuseStep 2905667 = 4358501) B4358501
theorem B1291843 : Blo 1289963 1291843 := bstep (se 1 (by rfl) ⟨968882, by rfl⟩ : syracuseStep 1291843 = 1937765) B1937765
theorem B1291859 : Blo 1289963 1291859 := bstep (se 1 (by rfl) ⟨968894, by rfl⟩ : syracuseStep 1291859 = 1937789) B1937789
theorem B6534755 : Blo 1289963 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B1291875 : Blo 1289963 1291875 := bstep (se 1 (by rfl) ⟨968906, by rfl⟩ : syracuseStep 1291875 = 1937813) B1937813
theorem B4355693 : Blo 1289963 4355693 := bstep (se 3 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 4355693 = 1633385) B1633385
theorem B1291891 : Blo 1289963 1291891 := bstep (se 1 (by rfl) ⟨968918, by rfl⟩ : syracuseStep 1291891 = 1937837) B1937837
theorem B1291907 : Blo 1289963 1291907 := bstep (se 1 (by rfl) ⟨968930, by rfl⟩ : syracuseStep 1291907 = 1937861) B1937861
theorem B20936333 : Blo 1289963 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B22066829 : Blo 1289963 22066829 := bstep (se 3 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 22066829 = 8275061) B8275061
theorem B1291923 : Blo 1289963 1291923 := bstep (se 1 (by rfl) ⟨968942, by rfl⟩ : syracuseStep 1291923 = 1937885) B1937885
theorem B4355747 : Blo 1289963 4355747 := bstep (se 1 (by rfl) ⟨3266810, by rfl⟩ : syracuseStep 4355747 = 6533621) B6533621
theorem B1291939 : Blo 1289963 1291939 := bstep (se 1 (by rfl) ⟨968954, by rfl⟩ : syracuseStep 1291939 = 1937909) B1937909
theorem B1291955 : Blo 1289963 1291955 := bstep (se 1 (by rfl) ⟨968966, by rfl⟩ : syracuseStep 1291955 = 1937933) B1937933
theorem B7354061 : Blo 1289963 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B8271629 : Blo 1289963 8271629 := bstep (se 3 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 8271629 = 3101861) B3101861
theorem B2094913 : Blo 1289963 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B2905937 : Blo 1289963 2905937 := bstep (se 2 (by rfl) ⟨1089726, by rfl⟩ : syracuseStep 2905937 = 2179453) B2179453
theorem B2905955 : Blo 1289963 2905955 := bstep (se 1 (by rfl) ⟨2179466, by rfl⟩ : syracuseStep 2905955 = 4358933) B4358933
theorem B2176915 : Blo 1289963 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B1472419 : Blo 1289963 1472419 := bstep (se 1 (by rfl) ⟨1104314, by rfl⟩ : syracuseStep 1472419 = 2208629) B2208629
theorem B4356017 : Blo 1289963 4356017 := bstep (se 2 (by rfl) ⟨1633506, by rfl⟩ : syracuseStep 4356017 = 3267013) B3267013
theorem B1963955 : Blo 1289963 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B2758627 : Blo 1289963 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B1964003 : Blo 1289963 1964003 := bstep (se 1 (by rfl) ⟨1473002, by rfl⟩ : syracuseStep 1964003 = 2946005) B2946005
theorem B2177057 : Blo 1289963 2177057 := bstep (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) B1632793
theorem B2906225 : Blo 1289963 2906225 := bstep (se 2 (by rfl) ⟨1089834, by rfl⟩ : syracuseStep 2906225 = 2179669) B2179669
theorem B2906243 : Blo 1289963 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B2177185 : Blo 1289963 2177185 := bstep (se 2 (by rfl) ⟨816444, by rfl⟩ : syracuseStep 2177185 = 1632889) B1632889
theorem B3676337 : Blo 1289963 3676337 := bstep (se 2 (by rfl) ⟨1378626, by rfl⟩ : syracuseStep 3676337 = 2757253) B2757253
theorem B4905137 : Blo 1289963 4905137 := bstep (se 2 (by rfl) ⟨1839426, by rfl⟩ : syracuseStep 4905137 = 3678853) B3678853
theorem B2177219 : Blo 1289963 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B31832261 : Blo 1289963 31832261 := bstep (se 4 (by rfl) ⟨2984274, by rfl⟩ : syracuseStep 31832261 = 5968549) B5968549
theorem B3266801 : Blo 1289963 3266801 := bstep (se 2 (by rfl) ⟨1225050, by rfl⟩ : syracuseStep 3266801 = 2450101) B2450101
theorem B1767683 : Blo 1289963 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B3266851 : Blo 1289963 3266851 := bstep (se 1 (by rfl) ⟨2450138, by rfl⟩ : syracuseStep 3266851 = 4900277) B4900277
theorem B2758961 : Blo 1289963 2758961 := bstep (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) B2069221
theorem B2177347 : Blo 1289963 2177347 := bstep (se 1 (by rfl) ⟨1633010, by rfl⟩ : syracuseStep 2177347 = 3266021) B3266021
theorem B3676529 : Blo 1289963 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B6535565 : Blo 1289963 6535565 := bstep (se 3 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 6535565 = 2450837) B2450837
theorem B2906513 : Blo 1289963 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B2906531 : Blo 1289963 2906531 := bstep (se 1 (by rfl) ⟨2179898, by rfl⟩ : syracuseStep 2906531 = 4359797) B4359797
theorem B3266993 : Blo 1289963 3266993 := bstep (se 2 (by rfl) ⟨1225122, by rfl⟩ : syracuseStep 3266993 = 2450245) B2450245
theorem B4356557 : Blo 1289963 4356557 := bstep (se 3 (by rfl) ⟨816854, by rfl⟩ : syracuseStep 4356557 = 1633709) B1633709
theorem B2177489 : Blo 1289963 2177489 := bstep (se 2 (by rfl) ⟨816558, by rfl⟩ : syracuseStep 2177489 = 1633117) B1633117
theorem B4356611 : Blo 1289963 4356611 := bstep (se 1 (by rfl) ⟨3267458, by rfl⟩ : syracuseStep 4356611 = 6534917) B6534917
theorem B11024909 : Blo 1289963 11024909 := bstep (se 3 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 11024909 = 4134341) B4134341
theorem B2177617 : Blo 1289963 2177617 := bstep (se 2 (by rfl) ⟨816606, by rfl⟩ : syracuseStep 2177617 = 1633213) B1633213
theorem B9435761 : Blo 1289963 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B2177651 : Blo 1289963 2177651 := bstep (se 1 (by rfl) ⟨1633238, by rfl⟩ : syracuseStep 2177651 = 3266477) B3266477
theorem B2906801 : Blo 1289963 2906801 := bstep (se 2 (by rfl) ⟨1090050, by rfl⟩ : syracuseStep 2906801 = 2180101) B2180101
theorem B2906819 : Blo 1289963 2906819 := bstep (se 1 (by rfl) ⟨2180114, by rfl⟩ : syracuseStep 2906819 = 4360229) B4360229
theorem B2177779 : Blo 1289963 2177779 := bstep (se 1 (by rfl) ⟨1633334, by rfl⟩ : syracuseStep 2177779 = 3266669) B3266669
theorem B14695181 : Blo 1289963 14695181 := bstep (se 3 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 14695181 = 5510693) B5510693
theorem B4356881 : Blo 1289963 4356881 := bstep (se 2 (by rfl) ⟨1633830, by rfl⟩ : syracuseStep 4356881 = 3267661) B3267661
theorem B2177921 : Blo 1289963 2177921 := bstep (se 2 (by rfl) ⟨816720, by rfl⟩ : syracuseStep 2177921 = 1633441) B1633441
theorem B3488707 : Blo 1289963 3488707 := bstep (se 1 (by rfl) ⟨2616530, by rfl⟩ : syracuseStep 3488707 = 5233061) B5233061
theorem B2178049 : Blo 1289963 2178049 := bstep (se 2 (by rfl) ⟨816768, by rfl⟩ : syracuseStep 2178049 = 1633537) B1633537
theorem B2178083 : Blo 1289963 2178083 := bstep (se 1 (by rfl) ⟨1633562, by rfl⟩ : syracuseStep 2178083 = 3267125) B3267125
theorem B2358371 : Blo 1289963 2358371 := bstep (se 1 (by rfl) ⟨1768778, by rfl⟩ : syracuseStep 2358371 = 3537557) B3537557
theorem B2178211 : Blo 1289963 2178211 := bstep (se 1 (by rfl) ⟨1633658, by rfl⟩ : syracuseStep 2178211 = 3267317) B3267317
theorem B4357421 : Blo 1289963 4357421 := bstep (se 3 (by rfl) ⟨817016, by rfl⟩ : syracuseStep 4357421 = 1634033) B1634033
theorem B2178353 : Blo 1289963 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B3677521 : Blo 1289963 3677521 := bstep (se 2 (by rfl) ⟨1379070, by rfl⟩ : syracuseStep 3677521 = 2758141) B2758141
theorem B4357475 : Blo 1289963 4357475 := bstep (se 1 (by rfl) ⟨3268106, by rfl⟩ : syracuseStep 4357475 = 6536213) B6536213
theorem B3267985 : Blo 1289963 3267985 := bstep (se 2 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 3267985 = 2450989) B2450989
theorem B2178481 : Blo 1289963 2178481 := bstep (se 2 (by rfl) ⟨816930, by rfl⟩ : syracuseStep 2178481 = 1633861) B1633861
theorem B2178515 : Blo 1289963 2178515 := bstep (se 1 (by rfl) ⟨1633886, by rfl⟩ : syracuseStep 2178515 = 3267773) B3267773
theorem B2178643 : Blo 1289963 2178643 := bstep (se 1 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 2178643 = 3267965) B3267965
theorem B1744483 : Blo 1289963 1744483 := bstep (se 1 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 1744483 = 2616725) B2616725
theorem B3677795 : Blo 1289963 3677795 := bstep (se 1 (by rfl) ⟨2758346, by rfl⟩ : syracuseStep 3677795 = 5516693) B5516693
theorem B14900849 : Blo 1289963 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B4357745 : Blo 1289963 4357745 := bstep (se 2 (by rfl) ⟨1634154, by rfl⟩ : syracuseStep 4357745 = 3268309) B3268309
theorem B4193905 : Blo 1289963 4193905 := bstep (se 2 (by rfl) ⟨1572714, by rfl⟩ : syracuseStep 4193905 = 3145429) B3145429
theorem B3268259 : Blo 1289963 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2449091 : Blo 1289963 2449091 := bstep (se 1 (by rfl) ⟨1836818, by rfl⟩ : syracuseStep 2449091 = 3673637) B3673637
theorem B3489485 : Blo 1289963 3489485 := bstep (se 3 (by rfl) ⟨654278, by rfl⟩ : syracuseStep 3489485 = 1308557) B1308557
theorem B2178785 : Blo 1289963 2178785 := bstep (se 2 (by rfl) ⟨817044, by rfl⟩ : syracuseStep 2178785 = 1634089) B1634089
theorem B3677987 : Blo 1289963 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B16539461 : Blo 1289963 16539461 := bstep (se 4 (by rfl) ⟨1550574, by rfl⟩ : syracuseStep 16539461 = 3101149) B3101149
theorem B2178913 : Blo 1289963 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B3268451 : Blo 1289963 3268451 := bstep (se 1 (by rfl) ⟨2451338, by rfl⟩ : syracuseStep 3268451 = 4902677) B4902677
theorem B2178947 : Blo 1289963 2178947 := bstep (se 1 (by rfl) ⟨1634210, by rfl⟩ : syracuseStep 2178947 = 3268421) B3268421
theorem B2449379 : Blo 1289963 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B4898819 : Blo 1289963 4898819 := bstep (se 1 (by rfl) ⟨3674114, by rfl⟩ : syracuseStep 4898819 = 7348229) B7348229
theorem B2449433 : Blo 1289963 2449433 := bstep (se 2 (by rfl) ⟨918537, by rfl⟩ : syracuseStep 2449433 = 1837075) B1837075
theorem B5513291 : Blo 1289963 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B6537347 : Blo 1289963 6537347 := bstep (se 1 (by rfl) ⟨4903010, by rfl⟩ : syracuseStep 6537347 = 9806021) B9806021
theorem B8274241 : Blo 1289963 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B4899275 : Blo 1289963 4899275 := bstep (se 1 (by rfl) ⟨3674456, by rfl⟩ : syracuseStep 4899275 = 7348913) B7348913
theorem B3490265 : Blo 1289963 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B2179595 : Blo 1289963 2179595 := bstep (se 1 (by rfl) ⟨1634696, by rfl⟩ : syracuseStep 2179595 = 3269393) B3269393
theorem B3727937 : Blo 1289963 3727937 := bstep (se 2 (by rfl) ⟨1397976, by rfl⟩ : syracuseStep 3727937 = 2795953) B2795953
theorem B9798245 : Blo 1289963 9798245 := bstep (se 4 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 9798245 = 1837171) B1837171
theorem B2179723 : Blo 1289963 2179723 := bstep (se 1 (by rfl) ⟨1634792, by rfl⟩ : syracuseStep 2179723 = 3269585) B3269585
theorem B4899473 : Blo 1289963 4899473 := bstep (se 2 (by rfl) ⟨1837302, by rfl⟩ : syracuseStep 4899473 = 3674605) B3674605
theorem B2179865 : Blo 1289963 2179865 := bstep (se 2 (by rfl) ⟨817449, by rfl⟩ : syracuseStep 2179865 = 1634899) B1634899
theorem B7357229 : Blo 1289963 7357229 := bstep (se 3 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 7357229 = 2758961) B2758961
theorem B4358987 : Blo 1289963 4358987 := bstep (se 1 (by rfl) ⟨3269240, by rfl⟩ : syracuseStep 4358987 = 6538481) B6538481
theorem B1745803 : Blo 1289963 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B2327449 : Blo 1289963 2327449 := bstep (se 2 (by rfl) ⟨872793, by rfl⟩ : syracuseStep 2327449 = 1745587) B1745587
theorem B2179993 : Blo 1289963 2179993 := bstep (se 2 (by rfl) ⟨817497, by rfl⟩ : syracuseStep 2179993 = 1634995) B1634995
theorem B3269555 : Blo 1289963 3269555 := bstep (se 1 (by rfl) ⟨2452166, by rfl⟩ : syracuseStep 3269555 = 4904333) B4904333
theorem B1745867 : Blo 1289963 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B9798731 : Blo 1289963 9798731 := bstep (se 1 (by rfl) ⟨7349048, by rfl⟩ : syracuseStep 9798731 = 14698097) B14698097
theorem B4359257 : Blo 1289963 4359257 := bstep (se 2 (by rfl) ⟨1634721, by rfl⟩ : syracuseStep 4359257 = 3269443) B3269443
theorem B7849061 : Blo 1289963 7849061 := bstep (se 4 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 7849061 = 1471699) B1471699
theorem B1655959 : Blo 1289963 1655959 := bstep (se 1 (by rfl) ⟨1241969, by rfl⟩ : syracuseStep 1655959 = 2483939) B2483939
theorem B5514419 : Blo 1289963 5514419 := bstep (se 1 (by rfl) ⟨4135814, by rfl⟩ : syracuseStep 5514419 = 8271629) B8271629
theorem B1451371 : Blo 1289963 1451371 := bstep (se 1 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 1451371 = 2177057) B2177057
theorem B4900247 : Blo 1289963 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B2450891 : Blo 1289963 2450891 := bstep (se 1 (by rfl) ⟨1838168, by rfl⟩ : syracuseStep 2450891 = 3676337) B3676337
theorem B2328011 : Blo 1289963 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B3270091 : Blo 1289963 3270091 := bstep (se 1 (by rfl) ⟨2452568, by rfl⟩ : syracuseStep 3270091 = 4905137) B4905137
theorem B1451479 : Blo 1289963 1451479 := bstep (se 1 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 1451479 = 2177219) B2177219
theorem B3270233 : Blo 1289963 3270233 := bstep (se 2 (by rfl) ⟨1226337, by rfl⟩ : syracuseStep 3270233 = 2452675) B2452675
theorem B4900445 : Blo 1289963 4900445 := bstep (se 3 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 4900445 = 1837667) B1837667
theorem B2451073 : Blo 1289963 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B8947331 : Blo 1289963 8947331 := bstep (se 1 (by rfl) ⟨6710498, by rfl⟩ : syracuseStep 8947331 = 13420997) B13420997
theorem B1934987 : Blo 1289963 1934987 := bstep (se 1 (by rfl) ⟨1451240, by rfl⟩ : syracuseStep 1934987 = 2902481) B2902481
theorem B1451659 : Blo 1289963 1451659 := bstep (se 1 (by rfl) ⟨1088744, by rfl⟩ : syracuseStep 1451659 = 2177489) B2177489
theorem B1492619 : Blo 1289963 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B1934999 : Blo 1289963 1934999 := bstep (se 1 (by rfl) ⟨1451249, by rfl⟩ : syracuseStep 1934999 = 2902499) B2902499
theorem B7349939 : Blo 1289963 7349939 := bstep (se 1 (by rfl) ⟨5512454, by rfl⟩ : syracuseStep 7349939 = 11024909) B11024909
theorem B1836761 : Blo 1289963 1836761 := bstep (se 2 (by rfl) ⟨688785, by rfl⟩ : syracuseStep 1836761 = 1377571) B1377571
theorem B1935065 : Blo 1289963 1935065 := bstep (se 2 (by rfl) ⟨725649, by rfl⟩ : syracuseStep 1935065 = 1451299) B1451299
theorem B1451767 : Blo 1289963 1451767 := bstep (se 1 (by rfl) ⟨1088825, by rfl⟩ : syracuseStep 1451767 = 2177651) B2177651
theorem B8275729 : Blo 1289963 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B4359959 : Blo 1289963 4359959 := bstep (se 1 (by rfl) ⟨3269969, by rfl⟩ : syracuseStep 4359959 = 6539939) B6539939
theorem B1935179 : Blo 1289963 1935179 := bstep (se 1 (by rfl) ⟨1451384, by rfl⟩ : syracuseStep 1935179 = 2902769) B2902769
theorem B1836875 : Blo 1289963 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1935191 : Blo 1289963 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B1378135 : Blo 1289963 1378135 := bstep (se 1 (by rfl) ⟨1033601, by rfl⟩ : syracuseStep 1378135 = 2067203) B2067203
theorem B1935257 : Blo 1289963 1935257 := bstep (se 2 (by rfl) ⟨725721, by rfl⟩ : syracuseStep 1935257 = 1451443) B1451443
theorem B1451947 : Blo 1289963 1451947 := bstep (se 1 (by rfl) ⟨1088960, by rfl⟩ : syracuseStep 1451947 = 2177921) B2177921
theorem B1935371 : Blo 1289963 1935371 := bstep (se 1 (by rfl) ⟨1451528, by rfl⟩ : syracuseStep 1935371 = 2903057) B2903057
theorem B21235729 : Blo 1289963 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1935383 : Blo 1289963 1935383 := bstep (se 1 (by rfl) ⟨1451537, by rfl⟩ : syracuseStep 1935383 = 2903075) B2903075
theorem B1452055 : Blo 1289963 1452055 := bstep (se 1 (by rfl) ⟨1089041, by rfl⟩ : syracuseStep 1452055 = 2178083) B2178083
theorem B2451521 : Blo 1289963 2451521 := bstep (se 2 (by rfl) ⟨919320, by rfl⟩ : syracuseStep 2451521 = 1838641) B1838641
theorem B1378391 : Blo 1289963 1378391 := bstep (se 1 (by rfl) ⟨1033793, by rfl⟩ : syracuseStep 1378391 = 2067587) B2067587
theorem B1935449 : Blo 1289963 1935449 := bstep (se 2 (by rfl) ⟨725793, by rfl⟩ : syracuseStep 1935449 = 1451587) B1451587
theorem B9807965 : Blo 1289963 9807965 := bstep (se 3 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 9807965 = 3677987) B3677987
theorem B1935563 : Blo 1289963 1935563 := bstep (se 1 (by rfl) ⟨1451672, by rfl⟩ : syracuseStep 1935563 = 2903345) B2903345
theorem B1452235 : Blo 1289963 1452235 := bstep (se 1 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 1452235 = 2178353) B2178353
theorem B1935575 : Blo 1289963 1935575 := bstep (se 1 (by rfl) ⟨1451681, by rfl⟩ : syracuseStep 1935575 = 2903363) B2903363
theorem B1935641 : Blo 1289963 1935641 := bstep (se 2 (by rfl) ⟨725865, by rfl⟩ : syracuseStep 1935641 = 1451731) B1451731
theorem B1452343 : Blo 1289963 1452343 := bstep (se 1 (by rfl) ⟨1089257, by rfl⟩ : syracuseStep 1452343 = 2178515) B2178515
theorem B1837399 : Blo 1289963 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B1935755 : Blo 1289963 1935755 := bstep (se 1 (by rfl) ⟨1451816, by rfl⟩ : syracuseStep 1935755 = 2903633) B2903633
theorem B1935767 : Blo 1289963 1935767 := bstep (se 1 (by rfl) ⟨1451825, by rfl⟩ : syracuseStep 1935767 = 2903651) B2903651
theorem B2451863 : Blo 1289963 2451863 := bstep (se 1 (by rfl) ⟨1838897, by rfl⟩ : syracuseStep 2451863 = 3677795) B3677795
theorem B1632727 : Blo 1289963 1632727 := bstep (se 1 (by rfl) ⟨1224545, by rfl⟩ : syracuseStep 1632727 = 2449091) B2449091
theorem B1935833 : Blo 1289963 1935833 := bstep (se 2 (by rfl) ⟨725937, by rfl⟩ : syracuseStep 1935833 = 1451875) B1451875
theorem B1452523 : Blo 1289963 1452523 := bstep (se 1 (by rfl) ⟨1089392, by rfl⟩ : syracuseStep 1452523 = 2178785) B2178785
theorem B2902553 : Blo 1289963 2902553 := bstep (se 2 (by rfl) ⟨1088457, by rfl⟩ : syracuseStep 2902553 = 2176915) B2176915
theorem B10619437 : Blo 1289963 10619437 := bstep (se 3 (by rfl) ⟨1991144, by rfl⟩ : syracuseStep 10619437 = 3982289) B3982289
theorem B1935947 : Blo 1289963 1935947 := bstep (se 1 (by rfl) ⟨1451960, by rfl⟩ : syracuseStep 1935947 = 2903921) B2903921
theorem B3312203 : Blo 1289963 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B1935959 : Blo 1289963 1935959 := bstep (se 1 (by rfl) ⟨1451969, by rfl⟩ : syracuseStep 1935959 = 2903939) B2903939
theorem B1452631 : Blo 1289963 1452631 := bstep (se 1 (by rfl) ⟨1089473, by rfl⟩ : syracuseStep 1452631 = 2178947) B2178947
theorem B6531677 : Blo 1289963 6531677 := bstep (se 3 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 6531677 = 2449379) B2449379
theorem B6982237 : Blo 1289963 6982237 := bstep (se 3 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 6982237 = 2618339) B2618339
theorem B5237341 : Blo 1289963 5237341 := bstep (se 3 (by rfl) ⟨982001, by rfl⟩ : syracuseStep 5237341 = 1964003) B1964003
theorem B2902643 : Blo 1289963 2902643 := bstep (se 1 (by rfl) ⟨2176982, by rfl⟩ : syracuseStep 2902643 = 4353965) B4353965
theorem B1378955 : Blo 1289963 1378955 := bstep (se 1 (by rfl) ⟨1034216, by rfl⟩ : syracuseStep 1378955 = 2068433) B2068433
theorem B2902679 : Blo 1289963 2902679 := bstep (se 1 (by rfl) ⟨2177009, by rfl⟩ : syracuseStep 2902679 = 4354019) B4354019
theorem B1936025 : Blo 1289963 1936025 := bstep (se 2 (by rfl) ⟨726009, by rfl⟩ : syracuseStep 1936025 = 1452019) B1452019
theorem B3926731 : Blo 1289963 3926731 := bstep (se 1 (by rfl) ⟨2945048, by rfl⟩ : syracuseStep 3926731 = 5890097) B5890097
theorem B4655819 : Blo 1289963 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1936139 : Blo 1289963 1936139 := bstep (se 1 (by rfl) ⟨1452104, by rfl⟩ : syracuseStep 1936139 = 2904209) B2904209
theorem B1452811 : Blo 1289963 1452811 := bstep (se 1 (by rfl) ⟨1089608, by rfl⟩ : syracuseStep 1452811 = 2179217) B2179217
theorem B1936151 : Blo 1289963 1936151 := bstep (se 1 (by rfl) ⟨1452113, by rfl⟩ : syracuseStep 1936151 = 2904227) B2904227
theorem B11029283 : Blo 1289963 11029283 := bstep (se 1 (by rfl) ⟨8271962, by rfl⟩ : syracuseStep 11029283 = 16543925) B16543925
theorem B2902859 : Blo 1289963 2902859 := bstep (se 1 (by rfl) ⟨2177144, by rfl⟩ : syracuseStep 2902859 = 4354289) B4354289
theorem B2755415 : Blo 1289963 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B1936217 : Blo 1289963 1936217 := bstep (se 2 (by rfl) ⟨726081, by rfl⟩ : syracuseStep 1936217 = 1452163) B1452163
theorem B1452919 : Blo 1289963 1452919 := bstep (se 1 (by rfl) ⟨1089689, by rfl⟩ : syracuseStep 1452919 = 2179379) B2179379
theorem B2902913 : Blo 1289963 2902913 := bstep (se 2 (by rfl) ⟨1088592, by rfl⟩ : syracuseStep 2902913 = 2177185) B2177185
theorem B1936331 : Blo 1289963 1936331 := bstep (se 1 (by rfl) ⟨1452248, by rfl⟩ : syracuseStep 1936331 = 2904497) B2904497
theorem B3926987 : Blo 1289963 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B1936343 : Blo 1289963 1936343 := bstep (se 1 (by rfl) ⟨1452257, by rfl⟩ : syracuseStep 1936343 = 2904515) B2904515
theorem B1936409 : Blo 1289963 1936409 := bstep (se 2 (by rfl) ⟨726153, by rfl⟩ : syracuseStep 1936409 = 1452307) B1452307
theorem B9301027 : Blo 1289963 9301027 := bstep (se 1 (by rfl) ⟨6975770, by rfl⟩ : syracuseStep 9301027 = 13951541) B13951541
theorem B14699555 : Blo 1289963 14699555 := bstep (se 1 (by rfl) ⟨11024666, by rfl⟩ : syracuseStep 14699555 = 22049333) B22049333
theorem B1453099 : Blo 1289963 1453099 := bstep (se 1 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 1453099 = 2179649) B2179649
theorem B5516333 : Blo 1289963 5516333 := bstep (se 3 (by rfl) ⟨1034312, by rfl⟩ : syracuseStep 5516333 = 2068625) B2068625
theorem B2452531 : Blo 1289963 2452531 := bstep (se 1 (by rfl) ⟨1839398, by rfl⟩ : syracuseStep 2452531 = 3678797) B3678797
theorem B47123531 : Blo 1289963 47123531 := bstep (se 1 (by rfl) ⟨35342648, by rfl⟩ : syracuseStep 47123531 = 70685297) B70685297
theorem B2903129 : Blo 1289963 2903129 := bstep (se 2 (by rfl) ⟨1088673, by rfl⟩ : syracuseStep 2903129 = 2177347) B2177347
theorem B7351397 : Blo 1289963 7351397 := bstep (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) B1378387
theorem B2755723 : Blo 1289963 2755723 := bstep (se 1 (by rfl) ⟨2066792, by rfl⟩ : syracuseStep 2755723 = 4133585) B4133585
theorem B1936523 : Blo 1289963 1936523 := bstep (se 1 (by rfl) ⟨1452392, by rfl⟩ : syracuseStep 1936523 = 2904785) B2904785
theorem B1838219 : Blo 1289963 1838219 := bstep (se 1 (by rfl) ⟨1378664, by rfl⟩ : syracuseStep 1838219 = 2757329) B2757329
theorem B1936535 : Blo 1289963 1936535 := bstep (se 1 (by rfl) ⟨1452401, by rfl⟩ : syracuseStep 1936535 = 2904803) B2904803
theorem B1453207 : Blo 1289963 1453207 := bstep (se 1 (by rfl) ⟨1089905, by rfl⟩ : syracuseStep 1453207 = 2179811) B2179811
theorem B2903219 : Blo 1289963 2903219 := bstep (se 1 (by rfl) ⟨2177414, by rfl⟩ : syracuseStep 2903219 = 4354829) B4354829
theorem B11177165 : Blo 1289963 11177165 := bstep (se 3 (by rfl) ⟨2095718, by rfl⟩ : syracuseStep 11177165 = 4191437) B4191437
theorem B2903255 : Blo 1289963 2903255 := bstep (se 1 (by rfl) ⟨2177441, by rfl⟩ : syracuseStep 2903255 = 4354883) B4354883
theorem B1936601 : Blo 1289963 1936601 := bstep (se 2 (by rfl) ⟨726225, by rfl⟩ : syracuseStep 1936601 = 1452451) B1452451
theorem B1633547 : Blo 1289963 1633547 := bstep (se 1 (by rfl) ⟨1225160, by rfl⟩ : syracuseStep 1633547 = 2450321) B2450321
theorem B1936715 : Blo 1289963 1936715 := bstep (se 1 (by rfl) ⟨1452536, by rfl⟩ : syracuseStep 1936715 = 2905073) B2905073
theorem B1453387 : Blo 1289963 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B1936727 : Blo 1289963 1936727 := bstep (se 1 (by rfl) ⟨1452545, by rfl⟩ : syracuseStep 1936727 = 2905091) B2905091
theorem B4713821 : Blo 1289963 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B7957853 : Blo 1289963 7957853 := bstep (se 3 (by rfl) ⟨1492097, by rfl⟩ : syracuseStep 7957853 = 2984195) B2984195
theorem B2903435 : Blo 1289963 2903435 := bstep (se 1 (by rfl) ⟨2177576, by rfl⟩ : syracuseStep 2903435 = 4355153) B4355153
theorem B1936793 : Blo 1289963 1936793 := bstep (se 2 (by rfl) ⟨726297, by rfl⟩ : syracuseStep 1936793 = 1452595) B1452595
theorem B2903489 : Blo 1289963 2903489 := bstep (se 2 (by rfl) ⟨1088808, by rfl⟩ : syracuseStep 2903489 = 2177617) B2177617
theorem B1961419 : Blo 1289963 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B4902403 : Blo 1289963 4902403 := bstep (se 1 (by rfl) ⟨3676802, by rfl⟩ : syracuseStep 4902403 = 7353605) B7353605
theorem B1936907 : Blo 1289963 1936907 := bstep (se 1 (by rfl) ⟨1452680, by rfl⟩ : syracuseStep 1936907 = 2905361) B2905361
theorem B1936919 : Blo 1289963 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B1936985 : Blo 1289963 1936985 := bstep (se 2 (by rfl) ⟨726369, by rfl⟩ : syracuseStep 1936985 = 1452739) B1452739
theorem B2903705 : Blo 1289963 2903705 := bstep (se 2 (by rfl) ⟨1088889, by rfl⟩ : syracuseStep 2903705 = 2177779) B2177779
theorem B1937099 : Blo 1289963 1937099 := bstep (se 1 (by rfl) ⟨1452824, by rfl⟩ : syracuseStep 1937099 = 2905649) B2905649
theorem B1937111 : Blo 1289963 1937111 := bstep (se 1 (by rfl) ⟨1452833, by rfl⟩ : syracuseStep 1937111 = 2905667) B2905667
theorem B5517017 : Blo 1289963 5517017 := bstep (se 2 (by rfl) ⟨2068881, by rfl⟩ : syracuseStep 5517017 = 4137763) B4137763
theorem B1289963 : Blo 1289963 1289963 := bstep (se 1 (by rfl) ⟨967472, by rfl⟩ : syracuseStep 1289963 = 1934945) B1934945
theorem B2903795 : Blo 1289963 2903795 := bstep (se 1 (by rfl) ⟨2177846, by rfl⟩ : syracuseStep 2903795 = 4355693) B4355693
theorem B1289975 : Blo 1289963 1289975 := bstep (se 1 (by rfl) ⟨967481, by rfl⟩ : syracuseStep 1289975 = 1934963) B1934963
theorem B1289995 : Blo 1289963 1289995 := bstep (se 1 (by rfl) ⟨967496, by rfl⟩ : syracuseStep 1289995 = 1934993) B1934993
theorem B1290007 : Blo 1289963 1290007 := bstep (se 1 (by rfl) ⟨967505, by rfl⟩ : syracuseStep 1290007 = 1935011) B1935011
theorem B2903831 : Blo 1289963 2903831 := bstep (se 1 (by rfl) ⟨2177873, by rfl⟩ : syracuseStep 2903831 = 4355747) B4355747
theorem B1937177 : Blo 1289963 1937177 := bstep (se 2 (by rfl) ⟨726441, by rfl⟩ : syracuseStep 1937177 = 1452883) B1452883
theorem B1290027 : Blo 1289963 1290027 := bstep (se 1 (by rfl) ⟨967520, by rfl⟩ : syracuseStep 1290027 = 1935041) B1935041
theorem B4902707 : Blo 1289963 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B1290039 : Blo 1289963 1290039 := bstep (se 1 (by rfl) ⟨967529, by rfl⟩ : syracuseStep 1290039 = 1935059) B1935059
theorem B4353857 : Blo 1289963 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B1290059 : Blo 1289963 1290059 := bstep (se 1 (by rfl) ⟨967544, by rfl⟩ : syracuseStep 1290059 = 1935089) B1935089
theorem B1290071 : Blo 1289963 1290071 := bstep (se 1 (by rfl) ⟨967553, by rfl⟩ : syracuseStep 1290071 = 1935107) B1935107
theorem B1961815 : Blo 1289963 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B1290091 : Blo 1289963 1290091 := bstep (se 1 (by rfl) ⟨967568, by rfl⟩ : syracuseStep 1290091 = 1935137) B1935137
theorem B1290103 : Blo 1289963 1290103 := bstep (se 1 (by rfl) ⟨967577, by rfl⟩ : syracuseStep 1290103 = 1935155) B1935155
theorem B1290123 : Blo 1289963 1290123 := bstep (se 1 (by rfl) ⟨967592, by rfl⟩ : syracuseStep 1290123 = 1935185) B1935185
theorem B1937291 : Blo 1289963 1937291 := bstep (se 1 (by rfl) ⟨1452968, by rfl⟩ : syracuseStep 1937291 = 2905937) B2905937
theorem B1290135 : Blo 1289963 1290135 := bstep (se 1 (by rfl) ⟨967601, by rfl⟩ : syracuseStep 1290135 = 1935203) B1935203
theorem B1937303 : Blo 1289963 1937303 := bstep (se 1 (by rfl) ⟨1452977, by rfl⟩ : syracuseStep 1937303 = 2905955) B2905955
theorem B1290155 : Blo 1289963 1290155 := bstep (se 1 (by rfl) ⟨967616, by rfl⟩ : syracuseStep 1290155 = 1935233) B1935233
theorem B1290167 : Blo 1289963 1290167 := bstep (se 1 (by rfl) ⟨967625, by rfl⟩ : syracuseStep 1290167 = 1935251) B1935251
theorem B4714433 : Blo 1289963 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B1290187 : Blo 1289963 1290187 := bstep (se 1 (by rfl) ⟨967640, by rfl⟩ : syracuseStep 1290187 = 1935281) B1935281
theorem B2904011 : Blo 1289963 2904011 := bstep (se 1 (by rfl) ⟨2178008, by rfl⟩ : syracuseStep 2904011 = 4356017) B4356017
theorem B1634251 : Blo 1289963 1634251 := bstep (se 1 (by rfl) ⟨1225688, by rfl⟩ : syracuseStep 1634251 = 2451377) B2451377
theorem B1290199 : Blo 1289963 1290199 := bstep (se 1 (by rfl) ⟨967649, by rfl⟩ : syracuseStep 1290199 = 1935299) B1935299
theorem B1937369 : Blo 1289963 1937369 := bstep (se 2 (by rfl) ⟨726513, by rfl⟩ : syracuseStep 1937369 = 1453027) B1453027
theorem B1290219 : Blo 1289963 1290219 := bstep (se 1 (by rfl) ⟨967664, by rfl⟩ : syracuseStep 1290219 = 1935329) B1935329
theorem B1290231 : Blo 1289963 1290231 := bstep (se 1 (by rfl) ⟨967673, by rfl⟩ : syracuseStep 1290231 = 1935347) B1935347
theorem B2904065 : Blo 1289963 2904065 := bstep (se 2 (by rfl) ⟨1089024, by rfl⟩ : syracuseStep 2904065 = 2178049) B2178049
theorem B1290251 : Blo 1289963 1290251 := bstep (se 1 (by rfl) ⟨967688, by rfl⟩ : syracuseStep 1290251 = 1935377) B1935377
theorem B1290263 : Blo 1289963 1290263 := bstep (se 1 (by rfl) ⟨967697, by rfl⟩ : syracuseStep 1290263 = 1935395) B1935395
theorem B1290283 : Blo 1289963 1290283 := bstep (se 1 (by rfl) ⟨967712, by rfl⟩ : syracuseStep 1290283 = 1935425) B1935425
theorem B1290295 : Blo 1289963 1290295 := bstep (se 1 (by rfl) ⟨967721, by rfl⟩ : syracuseStep 1290295 = 1935443) B1935443
theorem B1290315 : Blo 1289963 1290315 := bstep (se 1 (by rfl) ⟨967736, by rfl⟩ : syracuseStep 1290315 = 1935473) B1935473
theorem B1937483 : Blo 1289963 1937483 := bstep (se 1 (by rfl) ⟨1453112, by rfl⟩ : syracuseStep 1937483 = 2906225) B2906225
theorem B1290327 : Blo 1289963 1290327 := bstep (se 1 (by rfl) ⟨967745, by rfl⟩ : syracuseStep 1290327 = 1935491) B1935491
theorem B1937495 : Blo 1289963 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B1290347 : Blo 1289963 1290347 := bstep (se 1 (by rfl) ⟨967760, by rfl⟩ : syracuseStep 1290347 = 1935521) B1935521
theorem B1290359 : Blo 1289963 1290359 := bstep (se 1 (by rfl) ⟨967769, by rfl⟩ : syracuseStep 1290359 = 1935539) B1935539
theorem B21221507 : Blo 1289963 21221507 := bstep (se 1 (by rfl) ⟨15916130, by rfl⟩ : syracuseStep 21221507 = 31832261) B31832261
theorem B1290379 : Blo 1289963 1290379 := bstep (se 1 (by rfl) ⟨967784, by rfl⟩ : syracuseStep 1290379 = 1935569) B1935569
theorem B1290391 : Blo 1289963 1290391 := bstep (se 1 (by rfl) ⟨967793, by rfl⟩ : syracuseStep 1290391 = 1935587) B1935587
theorem B1937561 : Blo 1289963 1937561 := bstep (se 2 (by rfl) ⟨726585, by rfl⟩ : syracuseStep 1937561 = 1453171) B1453171
theorem B1290411 : Blo 1289963 1290411 := bstep (se 1 (by rfl) ⟨967808, by rfl⟩ : syracuseStep 1290411 = 1935617) B1935617
theorem B1290423 : Blo 1289963 1290423 := bstep (se 1 (by rfl) ⟨967817, by rfl⟩ : syracuseStep 1290423 = 1935635) B1935635
theorem B1290443 : Blo 1289963 1290443 := bstep (se 1 (by rfl) ⟨967832, by rfl⟩ : syracuseStep 1290443 = 1935665) B1935665
theorem B1290455 : Blo 1289963 1290455 := bstep (se 1 (by rfl) ⟨967841, by rfl⟩ : syracuseStep 1290455 = 1935683) B1935683
theorem B2904281 : Blo 1289963 2904281 := bstep (se 2 (by rfl) ⟨1089105, by rfl⟩ : syracuseStep 2904281 = 2178211) B2178211
theorem B1634519 : Blo 1289963 1634519 := bstep (se 1 (by rfl) ⟨1225889, by rfl⟩ : syracuseStep 1634519 = 2451779) B2451779
theorem B1290475 : Blo 1289963 1290475 := bstep (se 1 (by rfl) ⟨967856, by rfl⟩ : syracuseStep 1290475 = 1935713) B1935713
theorem B1290487 : Blo 1289963 1290487 := bstep (se 1 (by rfl) ⟨967865, by rfl⟩ : syracuseStep 1290487 = 1935731) B1935731
theorem B1290507 : Blo 1289963 1290507 := bstep (se 1 (by rfl) ⟨967880, by rfl⟩ : syracuseStep 1290507 = 1935761) B1935761
theorem B1937675 : Blo 1289963 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B1290519 : Blo 1289963 1290519 := bstep (se 1 (by rfl) ⟨967889, by rfl⟩ : syracuseStep 1290519 = 1935779) B1935779
theorem B1937687 : Blo 1289963 1937687 := bstep (se 1 (by rfl) ⟨1453265, by rfl⟩ : syracuseStep 1937687 = 2906531) B2906531
theorem B1290539 : Blo 1289963 1290539 := bstep (se 1 (by rfl) ⟨967904, by rfl⟩ : syracuseStep 1290539 = 1935809) B1935809
theorem B2904371 : Blo 1289963 2904371 := bstep (se 1 (by rfl) ⟨2178278, by rfl⟩ : syracuseStep 2904371 = 4356557) B4356557
theorem B1290551 : Blo 1289963 1290551 := bstep (se 1 (by rfl) ⟨967913, by rfl⟩ : syracuseStep 1290551 = 1935827) B1935827
theorem B1290571 : Blo 1289963 1290571 := bstep (se 1 (by rfl) ⟨967928, by rfl⟩ : syracuseStep 1290571 = 1935857) B1935857
theorem B1290583 : Blo 1289963 1290583 := bstep (se 1 (by rfl) ⟨967937, by rfl⟩ : syracuseStep 1290583 = 1935875) B1935875
theorem B2904407 : Blo 1289963 2904407 := bstep (se 1 (by rfl) ⟨2178305, by rfl⟩ : syracuseStep 2904407 = 4356611) B4356611
theorem B2756953 : Blo 1289963 2756953 := bstep (se 2 (by rfl) ⟨1033857, by rfl⟩ : syracuseStep 2756953 = 2067715) B2067715
theorem B1937753 : Blo 1289963 1937753 := bstep (se 2 (by rfl) ⟨726657, by rfl⟩ : syracuseStep 1937753 = 1453315) B1453315
theorem B4354397 : Blo 1289963 4354397 := bstep (se 3 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 4354397 = 1632899) B1632899
theorem B1290603 : Blo 1289963 1290603 := bstep (se 1 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 1290603 = 1935905) B1935905
theorem B1290615 : Blo 1289963 1290615 := bstep (se 1 (by rfl) ⟨967961, by rfl⟩ : syracuseStep 1290615 = 1935923) B1935923
theorem B1290635 : Blo 1289963 1290635 := bstep (se 1 (by rfl) ⟨967976, by rfl⟩ : syracuseStep 1290635 = 1935953) B1935953
theorem B1290647 : Blo 1289963 1290647 := bstep (se 1 (by rfl) ⟨967985, by rfl⟩ : syracuseStep 1290647 = 1935971) B1935971
theorem B1290667 : Blo 1289963 1290667 := bstep (se 1 (by rfl) ⟨968000, by rfl⟩ : syracuseStep 1290667 = 1936001) B1936001
theorem B1290679 : Blo 1289963 1290679 := bstep (se 1 (by rfl) ⟨968009, by rfl⟩ : syracuseStep 1290679 = 1936019) B1936019
theorem B4903361 : Blo 1289963 4903361 := bstep (se 2 (by rfl) ⟨1838760, by rfl⟩ : syracuseStep 4903361 = 3677521) B3677521
theorem B1290699 : Blo 1289963 1290699 := bstep (se 1 (by rfl) ⟨968024, by rfl⟩ : syracuseStep 1290699 = 1936049) B1936049
theorem B1937867 : Blo 1289963 1937867 := bstep (se 1 (by rfl) ⟨1453400, by rfl⟩ : syracuseStep 1937867 = 2906801) B2906801
theorem B1290711 : Blo 1289963 1290711 := bstep (se 1 (by rfl) ⟨968033, by rfl⟩ : syracuseStep 1290711 = 1936067) B1936067
theorem B1937879 : Blo 1289963 1937879 := bstep (se 1 (by rfl) ⟨1453409, by rfl⟩ : syracuseStep 1937879 = 2906819) B2906819
theorem B2945497 : Blo 1289963 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B1290731 : Blo 1289963 1290731 := bstep (se 1 (by rfl) ⟨968048, by rfl⟩ : syracuseStep 1290731 = 1936097) B1936097
theorem B1290743 : Blo 1289963 1290743 := bstep (se 1 (by rfl) ⟨968057, by rfl⟩ : syracuseStep 1290743 = 1936115) B1936115
theorem B1290763 : Blo 1289963 1290763 := bstep (se 1 (by rfl) ⟨968072, by rfl⟩ : syracuseStep 1290763 = 1936145) B1936145
theorem B2904587 : Blo 1289963 2904587 := bstep (se 1 (by rfl) ⟨2178440, by rfl⟩ : syracuseStep 2904587 = 4356881) B4356881
theorem B1290775 : Blo 1289963 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B1937945 : Blo 1289963 1937945 := bstep (se 2 (by rfl) ⟨726729, by rfl⟩ : syracuseStep 1937945 = 1453459) B1453459
theorem B1290795 : Blo 1289963 1290795 := bstep (se 1 (by rfl) ⟨968096, by rfl⟩ : syracuseStep 1290795 = 1936193) B1936193
theorem B1290807 : Blo 1289963 1290807 := bstep (se 1 (by rfl) ⟨968105, by rfl⟩ : syracuseStep 1290807 = 1936211) B1936211
theorem B2904641 : Blo 1289963 2904641 := bstep (se 2 (by rfl) ⟨1089240, by rfl⟩ : syracuseStep 2904641 = 2178481) B2178481
theorem B1290827 : Blo 1289963 1290827 := bstep (se 1 (by rfl) ⟨968120, by rfl⟩ : syracuseStep 1290827 = 1936241) B1936241
theorem B1290839 : Blo 1289963 1290839 := bstep (se 1 (by rfl) ⟨968129, by rfl⟩ : syracuseStep 1290839 = 1936259) B1936259
theorem B1290859 : Blo 1289963 1290859 := bstep (se 1 (by rfl) ⟨968144, by rfl⟩ : syracuseStep 1290859 = 1936289) B1936289
theorem B1290871 : Blo 1289963 1290871 := bstep (se 1 (by rfl) ⟨968153, by rfl⟩ : syracuseStep 1290871 = 1936307) B1936307
theorem B1290891 : Blo 1289963 1290891 := bstep (se 1 (by rfl) ⟨968168, by rfl⟩ : syracuseStep 1290891 = 1936337) B1936337
theorem B6533783 : Blo 1289963 6533783 := bstep (se 1 (by rfl) ⟨4900337, by rfl⟩ : syracuseStep 6533783 = 9800675) B9800675
theorem B1290903 : Blo 1289963 1290903 := bstep (se 1 (by rfl) ⟨968177, by rfl⟩ : syracuseStep 1290903 = 1936355) B1936355
theorem B1290923 : Blo 1289963 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B1290935 : Blo 1289963 1290935 := bstep (se 1 (by rfl) ⟨968201, by rfl⟩ : syracuseStep 1290935 = 1936403) B1936403
theorem B1290955 : Blo 1289963 1290955 := bstep (se 1 (by rfl) ⟨968216, by rfl⟩ : syracuseStep 1290955 = 1936433) B1936433
theorem B1290967 : Blo 1289963 1290967 := bstep (se 1 (by rfl) ⟨968225, by rfl⟩ : syracuseStep 1290967 = 1936451) B1936451
theorem B1290987 : Blo 1289963 1290987 := bstep (se 1 (by rfl) ⟨968240, by rfl⟩ : syracuseStep 1290987 = 1936481) B1936481
theorem B1290999 : Blo 1289963 1290999 := bstep (se 1 (by rfl) ⟨968249, by rfl⟩ : syracuseStep 1290999 = 1936499) B1936499
theorem B1291019 : Blo 1289963 1291019 := bstep (se 1 (by rfl) ⟨968264, by rfl⟩ : syracuseStep 1291019 = 1936529) B1936529
theorem B1291031 : Blo 1289963 1291031 := bstep (se 1 (by rfl) ⟨968273, by rfl⟩ : syracuseStep 1291031 = 1936547) B1936547
theorem B2904857 : Blo 1289963 2904857 := bstep (se 2 (by rfl) ⟨1089321, by rfl⟩ : syracuseStep 2904857 = 2178643) B2178643
theorem B1291051 : Blo 1289963 1291051 := bstep (se 1 (by rfl) ⟨968288, by rfl⟩ : syracuseStep 1291051 = 1936577) B1936577
theorem B1291063 : Blo 1289963 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B5591873 : Blo 1289963 5591873 := bstep (se 2 (by rfl) ⟨2096952, by rfl⟩ : syracuseStep 5591873 = 4193905) B4193905
theorem B1291083 : Blo 1289963 1291083 := bstep (se 1 (by rfl) ⟨968312, by rfl⟩ : syracuseStep 1291083 = 1936625) B1936625
theorem B1291095 : Blo 1289963 1291095 := bstep (se 1 (by rfl) ⟨968321, by rfl⟩ : syracuseStep 1291095 = 1936643) B1936643
theorem B1291115 : Blo 1289963 1291115 := bstep (se 1 (by rfl) ⟨968336, by rfl⟩ : syracuseStep 1291115 = 1936673) B1936673
theorem B2904947 : Blo 1289963 2904947 := bstep (se 1 (by rfl) ⟨2178710, by rfl⟩ : syracuseStep 2904947 = 4357421) B4357421
theorem B1291127 : Blo 1289963 1291127 := bstep (se 1 (by rfl) ⟨968345, by rfl⟩ : syracuseStep 1291127 = 1936691) B1936691
theorem B1291147 : Blo 1289963 1291147 := bstep (se 1 (by rfl) ⟨968360, by rfl⟩ : syracuseStep 1291147 = 1936721) B1936721
theorem B4649879 : Blo 1289963 4649879 := bstep (se 1 (by rfl) ⟨3487409, by rfl⟩ : syracuseStep 4649879 = 6974819) B6974819
theorem B2904983 : Blo 1289963 2904983 := bstep (se 1 (by rfl) ⟨2178737, by rfl⟩ : syracuseStep 2904983 = 4357475) B4357475
theorem B1291159 : Blo 1289963 1291159 := bstep (se 1 (by rfl) ⟨968369, by rfl⟩ : syracuseStep 1291159 = 1936739) B1936739
theorem B1291179 : Blo 1289963 1291179 := bstep (se 1 (by rfl) ⟨968384, by rfl⟩ : syracuseStep 1291179 = 1936769) B1936769
theorem B1291191 : Blo 1289963 1291191 := bstep (se 1 (by rfl) ⟨968393, by rfl⟩ : syracuseStep 1291191 = 1936787) B1936787
theorem B1291211 : Blo 1289963 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1291223 : Blo 1289963 1291223 := bstep (se 1 (by rfl) ⟨968417, by rfl⟩ : syracuseStep 1291223 = 1936835) B1936835
theorem B1291243 : Blo 1289963 1291243 := bstep (se 1 (by rfl) ⟨968432, by rfl⟩ : syracuseStep 1291243 = 1936865) B1936865
theorem B1291255 : Blo 1289963 1291255 := bstep (se 1 (by rfl) ⟨968441, by rfl⟩ : syracuseStep 1291255 = 1936883) B1936883
theorem B1291275 : Blo 1289963 1291275 := bstep (se 1 (by rfl) ⟨968456, by rfl⟩ : syracuseStep 1291275 = 1936913) B1936913
theorem B1291287 : Blo 1289963 1291287 := bstep (se 1 (by rfl) ⟨968465, by rfl⟩ : syracuseStep 1291287 = 1936931) B1936931
theorem B1291307 : Blo 1289963 1291307 := bstep (se 1 (by rfl) ⟨968480, by rfl⟩ : syracuseStep 1291307 = 1936961) B1936961
theorem B1291319 : Blo 1289963 1291319 := bstep (se 1 (by rfl) ⟨968489, by rfl⟩ : syracuseStep 1291319 = 1936979) B1936979
theorem B9933899 : Blo 1289963 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B2905163 : Blo 1289963 2905163 := bstep (se 1 (by rfl) ⟨2178872, by rfl⟩ : syracuseStep 2905163 = 4357745) B4357745
theorem B1291339 : Blo 1289963 1291339 := bstep (se 1 (by rfl) ⟨968504, by rfl⟩ : syracuseStep 1291339 = 1937009) B1937009
theorem B1291351 : Blo 1289963 1291351 := bstep (se 1 (by rfl) ⟨968513, by rfl⟩ : syracuseStep 1291351 = 1937027) B1937027
theorem B1307755 : Blo 1289963 1307755 := bstep (se 1 (by rfl) ⟨980816, by rfl⟩ : syracuseStep 1307755 = 1961633) B1961633
theorem B1291371 : Blo 1289963 1291371 := bstep (se 1 (by rfl) ⟨968528, by rfl⟩ : syracuseStep 1291371 = 1937057) B1937057
theorem B1291383 : Blo 1289963 1291383 := bstep (se 1 (by rfl) ⟨968537, by rfl⟩ : syracuseStep 1291383 = 1937075) B1937075
theorem B2905217 : Blo 1289963 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B1291403 : Blo 1289963 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B10613911 : Blo 1289963 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B1291415 : Blo 1289963 1291415 := bstep (se 1 (by rfl) ⟨968561, by rfl⟩ : syracuseStep 1291415 = 1937123) B1937123
theorem B1291435 : Blo 1289963 1291435 := bstep (se 1 (by rfl) ⟨968576, by rfl⟩ : syracuseStep 1291435 = 1937153) B1937153
theorem B1291447 : Blo 1289963 1291447 := bstep (se 1 (by rfl) ⟨968585, by rfl⟩ : syracuseStep 1291447 = 1937171) B1937171
theorem B1291467 : Blo 1289963 1291467 := bstep (se 1 (by rfl) ⟨968600, by rfl⟩ : syracuseStep 1291467 = 1937201) B1937201
theorem B1291479 : Blo 1289963 1291479 := bstep (se 1 (by rfl) ⟨968609, by rfl⟩ : syracuseStep 1291479 = 1937219) B1937219
theorem B1963225 : Blo 1289963 1963225 := bstep (se 2 (by rfl) ⟨736209, by rfl⟩ : syracuseStep 1963225 = 1472419) B1472419
theorem B1291499 : Blo 1289963 1291499 := bstep (se 1 (by rfl) ⟨968624, by rfl⟩ : syracuseStep 1291499 = 1937249) B1937249
theorem B1291511 : Blo 1289963 1291511 := bstep (se 1 (by rfl) ⟨968633, by rfl⟩ : syracuseStep 1291511 = 1937267) B1937267
theorem B1291531 : Blo 1289963 1291531 := bstep (se 1 (by rfl) ⟨968648, by rfl⟩ : syracuseStep 1291531 = 1937297) B1937297
theorem B1291543 : Blo 1289963 1291543 := bstep (se 1 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 1291543 = 1937315) B1937315
theorem B1291563 : Blo 1289963 1291563 := bstep (se 1 (by rfl) ⟨968672, by rfl⟩ : syracuseStep 1291563 = 1937345) B1937345
theorem B1291575 : Blo 1289963 1291575 := bstep (se 1 (by rfl) ⟨968681, by rfl⟩ : syracuseStep 1291575 = 1937363) B1937363
theorem B1291595 : Blo 1289963 1291595 := bstep (se 1 (by rfl) ⟨968696, by rfl⟩ : syracuseStep 1291595 = 1937393) B1937393
theorem B1291607 : Blo 1289963 1291607 := bstep (se 1 (by rfl) ⟨968705, by rfl⟩ : syracuseStep 1291607 = 1937411) B1937411
theorem B2905433 : Blo 1289963 2905433 := bstep (se 2 (by rfl) ⟨1089537, by rfl⟩ : syracuseStep 2905433 = 2179075) B2179075
theorem B1291627 : Blo 1289963 1291627 := bstep (se 1 (by rfl) ⟨968720, by rfl⟩ : syracuseStep 1291627 = 1937441) B1937441
theorem B1291639 : Blo 1289963 1291639 := bstep (se 1 (by rfl) ⟨968729, by rfl⟩ : syracuseStep 1291639 = 1937459) B1937459
theorem B1291659 : Blo 1289963 1291659 := bstep (se 1 (by rfl) ⟨968744, by rfl⟩ : syracuseStep 1291659 = 1937489) B1937489
theorem B28661141 : Blo 1289963 28661141 := bstep (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) B1343491
theorem B1291671 : Blo 1289963 1291671 := bstep (se 1 (by rfl) ⟨968753, by rfl⟩ : syracuseStep 1291671 = 1937507) B1937507
theorem B1291691 : Blo 1289963 1291691 := bstep (se 1 (by rfl) ⟨968768, by rfl⟩ : syracuseStep 1291691 = 1937537) B1937537
theorem B2905523 : Blo 1289963 2905523 := bstep (se 1 (by rfl) ⟨2179142, by rfl⟩ : syracuseStep 2905523 = 4358285) B4358285
theorem B1291703 : Blo 1289963 1291703 := bstep (se 1 (by rfl) ⟨968777, by rfl⟩ : syracuseStep 1291703 = 1937555) B1937555
theorem B4650443 : Blo 1289963 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B4355531 : Blo 1289963 4355531 := bstep (se 1 (by rfl) ⟨3266648, by rfl⟩ : syracuseStep 4355531 = 6533297) B6533297
theorem B1291723 : Blo 1289963 1291723 := bstep (se 1 (by rfl) ⟨968792, by rfl⟩ : syracuseStep 1291723 = 1937585) B1937585
theorem B2905559 : Blo 1289963 2905559 := bstep (se 1 (by rfl) ⟨2179169, by rfl⟩ : syracuseStep 2905559 = 4358339) B4358339
theorem B1291735 : Blo 1289963 1291735 := bstep (se 1 (by rfl) ⟨968801, by rfl⟩ : syracuseStep 1291735 = 1937603) B1937603
theorem B1291755 : Blo 1289963 1291755 := bstep (se 1 (by rfl) ⟨968816, by rfl⟩ : syracuseStep 1291755 = 1937633) B1937633
theorem B2618867 : Blo 1289963 2618867 := bstep (se 1 (by rfl) ⟨1964150, by rfl⟩ : syracuseStep 2618867 = 3928301) B3928301
theorem B1291767 : Blo 1289963 1291767 := bstep (se 1 (by rfl) ⟨968825, by rfl⟩ : syracuseStep 1291767 = 1937651) B1937651
theorem B1291787 : Blo 1289963 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B1291799 : Blo 1289963 1291799 := bstep (se 1 (by rfl) ⟨968849, by rfl⟩ : syracuseStep 1291799 = 1937699) B1937699
theorem B1291819 : Blo 1289963 1291819 := bstep (se 1 (by rfl) ⟨968864, by rfl⟩ : syracuseStep 1291819 = 1937729) B1937729
theorem B1291831 : Blo 1289963 1291831 := bstep (se 1 (by rfl) ⟨968873, by rfl⟩ : syracuseStep 1291831 = 1937747) B1937747
theorem B5969483 : Blo 1289963 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B1291851 : Blo 1289963 1291851 := bstep (se 1 (by rfl) ⟨968888, by rfl⟩ : syracuseStep 1291851 = 1937777) B1937777
theorem B1291863 : Blo 1289963 1291863 := bstep (se 1 (by rfl) ⟨968897, by rfl⟩ : syracuseStep 1291863 = 1937795) B1937795
theorem B5232221 : Blo 1289963 5232221 := bstep (se 3 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 5232221 = 1962083) B1962083
theorem B9557597 : Blo 1289963 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B1291883 : Blo 1289963 1291883 := bstep (se 1 (by rfl) ⟨968912, by rfl⟩ : syracuseStep 1291883 = 1937825) B1937825
theorem B1291895 : Blo 1289963 1291895 := bstep (se 1 (by rfl) ⟨968921, by rfl⟩ : syracuseStep 1291895 = 1937843) B1937843
theorem B8377987 : Blo 1289963 8377987 := bstep (se 1 (by rfl) ⟨6283490, by rfl⟩ : syracuseStep 8377987 = 12566981) B12566981
theorem B6624899 : Blo 1289963 6624899 := bstep (se 1 (by rfl) ⟨4968674, by rfl⟩ : syracuseStep 6624899 = 9937349) B9937349
theorem B11941507 : Blo 1289963 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B2905739 : Blo 1289963 2905739 := bstep (se 1 (by rfl) ⟨2179304, by rfl⟩ : syracuseStep 2905739 = 4358609) B4358609
theorem B1291915 : Blo 1289963 1291915 := bstep (se 1 (by rfl) ⟨968936, by rfl⟩ : syracuseStep 1291915 = 1937873) B1937873
theorem B1291927 : Blo 1289963 1291927 := bstep (se 1 (by rfl) ⟨968945, by rfl⟩ : syracuseStep 1291927 = 1937891) B1937891
theorem B1291947 : Blo 1289963 1291947 := bstep (se 1 (by rfl) ⟨968960, by rfl⟩ : syracuseStep 1291947 = 1937921) B1937921
theorem B4904621 : Blo 1289963 4904621 := bstep (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) B1839233
theorem B1291959 : Blo 1289963 1291959 := bstep (se 1 (by rfl) ⟨968969, by rfl⟩ : syracuseStep 1291959 = 1937939) B1937939
theorem B2905793 : Blo 1289963 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B4904651 : Blo 1289963 4904651 := bstep (se 1 (by rfl) ⟨3678488, by rfl⟩ : syracuseStep 4904651 = 7356977) B7356977
theorem B4355801 : Blo 1289963 4355801 := bstep (se 2 (by rfl) ⟨1633425, by rfl⟩ : syracuseStep 4355801 = 3266851) B3266851
theorem B4650803 : Blo 1289963 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B2906009 : Blo 1289963 2906009 := bstep (se 2 (by rfl) ⟨1089753, by rfl⟩ : syracuseStep 2906009 = 2179507) B2179507
theorem B41875379 : Blo 1289963 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B3676097 : Blo 1289963 3676097 := bstep (se 2 (by rfl) ⟨1378536, by rfl⟩ : syracuseStep 3676097 = 2757073) B2757073
theorem B3266507 : Blo 1289963 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B2906099 : Blo 1289963 2906099 := bstep (se 1 (by rfl) ⟨2179574, by rfl⟩ : syracuseStep 2906099 = 4359149) B4359149
theorem B2906135 : Blo 1289963 2906135 := bstep (se 1 (by rfl) ⟨2179601, by rfl⟩ : syracuseStep 2906135 = 4359203) B4359203
theorem B3676211 : Blo 1289963 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B6199361 : Blo 1289963 6199361 := bstep (se 2 (by rfl) ⟨2324760, by rfl⟩ : syracuseStep 6199361 = 4649521) B4649521
theorem B2177111 : Blo 1289963 2177111 := bstep (se 1 (by rfl) ⟨1632833, by rfl⟩ : syracuseStep 2177111 = 3265667) B3265667
theorem B5511361 : Blo 1289963 5511361 := bstep (se 2 (by rfl) ⟨2066760, by rfl⟩ : syracuseStep 5511361 = 4133521) B4133521
theorem B2906315 : Blo 1289963 2906315 := bstep (se 1 (by rfl) ⟨2179736, by rfl⟩ : syracuseStep 2906315 = 4359473) B4359473
theorem B2177239 : Blo 1289963 2177239 := bstep (se 1 (by rfl) ⟨1632929, by rfl⟩ : syracuseStep 2177239 = 3265859) B3265859
theorem B2906369 : Blo 1289963 2906369 := bstep (se 2 (by rfl) ⟨1089888, by rfl⟩ : syracuseStep 2906369 = 2179777) B2179777
theorem B9804077 : Blo 1289963 9804077 := bstep (se 3 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 9804077 = 3676529) B3676529
theorem B4905305 : Blo 1289963 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B4356503 : Blo 1289963 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B13957555 : Blo 1289963 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B14711219 : Blo 1289963 14711219 := bstep (se 1 (by rfl) ⟨11033414, by rfl⟩ : syracuseStep 14711219 = 22066829) B22066829
theorem B2906585 : Blo 1289963 2906585 := bstep (se 2 (by rfl) ⟨1089969, by rfl⟩ : syracuseStep 2906585 = 2179939) B2179939
theorem B2906675 : Blo 1289963 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B2906711 : Blo 1289963 2906711 := bstep (se 1 (by rfl) ⟨2180033, by rfl⟩ : syracuseStep 2906711 = 4360067) B4360067
theorem B4651609 : Blo 1289963 4651609 := bstep (se 2 (by rfl) ⟨1744353, by rfl⟩ : syracuseStep 4651609 = 3488707) B3488707
theorem B1309303 : Blo 1289963 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B5233355 : Blo 1289963 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B9796301 : Blo 1289963 9796301 := bstep (se 3 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 9796301 = 3673613) B3673613
theorem B8272601 : Blo 1289963 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B2906891 : Blo 1289963 2906891 := bstep (se 1 (by rfl) ⟨2180168, by rfl⟩ : syracuseStep 2906891 = 4360337) B4360337
theorem B5511959 : Blo 1289963 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B2177867 : Blo 1289963 2177867 := bstep (se 1 (by rfl) ⟨1633400, by rfl⟩ : syracuseStep 2177867 = 3266801) B3266801
theorem B3267479 : Blo 1289963 3267479 := bstep (se 1 (by rfl) ⟨2450609, by rfl⟩ : syracuseStep 3267479 = 4901219) B4901219
theorem B4357043 : Blo 1289963 4357043 := bstep (se 1 (by rfl) ⟨3267782, by rfl⟩ : syracuseStep 4357043 = 6535565) B6535565
theorem B2177995 : Blo 1289963 2177995 := bstep (se 1 (by rfl) ⟨1633496, by rfl⟩ : syracuseStep 2177995 = 3266993) B3266993
theorem B16555043 : Blo 1289963 16555043 := bstep (se 1 (by rfl) ⟨12416282, by rfl⟩ : syracuseStep 16555043 = 24832565) B24832565
theorem B6290507 : Blo 1289963 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B2178137 : Blo 1289963 2178137 := bstep (se 2 (by rfl) ⟨816801, by rfl⟩ : syracuseStep 2178137 = 1633603) B1633603
theorem B9796787 : Blo 1289963 9796787 := bstep (se 1 (by rfl) ⟨7347590, by rfl⟩ : syracuseStep 9796787 = 14695181) B14695181
theorem B4357313 : Blo 1289963 4357313 := bstep (se 2 (by rfl) ⟨1633992, by rfl⟩ : syracuseStep 4357313 = 3267985) B3267985
theorem B9305293 : Blo 1289963 9305293 := bstep (se 3 (by rfl) ⟨1744742, by rfl⟩ : syracuseStep 9305293 = 3489485) B3489485
theorem B2178265 : Blo 1289963 2178265 := bstep (se 2 (by rfl) ⟨816849, by rfl⟩ : syracuseStep 2178265 = 1633699) B1633699
theorem B1572247 : Blo 1289963 1572247 := bstep (se 1 (by rfl) ⟨1179185, by rfl⟩ : syracuseStep 1572247 = 2358371) B2358371
theorem B2325977 : Blo 1289963 2325977 := bstep (se 2 (by rfl) ⟨872241, by rfl⟩ : syracuseStep 2325977 = 1744483) B1744483
theorem B2448947 : Blo 1289963 2448947 := bstep (se 1 (by rfl) ⟨1836710, by rfl⟩ : syracuseStep 2448947 = 3673421) B3673421
theorem B3268147 : Blo 1289963 3268147 := bstep (se 1 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 3268147 = 4902221) B4902221
theorem B3268289 : Blo 1289963 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B4357853 : Blo 1289963 4357853 := bstep (se 3 (by rfl) ⟨817097, by rfl⟩ : syracuseStep 4357853 = 1634195) B1634195
theorem B2793217 : Blo 1289963 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B2178839 : Blo 1289963 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B14712677 : Blo 1289963 14712677 := bstep (se 4 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 14712677 = 2758627) B2758627
theorem B16990069 : Blo 1289963 16990069 := bstep (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) B1592819
theorem B11026307 : Blo 1289963 11026307 := bstep (se 1 (by rfl) ⟨8269730, by rfl⟩ : syracuseStep 11026307 = 16539461) B16539461
theorem B6627203 : Blo 1289963 6627203 := bstep (se 1 (by rfl) ⟨4970402, by rfl⟩ : syracuseStep 6627203 = 9940805) B9940805
theorem B2178967 : Blo 1289963 2178967 := bstep (se 1 (by rfl) ⟨1634225, by rfl⟩ : syracuseStep 2178967 = 3268451) B3268451
theorem B14147671 : Blo 1289963 14147671 := bstep (se 1 (by rfl) ⟨10610753, by rfl⟩ : syracuseStep 14147671 = 21221507) B21221507
theorem B4358231 : Blo 1289963 4358231 := bstep (se 1 (by rfl) ⟨3268673, by rfl⟩ : syracuseStep 4358231 = 6537347) B6537347
theorem B7348481 : Blo 1289963 7348481 := bstep (se 2 (by rfl) ⟨2755680, by rfl⟩ : syracuseStep 7348481 = 5511361) B5511361
theorem B3268907 : Blo 1289963 3268907 := bstep (se 1 (by rfl) ⟨2451680, by rfl⟩ : syracuseStep 3268907 = 4903361) B4903361
theorem B2326843 : Blo 1289963 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B2449865 : Blo 1289963 2449865 := bstep (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) B1837399
theorem B4358717 : Blo 1289963 4358717 := bstep (se 3 (by rfl) ⟨817259, by rfl⟩ : syracuseStep 4358717 = 1634519) B1634519
theorem B2179703 : Blo 1289963 2179703 := bstep (se 1 (by rfl) ⟨1634777, by rfl⟩ : syracuseStep 2179703 = 3269555) B3269555
theorem B6202145 : Blo 1289963 6202145 := bstep (se 2 (by rfl) ⟨2325804, by rfl⟩ : syracuseStep 6202145 = 4651609) B4651609
theorem B5235641 : Blo 1289963 5235641 := bstep (se 2 (by rfl) ⟨1963365, by rfl⟩ : syracuseStep 5235641 = 3926731) B3926731
theorem B1745911 : Blo 1289963 1745911 := bstep (se 1 (by rfl) ⟨1309433, by rfl⟩ : syracuseStep 1745911 = 2618867) B2618867
theorem B2180155 : Blo 1289963 2180155 := bstep (se 1 (by rfl) ⟨1635116, by rfl⟩ : syracuseStep 2180155 = 3270233) B3270233
theorem B4416599 : Blo 1289963 4416599 := bstep (se 1 (by rfl) ⟨3312449, by rfl⟩ : syracuseStep 4416599 = 6624899) B6624899
theorem B3269747 : Blo 1289963 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B4899959 : Blo 1289963 4899959 := bstep (se 1 (by rfl) ⟨3674969, by rfl⟩ : syracuseStep 4899959 = 7349939) B7349939
theorem B3269767 : Blo 1289963 3269767 := bstep (se 1 (by rfl) ⟨2452325, by rfl⟩ : syracuseStep 3269767 = 4904651) B4904651
theorem B2450731 : Blo 1289963 2450731 := bstep (se 1 (by rfl) ⟨1838048, by rfl⟩ : syracuseStep 2450731 = 3676097) B3676097
theorem B95438197 : Blo 1289963 95438197 := bstep (se 5 (by rfl) ⟨4473665, by rfl⟩ : syracuseStep 95438197 = 8947331) B8947331
theorem B2450807 : Blo 1289963 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B1451407 : Blo 1289963 1451407 := bstep (se 1 (by rfl) ⟨1088555, by rfl⟩ : syracuseStep 1451407 = 2177111) B2177111
theorem B6538643 : Blo 1289963 6538643 := bstep (se 1 (by rfl) ⟨4903982, by rfl⟩ : syracuseStep 6538643 = 9807965) B9807965
theorem B3270041 : Blo 1289963 3270041 := bstep (se 2 (by rfl) ⟨1226265, by rfl⟩ : syracuseStep 3270041 = 2452531) B2452531
theorem B3270203 : Blo 1289963 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B9807479 : Blo 1289963 9807479 := bstep (se 1 (by rfl) ⟨7355609, by rfl⟩ : syracuseStep 9807479 = 14711219) B14711219
theorem B1935035 : Blo 1289963 1935035 := bstep (se 1 (by rfl) ⟨1451276, by rfl⟩ : syracuseStep 1935035 = 2902553) B2902553
theorem B1935095 : Blo 1289963 1935095 := bstep (se 1 (by rfl) ⟨1451321, by rfl⟩ : syracuseStep 1935095 = 2902643) B2902643
theorem B1935119 : Blo 1289963 1935119 := bstep (se 1 (by rfl) ⟨1451339, by rfl⟩ : syracuseStep 1935119 = 2902679) B2902679
theorem B6530867 : Blo 1289963 6530867 := bstep (se 1 (by rfl) ⟨4898150, by rfl⟩ : syracuseStep 6530867 = 9796301) B9796301
theorem B1935161 : Blo 1289963 1935161 := bstep (se 2 (by rfl) ⟨725685, by rfl⟩ : syracuseStep 1935161 = 1451371) B1451371
theorem B5515067 : Blo 1289963 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B1935239 : Blo 1289963 1935239 := bstep (se 1 (by rfl) ⟨1451429, by rfl⟩ : syracuseStep 1935239 = 2902859) B2902859
theorem B1451911 : Blo 1289963 1451911 := bstep (se 1 (by rfl) ⟨1088933, by rfl⟩ : syracuseStep 1451911 = 2177867) B2177867
theorem B1935275 : Blo 1289963 1935275 := bstep (se 1 (by rfl) ⟨1451456, by rfl⟩ : syracuseStep 1935275 = 2902913) B2902913
theorem B2615225 : Blo 1289963 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B4360121 : Blo 1289963 4360121 := bstep (se 2 (by rfl) ⟨1635045, by rfl⟩ : syracuseStep 4360121 = 3270091) B3270091
theorem B1935305 : Blo 1289963 1935305 := bstep (se 2 (by rfl) ⟨725739, by rfl⟩ : syracuseStep 1935305 = 1451479) B1451479
theorem B9799703 : Blo 1289963 9799703 := bstep (se 1 (by rfl) ⟨7349777, by rfl⟩ : syracuseStep 9799703 = 14699555) B14699555
theorem B11036695 : Blo 1289963 11036695 := bstep (se 1 (by rfl) ⟨8277521, by rfl⟩ : syracuseStep 11036695 = 16555043) B16555043
theorem B1935419 : Blo 1289963 1935419 := bstep (se 1 (by rfl) ⟨1451564, by rfl⟩ : syracuseStep 1935419 = 2903129) B2903129
theorem B1452091 : Blo 1289963 1452091 := bstep (se 1 (by rfl) ⟨1089068, by rfl⟩ : syracuseStep 1452091 = 2178137) B2178137
theorem B4900931 : Blo 1289963 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B6531191 : Blo 1289963 6531191 := bstep (se 1 (by rfl) ⟨4898393, by rfl⟩ : syracuseStep 6531191 = 9796787) B9796787
theorem B1935479 : Blo 1289963 1935479 := bstep (se 1 (by rfl) ⟨1451609, by rfl⟩ : syracuseStep 1935479 = 2903219) B2903219
theorem B1935503 : Blo 1289963 1935503 := bstep (se 1 (by rfl) ⟨1451627, by rfl⟩ : syracuseStep 1935503 = 2903255) B2903255
theorem B14911661 : Blo 1289963 14911661 := bstep (se 3 (by rfl) ⟨2795936, by rfl⟩ : syracuseStep 14911661 = 5591873) B5591873
theorem B1935545 : Blo 1289963 1935545 := bstep (se 2 (by rfl) ⟨725829, by rfl⟩ : syracuseStep 1935545 = 1451659) B1451659
theorem B1935623 : Blo 1289963 1935623 := bstep (se 1 (by rfl) ⟨1451717, by rfl⟩ : syracuseStep 1935623 = 2903435) B2903435
theorem B1935659 : Blo 1289963 1935659 := bstep (se 1 (by rfl) ⟨1451744, by rfl⟩ : syracuseStep 1935659 = 2903489) B2903489
theorem B1935689 : Blo 1289963 1935689 := bstep (se 2 (by rfl) ⟨725883, by rfl⟩ : syracuseStep 1935689 = 1451767) B1451767
theorem B1632631 : Blo 1289963 1632631 := bstep (se 1 (by rfl) ⟨1224473, by rfl⟩ : syracuseStep 1632631 = 2448947) B2448947
theorem B1935803 : Blo 1289963 1935803 := bstep (se 1 (by rfl) ⟨1451852, by rfl⟩ : syracuseStep 1935803 = 2903705) B2903705
theorem B2615753 : Blo 1289963 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B1837513 : Blo 1289963 1837513 := bstep (se 2 (by rfl) ⟨689067, by rfl⟩ : syracuseStep 1837513 = 1378135) B1378135
theorem B22653425 : Blo 1289963 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B1935863 : Blo 1289963 1935863 := bstep (se 1 (by rfl) ⟨1451897, by rfl⟩ : syracuseStep 1935863 = 2903795) B2903795
theorem B1935887 : Blo 1289963 1935887 := bstep (se 1 (by rfl) ⟨1451915, by rfl⟩ : syracuseStep 1935887 = 2903831) B2903831
theorem B1452559 : Blo 1289963 1452559 := bstep (se 1 (by rfl) ⟨1089419, by rfl⟩ : syracuseStep 1452559 = 2178839) B2178839
theorem B4655645 : Blo 1289963 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B2902571 : Blo 1289963 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B1935929 : Blo 1289963 1935929 := bstep (se 2 (by rfl) ⟨725973, by rfl⟩ : syracuseStep 1935929 = 1451947) B1451947
theorem B9808451 : Blo 1289963 9808451 := bstep (se 1 (by rfl) ⟨7356338, by rfl⟩ : syracuseStep 9808451 = 14712677) B14712677
theorem B7350871 : Blo 1289963 7350871 := bstep (se 1 (by rfl) ⟨5513153, by rfl⟩ : syracuseStep 7350871 = 11026307) B11026307
theorem B4418135 : Blo 1289963 4418135 := bstep (se 1 (by rfl) ⟨3313601, by rfl⟩ : syracuseStep 4418135 = 6627203) B6627203
theorem B1936007 : Blo 1289963 1936007 := bstep (se 1 (by rfl) ⟨1452005, by rfl⟩ : syracuseStep 1936007 = 2904011) B2904011
theorem B1936043 : Blo 1289963 1936043 := bstep (se 1 (by rfl) ⟨1452032, by rfl⟩ : syracuseStep 1936043 = 2904065) B2904065
theorem B1632955 : Blo 1289963 1632955 := bstep (se 1 (by rfl) ⟨1224716, by rfl⟩ : syracuseStep 1632955 = 2449433) B2449433
theorem B28314305 : Blo 1289963 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B1936073 : Blo 1289963 1936073 := bstep (se 2 (by rfl) ⟨726027, by rfl⟩ : syracuseStep 1936073 = 1452055) B1452055
theorem B1936187 : Blo 1289963 1936187 := bstep (se 1 (by rfl) ⟨1452140, by rfl⟩ : syracuseStep 1936187 = 2904281) B2904281
theorem B1936247 : Blo 1289963 1936247 := bstep (se 1 (by rfl) ⟨1452185, by rfl⟩ : syracuseStep 1936247 = 2904371) B2904371
theorem B1936271 : Blo 1289963 1936271 := bstep (se 1 (by rfl) ⟨1452203, by rfl⟩ : syracuseStep 1936271 = 2904407) B2904407
theorem B2902931 : Blo 1289963 2902931 := bstep (se 1 (by rfl) ⟨2177198, by rfl⟩ : syracuseStep 2902931 = 4354397) B4354397
theorem B1936313 : Blo 1289963 1936313 := bstep (se 2 (by rfl) ⟨726117, by rfl⟩ : syracuseStep 1936313 = 1452235) B1452235
theorem B2902985 : Blo 1289963 2902985 := bstep (se 2 (by rfl) ⟨1088619, by rfl⟩ : syracuseStep 2902985 = 2177239) B2177239
theorem B1936391 : Blo 1289963 1936391 := bstep (se 1 (by rfl) ⟨1452293, by rfl⟩ : syracuseStep 1936391 = 2904587) B2904587
theorem B1453063 : Blo 1289963 1453063 := bstep (se 1 (by rfl) ⟨1089797, by rfl⟩ : syracuseStep 1453063 = 2179595) B2179595
theorem B4901917 : Blo 1289963 4901917 := bstep (se 3 (by rfl) ⟨919109, by rfl⟩ : syracuseStep 4901917 = 1838219) B1838219
theorem B1936427 : Blo 1289963 1936427 := bstep (se 1 (by rfl) ⟨1452320, by rfl⟩ : syracuseStep 1936427 = 2904641) B2904641
theorem B6532163 : Blo 1289963 6532163 := bstep (se 1 (by rfl) ⟨4899122, by rfl⟩ : syracuseStep 6532163 = 9798245) B9798245
theorem B1936457 : Blo 1289963 1936457 := bstep (se 2 (by rfl) ⟨726171, by rfl⟩ : syracuseStep 1936457 = 1452343) B1452343
theorem B1936571 : Blo 1289963 1936571 := bstep (se 1 (by rfl) ⟨1452428, by rfl⟩ : syracuseStep 1936571 = 2904857) B2904857
theorem B1453243 : Blo 1289963 1453243 := bstep (se 1 (by rfl) ⟨1089932, by rfl⟩ : syracuseStep 1453243 = 2179865) B2179865
theorem B6974693 : Blo 1289963 6974693 := bstep (se 4 (by rfl) ⟨653877, by rfl⟩ : syracuseStep 6974693 = 1307755) B1307755
theorem B1936631 : Blo 1289963 1936631 := bstep (se 1 (by rfl) ⟨1452473, by rfl⟩ : syracuseStep 1936631 = 2904947) B2904947
theorem B3099919 : Blo 1289963 3099919 := bstep (se 1 (by rfl) ⟨2324939, by rfl⟩ : syracuseStep 3099919 = 4649879) B4649879
theorem B1936655 : Blo 1289963 1936655 := bstep (se 1 (by rfl) ⟨1452491, by rfl⟩ : syracuseStep 1936655 = 2904983) B2904983
theorem B3927329 : Blo 1289963 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B6982949 : Blo 1289963 6982949 := bstep (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) B1309303
theorem B1936697 : Blo 1289963 1936697 := bstep (se 2 (by rfl) ⟨726261, by rfl⟩ : syracuseStep 1936697 = 1452523) B1452523
theorem B63688037 : Blo 1289963 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B6532487 : Blo 1289963 6532487 := bstep (se 1 (by rfl) ⟨4899365, by rfl⟩ : syracuseStep 6532487 = 9798731) B9798731
theorem B1936775 : Blo 1289963 1936775 := bstep (se 1 (by rfl) ⟨1452581, by rfl⟩ : syracuseStep 1936775 = 2905163) B2905163
theorem B14159249 : Blo 1289963 14159249 := bstep (se 2 (by rfl) ⟨5309718, by rfl⟩ : syracuseStep 14159249 = 10619437) B10619437
theorem B1936811 : Blo 1289963 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B1936841 : Blo 1289963 1936841 := bstep (se 2 (by rfl) ⟨726315, by rfl⟩ : syracuseStep 1936841 = 1452631) B1452631
theorem B9309649 : Blo 1289963 9309649 := bstep (se 2 (by rfl) ⟨3491118, by rfl⟩ : syracuseStep 9309649 = 6982237) B6982237
theorem B1936955 : Blo 1289963 1936955 := bstep (se 1 (by rfl) ⟨1452716, by rfl⟩ : syracuseStep 1936955 = 2905433) B2905433
theorem B19107427 : Blo 1289963 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B1937015 : Blo 1289963 1937015 := bstep (se 1 (by rfl) ⟨1452761, by rfl⟩ : syracuseStep 1937015 = 2905523) B2905523
theorem B3100295 : Blo 1289963 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B2903687 : Blo 1289963 2903687 := bstep (se 1 (by rfl) ⟨2177765, by rfl⟩ : syracuseStep 2903687 = 4355531) B4355531
theorem B1633927 : Blo 1289963 1633927 := bstep (se 1 (by rfl) ⟨1225445, by rfl⟩ : syracuseStep 1633927 = 2450891) B2450891
theorem B1552007 : Blo 1289963 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B1937039 : Blo 1289963 1937039 := bstep (se 1 (by rfl) ⟨1452779, by rfl⟩ : syracuseStep 1937039 = 2905559) B2905559
theorem B1937081 : Blo 1289963 1937081 := bstep (se 2 (by rfl) ⟨726405, by rfl⟩ : syracuseStep 1937081 = 1452811) B1452811
theorem B1289991 : Blo 1289963 1289991 := bstep (se 1 (by rfl) ⟨967493, by rfl⟩ : syracuseStep 1289991 = 1934987) B1934987
theorem B1937159 : Blo 1289963 1937159 := bstep (se 1 (by rfl) ⟨1452869, by rfl⟩ : syracuseStep 1937159 = 2905739) B2905739
theorem B1289999 : Blo 1289963 1289999 := bstep (se 1 (by rfl) ⟨967499, by rfl⟩ : syracuseStep 1289999 = 1934999) B1934999
theorem B1937195 : Blo 1289963 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B2903867 : Blo 1289963 2903867 := bstep (se 1 (by rfl) ⟨2177900, by rfl⟩ : syracuseStep 2903867 = 4355801) B4355801
theorem B1290043 : Blo 1289963 1290043 := bstep (se 1 (by rfl) ⟨967532, by rfl⟩ : syracuseStep 1290043 = 1935065) B1935065
theorem B1937225 : Blo 1289963 1937225 := bstep (se 2 (by rfl) ⟨726459, by rfl⟩ : syracuseStep 1937225 = 1452919) B1452919
theorem B3100535 : Blo 1289963 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B1290119 : Blo 1289963 1290119 := bstep (se 1 (by rfl) ⟨967589, by rfl⟩ : syracuseStep 1290119 = 1935179) B1935179
theorem B1290127 : Blo 1289963 1290127 := bstep (se 1 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 1290127 = 1935191) B1935191
theorem B2903993 : Blo 1289963 2903993 := bstep (se 2 (by rfl) ⟨1088997, by rfl⟩ : syracuseStep 2903993 = 2177995) B2177995
theorem B1290171 : Blo 1289963 1290171 := bstep (se 1 (by rfl) ⟨967628, by rfl⟩ : syracuseStep 1290171 = 1935257) B1935257
theorem B1937339 : Blo 1289963 1937339 := bstep (se 1 (by rfl) ⟨1453004, by rfl⟩ : syracuseStep 1937339 = 2906009) B2906009
theorem B1937399 : Blo 1289963 1937399 := bstep (se 1 (by rfl) ⟨1453049, by rfl⟩ : syracuseStep 1937399 = 2906099) B2906099
theorem B1290247 : Blo 1289963 1290247 := bstep (se 1 (by rfl) ⟨967685, by rfl⟩ : syracuseStep 1290247 = 1935371) B1935371
theorem B1290255 : Blo 1289963 1290255 := bstep (se 1 (by rfl) ⟨967691, by rfl⟩ : syracuseStep 1290255 = 1935383) B1935383
theorem B1937423 : Blo 1289963 1937423 := bstep (se 1 (by rfl) ⟨1453067, by rfl⟩ : syracuseStep 1937423 = 2906135) B2906135
theorem B4132907 : Blo 1289963 4132907 := bstep (se 1 (by rfl) ⟨3099680, by rfl⟩ : syracuseStep 4132907 = 6199361) B6199361
theorem B1634347 : Blo 1289963 1634347 := bstep (se 1 (by rfl) ⟨1225760, by rfl⟩ : syracuseStep 1634347 = 2451521) B2451521
theorem B1290299 : Blo 1289963 1290299 := bstep (se 1 (by rfl) ⟨967724, by rfl⟩ : syracuseStep 1290299 = 1935449) B1935449
theorem B1937465 : Blo 1289963 1937465 := bstep (se 2 (by rfl) ⟨726549, by rfl⟩ : syracuseStep 1937465 = 1453099) B1453099
theorem B15921269 : Blo 1289963 15921269 := bstep (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) B1492619
theorem B1290375 : Blo 1289963 1290375 := bstep (se 1 (by rfl) ⟨967781, by rfl⟩ : syracuseStep 1290375 = 1935563) B1935563
theorem B1937543 : Blo 1289963 1937543 := bstep (se 1 (by rfl) ⟨1453157, by rfl⟩ : syracuseStep 1937543 = 2906315) B2906315
theorem B1290383 : Blo 1289963 1290383 := bstep (se 1 (by rfl) ⟨967787, by rfl⟩ : syracuseStep 1290383 = 1935575) B1935575
theorem B1937579 : Blo 1289963 1937579 := bstep (se 1 (by rfl) ⟨1453184, by rfl⟩ : syracuseStep 1937579 = 2906369) B2906369
theorem B9941165 : Blo 1289963 9941165 := bstep (se 3 (by rfl) ⟨1863968, by rfl⟩ : syracuseStep 9941165 = 3727937) B3727937
theorem B3674297 : Blo 1289963 3674297 := bstep (se 2 (by rfl) ⟨1377861, by rfl⟩ : syracuseStep 3674297 = 2755723) B2755723
theorem B1290427 : Blo 1289963 1290427 := bstep (se 1 (by rfl) ⟨967820, by rfl⟩ : syracuseStep 1290427 = 1935641) B1935641
theorem B2207945 : Blo 1289963 2207945 := bstep (se 2 (by rfl) ⟨827979, by rfl⟩ : syracuseStep 2207945 = 1655959) B1655959
theorem B14151881 : Blo 1289963 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B1937609 : Blo 1289963 1937609 := bstep (se 2 (by rfl) ⟨726603, by rfl⟩ : syracuseStep 1937609 = 1453207) B1453207
theorem B1290503 : Blo 1289963 1290503 := bstep (se 1 (by rfl) ⟨967877, by rfl⟩ : syracuseStep 1290503 = 1935755) B1935755
theorem B1290511 : Blo 1289963 1290511 := bstep (se 1 (by rfl) ⟨967883, by rfl⟩ : syracuseStep 1290511 = 1935767) B1935767
theorem B2904335 : Blo 1289963 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B12407057 : Blo 1289963 12407057 := bstep (se 2 (by rfl) ⟨4652646, by rfl⟩ : syracuseStep 12407057 = 9305293) B9305293
theorem B1634575 : Blo 1289963 1634575 := bstep (se 1 (by rfl) ⟨1225931, by rfl⟩ : syracuseStep 1634575 = 2451863) B2451863
theorem B2904353 : Blo 1289963 2904353 := bstep (se 2 (by rfl) ⟨1089132, by rfl⟩ : syracuseStep 2904353 = 2178265) B2178265
theorem B2617633 : Blo 1289963 2617633 := bstep (se 2 (by rfl) ⟨981612, by rfl⟩ : syracuseStep 2617633 = 1963225) B1963225
theorem B1290555 : Blo 1289963 1290555 := bstep (se 1 (by rfl) ⟨967916, by rfl⟩ : syracuseStep 1290555 = 1935833) B1935833
theorem B1937723 : Blo 1289963 1937723 := bstep (se 1 (by rfl) ⟨1453292, by rfl⟩ : syracuseStep 1937723 = 2906585) B2906585
theorem B1937783 : Blo 1289963 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B1290631 : Blo 1289963 1290631 := bstep (se 1 (by rfl) ⟨967973, by rfl⟩ : syracuseStep 1290631 = 1935947) B1935947
theorem B1290639 : Blo 1289963 1290639 := bstep (se 1 (by rfl) ⟨967979, by rfl⟩ : syracuseStep 1290639 = 1935959) B1935959
theorem B1937807 : Blo 1289963 1937807 := bstep (se 1 (by rfl) ⟨1453355, by rfl⟩ : syracuseStep 1937807 = 2906711) B2906711
theorem B4354451 : Blo 1289963 4354451 := bstep (se 1 (by rfl) ⟨3265838, by rfl⟩ : syracuseStep 4354451 = 6531677) B6531677
theorem B1937849 : Blo 1289963 1937849 := bstep (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) B1453387
theorem B1290683 : Blo 1289963 1290683 := bstep (se 1 (by rfl) ⟨968012, by rfl⟩ : syracuseStep 1290683 = 1936025) B1936025
theorem B1290759 : Blo 1289963 1290759 := bstep (se 1 (by rfl) ⟨968069, by rfl⟩ : syracuseStep 1290759 = 1936139) B1936139
theorem B1937927 : Blo 1289963 1937927 := bstep (se 1 (by rfl) ⟨1453445, by rfl⟩ : syracuseStep 1937927 = 2906891) B2906891
theorem B3674639 : Blo 1289963 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B1290767 : Blo 1289963 1290767 := bstep (se 1 (by rfl) ⟨968075, by rfl⟩ : syracuseStep 1290767 = 1936151) B1936151
theorem B7352855 : Blo 1289963 7352855 := bstep (se 1 (by rfl) ⟨5514641, by rfl⟩ : syracuseStep 7352855 = 11029283) B11029283
theorem B12415517 : Blo 1289963 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B1290811 : Blo 1289963 1290811 := bstep (se 1 (by rfl) ⟨968108, by rfl⟩ : syracuseStep 1290811 = 1936217) B1936217
theorem B2904695 : Blo 1289963 2904695 := bstep (se 1 (by rfl) ⟨2178521, by rfl⟩ : syracuseStep 2904695 = 4357043) B4357043
theorem B1290887 : Blo 1289963 1290887 := bstep (se 1 (by rfl) ⟨968165, by rfl⟩ : syracuseStep 1290887 = 1936331) B1936331
theorem B2617991 : Blo 1289963 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B1290895 : Blo 1289963 1290895 := bstep (se 1 (by rfl) ⟨968171, by rfl⟩ : syracuseStep 1290895 = 1936343) B1936343
theorem B1290939 : Blo 1289963 1290939 := bstep (se 1 (by rfl) ⟨968204, by rfl⟩ : syracuseStep 1290939 = 1936409) B1936409
theorem B9310949 : Blo 1289963 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B1291015 : Blo 1289963 1291015 := bstep (se 1 (by rfl) ⟨968261, by rfl⟩ : syracuseStep 1291015 = 1936523) B1936523
theorem B1291023 : Blo 1289963 1291023 := bstep (se 1 (by rfl) ⟨968267, by rfl⟩ : syracuseStep 1291023 = 1936535) B1936535
theorem B2904875 : Blo 1289963 2904875 := bstep (se 1 (by rfl) ⟨2178656, by rfl⟩ : syracuseStep 2904875 = 4357313) B4357313
theorem B7451443 : Blo 1289963 7451443 := bstep (se 1 (by rfl) ⟨5588582, by rfl⟩ : syracuseStep 7451443 = 11177165) B11177165
theorem B1291067 : Blo 1289963 1291067 := bstep (se 1 (by rfl) ⟨968300, by rfl⟩ : syracuseStep 1291067 = 1936601) B1936601
theorem B11170649 : Blo 1289963 11170649 := bstep (se 2 (by rfl) ⟨4188993, by rfl⟩ : syracuseStep 11170649 = 8377987) B8377987
theorem B1291143 : Blo 1289963 1291143 := bstep (se 1 (by rfl) ⟨968357, by rfl⟩ : syracuseStep 1291143 = 1936715) B1936715
theorem B1291151 : Blo 1289963 1291151 := bstep (se 1 (by rfl) ⟨968363, by rfl⟩ : syracuseStep 1291151 = 1936727) B1936727
theorem B3142547 : Blo 1289963 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B5305235 : Blo 1289963 5305235 := bstep (se 1 (by rfl) ⟨3978926, by rfl⟩ : syracuseStep 5305235 = 7957853) B7957853
theorem B24810421 : Blo 1289963 24810421 := bstep (se 5 (by rfl) ⟨1162988, by rfl⟩ : syracuseStep 24810421 = 2325977) B2325977
theorem B1291195 : Blo 1289963 1291195 := bstep (se 1 (by rfl) ⟨968396, by rfl⟩ : syracuseStep 1291195 = 1936793) B1936793
theorem B3724289 : Blo 1289963 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B1291271 : Blo 1289963 1291271 := bstep (se 1 (by rfl) ⟨968453, by rfl⟩ : syracuseStep 1291271 = 1936907) B1936907
theorem B1291279 : Blo 1289963 1291279 := bstep (se 1 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 1291279 = 1936919) B1936919
theorem B1291323 : Blo 1289963 1291323 := bstep (se 1 (by rfl) ⟨968492, by rfl⟩ : syracuseStep 1291323 = 1936985) B1936985
theorem B1291399 : Blo 1289963 1291399 := bstep (se 1 (by rfl) ⟨968549, by rfl⟩ : syracuseStep 1291399 = 1937099) B1937099
theorem B1291407 : Blo 1289963 1291407 := bstep (se 1 (by rfl) ⟨968555, by rfl⟩ : syracuseStep 1291407 = 1937111) B1937111
theorem B2905235 : Blo 1289963 2905235 := bstep (se 1 (by rfl) ⟨2178926, by rfl⟩ : syracuseStep 2905235 = 4357853) B4357853
theorem B1291451 : Blo 1289963 1291451 := bstep (se 1 (by rfl) ⟨968588, by rfl⟩ : syracuseStep 1291451 = 1937177) B1937177
theorem B2905289 : Blo 1289963 2905289 := bstep (se 2 (by rfl) ⟨1089483, by rfl⟩ : syracuseStep 2905289 = 2178967) B2178967
theorem B1291527 : Blo 1289963 1291527 := bstep (se 1 (by rfl) ⟨968645, by rfl⟩ : syracuseStep 1291527 = 1937291) B1937291
theorem B1291535 : Blo 1289963 1291535 := bstep (se 1 (by rfl) ⟨968651, by rfl⟩ : syracuseStep 1291535 = 1937303) B1937303
theorem B3142955 : Blo 1289963 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B1291579 : Blo 1289963 1291579 := bstep (se 1 (by rfl) ⟨968684, by rfl⟩ : syracuseStep 1291579 = 1937369) B1937369
theorem B3265879 : Blo 1289963 3265879 := bstep (se 1 (by rfl) ⟨2449409, by rfl⟩ : syracuseStep 3265879 = 4898819) B4898819
theorem B3675527 : Blo 1289963 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B1291655 : Blo 1289963 1291655 := bstep (se 1 (by rfl) ⟨968741, by rfl⟩ : syracuseStep 1291655 = 1937483) B1937483
theorem B1291663 : Blo 1289963 1291663 := bstep (se 1 (by rfl) ⟨968747, by rfl⟩ : syracuseStep 1291663 = 1937495) B1937495
theorem B1291707 : Blo 1289963 1291707 := bstep (se 1 (by rfl) ⟨968780, by rfl⟩ : syracuseStep 1291707 = 1937561) B1937561
theorem B1291783 : Blo 1289963 1291783 := bstep (se 1 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 1291783 = 1937675) B1937675
theorem B1291791 : Blo 1289963 1291791 := bstep (se 1 (by rfl) ⟨968843, by rfl⟩ : syracuseStep 1291791 = 1937687) B1937687
theorem B26490397 : Blo 1289963 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B16774685 : Blo 1289963 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1291835 : Blo 1289963 1291835 := bstep (se 1 (by rfl) ⟨968876, by rfl⟩ : syracuseStep 1291835 = 1937753) B1937753
theorem B3675709 : Blo 1289963 3675709 := bstep (se 3 (by rfl) ⟨689195, by rfl⟩ : syracuseStep 3675709 = 1378391) B1378391
theorem B3266183 : Blo 1289963 3266183 := bstep (se 1 (by rfl) ⟨2449637, by rfl⟩ : syracuseStep 3266183 = 4899275) B4899275
theorem B1291911 : Blo 1289963 1291911 := bstep (se 1 (by rfl) ⟨968933, by rfl⟩ : syracuseStep 1291911 = 1937867) B1937867
theorem B1291919 : Blo 1289963 1291919 := bstep (se 1 (by rfl) ⟨968939, by rfl⟩ : syracuseStep 1291919 = 1937879) B1937879
theorem B1291963 : Blo 1289963 1291963 := bstep (se 1 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 1291963 = 1937945) B1937945
theorem B11032321 : Blo 1289963 11032321 := bstep (se 2 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 11032321 = 8274241) B8274241
theorem B3266315 : Blo 1289963 3266315 := bstep (se 1 (by rfl) ⟨2449736, by rfl⟩ : syracuseStep 3266315 = 4899473) B4899473
theorem B4355855 : Blo 1289963 4355855 := bstep (se 1 (by rfl) ⟨3266891, by rfl⟩ : syracuseStep 4355855 = 6533783) B6533783
theorem B3675937 : Blo 1289963 3675937 := bstep (se 2 (by rfl) ⟨1378476, by rfl⟩ : syracuseStep 3675937 = 2756953) B2756953
theorem B27932485 : Blo 1289963 27932485 := bstep (se 4 (by rfl) ⟨2618670, by rfl⟩ : syracuseStep 27932485 = 5237341) B5237341
theorem B4904819 : Blo 1289963 4904819 := bstep (se 1 (by rfl) ⟨3678614, by rfl⟩ : syracuseStep 4904819 = 7357229) B7357229
theorem B2905991 : Blo 1289963 2905991 := bstep (se 1 (by rfl) ⟨2179493, by rfl⟩ : syracuseStep 2905991 = 4358987) B4358987
theorem B18610073 : Blo 1289963 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B2176969 : Blo 1289963 2176969 := bstep (se 2 (by rfl) ⟨816363, by rfl⟩ : syracuseStep 2176969 = 1632727) B1632727
theorem B4356125 : Blo 1289963 4356125 := bstep (se 3 (by rfl) ⟨816773, by rfl⟩ : syracuseStep 4356125 = 1633547) B1633547
theorem B2906171 : Blo 1289963 2906171 := bstep (se 1 (by rfl) ⟨2179628, by rfl⟩ : syracuseStep 2906171 = 4359257) B4359257
theorem B5232707 : Blo 1289963 5232707 := bstep (se 1 (by rfl) ⟨3924530, by rfl⟩ : syracuseStep 5232707 = 7849061) B7849061
theorem B35330165 : Blo 1289963 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B3676279 : Blo 1289963 3676279 := bstep (se 1 (by rfl) ⟨2757209, by rfl⟩ : syracuseStep 3676279 = 5514419) B5514419
theorem B2906297 : Blo 1289963 2906297 := bstep (se 2 (by rfl) ⟨1089861, by rfl⟩ : syracuseStep 2906297 = 2179723) B2179723
theorem B3266831 : Blo 1289963 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B3979655 : Blo 1289963 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B3488147 : Blo 1289963 3488147 := bstep (se 1 (by rfl) ⟨2616110, by rfl⟩ : syracuseStep 3488147 = 5232221) B5232221
theorem B6371731 : Blo 1289963 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B3266963 : Blo 1289963 3266963 := bstep (se 1 (by rfl) ⟨2450222, by rfl⟩ : syracuseStep 3266963 = 4900445) B4900445
theorem B2906639 : Blo 1289963 2906639 := bstep (se 1 (by rfl) ⟨2179979, by rfl⟩ : syracuseStep 2906639 = 4359959) B4359959
theorem B3103265 : Blo 1289963 3103265 := bstep (se 2 (by rfl) ⟨1163724, by rfl⟩ : syracuseStep 3103265 = 2327449) B2327449
theorem B2906657 : Blo 1289963 2906657 := bstep (se 2 (by rfl) ⟨1089996, by rfl⟩ : syracuseStep 2906657 = 2179993) B2179993
theorem B27916919 : Blo 1289963 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B2177671 : Blo 1289963 2177671 := bstep (se 1 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 2177671 = 3266507) B3266507
theorem B12401369 : Blo 1289963 12401369 := bstep (se 2 (by rfl) ⟨4650513, by rfl⟩ : syracuseStep 12401369 = 9301027) B9301027
theorem B6536051 : Blo 1289963 6536051 := bstep (se 1 (by rfl) ⟨4902038, by rfl⟩ : syracuseStep 6536051 = 9804077) B9804077
theorem B3677213 : Blo 1289963 3677213 := bstep (se 3 (by rfl) ⟨689477, by rfl⟩ : syracuseStep 3677213 = 1378955) B1378955
theorem B3488903 : Blo 1289963 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B2096329 : Blo 1289963 2096329 := bstep (se 2 (by rfl) ⟨786123, by rfl⟩ : syracuseStep 2096329 = 1572247) B1572247
theorem B4898029 : Blo 1289963 4898029 := bstep (se 3 (by rfl) ⟨918380, by rfl⟩ : syracuseStep 4898029 = 1836761) B1836761
theorem B2178319 : Blo 1289963 2178319 := bstep (se 1 (by rfl) ⟨1633739, by rfl⟩ : syracuseStep 2178319 = 3267479) B3267479
theorem B6536537 : Blo 1289963 6536537 := bstep (se 2 (by rfl) ⟨2451201, by rfl⟩ : syracuseStep 6536537 = 4902403) B4902403
theorem B3677555 : Blo 1289963 3677555 := bstep (se 1 (by rfl) ⟨2758166, by rfl⟩ : syracuseStep 3677555 = 5516333) B5516333
theorem B31415687 : Blo 1289963 31415687 := bstep (se 1 (by rfl) ⟨23561765, by rfl⟩ : syracuseStep 31415687 = 47123531) B47123531
theorem B4357529 : Blo 1289963 4357529 := bstep (se 2 (by rfl) ⟨1634073, by rfl⟩ : syracuseStep 4357529 = 3268147) B3268147
theorem B3268097 : Blo 1289963 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B4898333 : Blo 1289963 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B7347773 : Blo 1289963 7347773 := bstep (se 3 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 7347773 = 2755415) B2755415
theorem B11034305 : Blo 1289963 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B2178859 : Blo 1289963 2178859 := bstep (se 1 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 2178859 = 3268289) B3268289
theorem B3678011 : Blo 1289963 3678011 := bstep (se 1 (by rfl) ⟨2758508, by rfl⟩ : syracuseStep 3678011 = 5517017) B5517017
theorem B3268471 : Blo 1289963 3268471 := bstep (se 1 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 3268471 = 4902707) B4902707
theorem B2179001 : Blo 1289963 2179001 := bstep (se 2 (by rfl) ⟨817125, by rfl⟩ : syracuseStep 2179001 = 1634251) B1634251
theorem B2179129 : Blo 1289963 2179129 := bstep (se 2 (by rfl) ⟨817173, by rfl⟩ : syracuseStep 2179129 = 1634347) B1634347
theorem B6627443 : Blo 1289963 6627443 := bstep (se 1 (by rfl) ⟨4970582, by rfl⟩ : syracuseStep 6627443 = 9941165) B9941165
theorem B2449531 : Blo 1289963 2449531 := bstep (se 1 (by rfl) ⟨1837148, by rfl⟩ : syracuseStep 2449531 = 3674297) B3674297
theorem B4898987 : Blo 1289963 4898987 := bstep (se 1 (by rfl) ⟨3674240, by rfl⟩ : syracuseStep 4898987 = 7348481) B7348481
theorem B2179271 : Blo 1289963 2179271 := bstep (se 1 (by rfl) ⟨1634453, by rfl⟩ : syracuseStep 2179271 = 3268907) B3268907
theorem B2449759 : Blo 1289963 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B2179433 : Blo 1289963 2179433 := bstep (se 2 (by rfl) ⟨817287, by rfl⟩ : syracuseStep 2179433 = 1634575) B1634575
theorem B3490177 : Blo 1289963 3490177 := bstep (se 2 (by rfl) ⟨1308816, by rfl⟩ : syracuseStep 3490177 = 2617633) B2617633
theorem B1745327 : Blo 1289963 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B39764429 : Blo 1289963 39764429 := bstep (se 3 (by rfl) ⟨7455830, by rfl⟩ : syracuseStep 39764429 = 14911661) B14911661
theorem B8495641 : Blo 1289963 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B2450017 : Blo 1289963 2450017 := bstep (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) B1837513
theorem B3490427 : Blo 1289963 3490427 := bstep (se 1 (by rfl) ⟨2617820, by rfl⟩ : syracuseStep 3490427 = 5235641) B5235641
theorem B2482859 : Blo 1289963 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2179831 : Blo 1289963 2179831 := bstep (se 1 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 2179831 = 3269747) B3269747
theorem B18621197 : Blo 1289963 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B2450351 : Blo 1289963 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B4359095 : Blo 1289963 4359095 := bstep (se 1 (by rfl) ⟨3269321, by rfl⟩ : syracuseStep 4359095 = 6538643) B6538643
theorem B2180027 : Blo 1289963 2180027 := bstep (se 1 (by rfl) ⟨1635020, by rfl⟩ : syracuseStep 2180027 = 3270041) B3270041
theorem B11183123 : Blo 1289963 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B2180135 : Blo 1289963 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B6538319 : Blo 1289963 6538319 := bstep (se 1 (by rfl) ⟨4903739, by rfl⟩ : syracuseStep 6538319 = 9807479) B9807479
theorem B33080561 : Blo 1289963 33080561 := bstep (se 2 (by rfl) ⟨12405210, by rfl⟩ : syracuseStep 33080561 = 24810421) B24810421
theorem B3269879 : Blo 1289963 3269879 := bstep (se 1 (by rfl) ⟨2452409, by rfl⟩ : syracuseStep 3269879 = 4904819) B4904819
theorem B2327881 : Blo 1289963 2327881 := bstep (se 2 (by rfl) ⟨872955, by rfl⟩ : syracuseStep 2327881 = 1745911) B1745911
theorem B23553443 : Blo 1289963 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B4359689 : Blo 1289963 4359689 := bstep (se 2 (by rfl) ⟨1634883, by rfl⟩ : syracuseStep 4359689 = 3269767) B3269767
theorem B2795105 : Blo 1289963 2795105 := bstep (se 2 (by rfl) ⟨1048164, by rfl⟩ : syracuseStep 2795105 = 2096329) B2096329
theorem B6530705 : Blo 1289963 6530705 := bstep (se 2 (by rfl) ⟨2449014, by rfl⟩ : syracuseStep 6530705 = 4898029) B4898029
theorem B8267453 : Blo 1289963 8267453 := bstep (se 3 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 8267453 = 3100295) B3100295
theorem B4138685 : Blo 1289963 4138685 := bstep (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) B1552007
theorem B1935047 : Blo 1289963 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B6538967 : Blo 1289963 6538967 := bstep (se 1 (by rfl) ⟨4904225, by rfl⟩ : syracuseStep 6538967 = 9808451) B9808451
theorem B18876203 : Blo 1289963 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B8267579 : Blo 1289963 8267579 := bstep (se 1 (by rfl) ⟨6200684, by rfl⟩ : syracuseStep 8267579 = 12401369) B12401369
theorem B1935209 : Blo 1289963 1935209 := bstep (se 2 (by rfl) ⟨725703, by rfl⟩ : syracuseStep 1935209 = 1451407) B1451407
theorem B1935287 : Blo 1289963 1935287 := bstep (se 1 (by rfl) ⟨1451465, by rfl⟩ : syracuseStep 1935287 = 2902931) B2902931
theorem B12412865 : Blo 1289963 12412865 := bstep (se 2 (by rfl) ⟨4654824, by rfl⟩ : syracuseStep 12412865 = 9309649) B9309649
theorem B1935323 : Blo 1289963 1935323 := bstep (se 1 (by rfl) ⟨1451492, by rfl⟩ : syracuseStep 1935323 = 2902985) B2902985
theorem B2451475 : Blo 1289963 2451475 := bstep (se 1 (by rfl) ⟨1838606, by rfl⟩ : syracuseStep 2451475 = 3677213) B3677213
theorem B4900945 : Blo 1289963 4900945 := bstep (se 2 (by rfl) ⟨1837854, by rfl⟩ : syracuseStep 4900945 = 3675709) B3675709
theorem B14706845 : Blo 1289963 14706845 := bstep (se 3 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 14706845 = 5515067) B5515067
theorem B29788397 : Blo 1289963 29788397 := bstep (se 3 (by rfl) ⟨5585324, by rfl⟩ : syracuseStep 29788397 = 11170649) B11170649
theorem B2451703 : Blo 1289963 2451703 := bstep (se 1 (by rfl) ⟨1838777, by rfl⟩ : syracuseStep 2451703 = 3677555) B3677555
theorem B9439499 : Blo 1289963 9439499 := bstep (se 1 (by rfl) ⟨7079624, by rfl⟩ : syracuseStep 9439499 = 14159249) B14159249
theorem B4901249 : Blo 1289963 4901249 := bstep (se 2 (by rfl) ⟨1837968, by rfl⟩ : syracuseStep 4901249 = 3675937) B3675937
theorem B1935791 : Blo 1289963 1935791 := bstep (se 1 (by rfl) ⟨1451843, by rfl⟩ : syracuseStep 1935791 = 2903687) B2903687
theorem B37243313 : Blo 1289963 37243313 := bstep (se 2 (by rfl) ⟨13966242, by rfl⟩ : syracuseStep 37243313 = 27932485) B27932485
theorem B6973933 : Blo 1289963 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B1935881 : Blo 1289963 1935881 := bstep (se 2 (by rfl) ⟨725955, by rfl⟩ : syracuseStep 1935881 = 1451911) B1451911
theorem B1935911 : Blo 1289963 1935911 := bstep (se 1 (by rfl) ⟨1451933, by rfl⟩ : syracuseStep 1935911 = 2903867) B2903867
theorem B2452007 : Blo 1289963 2452007 := bstep (se 1 (by rfl) ⟨1839005, by rfl⟩ : syracuseStep 2452007 = 3678011) B3678011
theorem B2067023 : Blo 1289963 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B2902625 : Blo 1289963 2902625 := bstep (se 2 (by rfl) ⟨1088484, by rfl⟩ : syracuseStep 2902625 = 2176969) B2176969
theorem B1935995 : Blo 1289963 1935995 := bstep (se 1 (by rfl) ⟨1451996, by rfl⟩ : syracuseStep 1935995 = 2903993) B2903993
theorem B1452667 : Blo 1289963 1452667 := bstep (se 1 (by rfl) ⟨1089500, by rfl⟩ : syracuseStep 1452667 = 2179001) B2179001
theorem B2755271 : Blo 1289963 2755271 := bstep (se 1 (by rfl) ⟨2066453, by rfl⟩ : syracuseStep 2755271 = 4132907) B4132907
theorem B14715593 : Blo 1289963 14715593 := bstep (se 2 (by rfl) ⟨5518347, by rfl⟩ : syracuseStep 14715593 = 11036695) B11036695
theorem B1936121 : Blo 1289963 1936121 := bstep (se 2 (by rfl) ⟨726045, by rfl⟩ : syracuseStep 1936121 = 1452091) B1452091
theorem B4901705 : Blo 1289963 4901705 := bstep (se 2 (by rfl) ⟨1838139, by rfl⟩ : syracuseStep 4901705 = 3676279) B3676279
theorem B1936223 : Blo 1289963 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B1936235 : Blo 1289963 1936235 := bstep (se 1 (by rfl) ⟨1452176, by rfl⟩ : syracuseStep 1936235 = 2904353) B2904353
theorem B2902967 : Blo 1289963 2902967 := bstep (se 1 (by rfl) ⟨2177225, by rfl⟩ : syracuseStep 2902967 = 4354451) B4354451
theorem B4901903 : Blo 1289963 4901903 := bstep (se 1 (by rfl) ⟨3676427, by rfl⟩ : syracuseStep 4901903 = 7352855) B7352855
theorem B8277011 : Blo 1289963 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B1936463 : Blo 1289963 1936463 := bstep (se 1 (by rfl) ⟨1452347, by rfl⟩ : syracuseStep 1936463 = 2904695) B2904695
theorem B1453135 : Blo 1289963 1453135 := bstep (se 1 (by rfl) ⟨1089851, by rfl⟩ : syracuseStep 1453135 = 2179703) B2179703
theorem B1936583 : Blo 1289963 1936583 := bstep (se 1 (by rfl) ⟨1452437, by rfl⟩ : syracuseStep 1936583 = 2904875) B2904875
theorem B1936745 : Blo 1289963 1936745 := bstep (se 2 (by rfl) ⟨726279, by rfl⟩ : syracuseStep 1936745 = 1452559) B1452559
theorem B2944399 : Blo 1289963 2944399 := bstep (se 1 (by rfl) ⟨2208299, by rfl⟩ : syracuseStep 2944399 = 4416599) B4416599
theorem B1936823 : Blo 1289963 1936823 := bstep (se 1 (by rfl) ⟨1452617, by rfl⟩ : syracuseStep 1936823 = 2905235) B2905235
theorem B9801161 : Blo 1289963 9801161 := bstep (se 2 (by rfl) ⟨3675435, by rfl⟩ : syracuseStep 9801161 = 7350871) B7350871
theorem B1936859 : Blo 1289963 1936859 := bstep (se 1 (by rfl) ⟨1452644, by rfl⟩ : syracuseStep 1936859 = 2905289) B2905289
theorem B2903561 : Blo 1289963 2903561 := bstep (se 2 (by rfl) ⟨1088835, by rfl⟩ : syracuseStep 2903561 = 2177671) B2177671
theorem B1633871 : Blo 1289963 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B1290023 : Blo 1289963 1290023 := bstep (se 1 (by rfl) ⟨967517, by rfl⟩ : syracuseStep 1290023 = 1935035) B1935035
theorem B1290063 : Blo 1289963 1290063 := bstep (se 1 (by rfl) ⟨967547, by rfl⟩ : syracuseStep 1290063 = 1935095) B1935095
theorem B1290079 : Blo 1289963 1290079 := bstep (se 1 (by rfl) ⟨967559, by rfl⟩ : syracuseStep 1290079 = 1935119) B1935119
theorem B2903903 : Blo 1289963 2903903 := bstep (se 1 (by rfl) ⟨2177927, by rfl⟩ : syracuseStep 2903903 = 4355855) B4355855
theorem B6532973 : Blo 1289963 6532973 := bstep (se 3 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 6532973 = 2449865) B2449865
theorem B4353911 : Blo 1289963 4353911 := bstep (se 1 (by rfl) ⟨3265433, by rfl⟩ : syracuseStep 4353911 = 6530867) B6530867
theorem B1290107 : Blo 1289963 1290107 := bstep (se 1 (by rfl) ⟨967580, by rfl⟩ : syracuseStep 1290107 = 1935161) B1935161
theorem B1290159 : Blo 1289963 1290159 := bstep (se 1 (by rfl) ⟨967619, by rfl⟩ : syracuseStep 1290159 = 1935239) B1935239
theorem B1937327 : Blo 1289963 1937327 := bstep (se 1 (by rfl) ⟨1452995, by rfl⟩ : syracuseStep 1937327 = 2905991) B2905991
theorem B12406715 : Blo 1289963 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B1290183 : Blo 1289963 1290183 := bstep (se 1 (by rfl) ⟨967637, by rfl⟩ : syracuseStep 1290183 = 1935275) B1935275
theorem B1290203 : Blo 1289963 1290203 := bstep (se 1 (by rfl) ⟨967652, by rfl⟩ : syracuseStep 1290203 = 1935305) B1935305
theorem B1937417 : Blo 1289963 1937417 := bstep (se 2 (by rfl) ⟨726531, by rfl⟩ : syracuseStep 1937417 = 1453063) B1453063
theorem B6533135 : Blo 1289963 6533135 := bstep (se 1 (by rfl) ⟨4899851, by rfl⟩ : syracuseStep 6533135 = 9799703) B9799703
theorem B2904083 : Blo 1289963 2904083 := bstep (se 1 (by rfl) ⟨2178062, by rfl⟩ : syracuseStep 2904083 = 4356125) B4356125
theorem B1290279 : Blo 1289963 1290279 := bstep (se 1 (by rfl) ⟨967709, by rfl⟩ : syracuseStep 1290279 = 1935419) B1935419
theorem B1937447 : Blo 1289963 1937447 := bstep (se 1 (by rfl) ⟨1453085, by rfl⟩ : syracuseStep 1937447 = 2906171) B2906171
theorem B4354127 : Blo 1289963 4354127 := bstep (se 1 (by rfl) ⟨3265595, by rfl⟩ : syracuseStep 4354127 = 6531191) B6531191
theorem B1290319 : Blo 1289963 1290319 := bstep (se 1 (by rfl) ⟨967739, by rfl⟩ : syracuseStep 1290319 = 1935479) B1935479
theorem B1290335 : Blo 1289963 1290335 := bstep (se 1 (by rfl) ⟨967751, by rfl⟩ : syracuseStep 1290335 = 1935503) B1935503
theorem B1290363 : Blo 1289963 1290363 := bstep (se 1 (by rfl) ⟨967772, by rfl⟩ : syracuseStep 1290363 = 1935545) B1935545
theorem B1937531 : Blo 1289963 1937531 := bstep (se 1 (by rfl) ⟨1453148, by rfl⟩ : syracuseStep 1937531 = 2906297) B2906297
theorem B1290415 : Blo 1289963 1290415 := bstep (se 1 (by rfl) ⟨967811, by rfl⟩ : syracuseStep 1290415 = 1935623) B1935623
theorem B1290439 : Blo 1289963 1290439 := bstep (se 1 (by rfl) ⟨967829, by rfl⟩ : syracuseStep 1290439 = 1935659) B1935659
theorem B1290459 : Blo 1289963 1290459 := bstep (se 1 (by rfl) ⟨967844, by rfl⟩ : syracuseStep 1290459 = 1935689) B1935689
theorem B1937657 : Blo 1289963 1937657 := bstep (se 2 (by rfl) ⟨726621, by rfl⟩ : syracuseStep 1937657 = 1453243) B1453243
theorem B1290535 : Blo 1289963 1290535 := bstep (se 1 (by rfl) ⟨967901, by rfl⟩ : syracuseStep 1290535 = 1935803) B1935803
theorem B15102283 : Blo 1289963 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B1290575 : Blo 1289963 1290575 := bstep (se 1 (by rfl) ⟨967931, by rfl⟩ : syracuseStep 1290575 = 1935863) B1935863
theorem B1290591 : Blo 1289963 1290591 := bstep (se 1 (by rfl) ⟨967943, by rfl⟩ : syracuseStep 1290591 = 1935887) B1935887
theorem B1937759 : Blo 1289963 1937759 := bstep (se 1 (by rfl) ⟨1453319, by rfl⟩ : syracuseStep 1937759 = 2906639) B2906639
theorem B4133225 : Blo 1289963 4133225 := bstep (se 2 (by rfl) ⟨1549959, by rfl⟩ : syracuseStep 4133225 = 3099919) B3099919
theorem B2904425 : Blo 1289963 2904425 := bstep (se 2 (by rfl) ⟨1089159, by rfl⟩ : syracuseStep 2904425 = 2178319) B2178319
theorem B2068843 : Blo 1289963 2068843 := bstep (se 1 (by rfl) ⟨1551632, by rfl⟩ : syracuseStep 2068843 = 3103265) B3103265
theorem B1937771 : Blo 1289963 1937771 := bstep (se 1 (by rfl) ⟨1453328, by rfl⟩ : syracuseStep 1937771 = 2906657) B2906657
theorem B1290619 : Blo 1289963 1290619 := bstep (se 1 (by rfl) ⟨967964, by rfl⟩ : syracuseStep 1290619 = 1935929) B1935929
theorem B2945423 : Blo 1289963 2945423 := bstep (se 1 (by rfl) ⟨2209067, by rfl⟩ : syracuseStep 2945423 = 4418135) B4418135
theorem B1290671 : Blo 1289963 1290671 := bstep (se 1 (by rfl) ⟨968003, by rfl⟩ : syracuseStep 1290671 = 1936007) B1936007
theorem B1290695 : Blo 1289963 1290695 := bstep (se 1 (by rfl) ⟨968021, by rfl⟩ : syracuseStep 1290695 = 1936043) B1936043
theorem B4354505 : Blo 1289963 4354505 := bstep (se 2 (by rfl) ⟨1632939, by rfl⟩ : syracuseStep 4354505 = 3265879) B3265879
theorem B1290715 : Blo 1289963 1290715 := bstep (se 1 (by rfl) ⟨968036, by rfl⟩ : syracuseStep 1290715 = 1936073) B1936073
theorem B127250929 : Blo 1289963 127250929 := bstep (se 2 (by rfl) ⟨47719098, by rfl⟩ : syracuseStep 127250929 = 95438197) B95438197
theorem B1290791 : Blo 1289963 1290791 := bstep (se 1 (by rfl) ⟨968093, by rfl⟩ : syracuseStep 1290791 = 1936187) B1936187
theorem B1290831 : Blo 1289963 1290831 := bstep (se 1 (by rfl) ⟨968123, by rfl⟩ : syracuseStep 1290831 = 1936247) B1936247
theorem B1290847 : Blo 1289963 1290847 := bstep (se 1 (by rfl) ⟨968135, by rfl⟩ : syracuseStep 1290847 = 1936271) B1936271
theorem B1290875 : Blo 1289963 1290875 := bstep (se 1 (by rfl) ⟨968156, by rfl⟩ : syracuseStep 1290875 = 1936313) B1936313
theorem B1290927 : Blo 1289963 1290927 := bstep (se 1 (by rfl) ⟨968195, by rfl⟩ : syracuseStep 1290927 = 1936391) B1936391
theorem B1290951 : Blo 1289963 1290951 := bstep (se 1 (by rfl) ⟨968213, by rfl⟩ : syracuseStep 1290951 = 1936427) B1936427
theorem B35320529 : Blo 1289963 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B4354775 : Blo 1289963 4354775 := bstep (se 1 (by rfl) ⟨3266081, by rfl⟩ : syracuseStep 4354775 = 6532163) B6532163
theorem B1290971 : Blo 1289963 1290971 := bstep (se 1 (by rfl) ⟨968228, by rfl⟩ : syracuseStep 1290971 = 1936457) B1936457
theorem B1291047 : Blo 1289963 1291047 := bstep (se 1 (by rfl) ⟨968285, by rfl⟩ : syracuseStep 1291047 = 1936571) B1936571
theorem B4649795 : Blo 1289963 4649795 := bstep (se 1 (by rfl) ⟨3487346, by rfl⟩ : syracuseStep 4649795 = 6974693) B6974693
theorem B1291087 : Blo 1289963 1291087 := bstep (se 1 (by rfl) ⟨968315, by rfl⟩ : syracuseStep 1291087 = 1936631) B1936631
theorem B1291103 : Blo 1289963 1291103 := bstep (se 1 (by rfl) ⟨968327, by rfl⟩ : syracuseStep 1291103 = 1936655) B1936655
theorem B2618219 : Blo 1289963 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B1291131 : Blo 1289963 1291131 := bstep (se 1 (by rfl) ⟨968348, by rfl⟩ : syracuseStep 1291131 = 1936697) B1936697
theorem B4354991 : Blo 1289963 4354991 := bstep (se 1 (by rfl) ⟨3266243, by rfl⟩ : syracuseStep 4354991 = 6532487) B6532487
theorem B1291183 : Blo 1289963 1291183 := bstep (se 1 (by rfl) ⟨968387, by rfl⟩ : syracuseStep 1291183 = 1936775) B1936775
theorem B20943791 : Blo 1289963 20943791 := bstep (se 1 (by rfl) ⟨15707843, by rfl⟩ : syracuseStep 20943791 = 31415687) B31415687
theorem B2905019 : Blo 1289963 2905019 := bstep (se 1 (by rfl) ⟨2178764, by rfl⟩ : syracuseStep 2905019 = 4357529) B4357529
theorem B1291207 : Blo 1289963 1291207 := bstep (se 1 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 1291207 = 1936811) B1936811
theorem B1291227 : Blo 1289963 1291227 := bstep (se 1 (by rfl) ⟨968420, by rfl⟩ : syracuseStep 1291227 = 1936841) B1936841
theorem B14709761 : Blo 1289963 14709761 := bstep (se 2 (by rfl) ⟨5516160, by rfl⟩ : syracuseStep 14709761 = 11032321) B11032321
theorem B3265555 : Blo 1289963 3265555 := bstep (se 1 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 3265555 = 4898333) B4898333
theorem B1291303 : Blo 1289963 1291303 := bstep (se 1 (by rfl) ⟨968477, by rfl⟩ : syracuseStep 1291303 = 1936955) B1936955
theorem B2905145 : Blo 1289963 2905145 := bstep (se 2 (by rfl) ⟨1089429, by rfl⟩ : syracuseStep 2905145 = 2178859) B2178859
theorem B1291343 : Blo 1289963 1291343 := bstep (se 1 (by rfl) ⟨968507, by rfl⟩ : syracuseStep 1291343 = 1937015) B1937015
theorem B1291359 : Blo 1289963 1291359 := bstep (se 1 (by rfl) ⟨968519, by rfl⟩ : syracuseStep 1291359 = 1937039) B1937039
theorem B1291387 : Blo 1289963 1291387 := bstep (se 1 (by rfl) ⟨968540, by rfl⟩ : syracuseStep 1291387 = 1937081) B1937081
theorem B1291439 : Blo 1289963 1291439 := bstep (se 1 (by rfl) ⟨968579, by rfl⟩ : syracuseStep 1291439 = 1937159) B1937159
theorem B1291463 : Blo 1289963 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B1291483 : Blo 1289963 1291483 := bstep (se 1 (by rfl) ⟨968612, by rfl⟩ : syracuseStep 1291483 = 1937225) B1937225
theorem B1291559 : Blo 1289963 1291559 := bstep (se 1 (by rfl) ⟨968669, by rfl⟩ : syracuseStep 1291559 = 1937339) B1937339
theorem B1291599 : Blo 1289963 1291599 := bstep (se 1 (by rfl) ⟨968699, by rfl⟩ : syracuseStep 1291599 = 1937399) B1937399
theorem B1291615 : Blo 1289963 1291615 := bstep (se 1 (by rfl) ⟨968711, by rfl⟩ : syracuseStep 1291615 = 1937423) B1937423
theorem B1291643 : Blo 1289963 1291643 := bstep (se 1 (by rfl) ⟨968732, by rfl⟩ : syracuseStep 1291643 = 1937465) B1937465
theorem B2905487 : Blo 1289963 2905487 := bstep (se 1 (by rfl) ⟨2179115, by rfl⟩ : syracuseStep 2905487 = 4358231) B4358231
theorem B10614179 : Blo 1289963 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B1291695 : Blo 1289963 1291695 := bstep (se 1 (by rfl) ⟨968771, by rfl⟩ : syracuseStep 1291695 = 1937543) B1937543
theorem B1291719 : Blo 1289963 1291719 := bstep (se 1 (by rfl) ⟨968789, by rfl⟩ : syracuseStep 1291719 = 1937579) B1937579
theorem B18863561 : Blo 1289963 18863561 := bstep (se 2 (by rfl) ⟨7073835, by rfl⟩ : syracuseStep 18863561 = 14147671) B14147671
theorem B1291739 : Blo 1289963 1291739 := bstep (se 1 (by rfl) ⟨968804, by rfl⟩ : syracuseStep 1291739 = 1937609) B1937609
theorem B8271371 : Blo 1289963 8271371 := bstep (se 1 (by rfl) ⟨6203528, by rfl⟩ : syracuseStep 8271371 = 12407057) B12407057
theorem B1291815 : Blo 1289963 1291815 := bstep (se 1 (by rfl) ⟨968861, by rfl⟩ : syracuseStep 1291815 = 1937723) B1937723
theorem B1291855 : Blo 1289963 1291855 := bstep (se 1 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 1291855 = 1937783) B1937783
theorem B1291871 : Blo 1289963 1291871 := bstep (se 1 (by rfl) ⟨968903, by rfl⟩ : syracuseStep 1291871 = 1937807) B1937807
theorem B1291899 : Blo 1289963 1291899 := bstep (se 1 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 1291899 = 1937849) B1937849
theorem B1291951 : Blo 1289963 1291951 := bstep (se 1 (by rfl) ⟨968963, by rfl⟩ : syracuseStep 1291951 = 1937927) B1937927
theorem B2905811 : Blo 1289963 2905811 := bstep (se 1 (by rfl) ⟨2179358, by rfl⟩ : syracuseStep 2905811 = 4358717) B4358717
theorem B3102457 : Blo 1289963 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B6207299 : Blo 1289963 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B2176841 : Blo 1289963 2176841 := bstep (se 2 (by rfl) ⟨816315, by rfl⟩ : syracuseStep 2176841 = 1632631) B1632631
theorem B4134763 : Blo 1289963 4134763 := bstep (se 1 (by rfl) ⟨3101072, by rfl⟩ : syracuseStep 4134763 = 6202145) B6202145
theorem B5887853 : Blo 1289963 5887853 := bstep (se 3 (by rfl) ⟨1103972, by rfl⟩ : syracuseStep 5887853 = 2207945) B2207945
theorem B37738349 : Blo 1289963 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B2095031 : Blo 1289963 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B3266639 : Blo 1289963 3266639 := bstep (se 1 (by rfl) ⟨2449979, by rfl⟩ : syracuseStep 3266639 = 4899959) B4899959
theorem B2095303 : Blo 1289963 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B2177273 : Blo 1289963 2177273 := bstep (se 2 (by rfl) ⟨816477, by rfl⟩ : syracuseStep 2177273 = 1632955) B1632955
theorem B169834765 : Blo 1289963 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B9935257 : Blo 1289963 9935257 := bstep (se 2 (by rfl) ⟨3725721, by rfl⟩ : syracuseStep 9935257 = 7451443) B7451443
theorem B2177455 : Blo 1289963 2177455 := bstep (se 1 (by rfl) ⟨1633091, by rfl⟩ : syracuseStep 2177455 = 3266183) B3266183
theorem B2177543 : Blo 1289963 2177543 := bstep (se 1 (by rfl) ⟨1633157, by rfl⟩ : syracuseStep 2177543 = 3266315) B3266315
theorem B2906747 : Blo 1289963 2906747 := bstep (se 1 (by rfl) ⟨2180060, by rfl⟩ : syracuseStep 2906747 = 4360121) B4360121
theorem B6535889 : Blo 1289963 6535889 := bstep (se 2 (by rfl) ⟨2450958, by rfl⟩ : syracuseStep 6535889 = 4901917) B4901917
theorem B3488471 : Blo 1289963 3488471 := bstep (se 1 (by rfl) ⟨2616353, by rfl⟩ : syracuseStep 3488471 = 5232707) B5232707
theorem B3267287 : Blo 1289963 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B2906873 : Blo 1289963 2906873 := bstep (se 2 (by rfl) ⟨1090077, by rfl⟩ : syracuseStep 2906873 = 2180155) B2180155
theorem B2177887 : Blo 1289963 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B2653103 : Blo 1289963 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B2325431 : Blo 1289963 2325431 := bstep (se 1 (by rfl) ⟨1744073, by rfl⟩ : syracuseStep 2325431 = 3488147) B3488147
theorem B2177975 : Blo 1289963 2177975 := bstep (se 1 (by rfl) ⟨1633481, by rfl⟩ : syracuseStep 2177975 = 3266963) B3266963
theorem B1743835 : Blo 1289963 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B3103763 : Blo 1289963 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B3267641 : Blo 1289963 3267641 := bstep (se 2 (by rfl) ⟨1225365, by rfl⟩ : syracuseStep 3267641 = 2450731) B2450731
theorem B18611279 : Blo 1289963 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B4357367 : Blo 1289963 4357367 := bstep (se 1 (by rfl) ⟨3268025, by rfl⟩ : syracuseStep 4357367 = 6536051) B6536051
theorem B2325935 : Blo 1289963 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B25476569 : Blo 1289963 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B2178569 : Blo 1289963 2178569 := bstep (se 2 (by rfl) ⟨816963, by rfl⟩ : syracuseStep 2178569 = 1633927) B1633927
theorem B4357691 : Blo 1289963 4357691 := bstep (se 1 (by rfl) ⟨3268268, by rfl⟩ : syracuseStep 4357691 = 6536537) B6536537
theorem B2178731 : Blo 1289963 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B4898515 : Blo 1289963 4898515 := bstep (se 1 (by rfl) ⟨3673886, by rfl⟩ : syracuseStep 4898515 = 7347773) B7347773
theorem B14147293 : Blo 1289963 14147293 := bstep (se 3 (by rfl) ⟨2652617, by rfl⟩ : syracuseStep 14147293 = 5305235) B5305235
theorem B7356203 : Blo 1289963 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4357961 : Blo 1289963 4357961 := bstep (se 2 (by rfl) ⟨1634235, by rfl⟩ : syracuseStep 4357961 = 3268471) B3268471
theorem B3268633 : Blo 1289963 3268633 := bstep (se 2 (by rfl) ⟨1225737, by rfl⟩ : syracuseStep 3268633 = 2451475) B2451475
theorem B2793737 : Blo 1289963 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B26509619 : Blo 1289963 26509619 := bstep (se 1 (by rfl) ⟨19882214, by rfl⟩ : syracuseStep 26509619 = 39764429) B39764429
theorem B3268937 : Blo 1289963 3268937 := bstep (se 2 (by rfl) ⟨1225851, by rfl⟩ : syracuseStep 3268937 = 2451703) B2451703
theorem B2326951 : Blo 1289963 2326951 := bstep (se 1 (by rfl) ⟨1745213, by rfl⟩ : syracuseStep 2326951 = 3490427) B3490427
theorem B20136377 : Blo 1289963 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B4653569 : Blo 1289963 4653569 := bstep (se 2 (by rfl) ⟨1745088, by rfl⟩ : syracuseStep 4653569 = 3490177) B3490177
theorem B13247009 : Blo 1289963 13247009 := bstep (se 2 (by rfl) ⟨4967628, by rfl⟩ : syracuseStep 13247009 = 9935257) B9935257
theorem B1745479 : Blo 1289963 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B9298577 : Blo 1289963 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B9806507 : Blo 1289963 9806507 := bstep (se 1 (by rfl) ⟨7354880, by rfl⟩ : syracuseStep 9806507 = 14709761) B14709761
theorem B7455415 : Blo 1289963 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B4358879 : Blo 1289963 4358879 := bstep (se 1 (by rfl) ⟨3269159, by rfl⟩ : syracuseStep 4358879 = 6538319) B6538319
theorem B22053707 : Blo 1289963 22053707 := bstep (se 1 (by rfl) ⟨16540280, by rfl⟩ : syracuseStep 22053707 = 33080561) B33080561
theorem B2179919 : Blo 1289963 2179919 := bstep (se 1 (by rfl) ⟨1634939, by rfl⟩ : syracuseStep 2179919 = 3269879) B3269879
theorem B5514247 : Blo 1289963 5514247 := bstep (se 1 (by rfl) ⟨4135685, by rfl⟩ : syracuseStep 5514247 = 8271371) B8271371
theorem B6202493 : Blo 1289963 6202493 := bstep (se 3 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 6202493 = 2325935) B2325935
theorem B4654205 : Blo 1289963 4654205 := bstep (se 3 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 4654205 = 1745327) B1745327
theorem B4359311 : Blo 1289963 4359311 := bstep (se 1 (by rfl) ⟨3269483, by rfl⟩ : syracuseStep 4359311 = 6538967) B6538967
theorem B12584135 : Blo 1289963 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B4138199 : Blo 1289963 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B1451227 : Blo 1289963 1451227 := bstep (se 1 (by rfl) ⟨1088420, by rfl⟩ : syracuseStep 1451227 = 2176841) B2176841
theorem B3925235 : Blo 1289963 3925235 := bstep (se 1 (by rfl) ⟨2943926, by rfl⟩ : syracuseStep 3925235 = 5887853) B5887853
theorem B25158899 : Blo 1289963 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B8275243 : Blo 1289963 8275243 := bstep (se 1 (by rfl) ⟨6206432, by rfl⟩ : syracuseStep 8275243 = 12412865) B12412865
theorem B19858931 : Blo 1289963 19858931 := bstep (se 1 (by rfl) ⟨14894198, by rfl⟩ : syracuseStep 19858931 = 29788397) B29788397
theorem B1451515 : Blo 1289963 1451515 := bstep (se 1 (by rfl) ⟨1088636, by rfl⟩ : syracuseStep 1451515 = 2177273) B2177273
theorem B6292999 : Blo 1289963 6292999 := bstep (se 1 (by rfl) ⟨4719749, by rfl⟩ : syracuseStep 6292999 = 9439499) B9439499
theorem B1451695 : Blo 1289963 1451695 := bstep (se 1 (by rfl) ⟨1088771, by rfl⟩ : syracuseStep 1451695 = 2177543) B2177543
theorem B1378015 : Blo 1289963 1378015 := bstep (se 1 (by rfl) ⟨1033511, by rfl⟩ : syracuseStep 1378015 = 2067023) B2067023
theorem B1935083 : Blo 1289963 1935083 := bstep (se 1 (by rfl) ⟨1451312, by rfl⟩ : syracuseStep 1935083 = 2902625) B2902625
theorem B6620957 : Blo 1289963 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1836847 : Blo 1289963 1836847 := bstep (se 1 (by rfl) ⟨1377635, by rfl⟩ : syracuseStep 1836847 = 2755271) B2755271
theorem B3925865 : Blo 1289963 3925865 := bstep (se 2 (by rfl) ⟨1472199, by rfl⟩ : syracuseStep 3925865 = 2944399) B2944399
theorem B1935311 : Blo 1289963 1935311 := bstep (se 1 (by rfl) ⟨1451483, by rfl⟩ : syracuseStep 1935311 = 2902967) B2902967
theorem B1550287 : Blo 1289963 1550287 := bstep (se 1 (by rfl) ⟨1162715, by rfl⟩ : syracuseStep 1550287 = 2325431) B2325431
theorem B1451983 : Blo 1289963 1451983 := bstep (se 1 (by rfl) ⟨1088987, by rfl⟩ : syracuseStep 1451983 = 2177975) B2177975
theorem B6531353 : Blo 1289963 6531353 := bstep (se 2 (by rfl) ⟨2449257, by rfl⟩ : syracuseStep 6531353 = 4898515) B4898515
theorem B16984379 : Blo 1289963 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B1935707 : Blo 1289963 1935707 := bstep (se 1 (by rfl) ⟨1451780, by rfl⟩ : syracuseStep 1935707 = 2903561) B2903561
theorem B1452379 : Blo 1289963 1452379 := bstep (se 1 (by rfl) ⟨1089284, by rfl⟩ : syracuseStep 1452379 = 2178569) B2178569
theorem B1452487 : Blo 1289963 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B1935935 : Blo 1289963 1935935 := bstep (se 1 (by rfl) ⟨1451951, by rfl⟩ : syracuseStep 1935935 = 2903903) B2903903
theorem B2902607 : Blo 1289963 2902607 := bstep (se 1 (by rfl) ⟨2176955, by rfl⟩ : syracuseStep 2902607 = 4353911) B4353911
theorem B1936055 : Blo 1289963 1936055 := bstep (se 1 (by rfl) ⟨1452041, by rfl⟩ : syracuseStep 1936055 = 2904083) B2904083
theorem B2902751 : Blo 1289963 2902751 := bstep (se 1 (by rfl) ⟨2177063, by rfl⟩ : syracuseStep 2902751 = 4354127) B4354127
theorem B1452847 : Blo 1289963 1452847 := bstep (se 1 (by rfl) ⟨1089635, by rfl⟩ : syracuseStep 1452847 = 2179271) B2179271
theorem B33106805 : Blo 1289963 33106805 := bstep (se 5 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 33106805 = 3103763) B3103763
theorem B1936283 : Blo 1289963 1936283 := bstep (se 1 (by rfl) ⟨1452212, by rfl⟩ : syracuseStep 1936283 = 2904425) B2904425
theorem B1452955 : Blo 1289963 1452955 := bstep (se 1 (by rfl) ⟨1089716, by rfl⟩ : syracuseStep 1452955 = 2179433) B2179433
theorem B2903003 : Blo 1289963 2903003 := bstep (se 1 (by rfl) ⟨2177252, by rfl⟩ : syracuseStep 2903003 = 4354505) B4354505
theorem B226446353 : Blo 1289963 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B23547019 : Blo 1289963 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B2903183 : Blo 1289963 2903183 := bstep (se 1 (by rfl) ⟨2177387, by rfl⟩ : syracuseStep 2903183 = 4354775) B4354775
theorem B12414131 : Blo 1289963 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B3099863 : Blo 1289963 3099863 := bstep (se 1 (by rfl) ⟨2324897, by rfl⟩ : syracuseStep 3099863 = 4649795) B4649795
theorem B2903273 : Blo 1289963 2903273 := bstep (se 2 (by rfl) ⟨1088727, by rfl⟩ : syracuseStep 2903273 = 2177455) B2177455
theorem B2903327 : Blo 1289963 2903327 := bstep (se 1 (by rfl) ⟨2177495, by rfl⟩ : syracuseStep 2903327 = 4354991) B4354991
theorem B13962527 : Blo 1289963 13962527 := bstep (se 1 (by rfl) ⟨10471895, by rfl⟩ : syracuseStep 13962527 = 20943791) B20943791
theorem B1936679 : Blo 1289963 1936679 := bstep (se 1 (by rfl) ⟨1452509, by rfl⟩ : syracuseStep 1936679 = 2905019) B2905019
theorem B1453351 : Blo 1289963 1453351 := bstep (se 1 (by rfl) ⟨1090013, by rfl⟩ : syracuseStep 1453351 = 2180027) B2180027
theorem B169667905 : Blo 1289963 169667905 := bstep (se 2 (by rfl) ⟨63625464, by rfl⟩ : syracuseStep 169667905 = 127250929) B127250929
theorem B1453423 : Blo 1289963 1453423 := bstep (se 1 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 1453423 = 2180135) B2180135
theorem B1936763 : Blo 1289963 1936763 := bstep (se 1 (by rfl) ⟨1452572, by rfl⟩ : syracuseStep 1936763 = 2905145) B2905145
theorem B1936889 : Blo 1289963 1936889 := bstep (se 2 (by rfl) ⟨726333, by rfl⟩ : syracuseStep 1936889 = 1452667) B1452667
theorem B1936991 : Blo 1289963 1936991 := bstep (se 1 (by rfl) ⟨1452743, by rfl⟩ : syracuseStep 1936991 = 2905487) B2905487
theorem B11021933 : Blo 1289963 11021933 := bstep (se 3 (by rfl) ⟨2066612, by rfl⟩ : syracuseStep 11021933 = 4133225) B4133225
theorem B4353803 : Blo 1289963 4353803 := bstep (se 1 (by rfl) ⟨3265352, by rfl⟩ : syracuseStep 4353803 = 6530705) B6530705
theorem B2903849 : Blo 1289963 2903849 := bstep (se 2 (by rfl) ⟨1088943, by rfl⟩ : syracuseStep 2903849 = 2177887) B2177887
theorem B1290031 : Blo 1289963 1290031 := bstep (se 1 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 1290031 = 1935047) B1935047
theorem B1937207 : Blo 1289963 1937207 := bstep (se 1 (by rfl) ⟨1452905, by rfl⟩ : syracuseStep 1937207 = 2905811) B2905811
theorem B50302829 : Blo 1289963 50302829 := bstep (se 3 (by rfl) ⟨9431780, by rfl⟩ : syracuseStep 50302829 = 18863561) B18863561
theorem B70692725 : Blo 1289963 70692725 := bstep (se 5 (by rfl) ⟨3313721, by rfl⟩ : syracuseStep 70692725 = 6627443) B6627443
theorem B1290139 : Blo 1289963 1290139 := bstep (se 1 (by rfl) ⟨967604, by rfl⟩ : syracuseStep 1290139 = 1935209) B1935209
theorem B1290191 : Blo 1289963 1290191 := bstep (se 1 (by rfl) ⟨967643, by rfl⟩ : syracuseStep 1290191 = 1935287) B1935287
theorem B1290215 : Blo 1289963 1290215 := bstep (se 1 (by rfl) ⟨967661, by rfl⟩ : syracuseStep 1290215 = 1935323) B1935323
theorem B4354073 : Blo 1289963 4354073 := bstep (se 2 (by rfl) ⟨1632777, by rfl⟩ : syracuseStep 4354073 = 3265555) B3265555
theorem B1937513 : Blo 1289963 1937513 := bstep (se 2 (by rfl) ⟨726567, by rfl⟩ : syracuseStep 1937513 = 1453135) B1453135
theorem B1290527 : Blo 1289963 1290527 := bstep (se 1 (by rfl) ⟨967895, by rfl⟩ : syracuseStep 1290527 = 1935791) B1935791
theorem B1290587 : Blo 1289963 1290587 := bstep (se 1 (by rfl) ⟨967940, by rfl⟩ : syracuseStep 1290587 = 1935881) B1935881
theorem B1290607 : Blo 1289963 1290607 := bstep (se 1 (by rfl) ⟨967955, by rfl⟩ : syracuseStep 1290607 = 1935911) B1935911
theorem B1634671 : Blo 1289963 1634671 := bstep (se 1 (by rfl) ⟨1226003, by rfl⟩ : syracuseStep 1634671 = 2452007) B2452007
theorem B1290663 : Blo 1289963 1290663 := bstep (se 1 (by rfl) ⟨967997, by rfl⟩ : syracuseStep 1290663 = 1935995) B1935995
theorem B1937831 : Blo 1289963 1937831 := bstep (se 1 (by rfl) ⟨1453373, by rfl⟩ : syracuseStep 1937831 = 2906747) B2906747
theorem B9810395 : Blo 1289963 9810395 := bstep (se 1 (by rfl) ⟨7357796, by rfl⟩ : syracuseStep 9810395 = 14715593) B14715593
theorem B1290747 : Blo 1289963 1290747 := bstep (se 1 (by rfl) ⟨968060, by rfl⟩ : syracuseStep 1290747 = 1936121) B1936121
theorem B1937915 : Blo 1289963 1937915 := bstep (se 1 (by rfl) ⟨1453436, by rfl⟩ : syracuseStep 1937915 = 2906873) B2906873
theorem B1290815 : Blo 1289963 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B1290823 : Blo 1289963 1290823 := bstep (se 1 (by rfl) ⟨968117, by rfl⟩ : syracuseStep 1290823 = 1936235) B1936235
theorem B5518007 : Blo 1289963 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B1290975 : Blo 1289963 1290975 := bstep (se 1 (by rfl) ⟨968231, by rfl⟩ : syracuseStep 1290975 = 1936463) B1936463
theorem B12407519 : Blo 1289963 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B1291055 : Blo 1289963 1291055 := bstep (se 1 (by rfl) ⟨968291, by rfl⟩ : syracuseStep 1291055 = 1936583) B1936583
theorem B2904911 : Blo 1289963 2904911 := bstep (se 1 (by rfl) ⟨2178683, by rfl⟩ : syracuseStep 2904911 = 4357367) B4357367
theorem B1291163 : Blo 1289963 1291163 := bstep (se 1 (by rfl) ⟨968372, by rfl⟩ : syracuseStep 1291163 = 1936745) B1936745
theorem B1291215 : Blo 1289963 1291215 := bstep (se 1 (by rfl) ⟨968411, by rfl⟩ : syracuseStep 1291215 = 1936823) B1936823
theorem B18863057 : Blo 1289963 18863057 := bstep (se 2 (by rfl) ⟨7073646, by rfl⟩ : syracuseStep 18863057 = 14147293) B14147293
theorem B6534107 : Blo 1289963 6534107 := bstep (se 1 (by rfl) ⟨4900580, by rfl⟩ : syracuseStep 6534107 = 9801161) B9801161
theorem B1291239 : Blo 1289963 1291239 := bstep (se 1 (by rfl) ⟨968429, by rfl⟩ : syracuseStep 1291239 = 1936859) B1936859
theorem B2905127 : Blo 1289963 2905127 := bstep (se 1 (by rfl) ⟨2178845, by rfl⟩ : syracuseStep 2905127 = 4357691) B4357691
theorem B6534269 : Blo 1289963 6534269 := bstep (se 3 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 6534269 = 2450351) B2450351
theorem B4904135 : Blo 1289963 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B2905307 : Blo 1289963 2905307 := bstep (se 1 (by rfl) ⟨2178980, by rfl⟩ : syracuseStep 2905307 = 4357961) B4357961
theorem B4355315 : Blo 1289963 4355315 := bstep (se 1 (by rfl) ⟨3266486, by rfl⟩ : syracuseStep 4355315 = 6532973) B6532973
theorem B1291551 : Blo 1289963 1291551 := bstep (se 1 (by rfl) ⟨968663, by rfl⟩ : syracuseStep 1291551 = 1937327) B1937327
theorem B8271143 : Blo 1289963 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B1291611 : Blo 1289963 1291611 := bstep (se 1 (by rfl) ⟨968708, by rfl⟩ : syracuseStep 1291611 = 1937417) B1937417
theorem B4355423 : Blo 1289963 4355423 := bstep (se 1 (by rfl) ⟨3266567, by rfl⟩ : syracuseStep 4355423 = 6533135) B6533135
theorem B1291631 : Blo 1289963 1291631 := bstep (se 1 (by rfl) ⟨968723, by rfl⟩ : syracuseStep 1291631 = 1937447) B1937447
theorem B2905505 : Blo 1289963 2905505 := bstep (se 2 (by rfl) ⟨1089564, by rfl⟩ : syracuseStep 2905505 = 2179129) B2179129
theorem B1291687 : Blo 1289963 1291687 := bstep (se 1 (by rfl) ⟨968765, by rfl⟩ : syracuseStep 1291687 = 1937531) B1937531
theorem B6534593 : Blo 1289963 6534593 := bstep (se 2 (by rfl) ⟨2450472, by rfl⟩ : syracuseStep 6534593 = 4900945) B4900945
theorem B3265991 : Blo 1289963 3265991 := bstep (se 1 (by rfl) ⟨2449493, by rfl⟩ : syracuseStep 3265991 = 4898987) B4898987
theorem B3266041 : Blo 1289963 3266041 := bstep (se 2 (by rfl) ⟨1224765, by rfl⟩ : syracuseStep 3266041 = 2449531) B2449531
theorem B1291771 : Blo 1289963 1291771 := bstep (se 1 (by rfl) ⟨968828, by rfl⟩ : syracuseStep 1291771 = 1937657) B1937657
theorem B1291839 : Blo 1289963 1291839 := bstep (se 1 (by rfl) ⟨968879, by rfl⟩ : syracuseStep 1291839 = 1937759) B1937759
theorem B1291847 : Blo 1289963 1291847 := bstep (se 1 (by rfl) ⟨968885, by rfl⟩ : syracuseStep 1291847 = 1937771) B1937771
theorem B1963615 : Blo 1289963 1963615 := bstep (se 1 (by rfl) ⟨1472711, by rfl⟩ : syracuseStep 1963615 = 2945423) B2945423
theorem B3266345 : Blo 1289963 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B2758457 : Blo 1289963 2758457 := bstep (se 2 (by rfl) ⟨1034421, by rfl⟩ : syracuseStep 2758457 = 2068843) B2068843
theorem B2906063 : Blo 1289963 2906063 := bstep (se 1 (by rfl) ⟨2179547, by rfl⟩ : syracuseStep 2906063 = 4359095) B4359095
theorem B11327521 : Blo 1289963 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B3266689 : Blo 1289963 3266689 := bstep (se 2 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 3266689 = 2450017) B2450017
theorem B15702295 : Blo 1289963 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B7076119 : Blo 1289963 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B2906441 : Blo 1289963 2906441 := bstep (se 2 (by rfl) ⟨1089915, by rfl⟩ : syracuseStep 2906441 = 2179831) B2179831
theorem B2906459 : Blo 1289963 2906459 := bstep (se 1 (by rfl) ⟨2179844, by rfl⟩ : syracuseStep 2906459 = 4359689) B4359689
theorem B5511635 : Blo 1289963 5511635 := bstep (se 1 (by rfl) ⟨4133726, by rfl⟩ : syracuseStep 5511635 = 8267453) B8267453
theorem B2759123 : Blo 1289963 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B5511719 : Blo 1289963 5511719 := bstep (se 1 (by rfl) ⟨4133789, by rfl⟩ : syracuseStep 5511719 = 8267579) B8267579
theorem B2325113 : Blo 1289963 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B2177759 : Blo 1289963 2177759 := bstep (se 1 (by rfl) ⟨1633319, by rfl⟩ : syracuseStep 2177759 = 3266639) B3266639
theorem B9804563 : Blo 1289963 9804563 := bstep (se 1 (by rfl) ⟨7353422, by rfl⟩ : syracuseStep 9804563 = 14706845) B14706845
theorem B4356989 : Blo 1289963 4356989 := bstep (se 3 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 4356989 = 1633871) B1633871
theorem B3267499 : Blo 1289963 3267499 := bstep (se 1 (by rfl) ⟨2450624, by rfl⟩ : syracuseStep 3267499 = 4901249) B4901249
theorem B7453613 : Blo 1289963 7453613 := bstep (se 3 (by rfl) ⟨1397552, by rfl⟩ : syracuseStep 7453613 = 2795105) B2795105
theorem B24828875 : Blo 1289963 24828875 := bstep (se 1 (by rfl) ⟨18621656, by rfl⟩ : syracuseStep 24828875 = 37243313) B37243313
theorem B3103841 : Blo 1289963 3103841 := bstep (se 2 (by rfl) ⟨1163940, by rfl⟩ : syracuseStep 3103841 = 2327881) B2327881
theorem B4357259 : Blo 1289963 4357259 := bstep (se 1 (by rfl) ⟨3267944, by rfl⟩ : syracuseStep 4357259 = 6535889) B6535889
theorem B2325647 : Blo 1289963 2325647 := bstep (se 1 (by rfl) ⟨1744235, by rfl⟩ : syracuseStep 2325647 = 3488471) B3488471
theorem B2178191 : Blo 1289963 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B3267803 : Blo 1289963 3267803 := bstep (se 1 (by rfl) ⟨2450852, by rfl⟩ : syracuseStep 3267803 = 4901705) B4901705
theorem B1768735 : Blo 1289963 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B3267935 : Blo 1289963 3267935 := bstep (se 1 (by rfl) ⟨2450951, by rfl⟩ : syracuseStep 3267935 = 4901903) B4901903
theorem B2178427 : Blo 1289963 2178427 := bstep (se 1 (by rfl) ⟨1633820, by rfl⟩ : syracuseStep 2178427 = 3267641) B3267641
theorem B4136609 : Blo 1289963 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B5513017 : Blo 1289963 5513017 := bstep (se 2 (by rfl) ⟨2067381, by rfl⟩ : syracuseStep 5513017 = 4134763) B4134763
theorem B5586749 : Blo 1289963 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B4358177 : Blo 1289963 4358177 := bstep (se 2 (by rfl) ⟨1634316, by rfl⟩ : syracuseStep 4358177 = 3268633) B3268633
theorem B2179291 : Blo 1289963 2179291 := bstep (se 1 (by rfl) ⟨1634468, by rfl⟩ : syracuseStep 2179291 = 3268937) B3268937
theorem B8831339 : Blo 1289963 8831339 := bstep (se 1 (by rfl) ⟨6623504, by rfl⟩ : syracuseStep 8831339 = 13247009) B13247009
theorem B6537671 : Blo 1289963 6537671 := bstep (se 1 (by rfl) ⟨4903253, by rfl⟩ : syracuseStep 6537671 = 9806507) B9806507
theorem B3678671 : Blo 1289963 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B2179561 : Blo 1289963 2179561 := bstep (se 2 (by rfl) ⟨817335, by rfl⟩ : syracuseStep 2179561 = 1634671) B1634671
theorem B12575371 : Blo 1289963 12575371 := bstep (se 1 (by rfl) ⟨9431528, by rfl⟩ : syracuseStep 12575371 = 18863057) B18863057
theorem B2327305 : Blo 1289963 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B3269423 : Blo 1289963 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B8389423 : Blo 1289963 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B5514095 : Blo 1289963 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B13239287 : Blo 1289963 13239287 := bstep (se 1 (by rfl) ⟨9929465, by rfl⟩ : syracuseStep 13239287 = 19858931) B19858931
theorem B7349413 : Blo 1289963 7349413 := bstep (se 4 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 7349413 = 1378015) B1378015
theorem B7357661 : Blo 1289963 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B11322919 : Blo 1289963 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B1934969 : Blo 1289963 1934969 := bstep (se 2 (by rfl) ⟨725613, by rfl⟩ : syracuseStep 1934969 = 1451227) B1451227
theorem B1935071 : Blo 1289963 1935071 := bstep (se 1 (by rfl) ⟨1451303, by rfl⟩ : syracuseStep 1935071 = 2902607) B2902607
theorem B1550075 : Blo 1289963 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B226223873 : Blo 1289963 226223873 := bstep (se 2 (by rfl) ⟨84833952, by rfl⟩ : syracuseStep 226223873 = 169667905) B169667905
theorem B1935167 : Blo 1289963 1935167 := bstep (se 1 (by rfl) ⟨1451375, by rfl⟩ : syracuseStep 1935167 = 2902751) B2902751
theorem B1451839 : Blo 1289963 1451839 := bstep (se 1 (by rfl) ⟨1088879, by rfl⟩ : syracuseStep 1451839 = 2177759) B2177759
theorem B22071203 : Blo 1289963 22071203 := bstep (se 1 (by rfl) ⟨16553402, by rfl⟩ : syracuseStep 22071203 = 33106805) B33106805
theorem B1935335 : Blo 1289963 1935335 := bstep (se 1 (by rfl) ⟨1451501, by rfl⟩ : syracuseStep 1935335 = 2903003) B2903003
theorem B1935353 : Blo 1289963 1935353 := bstep (se 2 (by rfl) ⟨725757, by rfl⟩ : syracuseStep 1935353 = 1451515) B1451515
theorem B8390665 : Blo 1289963 8390665 := bstep (se 2 (by rfl) ⟨3146499, by rfl⟩ : syracuseStep 8390665 = 6292999) B6292999
theorem B150964235 : Blo 1289963 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1935455 : Blo 1289963 1935455 := bstep (se 1 (by rfl) ⟨1451591, by rfl⟩ : syracuseStep 1935455 = 2903183) B2903183
theorem B1550431 : Blo 1289963 1550431 := bstep (se 1 (by rfl) ⟨1162823, by rfl⟩ : syracuseStep 1550431 = 2325647) B2325647
theorem B1452127 : Blo 1289963 1452127 := bstep (se 1 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 1452127 = 2178191) B2178191
theorem B8276087 : Blo 1289963 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B2066575 : Blo 1289963 2066575 := bstep (se 1 (by rfl) ⟨1549931, by rfl⟩ : syracuseStep 2066575 = 3099863) B3099863
theorem B1935515 : Blo 1289963 1935515 := bstep (se 1 (by rfl) ⟨1451636, by rfl⟩ : syracuseStep 1935515 = 2903273) B2903273
theorem B1935551 : Blo 1289963 1935551 := bstep (se 1 (by rfl) ⟨1451663, by rfl⟩ : syracuseStep 1935551 = 2903327) B2903327
theorem B9308351 : Blo 1289963 9308351 := bstep (se 1 (by rfl) ⟨6981263, by rfl⟩ : syracuseStep 9308351 = 13962527) B13962527
theorem B1935593 : Blo 1289963 1935593 := bstep (se 2 (by rfl) ⟨725847, by rfl⟩ : syracuseStep 1935593 = 1451695) B1451695
theorem B7350689 : Blo 1289963 7350689 := bstep (se 2 (by rfl) ⟨2756508, by rfl⟩ : syracuseStep 7350689 = 5513017) B5513017
theorem B2902535 : Blo 1289963 2902535 := bstep (se 1 (by rfl) ⟨2176901, by rfl⟩ : syracuseStep 2902535 = 4353803) B4353803
theorem B1935899 : Blo 1289963 1935899 := bstep (se 1 (by rfl) ⟨1451924, by rfl⟩ : syracuseStep 1935899 = 2903849) B2903849
theorem B2067049 : Blo 1289963 2067049 := bstep (se 2 (by rfl) ⟨775143, by rfl⟩ : syracuseStep 2067049 = 1550287) B1550287
theorem B1935977 : Blo 1289963 1935977 := bstep (se 2 (by rfl) ⟨725991, by rfl⟩ : syracuseStep 1935977 = 1451983) B1451983
theorem B2902715 : Blo 1289963 2902715 := bstep (se 1 (by rfl) ⟨2177036, by rfl⟩ : syracuseStep 2902715 = 4354073) B4354073
theorem B17673079 : Blo 1289963 17673079 := bstep (se 1 (by rfl) ⟨13254809, by rfl⟩ : syracuseStep 17673079 = 26509619) B26509619
theorem B6540263 : Blo 1289963 6540263 := bstep (se 1 (by rfl) ⟨4905197, by rfl⟩ : syracuseStep 6540263 = 9810395) B9810395
theorem B1936505 : Blo 1289963 1936505 := bstep (se 2 (by rfl) ⟨726189, by rfl⟩ : syracuseStep 1936505 = 1452379) B1452379
theorem B1936607 : Blo 1289963 1936607 := bstep (se 1 (by rfl) ⟨1452455, by rfl⟩ : syracuseStep 1936607 = 2904911) B2904911
theorem B1453279 : Blo 1289963 1453279 := bstep (se 1 (by rfl) ⟨1089959, by rfl⟩ : syracuseStep 1453279 = 2179919) B2179919
theorem B1936649 : Blo 1289963 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B7449965 : Blo 1289963 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B1936751 : Blo 1289963 1936751 := bstep (se 1 (by rfl) ⟨1452563, by rfl⟩ : syracuseStep 1936751 = 2905127) B2905127
theorem B1936871 : Blo 1289963 1936871 := bstep (se 1 (by rfl) ⟨1452653, by rfl⟩ : syracuseStep 1936871 = 2905307) B2905307
theorem B2903543 : Blo 1289963 2903543 := bstep (se 1 (by rfl) ⟨2177657, by rfl⟩ : syracuseStep 2903543 = 4355315) B4355315
theorem B2616823 : Blo 1289963 2616823 := bstep (se 1 (by rfl) ⟨1962617, by rfl⟩ : syracuseStep 2616823 = 3925235) B3925235
theorem B16772599 : Blo 1289963 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B2903615 : Blo 1289963 2903615 := bstep (se 1 (by rfl) ⟨2177711, by rfl⟩ : syracuseStep 2903615 = 4355423) B4355423
theorem B9940553 : Blo 1289963 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B1937003 : Blo 1289963 1937003 := bstep (se 1 (by rfl) ⟨1452752, by rfl⟩ : syracuseStep 1937003 = 2905505) B2905505
theorem B1937129 : Blo 1289963 1937129 := bstep (se 2 (by rfl) ⟨726423, by rfl⟩ : syracuseStep 1937129 = 1452847) B1452847
theorem B1290055 : Blo 1289963 1290055 := bstep (se 1 (by rfl) ⟨967541, by rfl⟩ : syracuseStep 1290055 = 1935083) B1935083
theorem B1937273 : Blo 1289963 1937273 := bstep (se 2 (by rfl) ⟨726477, by rfl⟩ : syracuseStep 1937273 = 1452955) B1452955
theorem B1838971 : Blo 1289963 1838971 := bstep (se 1 (by rfl) ⟨1379228, by rfl⟩ : syracuseStep 1838971 = 2758457) B2758457
theorem B1290207 : Blo 1289963 1290207 := bstep (se 1 (by rfl) ⟨967655, by rfl⟩ : syracuseStep 1290207 = 1935311) B1935311
theorem B1937375 : Blo 1289963 1937375 := bstep (se 1 (by rfl) ⟨1453031, by rfl⟩ : syracuseStep 1937375 = 2906063) B2906063
theorem B7352329 : Blo 1289963 7352329 := bstep (se 2 (by rfl) ⟨2757123, by rfl⟩ : syracuseStep 7352329 = 5514247) B5514247
theorem B9433253 : Blo 1289963 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B31396025 : Blo 1289963 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B4354235 : Blo 1289963 4354235 := bstep (se 1 (by rfl) ⟨3265676, by rfl⟩ : syracuseStep 4354235 = 6531353) B6531353
theorem B1937627 : Blo 1289963 1937627 := bstep (se 1 (by rfl) ⟨1453220, by rfl⟩ : syracuseStep 1937627 = 2906441) B2906441
theorem B1290471 : Blo 1289963 1290471 := bstep (se 1 (by rfl) ⟨967853, by rfl⟩ : syracuseStep 1290471 = 1935707) B1935707
theorem B1937639 : Blo 1289963 1937639 := bstep (se 1 (by rfl) ⟨1453229, by rfl⟩ : syracuseStep 1937639 = 2906459) B2906459
theorem B3674423 : Blo 1289963 3674423 := bstep (se 1 (by rfl) ⟨2755817, by rfl⟩ : syracuseStep 3674423 = 5511635) B5511635
theorem B3674479 : Blo 1289963 3674479 := bstep (se 1 (by rfl) ⟨2755859, by rfl⟩ : syracuseStep 3674479 = 5511719) B5511719
theorem B1290623 : Blo 1289963 1290623 := bstep (se 1 (by rfl) ⟨967967, by rfl⟩ : syracuseStep 1290623 = 1935935) B1935935
theorem B1937801 : Blo 1289963 1937801 := bstep (se 2 (by rfl) ⟨726675, by rfl⟩ : syracuseStep 1937801 = 1453351) B1453351
theorem B1290703 : Blo 1289963 1290703 := bstep (se 1 (by rfl) ⟨968027, by rfl⟩ : syracuseStep 1290703 = 1936055) B1936055
theorem B1937897 : Blo 1289963 1937897 := bstep (se 2 (by rfl) ⟨726711, by rfl⟩ : syracuseStep 1937897 = 1453423) B1453423
theorem B2904569 : Blo 1289963 2904569 := bstep (se 2 (by rfl) ⟨1089213, by rfl⟩ : syracuseStep 2904569 = 2178427) B2178427
theorem B2904659 : Blo 1289963 2904659 := bstep (se 1 (by rfl) ⟨2178494, by rfl⟩ : syracuseStep 2904659 = 4356989) B4356989
theorem B1290855 : Blo 1289963 1290855 := bstep (se 1 (by rfl) ⟨968141, by rfl⟩ : syracuseStep 1290855 = 1936283) B1936283
theorem B4969075 : Blo 1289963 4969075 := bstep (se 1 (by rfl) ⟨3726806, by rfl⟩ : syracuseStep 4969075 = 7453613) B7453613
theorem B16552583 : Blo 1289963 16552583 := bstep (se 1 (by rfl) ⟨12414437, by rfl⟩ : syracuseStep 16552583 = 24828875) B24828875
theorem B4354721 : Blo 1289963 4354721 := bstep (se 2 (by rfl) ⟨1633020, by rfl⟩ : syracuseStep 4354721 = 3266041) B3266041
theorem B2069227 : Blo 1289963 2069227 := bstep (se 1 (by rfl) ⟨1551920, by rfl⟩ : syracuseStep 2069227 = 3103841) B3103841
theorem B2904839 : Blo 1289963 2904839 := bstep (se 1 (by rfl) ⟨2178629, by rfl⟩ : syracuseStep 2904839 = 4357259) B4357259
theorem B2618153 : Blo 1289963 2618153 := bstep (se 2 (by rfl) ⟨981807, by rfl⟩ : syracuseStep 2618153 = 1963615) B1963615
theorem B1291119 : Blo 1289963 1291119 := bstep (se 1 (by rfl) ⟨968339, by rfl⟩ : syracuseStep 1291119 = 1936679) B1936679
theorem B1291175 : Blo 1289963 1291175 := bstep (se 1 (by rfl) ⟨968381, by rfl⟩ : syracuseStep 1291175 = 1936763) B1936763
theorem B1291259 : Blo 1289963 1291259 := bstep (se 1 (by rfl) ⟨968444, by rfl⟩ : syracuseStep 1291259 = 1936889) B1936889
theorem B1291327 : Blo 1289963 1291327 := bstep (se 1 (by rfl) ⟨968495, by rfl⟩ : syracuseStep 1291327 = 1936991) B1936991
theorem B2757739 : Blo 1289963 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B1291471 : Blo 1289963 1291471 := bstep (se 1 (by rfl) ⟨968603, by rfl⟩ : syracuseStep 1291471 = 1937207) B1937207
theorem B3724499 : Blo 1289963 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B33535219 : Blo 1289963 33535219 := bstep (se 1 (by rfl) ⟨25151414, by rfl⟩ : syracuseStep 33535219 = 50302829) B50302829
theorem B15103361 : Blo 1289963 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B1291675 : Blo 1289963 1291675 := bstep (se 1 (by rfl) ⟨968756, by rfl⟩ : syracuseStep 1291675 = 1937513) B1937513
theorem B4355585 : Blo 1289963 4355585 := bstep (se 2 (by rfl) ⟨1633344, by rfl⟩ : syracuseStep 4355585 = 3266689) B3266689
theorem B1291887 : Blo 1289963 1291887 := bstep (se 1 (by rfl) ⟨968915, by rfl⟩ : syracuseStep 1291887 = 1937831) B1937831
theorem B13424251 : Blo 1289963 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B1291943 : Blo 1289963 1291943 := bstep (se 1 (by rfl) ⟨968957, by rfl⟩ : syracuseStep 1291943 = 1937915) B1937915
theorem B20936393 : Blo 1289963 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B9434825 : Blo 1289963 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B8271679 : Blo 1289963 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B2905919 : Blo 1289963 2905919 := bstep (se 1 (by rfl) ⟨2179439, by rfl⟩ : syracuseStep 2905919 = 4358879) B4358879
theorem B14702471 : Blo 1289963 14702471 := bstep (se 1 (by rfl) ⟨11026853, by rfl⟩ : syracuseStep 14702471 = 22053707) B22053707
theorem B4356071 : Blo 1289963 4356071 := bstep (se 1 (by rfl) ⟨3267053, by rfl⟩ : syracuseStep 4356071 = 6534107) B6534107
theorem B4356179 : Blo 1289963 4356179 := bstep (se 1 (by rfl) ⟨3267134, by rfl⟩ : syracuseStep 4356179 = 6534269) B6534269
theorem B4134995 : Blo 1289963 4134995 := bstep (se 1 (by rfl) ⟨3101246, by rfl⟩ : syracuseStep 4134995 = 6202493) B6202493
theorem B3102803 : Blo 1289963 3102803 := bstep (se 1 (by rfl) ⟨2327102, by rfl⟩ : syracuseStep 3102803 = 4654205) B4654205
theorem B2906207 : Blo 1289963 2906207 := bstep (se 1 (by rfl) ⟨2179655, by rfl⟩ : syracuseStep 2906207 = 4359311) B4359311
theorem B2758799 : Blo 1289963 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B4356395 : Blo 1289963 4356395 := bstep (se 1 (by rfl) ⟨3267296, by rfl⟩ : syracuseStep 4356395 = 6534593) B6534593
theorem B2177327 : Blo 1289963 2177327 := bstep (se 1 (by rfl) ⟨1632995, by rfl⟩ : syracuseStep 2177327 = 3265991) B3265991
theorem B4413971 : Blo 1289963 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B2177563 : Blo 1289963 2177563 := bstep (se 1 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 2177563 = 3266345) B3266345
theorem B4356665 : Blo 1289963 4356665 := bstep (se 2 (by rfl) ⟨1633749, by rfl⟩ : syracuseStep 4356665 = 3267499) B3267499
theorem B12409517 : Blo 1289963 12409517 := bstep (se 3 (by rfl) ⟨2326784, by rfl⟩ : syracuseStep 12409517 = 4653569) B4653569
theorem B24796205 : Blo 1289963 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B11033657 : Blo 1289963 11033657 := bstep (se 2 (by rfl) ⟨4137621, by rfl⟩ : syracuseStep 11033657 = 8275243) B8275243
theorem B6536375 : Blo 1289963 6536375 := bstep (se 1 (by rfl) ⟨4902281, by rfl⟩ : syracuseStep 6536375 = 9804563) B9804563
theorem B2178535 : Blo 1289963 2178535 := bstep (se 1 (by rfl) ⟨1633901, by rfl⟩ : syracuseStep 2178535 = 3267803) B3267803
theorem B12410405 : Blo 1289963 12410405 := bstep (se 4 (by rfl) ⟨1163475, by rfl⟩ : syracuseStep 12410405 = 2326951) B2326951
theorem B2178623 : Blo 1289963 2178623 := bstep (se 1 (by rfl) ⟨1633967, by rfl⟩ : syracuseStep 2178623 = 3267935) B3267935
theorem B10468973 : Blo 1289963 10468973 := bstep (se 3 (by rfl) ⟨1962932, by rfl⟩ : syracuseStep 10468973 = 3925865) B3925865
theorem B2449129 : Blo 1289963 2449129 := bstep (se 2 (by rfl) ⟨918423, by rfl⟩ : syracuseStep 2449129 = 1836847) B1836847
theorem B7347955 : Blo 1289963 7347955 := bstep (se 1 (by rfl) ⟨5510966, by rfl⟩ : syracuseStep 7347955 = 11021933) B11021933
theorem B47128483 : Blo 1289963 47128483 := bstep (se 1 (by rfl) ⟨35346362, by rfl⟩ : syracuseStep 47128483 = 70692725) B70692725
theorem B20930683 : Blo 1289963 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B2449615 : Blo 1289963 2449615 := bstep (se 1 (by rfl) ⟨1837211, by rfl⟩ : syracuseStep 2449615 = 3674423) B3674423
theorem B4358447 : Blo 1289963 4358447 := bstep (se 1 (by rfl) ⟨3268835, by rfl⟩ : syracuseStep 4358447 = 6537671) B6537671
theorem B11035055 : Blo 1289963 11035055 := bstep (se 1 (by rfl) ⟨8276291, by rfl⟩ : syracuseStep 11035055 = 16552583) B16552583
theorem B4899305 : Blo 1289963 4899305 := bstep (se 2 (by rfl) ⟨1837239, by rfl⟩ : syracuseStep 4899305 = 3674479) B3674479
theorem B1745435 : Blo 1289963 1745435 := bstep (se 1 (by rfl) ⟨1309076, by rfl⟩ : syracuseStep 1745435 = 2618153) B2618153
theorem B2179615 : Blo 1289963 2179615 := bstep (se 1 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 2179615 = 3269423) B3269423
theorem B10068907 : Blo 1289963 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B150815915 : Blo 1289963 150815915 := bstep (se 1 (by rfl) ⟨113111936, by rfl⟩ : syracuseStep 150815915 = 226223873) B226223873
theorem B14714135 : Blo 1289963 14714135 := bstep (se 1 (by rfl) ⟨11035601, by rfl⟩ : syracuseStep 14714135 = 22071203) B22071203
theorem B1451551 : Blo 1289963 1451551 := bstep (se 1 (by rfl) ⟨1088663, by rfl⟩ : syracuseStep 1451551 = 2177327) B2177327
theorem B9799217 : Blo 1289963 9799217 := bstep (se 2 (by rfl) ⟨3674706, by rfl⟩ : syracuseStep 9799217 = 7349413) B7349413
theorem B4900459 : Blo 1289963 4900459 := bstep (se 1 (by rfl) ⟨3675344, by rfl⟩ : syracuseStep 4900459 = 7350689) B7350689
theorem B44713625 : Blo 1289963 44713625 := bstep (se 2 (by rfl) ⟨16767609, by rfl⟩ : syracuseStep 44713625 = 33535219) B33535219
theorem B1935023 : Blo 1289963 1935023 := bstep (se 1 (by rfl) ⟨1451267, by rfl⟩ : syracuseStep 1935023 = 2902535) B2902535
theorem B2942647 : Blo 1289963 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B1935143 : Blo 1289963 1935143 := bstep (se 1 (by rfl) ⟨1451357, by rfl⟩ : syracuseStep 1935143 = 2902715) B2902715
theorem B4360175 : Blo 1289963 4360175 := bstep (se 1 (by rfl) ⟨3270131, by rfl⟩ : syracuseStep 4360175 = 6540263) B6540263
theorem B4966643 : Blo 1289963 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B1935695 : Blo 1289963 1935695 := bstep (se 1 (by rfl) ⟨1451771, by rfl⟩ : syracuseStep 1935695 = 2903543) B2903543
theorem B1935743 : Blo 1289963 1935743 := bstep (se 1 (by rfl) ⟨1451807, by rfl⟩ : syracuseStep 1935743 = 2903615) B2903615
theorem B1452415 : Blo 1289963 1452415 := bstep (se 1 (by rfl) ⟨1089311, by rfl⟩ : syracuseStep 1452415 = 2178623) B2178623
theorem B1935785 : Blo 1289963 1935785 := bstep (se 2 (by rfl) ⟨725919, by rfl⟩ : syracuseStep 1935785 = 1451839) B1451839
theorem B11028905 : Blo 1289963 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B2451961 : Blo 1289963 2451961 := bstep (se 2 (by rfl) ⟨919485, by rfl⟩ : syracuseStep 2451961 = 1838971) B1838971
theorem B2902823 : Blo 1289963 2902823 := bstep (se 1 (by rfl) ⟨2177117, by rfl⟩ : syracuseStep 2902823 = 4354235) B4354235
theorem B1936169 : Blo 1289963 1936169 := bstep (se 2 (by rfl) ⟨726063, by rfl⟩ : syracuseStep 1936169 = 1452127) B1452127
theorem B2755433 : Blo 1289963 2755433 := bstep (se 2 (by rfl) ⟨1033287, by rfl⟩ : syracuseStep 2755433 = 2066575) B2066575
theorem B2452447 : Blo 1289963 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B1936379 : Blo 1289963 1936379 := bstep (se 1 (by rfl) ⟨1452284, by rfl⟩ : syracuseStep 1936379 = 2904569) B2904569
theorem B1936439 : Blo 1289963 1936439 := bstep (se 1 (by rfl) ⟨1452329, by rfl⟩ : syracuseStep 1936439 = 2904659) B2904659
theorem B2903147 : Blo 1289963 2903147 := bstep (se 1 (by rfl) ⟨2177360, by rfl⟩ : syracuseStep 2903147 = 4354721) B4354721
theorem B8268965 : Blo 1289963 8268965 := bstep (se 4 (by rfl) ⟨775215, by rfl⟩ : syracuseStep 8268965 = 1550431) B1550431
theorem B1936559 : Blo 1289963 1936559 := bstep (se 1 (by rfl) ⟨1452419, by rfl⟩ : syracuseStep 1936559 = 2904839) B2904839
theorem B9931997 : Blo 1289963 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B8826191 : Blo 1289963 8826191 := bstep (se 1 (by rfl) ⟨6619643, by rfl⟩ : syracuseStep 8826191 = 13239287) B13239287
theorem B2903417 : Blo 1289963 2903417 := bstep (se 2 (by rfl) ⟨1088781, by rfl⟩ : syracuseStep 2903417 = 2177563) B2177563
theorem B2756065 : Blo 1289963 2756065 := bstep (se 2 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 2756065 = 2067049) B2067049
theorem B2903723 : Blo 1289963 2903723 := bstep (se 1 (by rfl) ⟨2177792, by rfl⟩ : syracuseStep 2903723 = 4355585) B4355585
theorem B11185897 : Blo 1289963 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B1289979 : Blo 1289963 1289979 := bstep (se 1 (by rfl) ⟨967484, by rfl⟩ : syracuseStep 1289979 = 1934969) B1934969
theorem B1290047 : Blo 1289963 1290047 := bstep (se 1 (by rfl) ⟨967535, by rfl⟩ : syracuseStep 1290047 = 1935071) B1935071
theorem B23564105 : Blo 1289963 23564105 := bstep (se 2 (by rfl) ⟨8836539, by rfl⟩ : syracuseStep 23564105 = 17673079) B17673079
theorem B1290111 : Blo 1289963 1290111 := bstep (se 1 (by rfl) ⟨967583, by rfl⟩ : syracuseStep 1290111 = 1935167) B1935167
theorem B1937279 : Blo 1289963 1937279 := bstep (se 1 (by rfl) ⟨1452959, by rfl⟩ : syracuseStep 1937279 = 2905919) B2905919
theorem B9801647 : Blo 1289963 9801647 := bstep (se 1 (by rfl) ⟨7351235, by rfl⟩ : syracuseStep 9801647 = 14702471) B14702471
theorem B1290223 : Blo 1289963 1290223 := bstep (se 1 (by rfl) ⟨967667, by rfl⟩ : syracuseStep 1290223 = 1935335) B1935335
theorem B2904047 : Blo 1289963 2904047 := bstep (se 1 (by rfl) ⟨2178035, by rfl⟩ : syracuseStep 2904047 = 4356071) B4356071
theorem B1290235 : Blo 1289963 1290235 := bstep (se 1 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 1290235 = 1935353) B1935353
theorem B100642823 : Blo 1289963 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B2904119 : Blo 1289963 2904119 := bstep (se 1 (by rfl) ⟨2178089, by rfl⟩ : syracuseStep 2904119 = 4356179) B4356179
theorem B2756663 : Blo 1289963 2756663 := bstep (se 1 (by rfl) ⟨2067497, by rfl⟩ : syracuseStep 2756663 = 4134995) B4134995
theorem B2068535 : Blo 1289963 2068535 := bstep (se 1 (by rfl) ⟨1551401, by rfl⟩ : syracuseStep 2068535 = 3102803) B3102803
theorem B1290303 : Blo 1289963 1290303 := bstep (se 1 (by rfl) ⟨967727, by rfl⟩ : syracuseStep 1290303 = 1935455) B1935455
theorem B1937471 : Blo 1289963 1937471 := bstep (se 1 (by rfl) ⟨1453103, by rfl⟩ : syracuseStep 1937471 = 2906207) B2906207
theorem B5517391 : Blo 1289963 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B1839199 : Blo 1289963 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B1290343 : Blo 1289963 1290343 := bstep (se 1 (by rfl) ⟨967757, by rfl⟩ : syracuseStep 1290343 = 1935515) B1935515
theorem B1290367 : Blo 1289963 1290367 := bstep (se 1 (by rfl) ⟨967775, by rfl⟩ : syracuseStep 1290367 = 1935551) B1935551
theorem B6205567 : Blo 1289963 6205567 := bstep (se 1 (by rfl) ⟨4654175, by rfl⟩ : syracuseStep 6205567 = 9308351) B9308351
theorem B1290395 : Blo 1289963 1290395 := bstep (se 1 (by rfl) ⟨967796, by rfl⟩ : syracuseStep 1290395 = 1935593) B1935593
theorem B2904263 : Blo 1289963 2904263 := bstep (se 1 (by rfl) ⟨2178197, by rfl⟩ : syracuseStep 2904263 = 4356395) B4356395
theorem B1937705 : Blo 1289963 1937705 := bstep (se 2 (by rfl) ⟨726639, by rfl⟩ : syracuseStep 1937705 = 1453279) B1453279
theorem B1290599 : Blo 1289963 1290599 := bstep (se 1 (by rfl) ⟨967949, by rfl⟩ : syracuseStep 1290599 = 1935899) B1935899
theorem B2904443 : Blo 1289963 2904443 := bstep (se 1 (by rfl) ⟨2178332, by rfl⟩ : syracuseStep 2904443 = 4356665) B4356665
theorem B1290651 : Blo 1289963 1290651 := bstep (se 1 (by rfl) ⟨967988, by rfl⟩ : syracuseStep 1290651 = 1935977) B1935977
theorem B2904713 : Blo 1289963 2904713 := bstep (se 2 (by rfl) ⟨1089267, by rfl⟩ : syracuseStep 2904713 = 2178535) B2178535
theorem B4133533 : Blo 1289963 4133533 := bstep (se 3 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 4133533 = 1550075) B1550075
theorem B1291003 : Blo 1289963 1291003 := bstep (se 1 (by rfl) ⟨968252, by rfl⟩ : syracuseStep 1291003 = 1936505) B1936505
theorem B1291071 : Blo 1289963 1291071 := bstep (se 1 (by rfl) ⟨968303, by rfl⟩ : syracuseStep 1291071 = 1936607) B1936607
theorem B1291099 : Blo 1289963 1291099 := bstep (se 1 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 1291099 = 1936649) B1936649
theorem B1291167 : Blo 1289963 1291167 := bstep (se 1 (by rfl) ⟨968375, by rfl⟩ : syracuseStep 1291167 = 1936751) B1936751
theorem B3265505 : Blo 1289963 3265505 := bstep (se 2 (by rfl) ⟨1224564, by rfl⟩ : syracuseStep 3265505 = 2449129) B2449129
theorem B1291247 : Blo 1289963 1291247 := bstep (se 1 (by rfl) ⟨968435, by rfl⟩ : syracuseStep 1291247 = 1936871) B1936871
theorem B1291335 : Blo 1289963 1291335 := bstep (se 1 (by rfl) ⟨968501, by rfl⟩ : syracuseStep 1291335 = 1937003) B1937003
theorem B1291419 : Blo 1289963 1291419 := bstep (se 1 (by rfl) ⟨968564, by rfl⟩ : syracuseStep 1291419 = 1937129) B1937129
theorem B62837977 : Blo 1289963 62837977 := bstep (se 2 (by rfl) ⟨23564241, by rfl⟩ : syracuseStep 62837977 = 47128483) B47128483
theorem B1291515 : Blo 1289963 1291515 := bstep (se 1 (by rfl) ⟨968636, by rfl⟩ : syracuseStep 1291515 = 1937273) B1937273
theorem B1291583 : Blo 1289963 1291583 := bstep (se 1 (by rfl) ⟨968687, by rfl⟩ : syracuseStep 1291583 = 1937375) B1937375
theorem B9803105 : Blo 1289963 9803105 := bstep (se 2 (by rfl) ⟨3676164, by rfl⟩ : syracuseStep 9803105 = 7352329) B7352329
theorem B11187553 : Blo 1289963 11187553 := bstep (se 2 (by rfl) ⟨4195332, by rfl⟩ : syracuseStep 11187553 = 8390665) B8390665
theorem B2905451 : Blo 1289963 2905451 := bstep (se 1 (by rfl) ⟨2179088, by rfl⟩ : syracuseStep 2905451 = 4358177) B4358177
theorem B6288835 : Blo 1289963 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B1291751 : Blo 1289963 1291751 := bstep (se 1 (by rfl) ⟨968813, by rfl⟩ : syracuseStep 1291751 = 1937627) B1937627
theorem B1291759 : Blo 1289963 1291759 := bstep (se 1 (by rfl) ⟨968819, by rfl⟩ : syracuseStep 1291759 = 1937639) B1937639
theorem B5887559 : Blo 1289963 5887559 := bstep (se 1 (by rfl) ⟨4415669, by rfl⟩ : syracuseStep 5887559 = 8831339) B8831339
theorem B1291867 : Blo 1289963 1291867 := bstep (se 1 (by rfl) ⟨968900, by rfl⟩ : syracuseStep 1291867 = 1937801) B1937801
theorem B2905721 : Blo 1289963 2905721 := bstep (se 2 (by rfl) ⟨1089645, by rfl⟩ : syracuseStep 2905721 = 2179291) B2179291
theorem B1291931 : Blo 1289963 1291931 := bstep (se 1 (by rfl) ⟨968948, by rfl⟩ : syracuseStep 1291931 = 1937897) B1937897
theorem B3676063 : Blo 1289963 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B2906081 : Blo 1289963 2906081 := bstep (se 2 (by rfl) ⟨1089780, by rfl⟩ : syracuseStep 2906081 = 2179561) B2179561
theorem B4905107 : Blo 1289963 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B6625433 : Blo 1289963 6625433 := bstep (se 2 (by rfl) ⟨2484537, by rfl⟩ : syracuseStep 6625433 = 4969075) B4969075
theorem B16767161 : Blo 1289963 16767161 := bstep (se 2 (by rfl) ⟨6287685, by rfl⟩ : syracuseStep 16767161 = 12575371) B12575371
theorem B2758969 : Blo 1289963 2758969 := bstep (se 2 (by rfl) ⟨1034613, by rfl⟩ : syracuseStep 2758969 = 2069227) B2069227
theorem B3103073 : Blo 1289963 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B13957595 : Blo 1289963 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B6289883 : Blo 1289963 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B3676985 : Blo 1289963 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B27917261 : Blo 1289963 27917261 := bstep (se 3 (by rfl) ⟨5234486, by rfl⟩ : syracuseStep 27917261 = 10468973) B10468973
theorem B8273011 : Blo 1289963 8273011 := bstep (se 1 (by rfl) ⟨6204758, by rfl⟩ : syracuseStep 8273011 = 12409517) B12409517
theorem B3489097 : Blo 1289963 3489097 := bstep (se 2 (by rfl) ⟨1308411, by rfl⟩ : syracuseStep 3489097 = 2616823) B2616823
theorem B22363465 : Blo 1289963 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B16530803 : Blo 1289963 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B7355771 : Blo 1289963 7355771 := bstep (se 1 (by rfl) ⟨5516828, by rfl⟩ : syracuseStep 7355771 = 11033657) B11033657
theorem B15097225 : Blo 1289963 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B4357583 : Blo 1289963 4357583 := bstep (se 1 (by rfl) ⟨3268187, by rfl⟩ : syracuseStep 4357583 = 6536375) B6536375
theorem B17899001 : Blo 1289963 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B9797273 : Blo 1289963 9797273 := bstep (se 2 (by rfl) ⟨3673977, by rfl⟩ : syracuseStep 9797273 = 7347955) B7347955
theorem B8273603 : Blo 1289963 8273603 := bstep (se 1 (by rfl) ⟨6205202, by rfl⟩ : syracuseStep 8273603 = 12410405) B12410405
theorem B6627035 : Blo 1289963 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B7356521 : Blo 1289963 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B8274089 : Blo 1289963 8274089 := bstep (se 2 (by rfl) ⟨3102783, by rfl⟩ : syracuseStep 8274089 = 6205567) B6205567
theorem B7356703 : Blo 1289963 7356703 := bstep (se 1 (by rfl) ⟨5517527, by rfl⟩ : syracuseStep 7356703 = 11035055) B11035055
theorem B3678625 : Blo 1289963 3678625 := bstep (se 2 (by rfl) ⟨1379484, by rfl⟩ : syracuseStep 3678625 = 2758969) B2758969
theorem B3269281 : Blo 1289963 3269281 := bstep (se 2 (by rfl) ⟨1225980, by rfl⟩ : syracuseStep 3269281 = 2451961) B2451961
theorem B3925039 : Blo 1289963 3925039 := bstep (se 1 (by rfl) ⟨2943779, by rfl⟩ : syracuseStep 3925039 = 5887559) B5887559
theorem B3269929 : Blo 1289963 3269929 := bstep (se 2 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 3269929 = 2452447) B2452447
theorem B4654493 : Blo 1289963 4654493 := bstep (se 3 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 4654493 = 1745435) B1745435
theorem B3270071 : Blo 1289963 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B119236333 : Blo 1289963 119236333 := bstep (se 3 (by rfl) ⟨22356812, by rfl⟩ : syracuseStep 119236333 = 44713625) B44713625
theorem B20129633 : Blo 1289963 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B1935215 : Blo 1289963 1935215 := bstep (se 1 (by rfl) ⟨1451411, by rfl⟩ : syracuseStep 1935215 = 2902823) B2902823
theorem B2451323 : Blo 1289963 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B1836955 : Blo 1289963 1836955 := bstep (se 1 (by rfl) ⟨1377716, by rfl⟩ : syracuseStep 1836955 = 2755433) B2755433
theorem B1935401 : Blo 1289963 1935401 := bstep (se 2 (by rfl) ⟨725775, by rfl⟩ : syracuseStep 1935401 = 1451551) B1451551
theorem B1935431 : Blo 1289963 1935431 := bstep (se 1 (by rfl) ⟨1451573, by rfl⟩ : syracuseStep 1935431 = 2903147) B2903147
theorem B6621331 : Blo 1289963 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B5884127 : Blo 1289963 5884127 := bstep (se 1 (by rfl) ⟨4413095, by rfl⟩ : syracuseStep 5884127 = 8826191) B8826191
theorem B11020535 : Blo 1289963 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B1935611 : Blo 1289963 1935611 := bstep (se 1 (by rfl) ⟨1451708, by rfl⟩ : syracuseStep 1935611 = 2903417) B2903417
theorem B6531515 : Blo 1289963 6531515 := bstep (se 1 (by rfl) ⟨4898636, by rfl⟩ : syracuseStep 6531515 = 9797273) B9797273
theorem B1935815 : Blo 1289963 1935815 := bstep (se 1 (by rfl) ⟨1451861, by rfl⟩ : syracuseStep 1935815 = 2903723) B2903723
theorem B5515735 : Blo 1289963 5515735 := bstep (se 1 (by rfl) ⟨4136801, by rfl⟩ : syracuseStep 5515735 = 8273603) B8273603
theorem B4418023 : Blo 1289963 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B4901417 : Blo 1289963 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B1936031 : Blo 1289963 1936031 := bstep (se 1 (by rfl) ⟨1452023, by rfl⟩ : syracuseStep 1936031 = 2904047) B2904047
theorem B67095215 : Blo 1289963 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B1936079 : Blo 1289963 1936079 := bstep (se 1 (by rfl) ⟨1452059, by rfl⟩ : syracuseStep 1936079 = 2904119) B2904119
theorem B1837775 : Blo 1289963 1837775 := bstep (se 1 (by rfl) ⟨1378331, by rfl⟩ : syracuseStep 1837775 = 2756663) B2756663
theorem B2452265 : Blo 1289963 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B1936175 : Blo 1289963 1936175 := bstep (se 1 (by rfl) ⟨1452131, by rfl⟩ : syracuseStep 1936175 = 2904263) B2904263
theorem B5516093 : Blo 1289963 5516093 := bstep (se 3 (by rfl) ⟨1034267, by rfl⟩ : syracuseStep 5516093 = 2068535) B2068535
theorem B1936295 : Blo 1289963 1936295 := bstep (se 1 (by rfl) ⟨1452221, by rfl⟩ : syracuseStep 1936295 = 2904443) B2904443
theorem B1936475 : Blo 1289963 1936475 := bstep (se 1 (by rfl) ⟨1452356, by rfl⟩ : syracuseStep 1936475 = 2904713) B2904713
theorem B1936553 : Blo 1289963 1936553 := bstep (se 2 (by rfl) ⟨726207, by rfl⟩ : syracuseStep 1936553 = 1452415) B1452415
theorem B100543943 : Blo 1289963 100543943 := bstep (se 1 (by rfl) ⟨75407957, by rfl⟩ : syracuseStep 100543943 = 150815915) B150815915
theorem B9809423 : Blo 1289963 9809423 := bstep (se 1 (by rfl) ⟨7357067, by rfl⟩ : syracuseStep 9809423 = 14714135) B14714135
theorem B1936967 : Blo 1289963 1936967 := bstep (se 1 (by rfl) ⟨1452725, by rfl⟩ : syracuseStep 1936967 = 2905451) B2905451
theorem B6532811 : Blo 1289963 6532811 := bstep (se 1 (by rfl) ⟨4899608, by rfl⟩ : syracuseStep 6532811 = 9799217) B9799217
theorem B1937147 : Blo 1289963 1937147 := bstep (se 1 (by rfl) ⟨1452860, by rfl⟩ : syracuseStep 1937147 = 2905721) B2905721
theorem B1290015 : Blo 1289963 1290015 := bstep (se 1 (by rfl) ⟨967511, by rfl⟩ : syracuseStep 1290015 = 1935023) B1935023
theorem B1290095 : Blo 1289963 1290095 := bstep (se 1 (by rfl) ⟨967571, by rfl⟩ : syracuseStep 1290095 = 1935143) B1935143
theorem B1937387 : Blo 1289963 1937387 := bstep (se 1 (by rfl) ⟨1453040, by rfl⟩ : syracuseStep 1937387 = 2906081) B2906081
theorem B11178107 : Blo 1289963 11178107 := bstep (se 1 (by rfl) ⟨8383580, by rfl⟩ : syracuseStep 11178107 = 16767161) B16767161
theorem B11030681 : Blo 1289963 11030681 := bstep (se 2 (by rfl) ⟨4136505, by rfl⟩ : syracuseStep 11030681 = 8273011) B8273011
theorem B1290463 : Blo 1289963 1290463 := bstep (se 1 (by rfl) ⟨967847, by rfl⟩ : syracuseStep 1290463 = 1935695) B1935695
theorem B2068715 : Blo 1289963 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B1290495 : Blo 1289963 1290495 := bstep (se 1 (by rfl) ⟨967871, by rfl⟩ : syracuseStep 1290495 = 1935743) B1935743
theorem B1290523 : Blo 1289963 1290523 := bstep (se 1 (by rfl) ⟨967892, by rfl⟩ : syracuseStep 1290523 = 1935785) B1935785
theorem B7352603 : Blo 1289963 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B83783969 : Blo 1289963 83783969 := bstep (se 2 (by rfl) ⟨31418988, by rfl⟩ : syracuseStep 83783969 = 62837977) B62837977
theorem B1290779 : Blo 1289963 1290779 := bstep (se 1 (by rfl) ⟨968084, by rfl⟩ : syracuseStep 1290779 = 1936169) B1936169
theorem B8385113 : Blo 1289963 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B3674753 : Blo 1289963 3674753 := bstep (se 2 (by rfl) ⟨1378032, by rfl⟩ : syracuseStep 3674753 = 2756065) B2756065
theorem B1290919 : Blo 1289963 1290919 := bstep (se 1 (by rfl) ⟨968189, by rfl⟩ : syracuseStep 1290919 = 1936379) B1936379
theorem B1290959 : Blo 1289963 1290959 := bstep (se 1 (by rfl) ⟨968219, by rfl⟩ : syracuseStep 1290959 = 1936439) B1936439
theorem B1291039 : Blo 1289963 1291039 := bstep (se 1 (by rfl) ⟨968279, by rfl⟩ : syracuseStep 1291039 = 1936559) B1936559
theorem B6533945 : Blo 1289963 6533945 := bstep (se 2 (by rfl) ⟨2450229, by rfl⟩ : syracuseStep 6533945 = 4900459) B4900459
theorem B4903847 : Blo 1289963 4903847 := bstep (se 1 (by rfl) ⟨3677885, by rfl⟩ : syracuseStep 4903847 = 7355771) B7355771
theorem B2905055 : Blo 1289963 2905055 := bstep (se 1 (by rfl) ⟨2178791, by rfl⟩ : syracuseStep 2905055 = 4357583) B4357583
theorem B14914529 : Blo 1289963 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B11932667 : Blo 1289963 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B15709403 : Blo 1289963 15709403 := bstep (se 1 (by rfl) ⟨11782052, by rfl⟩ : syracuseStep 15709403 = 23564105) B23564105
theorem B1291519 : Blo 1289963 1291519 := bstep (se 1 (by rfl) ⟨968639, by rfl⟩ : syracuseStep 1291519 = 1937279) B1937279
theorem B6534431 : Blo 1289963 6534431 := bstep (se 1 (by rfl) ⟨4900823, by rfl⟩ : syracuseStep 6534431 = 9801647) B9801647
theorem B1291647 : Blo 1289963 1291647 := bstep (se 1 (by rfl) ⟨968735, by rfl⟩ : syracuseStep 1291647 = 1937471) B1937471
theorem B27907577 : Blo 1289963 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B1291803 : Blo 1289963 1291803 := bstep (se 1 (by rfl) ⟨968852, by rfl⟩ : syracuseStep 1291803 = 1937705) B1937705
theorem B2905631 : Blo 1289963 2905631 := bstep (se 1 (by rfl) ⟨2179223, by rfl⟩ : syracuseStep 2905631 = 4358447) B4358447
theorem B3266153 : Blo 1289963 3266153 := bstep (se 2 (by rfl) ⟨1224807, by rfl⟩ : syracuseStep 3266153 = 2449615) B2449615
theorem B3266203 : Blo 1289963 3266203 := bstep (se 1 (by rfl) ⟨2449652, by rfl⟩ : syracuseStep 3266203 = 4899305) B4899305
theorem B17667821 : Blo 1289963 17667821 := bstep (se 3 (by rfl) ⟨3312716, by rfl⟩ : syracuseStep 17667821 = 6625433) B6625433
theorem B13244381 : Blo 1289963 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B2177003 : Blo 1289963 2177003 := bstep (se 1 (by rfl) ⟨1632752, by rfl⟩ : syracuseStep 2177003 = 3265505) B3265505
theorem B2906153 : Blo 1289963 2906153 := bstep (se 2 (by rfl) ⟨1089807, by rfl⟩ : syracuseStep 2906153 = 2179615) B2179615
theorem B5511377 : Blo 1289963 5511377 := bstep (se 2 (by rfl) ⟨2066766, by rfl⟩ : syracuseStep 5511377 = 4133533) B4133533
theorem B6535403 : Blo 1289963 6535403 := bstep (se 1 (by rfl) ⟨4901552, by rfl⟩ : syracuseStep 6535403 = 9803105) B9803105
theorem B15694117 : Blo 1289963 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B13425209 : Blo 1289963 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B2906783 : Blo 1289963 2906783 := bstep (se 1 (by rfl) ⟨2180087, by rfl⟩ : syracuseStep 2906783 = 4360175) B4360175
theorem B9305063 : Blo 1289963 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B4193255 : Blo 1289963 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B4652129 : Blo 1289963 4652129 := bstep (se 2 (by rfl) ⟨1744548, by rfl⟩ : syracuseStep 4652129 = 3489097) B3489097
theorem B29817953 : Blo 1289963 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B14916737 : Blo 1289963 14916737 := bstep (se 2 (by rfl) ⟨5593776, by rfl⟩ : syracuseStep 14916737 = 11187553) B11187553
theorem B18611507 : Blo 1289963 18611507 := bstep (se 1 (by rfl) ⟨13958630, by rfl⟩ : syracuseStep 18611507 = 27917261) B27917261
theorem B5512643 : Blo 1289963 5512643 := bstep (se 1 (by rfl) ⟨4134482, by rfl⟩ : syracuseStep 5512643 = 8268965) B8268965
theorem B2449835 : Blo 1289963 2449835 := bstep (se 1 (by rfl) ⟨1837376, by rfl⟩ : syracuseStep 2449835 = 3674753) B3674753
theorem B3269231 : Blo 1289963 3269231 := bstep (se 1 (by rfl) ⟨2451923, by rfl⟩ : syracuseStep 3269231 = 4903847) B4903847
theorem B5890697 : Blo 1289963 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B7955111 : Blo 1289963 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B4359041 : Blo 1289963 4359041 := bstep (se 2 (by rfl) ⟨1634640, by rfl⟩ : syracuseStep 4359041 = 3269281) B3269281
theorem B2180047 : Blo 1289963 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B18605051 : Blo 1289963 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B13419755 : Blo 1289963 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B1451335 : Blo 1289963 1451335 := bstep (se 1 (by rfl) ⟨1088501, by rfl⟩ : syracuseStep 1451335 = 2177003) B2177003
theorem B4359905 : Blo 1289963 4359905 := bstep (se 2 (by rfl) ⟨1634964, by rfl⟩ : syracuseStep 4359905 = 3269929) B3269929
theorem B44730143 : Blo 1289963 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B4900733 : Blo 1289963 4900733 := bstep (se 3 (by rfl) ⟨918887, by rfl⟩ : syracuseStep 4900733 = 1837775) B1837775
theorem B6203375 : Blo 1289963 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B67029295 : Blo 1289963 67029295 := bstep (se 1 (by rfl) ⟨50271971, by rfl⟩ : syracuseStep 67029295 = 100543943) B100543943
theorem B6539615 : Blo 1289963 6539615 := bstep (se 1 (by rfl) ⟨4904711, by rfl⟩ : syracuseStep 6539615 = 9809423) B9809423
theorem B5516059 : Blo 1289963 5516059 := bstep (se 1 (by rfl) ⟨4137044, by rfl⟩ : syracuseStep 5516059 = 8274089) B8274089
theorem B1379143 : Blo 1289963 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B4901735 : Blo 1289963 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B55855979 : Blo 1289963 55855979 := bstep (se 1 (by rfl) ⟨41891984, by rfl⟩ : syracuseStep 55855979 = 83783969) B83783969
theorem B9808937 : Blo 1289963 9808937 := bstep (se 2 (by rfl) ⟨3678351, by rfl⟩ : syracuseStep 9808937 = 7356703) B7356703
theorem B5590075 : Blo 1289963 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B1936703 : Blo 1289963 1936703 := bstep (se 1 (by rfl) ⟨1452527, by rfl⟩ : syracuseStep 1936703 = 2905055) B2905055
theorem B10472935 : Blo 1289963 10472935 := bstep (se 1 (by rfl) ⟨7854701, by rfl⟩ : syracuseStep 10472935 = 15709403) B15709403
theorem B1937087 : Blo 1289963 1937087 := bstep (se 1 (by rfl) ⟨1452815, by rfl⟩ : syracuseStep 1937087 = 2905631) B2905631
theorem B1290143 : Blo 1289963 1290143 := bstep (se 1 (by rfl) ⟨967607, by rfl⟩ : syracuseStep 1290143 = 1935215) B1935215
theorem B1290267 : Blo 1289963 1290267 := bstep (se 1 (by rfl) ⟨967700, by rfl⟩ : syracuseStep 1290267 = 1935401) B1935401
theorem B1937435 : Blo 1289963 1937435 := bstep (se 1 (by rfl) ⟨1453076, by rfl⟩ : syracuseStep 1937435 = 2906153) B2906153
theorem B1290287 : Blo 1289963 1290287 := bstep (se 1 (by rfl) ⟨967715, by rfl⟩ : syracuseStep 1290287 = 1935431) B1935431
theorem B3674251 : Blo 1289963 3674251 := bstep (se 1 (by rfl) ⟨2755688, by rfl⟩ : syracuseStep 3674251 = 5511377) B5511377
theorem B1290407 : Blo 1289963 1290407 := bstep (se 1 (by rfl) ⟨967805, by rfl⟩ : syracuseStep 1290407 = 1935611) B1935611
theorem B83701957 : Blo 1289963 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B4354343 : Blo 1289963 4354343 := bstep (se 1 (by rfl) ⟨3265757, by rfl⟩ : syracuseStep 4354343 = 6531515) B6531515
theorem B1290543 : Blo 1289963 1290543 := bstep (se 1 (by rfl) ⟨967907, by rfl⟩ : syracuseStep 1290543 = 1935815) B1935815
theorem B8950139 : Blo 1289963 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B1290687 : Blo 1289963 1290687 := bstep (se 1 (by rfl) ⟨968015, by rfl⟩ : syracuseStep 1290687 = 1936031) B1936031
theorem B1937855 : Blo 1289963 1937855 := bstep (se 1 (by rfl) ⟨1453391, by rfl⟩ : syracuseStep 1937855 = 2906783) B2906783
theorem B1290719 : Blo 1289963 1290719 := bstep (se 1 (by rfl) ⟨968039, by rfl⟩ : syracuseStep 1290719 = 1936079) B1936079
theorem B1634843 : Blo 1289963 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B1290783 : Blo 1289963 1290783 := bstep (se 1 (by rfl) ⟨968087, by rfl⟩ : syracuseStep 1290783 = 1936175) B1936175
theorem B1290863 : Blo 1289963 1290863 := bstep (se 1 (by rfl) ⟨968147, by rfl⟩ : syracuseStep 1290863 = 1936295) B1936295
theorem B1290983 : Blo 1289963 1290983 := bstep (se 1 (by rfl) ⟨968237, by rfl⟩ : syracuseStep 1290983 = 1936475) B1936475
theorem B3101419 : Blo 1289963 3101419 := bstep (se 1 (by rfl) ⟨2326064, by rfl⟩ : syracuseStep 3101419 = 4652129) B4652129
theorem B19878635 : Blo 1289963 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B1291035 : Blo 1289963 1291035 := bstep (se 1 (by rfl) ⟨968276, by rfl⟩ : syracuseStep 1291035 = 1936553) B1936553
theorem B12407671 : Blo 1289963 12407671 := bstep (se 1 (by rfl) ⟨9305753, by rfl⟩ : syracuseStep 12407671 = 18611507) B18611507
theorem B4354937 : Blo 1289963 4354937 := bstep (se 2 (by rfl) ⟨1633101, by rfl⟩ : syracuseStep 4354937 = 3266203) B3266203
theorem B3675095 : Blo 1289963 3675095 := bstep (se 1 (by rfl) ⟨2756321, by rfl⟩ : syracuseStep 3675095 = 5512643) B5512643
theorem B1291311 : Blo 1289963 1291311 := bstep (se 1 (by rfl) ⟨968483, by rfl⟩ : syracuseStep 1291311 = 1936967) B1936967
theorem B4355207 : Blo 1289963 4355207 := bstep (se 1 (by rfl) ⟨3266405, by rfl⟩ : syracuseStep 4355207 = 6532811) B6532811
theorem B1291431 : Blo 1289963 1291431 := bstep (se 1 (by rfl) ⟨968573, by rfl⟩ : syracuseStep 1291431 = 1937147) B1937147
theorem B1291591 : Blo 1289963 1291591 := bstep (se 1 (by rfl) ⟨968693, by rfl⟩ : syracuseStep 1291591 = 1937387) B1937387
theorem B4904347 : Blo 1289963 4904347 := bstep (se 1 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 4904347 = 7356521) B7356521
theorem B7452071 : Blo 1289963 7452071 := bstep (se 1 (by rfl) ⟨5589053, by rfl⟩ : syracuseStep 7452071 = 11178107) B11178107
theorem B7353787 : Blo 1289963 7353787 := bstep (se 1 (by rfl) ⟨5515340, by rfl⟩ : syracuseStep 7353787 = 11030681) B11030681
theorem B8828441 : Blo 1289963 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B4355963 : Blo 1289963 4355963 := bstep (se 1 (by rfl) ⟨3266972, by rfl⟩ : syracuseStep 4355963 = 6533945) B6533945
theorem B4904833 : Blo 1289963 4904833 := bstep (se 2 (by rfl) ⟨1839312, by rfl⟩ : syracuseStep 4904833 = 3678625) B3678625
theorem B7354313 : Blo 1289963 7354313 := bstep (se 2 (by rfl) ⟨2757867, by rfl⟩ : syracuseStep 7354313 = 5515735) B5515735
theorem B9943019 : Blo 1289963 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B4356287 : Blo 1289963 4356287 := bstep (se 1 (by rfl) ⟨3267215, by rfl⟩ : syracuseStep 4356287 = 6534431) B6534431
theorem B3102995 : Blo 1289963 3102995 := bstep (se 1 (by rfl) ⟨2327246, by rfl⟩ : syracuseStep 3102995 = 4654493) B4654493
theorem B2177435 : Blo 1289963 2177435 := bstep (se 1 (by rfl) ⟨1633076, by rfl⟩ : syracuseStep 2177435 = 3266153) B3266153
theorem B11778547 : Blo 1289963 11778547 := bstep (se 1 (by rfl) ⟨8833910, by rfl⟩ : syracuseStep 11778547 = 17667821) B17667821
theorem B8829587 : Blo 1289963 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B5233385 : Blo 1289963 5233385 := bstep (se 2 (by rfl) ⟨1962519, by rfl⟩ : syracuseStep 5233385 = 3925039) B3925039
theorem B3922751 : Blo 1289963 3922751 := bstep (se 1 (by rfl) ⟨2942063, by rfl⟩ : syracuseStep 3922751 = 5884127) B5884127
theorem B4356935 : Blo 1289963 4356935 := bstep (se 1 (by rfl) ⟨3267701, by rfl⟩ : syracuseStep 4356935 = 6535403) B6535403
theorem B7347023 : Blo 1289963 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B3267611 : Blo 1289963 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B3677395 : Blo 1289963 3677395 := bstep (se 1 (by rfl) ⟨2758046, by rfl⟩ : syracuseStep 3677395 = 5516093) B5516093
theorem B9944491 : Blo 1289963 9944491 := bstep (se 1 (by rfl) ⟨7458368, by rfl⟩ : syracuseStep 9944491 = 14916737) B14916737
theorem B158981777 : Blo 1289963 158981777 := bstep (se 2 (by rfl) ⟨59618166, by rfl⟩ : syracuseStep 158981777 = 119236333) B119236333
theorem B6536861 : Blo 1289963 6536861 := bstep (se 3 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 6536861 = 2451323) B2451323
theorem B2449273 : Blo 1289963 2449273 := bstep (se 2 (by rfl) ⟨918477, by rfl⟩ : syracuseStep 2449273 = 1836955) B1836955
theorem B11182013 : Blo 1289963 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B4899001 : Blo 1289963 4899001 := bstep (se 2 (by rfl) ⟨1837125, by rfl⟩ : syracuseStep 4899001 = 3674251) B3674251
theorem B2179487 : Blo 1289963 2179487 := bstep (se 1 (by rfl) ⟨1634615, by rfl⟩ : syracuseStep 2179487 = 3269231) B3269231
theorem B2450063 : Blo 1289963 2450063 := bstep (se 1 (by rfl) ⟨1837547, by rfl⟩ : syracuseStep 2450063 = 3675095) B3675095
theorem B15704729 : Blo 1289963 15704729 := bstep (se 2 (by rfl) ⟨5889273, by rfl⟩ : syracuseStep 15704729 = 11778547) B11778547
theorem B12403367 : Blo 1289963 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B8946503 : Blo 1289963 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B29820095 : Blo 1289963 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B6628679 : Blo 1289963 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B4359581 : Blo 1289963 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B4359743 : Blo 1289963 4359743 := bstep (se 1 (by rfl) ⟨3269807, by rfl⟩ : syracuseStep 4359743 = 6539615) B6539615
theorem B1451623 : Blo 1289963 1451623 := bstep (se 1 (by rfl) ⟨1088717, by rfl⟩ : syracuseStep 1451623 = 2177435) B2177435
theorem B1935113 : Blo 1289963 1935113 := bstep (se 2 (by rfl) ⟨725667, by rfl⟩ : syracuseStep 1935113 = 1451335) B1451335
theorem B6539129 : Blo 1289963 6539129 := bstep (se 2 (by rfl) ⟨2452173, by rfl⟩ : syracuseStep 6539129 = 4904347) B4904347
theorem B6539291 : Blo 1289963 6539291 := bstep (se 1 (by rfl) ⟨4904468, by rfl⟩ : syracuseStep 6539291 = 9808937) B9808937
theorem B6539777 : Blo 1289963 6539777 := bstep (se 2 (by rfl) ⟨2452416, by rfl⟩ : syracuseStep 6539777 = 4904833) B4904833
theorem B2902895 : Blo 1289963 2902895 := bstep (se 1 (by rfl) ⟨2177171, by rfl⟩ : syracuseStep 2902895 = 4354343) B4354343
theorem B5966759 : Blo 1289963 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B111602609 : Blo 1289963 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B1633223 : Blo 1289963 1633223 := bstep (se 1 (by rfl) ⟨1224917, by rfl⟩ : syracuseStep 1633223 = 2449835) B2449835
theorem B3927131 : Blo 1289963 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B5303407 : Blo 1289963 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B2903291 : Blo 1289963 2903291 := bstep (se 1 (by rfl) ⟨2177468, by rfl⟩ : syracuseStep 2903291 = 4354937) B4354937
theorem B2903471 : Blo 1289963 2903471 := bstep (se 1 (by rfl) ⟨2177603, by rfl⟩ : syracuseStep 2903471 = 4355207) B4355207
theorem B4968047 : Blo 1289963 4968047 := bstep (se 1 (by rfl) ⟨3726035, by rfl⟩ : syracuseStep 4968047 = 7452071) B7452071
theorem B5885627 : Blo 1289963 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B1838857 : Blo 1289963 1838857 := bstep (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) B1379143
theorem B16543561 : Blo 1289963 16543561 := bstep (se 2 (by rfl) ⟨6203835, by rfl⟩ : syracuseStep 16543561 = 12407671) B12407671
theorem B2903975 : Blo 1289963 2903975 := bstep (se 1 (by rfl) ⟨2177981, by rfl⟩ : syracuseStep 2903975 = 4355963) B4355963
theorem B4902875 : Blo 1289963 4902875 := bstep (se 1 (by rfl) ⟨3677156, by rfl⟩ : syracuseStep 4902875 = 7354313) B7354313
theorem B2904191 : Blo 1289963 2904191 := bstep (se 1 (by rfl) ⟨2178143, by rfl⟩ : syracuseStep 2904191 = 4356287) B4356287
theorem B2068663 : Blo 1289963 2068663 := bstep (se 1 (by rfl) ⟨1551497, by rfl⟩ : syracuseStep 2068663 = 3102995) B3102995
theorem B4903193 : Blo 1289963 4903193 := bstep (se 2 (by rfl) ⟨1838697, by rfl⟩ : syracuseStep 4903193 = 3677395) B3677395
theorem B5886391 : Blo 1289963 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B2904623 : Blo 1289963 2904623 := bstep (se 1 (by rfl) ⟨2178467, by rfl⟩ : syracuseStep 2904623 = 4356935) B4356935
theorem B13259321 : Blo 1289963 13259321 := bstep (se 2 (by rfl) ⟨4972245, by rfl⟩ : syracuseStep 13259321 = 9944491) B9944491
theorem B37237319 : Blo 1289963 37237319 := bstep (se 1 (by rfl) ⟨27927989, by rfl⟩ : syracuseStep 37237319 = 55855979) B55855979
theorem B13963913 : Blo 1289963 13963913 := bstep (se 2 (by rfl) ⟨5236467, by rfl⟩ : syracuseStep 13963913 = 10472935) B10472935
theorem B1291135 : Blo 1289963 1291135 := bstep (se 1 (by rfl) ⟨968351, by rfl⟩ : syracuseStep 1291135 = 1936703) B1936703
theorem B1291391 : Blo 1289963 1291391 := bstep (se 1 (by rfl) ⟨968543, by rfl⟩ : syracuseStep 1291391 = 1937087) B1937087
theorem B3265697 : Blo 1289963 3265697 := bstep (se 2 (by rfl) ⟨1224636, by rfl⟩ : syracuseStep 3265697 = 2449273) B2449273
theorem B1291623 : Blo 1289963 1291623 := bstep (se 1 (by rfl) ⟨968717, by rfl⟩ : syracuseStep 1291623 = 1937435) B1937435
theorem B1291903 : Blo 1289963 1291903 := bstep (se 1 (by rfl) ⟨968927, by rfl⟩ : syracuseStep 1291903 = 1937855) B1937855
theorem B89372393 : Blo 1289963 89372393 := bstep (se 2 (by rfl) ⟨33514647, by rfl⟩ : syracuseStep 89372393 = 67029295) B67029295
theorem B13252423 : Blo 1289963 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B2906027 : Blo 1289963 2906027 := bstep (se 1 (by rfl) ⟨2179520, by rfl⟩ : syracuseStep 2906027 = 4359041) B4359041
theorem B4135225 : Blo 1289963 4135225 := bstep (se 2 (by rfl) ⟨1550709, by rfl⟩ : syracuseStep 4135225 = 3101419) B3101419
theorem B7354745 : Blo 1289963 7354745 := bstep (se 2 (by rfl) ⟨2758029, by rfl⟩ : syracuseStep 7354745 = 5516059) B5516059
theorem B2906603 : Blo 1289963 2906603 := bstep (se 1 (by rfl) ⟨2179952, by rfl⟩ : syracuseStep 2906603 = 4359905) B4359905
theorem B3267155 : Blo 1289963 3267155 := bstep (se 1 (by rfl) ⟨2450366, by rfl⟩ : syracuseStep 3267155 = 4900733) B4900733
theorem B2906729 : Blo 1289963 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B4135583 : Blo 1289963 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B7453433 : Blo 1289963 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B3488923 : Blo 1289963 3488923 := bstep (se 1 (by rfl) ⟨2616692, by rfl⟩ : syracuseStep 3488923 = 5233385) B5233385
theorem B4898015 : Blo 1289963 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B3267823 : Blo 1289963 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B9805049 : Blo 1289963 9805049 := bstep (se 2 (by rfl) ⟨3676893, by rfl⟩ : syracuseStep 9805049 = 7353787) B7353787
theorem B2178407 : Blo 1289963 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B10460669 : Blo 1289963 10460669 := bstep (se 3 (by rfl) ⟨1961375, by rfl⟩ : syracuseStep 10460669 = 3922751) B3922751
theorem B105987851 : Blo 1289963 105987851 := bstep (se 1 (by rfl) ⟨79490888, by rfl⟩ : syracuseStep 105987851 = 158981777) B158981777
theorem B4357907 : Blo 1289963 4357907 := bstep (se 1 (by rfl) ⟨3268430, by rfl⟩ : syracuseStep 4357907 = 6536861) B6536861
theorem B7454675 : Blo 1289963 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B3268795 : Blo 1289963 3268795 := bstep (se 1 (by rfl) ⟨2451596, by rfl⟩ : syracuseStep 3268795 = 4903193) B4903193
theorem B8839547 : Blo 1289963 8839547 := bstep (se 1 (by rfl) ⟨6629660, by rfl⟩ : syracuseStep 8839547 = 13259321) B13259321
theorem B5513633 : Blo 1289963 5513633 := bstep (se 2 (by rfl) ⟨2067612, by rfl⟩ : syracuseStep 5513633 = 4135225) B4135225
theorem B10469819 : Blo 1289963 10469819 := bstep (se 1 (by rfl) ⟨7852364, by rfl⟩ : syracuseStep 10469819 = 15704729) B15704729
theorem B5964335 : Blo 1289963 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B7848521 : Blo 1289963 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B59581595 : Blo 1289963 59581595 := bstep (se 1 (by rfl) ⟨44686196, by rfl⟩ : syracuseStep 59581595 = 89372393) B89372393
theorem B4359419 : Blo 1289963 4359419 := bstep (se 1 (by rfl) ⟨3269564, by rfl⟩ : syracuseStep 4359419 = 6539129) B6539129
theorem B27895117 : Blo 1289963 27895117 := bstep (se 3 (by rfl) ⟨5230334, by rfl⟩ : syracuseStep 27895117 = 10460669) B10460669
theorem B4359527 : Blo 1289963 4359527 := bstep (se 1 (by rfl) ⟨3269645, by rfl⟩ : syracuseStep 4359527 = 6539291) B6539291
theorem B7071209 : Blo 1289963 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B4359851 : Blo 1289963 4359851 := bstep (se 1 (by rfl) ⟨3269888, by rfl⟩ : syracuseStep 4359851 = 6539777) B6539777
theorem B11028221 : Blo 1289963 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B1935263 : Blo 1289963 1935263 := bstep (se 1 (by rfl) ⟨1451447, by rfl⟩ : syracuseStep 1935263 = 2902895) B2902895
theorem B74401739 : Blo 1289963 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B1935497 : Blo 1289963 1935497 := bstep (se 2 (by rfl) ⟨725811, by rfl⟩ : syracuseStep 1935497 = 1451623) B1451623
theorem B1935527 : Blo 1289963 1935527 := bstep (se 1 (by rfl) ⟨1451645, by rfl⟩ : syracuseStep 1935527 = 2903291) B2903291
theorem B1452271 : Blo 1289963 1452271 := bstep (se 1 (by rfl) ⟨1089203, by rfl⟩ : syracuseStep 1452271 = 2178407) B2178407
theorem B1935647 : Blo 1289963 1935647 := bstep (se 1 (by rfl) ⟨1451735, by rfl⟩ : syracuseStep 1935647 = 2903471) B2903471
theorem B2451809 : Blo 1289963 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B3312031 : Blo 1289963 3312031 := bstep (se 1 (by rfl) ⟨2484023, by rfl⟩ : syracuseStep 3312031 = 4968047) B4968047
theorem B70658567 : Blo 1289963 70658567 := bstep (se 1 (by rfl) ⟨52993925, by rfl⟩ : syracuseStep 70658567 = 105987851) B105987851
theorem B1935983 : Blo 1289963 1935983 := bstep (se 1 (by rfl) ⟨1451987, by rfl⟩ : syracuseStep 1935983 = 2903975) B2903975
theorem B1936127 : Blo 1289963 1936127 := bstep (se 1 (by rfl) ⟨1452095, by rfl⟩ : syracuseStep 1936127 = 2904191) B2904191
theorem B6532001 : Blo 1289963 6532001 := bstep (se 2 (by rfl) ⟨2449500, by rfl⟩ : syracuseStep 6532001 = 4899001) B4899001
theorem B1452991 : Blo 1289963 1452991 := bstep (se 1 (by rfl) ⟨1089743, by rfl⟩ : syracuseStep 1452991 = 2179487) B2179487
theorem B1936415 : Blo 1289963 1936415 := bstep (se 1 (by rfl) ⟨1452311, by rfl⟩ : syracuseStep 1936415 = 2904623) B2904623
theorem B24824879 : Blo 1289963 24824879 := bstep (se 1 (by rfl) ⟨18618659, by rfl⟩ : syracuseStep 24824879 = 37237319) B37237319
theorem B9309275 : Blo 1289963 9309275 := bstep (se 1 (by rfl) ⟨6981956, by rfl⟩ : syracuseStep 9309275 = 13963913) B13963913
theorem B1633375 : Blo 1289963 1633375 := bstep (se 1 (by rfl) ⟨1225031, by rfl⟩ : syracuseStep 1633375 = 2450063) B2450063
theorem B8268911 : Blo 1289963 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B18607589 : Blo 1289963 18607589 := bstep (se 4 (by rfl) ⟨1744461, by rfl⟩ : syracuseStep 18607589 = 3488923) B3488923
theorem B4419119 : Blo 1289963 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B1290075 : Blo 1289963 1290075 := bstep (se 1 (by rfl) ⟨967556, by rfl⟩ : syracuseStep 1290075 = 1935113) B1935113
theorem B1937351 : Blo 1289963 1937351 := bstep (se 1 (by rfl) ⟨1453013, by rfl⟩ : syracuseStep 1937351 = 2906027) B2906027
theorem B4903163 : Blo 1289963 4903163 := bstep (se 1 (by rfl) ⟨3677372, by rfl⟩ : syracuseStep 4903163 = 7354745) B7354745
theorem B1937735 : Blo 1289963 1937735 := bstep (se 1 (by rfl) ⟨1453301, by rfl⟩ : syracuseStep 1937735 = 2906603) B2906603
theorem B1937819 : Blo 1289963 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B4968955 : Blo 1289963 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B3977839 : Blo 1289963 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B2618087 : Blo 1289963 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B3265343 : Blo 1289963 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B22058081 : Blo 1289963 22058081 := bstep (se 2 (by rfl) ⟨8271780, by rfl⟩ : syracuseStep 22058081 = 16543561) B16543561
theorem B2905271 : Blo 1289963 2905271 := bstep (se 1 (by rfl) ⟨2178953, by rfl⟩ : syracuseStep 2905271 = 4357907) B4357907
theorem B4355261 : Blo 1289963 4355261 := bstep (se 3 (by rfl) ⟨816611, by rfl⟩ : syracuseStep 4355261 = 1633223) B1633223
theorem B4969783 : Blo 1289963 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B2758217 : Blo 1289963 2758217 := bstep (se 2 (by rfl) ⟨1034331, by rfl⟩ : syracuseStep 2758217 = 2068663) B2068663
theorem B2177131 : Blo 1289963 2177131 := bstep (se 1 (by rfl) ⟨1632848, by rfl⟩ : syracuseStep 2177131 = 3265697) B3265697
theorem B19880063 : Blo 1289963 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B2906387 : Blo 1289963 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B2906495 : Blo 1289963 2906495 := bstep (se 1 (by rfl) ⟨2179871, by rfl⟩ : syracuseStep 2906495 = 4359743) B4359743
theorem B4357097 : Blo 1289963 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B2178103 : Blo 1289963 2178103 := bstep (se 1 (by rfl) ⟨1633577, by rfl⟩ : syracuseStep 2178103 = 3267155) B3267155
theorem B15695005 : Blo 1289963 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B6536699 : Blo 1289963 6536699 := bstep (se 1 (by rfl) ⟨4902524, by rfl⟩ : syracuseStep 6536699 = 9805049) B9805049
theorem B17669897 : Blo 1289963 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B3268583 : Blo 1289963 3268583 := bstep (se 1 (by rfl) ⟨2451437, by rfl⟩ : syracuseStep 3268583 = 4902875) B4902875
theorem B3268775 : Blo 1289963 3268775 := bstep (se 1 (by rfl) ⟨2451581, by rfl⟩ : syracuseStep 3268775 = 4903163) B4903163
theorem B4358393 : Blo 1289963 4358393 := bstep (se 2 (by rfl) ⟨1634397, by rfl⟩ : syracuseStep 4358393 = 3268795) B3268795
theorem B6979879 : Blo 1289963 6979879 := bstep (se 1 (by rfl) ⟨5234909, by rfl⟩ : syracuseStep 6979879 = 10469819) B10469819
theorem B158884253 : Blo 1289963 158884253 := bstep (se 3 (by rfl) ⟨29790797, by rfl⟩ : syracuseStep 158884253 = 59581595) B59581595
theorem B4416041 : Blo 1289963 4416041 := bstep (se 2 (by rfl) ⟨1656015, by rfl⟩ : syracuseStep 4416041 = 3312031) B3312031
theorem B14705387 : Blo 1289963 14705387 := bstep (se 1 (by rfl) ⟨11029040, by rfl⟩ : syracuseStep 14705387 = 22058081) B22058081
theorem B6538157 : Blo 1289963 6538157 := bstep (se 3 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 6538157 = 2451809) B2451809
theorem B47105711 : Blo 1289963 47105711 := bstep (se 1 (by rfl) ⟨35329283, by rfl⟩ : syracuseStep 47105711 = 70658567) B70658567
theorem B37193489 : Blo 1289963 37193489 := bstep (se 2 (by rfl) ⟨13947558, by rfl⟩ : syracuseStep 37193489 = 27895117) B27895117
theorem B6981565 : Blo 1289963 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B16549919 : Blo 1289963 16549919 := bstep (se 1 (by rfl) ⟨12412439, by rfl⟩ : syracuseStep 16549919 = 24824879) B24824879
theorem B12405059 : Blo 1289963 12405059 := bstep (se 1 (by rfl) ⟨9303794, by rfl⟩ : syracuseStep 12405059 = 18607589) B18607589
theorem B2902841 : Blo 1289963 2902841 := bstep (se 2 (by rfl) ⟨1088565, by rfl⟩ : syracuseStep 2902841 = 2177131) B2177131
theorem B5893031 : Blo 1289963 5893031 := bstep (se 1 (by rfl) ⟨4419773, by rfl⟩ : syracuseStep 5893031 = 8839547) B8839547
theorem B1936361 : Blo 1289963 1936361 := bstep (se 2 (by rfl) ⟨726135, by rfl⟩ : syracuseStep 1936361 = 1452271) B1452271
theorem B3976223 : Blo 1289963 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B1936847 : Blo 1289963 1936847 := bstep (se 1 (by rfl) ⟨1452635, by rfl⟩ : syracuseStep 1936847 = 2905271) B2905271
theorem B2903507 : Blo 1289963 2903507 := bstep (se 1 (by rfl) ⟨2177630, by rfl⟩ : syracuseStep 2903507 = 4355261) B4355261
theorem B4714139 : Blo 1289963 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B7352147 : Blo 1289963 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B1937321 : Blo 1289963 1937321 := bstep (se 2 (by rfl) ⟨726495, by rfl⟩ : syracuseStep 1937321 = 1452991) B1452991
theorem B1290175 : Blo 1289963 1290175 := bstep (se 1 (by rfl) ⟨967631, by rfl⟩ : syracuseStep 1290175 = 1935263) B1935263
theorem B2904137 : Blo 1289963 2904137 := bstep (se 2 (by rfl) ⟨1089051, by rfl⟩ : syracuseStep 2904137 = 2178103) B2178103
theorem B1290331 : Blo 1289963 1290331 := bstep (se 1 (by rfl) ⟨967748, by rfl⟩ : syracuseStep 1290331 = 1935497) B1935497
theorem B1290351 : Blo 1289963 1290351 := bstep (se 1 (by rfl) ⟨967763, by rfl⟩ : syracuseStep 1290351 = 1935527) B1935527
theorem B1937591 : Blo 1289963 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B1290431 : Blo 1289963 1290431 := bstep (se 1 (by rfl) ⟨967823, by rfl⟩ : syracuseStep 1290431 = 1935647) B1935647
theorem B20926673 : Blo 1289963 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B1937663 : Blo 1289963 1937663 := bstep (se 1 (by rfl) ⟨1453247, by rfl⟩ : syracuseStep 1937663 = 2906495) B2906495
theorem B1290655 : Blo 1289963 1290655 := bstep (se 1 (by rfl) ⟨967991, by rfl⟩ : syracuseStep 1290655 = 1935983) B1935983
theorem B1290751 : Blo 1289963 1290751 := bstep (se 1 (by rfl) ⟨968063, by rfl⟩ : syracuseStep 1290751 = 1936127) B1936127
theorem B4354667 : Blo 1289963 4354667 := bstep (se 1 (by rfl) ⟨3266000, by rfl⟩ : syracuseStep 4354667 = 6532001) B6532001
theorem B2904731 : Blo 1289963 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B1290943 : Blo 1289963 1290943 := bstep (se 1 (by rfl) ⟨968207, by rfl⟩ : syracuseStep 1290943 = 1936415) B1936415
theorem B6206183 : Blo 1289963 6206183 := bstep (se 1 (by rfl) ⟨4654637, by rfl⟩ : syracuseStep 6206183 = 9309275) B9309275
theorem B2946079 : Blo 1289963 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B1291567 : Blo 1289963 1291567 := bstep (se 1 (by rfl) ⟨968675, by rfl⟩ : syracuseStep 1291567 = 1937351) B1937351
theorem B1291823 : Blo 1289963 1291823 := bstep (se 1 (by rfl) ⟨968867, by rfl⟩ : syracuseStep 1291823 = 1937735) B1937735
theorem B1291879 : Blo 1289963 1291879 := bstep (se 1 (by rfl) ⟨968909, by rfl⟩ : syracuseStep 1291879 = 1937819) B1937819
theorem B3675755 : Blo 1289963 3675755 := bstep (se 1 (by rfl) ⟨2756816, by rfl⟩ : syracuseStep 3675755 = 5513633) B5513633
theorem B5232347 : Blo 1289963 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B2176895 : Blo 1289963 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B21215141 : Blo 1289963 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B6625273 : Blo 1289963 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B2906279 : Blo 1289963 2906279 := bstep (se 1 (by rfl) ⟨2179709, by rfl⟩ : syracuseStep 2906279 = 4359419) B4359419
theorem B2906351 : Blo 1289963 2906351 := bstep (se 1 (by rfl) ⟨2179763, by rfl⟩ : syracuseStep 2906351 = 4359527) B4359527
theorem B2906567 : Blo 1289963 2906567 := bstep (se 1 (by rfl) ⟨2179925, by rfl⟩ : syracuseStep 2906567 = 4359851) B4359851
theorem B49601159 : Blo 1289963 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B13253375 : Blo 1289963 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B2177833 : Blo 1289963 2177833 := bstep (se 2 (by rfl) ⟨816687, by rfl⟩ : syracuseStep 2177833 = 1633375) B1633375
theorem B7355245 : Blo 1289963 7355245 := bstep (se 3 (by rfl) ⟨1379108, by rfl⟩ : syracuseStep 7355245 = 2758217) B2758217
theorem B6626377 : Blo 1289963 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B5512607 : Blo 1289963 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B4357799 : Blo 1289963 4357799 := bstep (se 1 (by rfl) ⟨3268349, by rfl⟩ : syracuseStep 4357799 = 6536699) B6536699
theorem B11779931 : Blo 1289963 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B2179055 : Blo 1289963 2179055 := bstep (se 1 (by rfl) ⟨1634291, by rfl⟩ : syracuseStep 2179055 = 3268583) B3268583
theorem B2179183 : Blo 1289963 2179183 := bstep (se 1 (by rfl) ⟨1634387, by rfl⟩ : syracuseStep 2179183 = 3268775) B3268775
theorem B13951115 : Blo 1289963 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B105922835 : Blo 1289963 105922835 := bstep (se 1 (by rfl) ⟨79442126, by rfl⟩ : syracuseStep 105922835 = 158884253) B158884253
theorem B9306505 : Blo 1289963 9306505 := bstep (se 2 (by rfl) ⟨3489939, by rfl⟩ : syracuseStep 9306505 = 6979879) B6979879
theorem B4137455 : Blo 1289963 4137455 := bstep (se 1 (by rfl) ⟨3103091, by rfl⟩ : syracuseStep 4137455 = 6206183) B6206183
theorem B4358771 : Blo 1289963 4358771 := bstep (se 1 (by rfl) ⟨3269078, by rfl⟩ : syracuseStep 4358771 = 6538157) B6538157
theorem B2450503 : Blo 1289963 2450503 := bstep (se 1 (by rfl) ⟨1837877, by rfl⟩ : syracuseStep 2450503 = 3675755) B3675755
theorem B9806993 : Blo 1289963 9806993 := bstep (se 2 (by rfl) ⟨3677622, by rfl⟩ : syracuseStep 9806993 = 7355245) B7355245
theorem B1451263 : Blo 1289963 1451263 := bstep (se 1 (by rfl) ⟨1088447, by rfl⟩ : syracuseStep 1451263 = 2176895) B2176895
theorem B1935227 : Blo 1289963 1935227 := bstep (se 1 (by rfl) ⟨1451420, by rfl⟩ : syracuseStep 1935227 = 2902841) B2902841
theorem B1935671 : Blo 1289963 1935671 := bstep (se 1 (by rfl) ⟨1451753, by rfl⟩ : syracuseStep 1935671 = 2903507) B2903507
theorem B15714749 : Blo 1289963 15714749 := bstep (se 3 (by rfl) ⟨2946515, by rfl⟩ : syracuseStep 15714749 = 5893031) B5893031
theorem B4901431 : Blo 1289963 4901431 := bstep (se 1 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 4901431 = 7352147) B7352147
theorem B9308753 : Blo 1289963 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B1452703 : Blo 1289963 1452703 := bstep (se 1 (by rfl) ⟨1089527, by rfl⟩ : syracuseStep 1452703 = 2179055) B2179055
theorem B8833697 : Blo 1289963 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B1936091 : Blo 1289963 1936091 := bstep (se 1 (by rfl) ⟨1452068, by rfl⟩ : syracuseStep 1936091 = 2904137) B2904137
theorem B10603261 : Blo 1289963 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B2944027 : Blo 1289963 2944027 := bstep (se 1 (by rfl) ⟨2208020, by rfl⟩ : syracuseStep 2944027 = 4416041) B4416041
theorem B2903111 : Blo 1289963 2903111 := bstep (se 1 (by rfl) ⟨2177333, by rfl⟩ : syracuseStep 2903111 = 4354667) B4354667
theorem B1936487 : Blo 1289963 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B2903777 : Blo 1289963 2903777 := bstep (se 2 (by rfl) ⟨1088916, by rfl⟩ : syracuseStep 2903777 = 2177833) B2177833
theorem B31403807 : Blo 1289963 31403807 := bstep (se 1 (by rfl) ⟨23552855, by rfl⟩ : syracuseStep 31403807 = 47105711) B47105711
theorem B14143427 : Blo 1289963 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B3928105 : Blo 1289963 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B8835169 : Blo 1289963 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B1937519 : Blo 1289963 1937519 := bstep (se 1 (by rfl) ⟨1453139, by rfl⟩ : syracuseStep 1937519 = 2906279) B2906279
theorem B1937567 : Blo 1289963 1937567 := bstep (se 1 (by rfl) ⟨1453175, by rfl⟩ : syracuseStep 1937567 = 2906351) B2906351
theorem B8270039 : Blo 1289963 8270039 := bstep (se 1 (by rfl) ⟨6202529, by rfl⟩ : syracuseStep 8270039 = 12405059) B12405059
theorem B1937711 : Blo 1289963 1937711 := bstep (se 1 (by rfl) ⟨1453283, by rfl⟩ : syracuseStep 1937711 = 2906567) B2906567
theorem B12571037 : Blo 1289963 12571037 := bstep (se 3 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 12571037 = 4714139) B4714139
theorem B33067439 : Blo 1289963 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B8835583 : Blo 1289963 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B1290907 : Blo 1289963 1290907 := bstep (se 1 (by rfl) ⟨968180, by rfl⟩ : syracuseStep 1290907 = 1936361) B1936361
theorem B3675071 : Blo 1289963 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B1291231 : Blo 1289963 1291231 := bstep (se 1 (by rfl) ⟨968423, by rfl⟩ : syracuseStep 1291231 = 1936847) B1936847
theorem B2905199 : Blo 1289963 2905199 := bstep (se 1 (by rfl) ⟨2178899, by rfl⟩ : syracuseStep 2905199 = 4357799) B4357799
theorem B7853287 : Blo 1289963 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B1291547 : Blo 1289963 1291547 := bstep (se 1 (by rfl) ⟨968660, by rfl⟩ : syracuseStep 1291547 = 1937321) B1937321
theorem B1291727 : Blo 1289963 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B2905595 : Blo 1289963 2905595 := bstep (se 1 (by rfl) ⟨2179196, by rfl⟩ : syracuseStep 2905595 = 4358393) B4358393
theorem B1291775 : Blo 1289963 1291775 := bstep (se 1 (by rfl) ⟨968831, by rfl⟩ : syracuseStep 1291775 = 1937663) B1937663
theorem B9803591 : Blo 1289963 9803591 := bstep (se 1 (by rfl) ⟨7352693, by rfl⟩ : syracuseStep 9803591 = 14705387) B14705387
theorem B3488231 : Blo 1289963 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B24795659 : Blo 1289963 24795659 := bstep (se 1 (by rfl) ⟨18596744, by rfl⟩ : syracuseStep 24795659 = 37193489) B37193489
theorem B11033279 : Blo 1289963 11033279 := bstep (se 1 (by rfl) ⟨8274959, by rfl⟩ : syracuseStep 11033279 = 16549919) B16549919
theorem B11780225 : Blo 1289963 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B5513359 : Blo 1289963 5513359 := bstep (se 1 (by rfl) ⟨4135019, by rfl⟩ : syracuseStep 5513359 = 8270039) B8270039
theorem B70615223 : Blo 1289963 70615223 := bstep (se 1 (by rfl) ⟨52961417, by rfl⟩ : syracuseStep 70615223 = 105922835) B105922835
theorem B8380691 : Blo 1289963 8380691 := bstep (se 1 (by rfl) ⟨6285518, by rfl⟩ : syracuseStep 8380691 = 12571037) B12571037
theorem B22044959 : Blo 1289963 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B11780777 : Blo 1289963 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B6537995 : Blo 1289963 6537995 := bstep (se 1 (by rfl) ⟨4903496, by rfl⟩ : syracuseStep 6537995 = 9806993) B9806993
theorem B3925369 : Blo 1289963 3925369 := bstep (se 2 (by rfl) ⟨1472013, by rfl⟩ : syracuseStep 3925369 = 2944027) B2944027
theorem B10471049 : Blo 1289963 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B1935017 : Blo 1289963 1935017 := bstep (se 2 (by rfl) ⟨725631, by rfl⟩ : syracuseStep 1935017 = 1451263) B1451263
theorem B1935407 : Blo 1289963 1935407 := bstep (se 1 (by rfl) ⟨1451555, by rfl⟩ : syracuseStep 1935407 = 2903111) B2903111
theorem B1935851 : Blo 1289963 1935851 := bstep (se 1 (by rfl) ⟨1451888, by rfl⟩ : syracuseStep 1935851 = 2903777) B2903777
theorem B9800189 : Blo 1289963 9800189 := bstep (se 3 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 9800189 = 3675071) B3675071
theorem B5237473 : Blo 1289963 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B9300743 : Blo 1289963 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B1936799 : Blo 1289963 1936799 := bstep (se 1 (by rfl) ⟨1452599, by rfl⟩ : syracuseStep 1936799 = 2905199) B2905199
theorem B1936937 : Blo 1289963 1936937 := bstep (se 2 (by rfl) ⟨726351, by rfl⟩ : syracuseStep 1936937 = 1452703) B1452703
theorem B1937063 : Blo 1289963 1937063 := bstep (se 1 (by rfl) ⟨1452797, by rfl⟩ : syracuseStep 1937063 = 2905595) B2905595
theorem B41905997 : Blo 1289963 41905997 := bstep (se 3 (by rfl) ⟨7857374, by rfl⟩ : syracuseStep 41905997 = 15714749) B15714749
theorem B1290151 : Blo 1289963 1290151 := bstep (se 1 (by rfl) ⟨967613, by rfl⟩ : syracuseStep 1290151 = 1935227) B1935227
theorem B9301949 : Blo 1289963 9301949 := bstep (se 3 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 9301949 = 3488231) B3488231
theorem B1290447 : Blo 1289963 1290447 := bstep (se 1 (by rfl) ⟨967835, by rfl⟩ : syracuseStep 1290447 = 1935671) B1935671
theorem B6205835 : Blo 1289963 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B1290727 : Blo 1289963 1290727 := bstep (se 1 (by rfl) ⟨968045, by rfl⟩ : syracuseStep 1290727 = 1936091) B1936091
theorem B1290991 : Blo 1289963 1290991 := bstep (se 1 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 1290991 = 1936487) B1936487
theorem B20935871 : Blo 1289963 20935871 := bstep (se 1 (by rfl) ⟨15701903, by rfl⟩ : syracuseStep 20935871 = 31403807) B31403807
theorem B1291679 : Blo 1289963 1291679 := bstep (se 1 (by rfl) ⟨968759, by rfl⟩ : syracuseStep 1291679 = 1937519) B1937519
theorem B1291711 : Blo 1289963 1291711 := bstep (se 1 (by rfl) ⟨968783, by rfl⟩ : syracuseStep 1291711 = 1937567) B1937567
theorem B2905577 : Blo 1289963 2905577 := bstep (se 2 (by rfl) ⟨1089591, by rfl⟩ : syracuseStep 2905577 = 2179183) B2179183
theorem B1291807 : Blo 1289963 1291807 := bstep (se 1 (by rfl) ⟨968855, by rfl⟩ : syracuseStep 1291807 = 1937711) B1937711
theorem B2758303 : Blo 1289963 2758303 := bstep (se 1 (by rfl) ⟨2068727, by rfl⟩ : syracuseStep 2758303 = 4137455) B4137455
theorem B2905847 : Blo 1289963 2905847 := bstep (se 1 (by rfl) ⟨2179385, by rfl⟩ : syracuseStep 2905847 = 4358771) B4358771
theorem B12408673 : Blo 1289963 12408673 := bstep (se 2 (by rfl) ⟨4653252, by rfl⟩ : syracuseStep 12408673 = 9306505) B9306505
theorem B6535241 : Blo 1289963 6535241 := bstep (se 2 (by rfl) ⟨2450715, by rfl⟩ : syracuseStep 6535241 = 4901431) B4901431
theorem B14137681 : Blo 1289963 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B6535727 : Blo 1289963 6535727 := bstep (se 1 (by rfl) ⟨4901795, by rfl⟩ : syracuseStep 6535727 = 9803591) B9803591
theorem B3267337 : Blo 1289963 3267337 := bstep (se 2 (by rfl) ⟨1225251, by rfl⟩ : syracuseStep 3267337 = 2450503) B2450503
theorem B16530439 : Blo 1289963 16530439 := bstep (se 1 (by rfl) ⟨12397829, by rfl⟩ : syracuseStep 16530439 = 24795659) B24795659
theorem B5889131 : Blo 1289963 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B7355519 : Blo 1289963 7355519 := bstep (se 1 (by rfl) ⟨5516639, by rfl⟩ : syracuseStep 7355519 = 11033279) B11033279
theorem B9428951 : Blo 1289963 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B5587127 : Blo 1289963 5587127 := bstep (se 1 (by rfl) ⟨4190345, by rfl⟩ : syracuseStep 5587127 = 8380691) B8380691
theorem B14696639 : Blo 1289963 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B18850241 : Blo 1289963 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B4358663 : Blo 1289963 4358663 := bstep (se 1 (by rfl) ⟨3268997, by rfl⟩ : syracuseStep 4358663 = 6537995) B6537995
theorem B16548893 : Blo 1289963 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B6980699 : Blo 1289963 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B3926087 : Blo 1289963 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B27937331 : Blo 1289963 27937331 := bstep (se 1 (by rfl) ⟨20952998, by rfl⟩ : syracuseStep 27937331 = 41905997) B41905997
theorem B6285967 : Blo 1289963 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B7351145 : Blo 1289963 7351145 := bstep (se 2 (by rfl) ⟨2756679, by rfl⟩ : syracuseStep 7351145 = 5513359) B5513359
theorem B6983297 : Blo 1289963 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B1937051 : Blo 1289963 1937051 := bstep (se 1 (by rfl) ⟨1452788, by rfl⟩ : syracuseStep 1937051 = 2905577) B2905577
theorem B1290011 : Blo 1289963 1290011 := bstep (se 1 (by rfl) ⟨967508, by rfl⟩ : syracuseStep 1290011 = 1935017) B1935017
theorem B1937231 : Blo 1289963 1937231 := bstep (se 1 (by rfl) ⟨1452923, by rfl⟩ : syracuseStep 1937231 = 2905847) B2905847
theorem B22040585 : Blo 1289963 22040585 := bstep (se 2 (by rfl) ⟨8265219, by rfl⟩ : syracuseStep 22040585 = 16530439) B16530439
theorem B1290271 : Blo 1289963 1290271 := bstep (se 1 (by rfl) ⟨967703, by rfl⟩ : syracuseStep 1290271 = 1935407) B1935407
theorem B1290567 : Blo 1289963 1290567 := bstep (se 1 (by rfl) ⟨967925, by rfl⟩ : syracuseStep 1290567 = 1935851) B1935851
theorem B6533459 : Blo 1289963 6533459 := bstep (se 1 (by rfl) ⟨4900094, by rfl⟩ : syracuseStep 6533459 = 9800189) B9800189
theorem B4903679 : Blo 1289963 4903679 := bstep (se 1 (by rfl) ⟨3677759, by rfl⟩ : syracuseStep 4903679 = 7355519) B7355519
theorem B1291199 : Blo 1289963 1291199 := bstep (se 1 (by rfl) ⟨968399, by rfl⟩ : syracuseStep 1291199 = 1936799) B1936799
theorem B1291291 : Blo 1289963 1291291 := bstep (se 1 (by rfl) ⟨968468, by rfl⟩ : syracuseStep 1291291 = 1936937) B1936937
theorem B1291375 : Blo 1289963 1291375 := bstep (se 1 (by rfl) ⟨968531, by rfl⟩ : syracuseStep 1291375 = 1937063) B1937063
theorem B16544897 : Blo 1289963 16544897 := bstep (se 2 (by rfl) ⟨6204336, by rfl⟩ : syracuseStep 16544897 = 12408673) B12408673
theorem B7853483 : Blo 1289963 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B47076815 : Blo 1289963 47076815 := bstep (se 1 (by rfl) ⟨35307611, by rfl⟩ : syracuseStep 47076815 = 70615223) B70615223
theorem B7853851 : Blo 1289963 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B13957247 : Blo 1289963 13957247 := bstep (se 1 (by rfl) ⟨10467935, by rfl⟩ : syracuseStep 13957247 = 20935871) B20935871
theorem B4356449 : Blo 1289963 4356449 := bstep (se 2 (by rfl) ⟨1633668, by rfl⟩ : syracuseStep 4356449 = 3267337) B3267337
theorem B4356827 : Blo 1289963 4356827 := bstep (se 1 (by rfl) ⟨3267620, by rfl⟩ : syracuseStep 4356827 = 6535241) B6535241
theorem B4357151 : Blo 1289963 4357151 := bstep (se 1 (by rfl) ⟨3267863, by rfl⟩ : syracuseStep 4357151 = 6535727) B6535727
theorem B5233825 : Blo 1289963 5233825 := bstep (se 2 (by rfl) ⟨1962684, by rfl⟩ : syracuseStep 5233825 = 3925369) B3925369
theorem B6200495 : Blo 1289963 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B3677737 : Blo 1289963 3677737 := bstep (se 2 (by rfl) ⟨1379151, by rfl⟩ : syracuseStep 3677737 = 2758303) B2758303
theorem B6201299 : Blo 1289963 6201299 := bstep (se 1 (by rfl) ⟨4650974, by rfl⟩ : syracuseStep 6201299 = 9301949) B9301949
theorem B9797759 : Blo 1289963 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B12566827 : Blo 1289963 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B3269119 : Blo 1289963 3269119 := bstep (se 1 (by rfl) ⟨2451839, by rfl⟩ : syracuseStep 3269119 = 4903679) B4903679
theorem B4900763 : Blo 1289963 4900763 := bstep (se 1 (by rfl) ⟨3675572, by rfl⟩ : syracuseStep 4900763 = 7351145) B7351145
theorem B10471801 : Blo 1289963 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B4655531 : Blo 1289963 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B18615197 : Blo 1289963 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B11029931 : Blo 1289963 11029931 := bstep (se 1 (by rfl) ⟨8272448, by rfl⟩ : syracuseStep 11029931 = 16544897) B16544897
theorem B20942621 : Blo 1289963 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B125538173 : Blo 1289963 125538173 := bstep (se 3 (by rfl) ⟨23538407, by rfl⟩ : syracuseStep 125538173 = 47076815) B47076815
theorem B2617391 : Blo 1289963 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B2904299 : Blo 1289963 2904299 := bstep (se 1 (by rfl) ⟨2178224, by rfl⟩ : syracuseStep 2904299 = 4356449) B4356449
theorem B18624887 : Blo 1289963 18624887 := bstep (se 1 (by rfl) ⟨13968665, by rfl⟩ : syracuseStep 18624887 = 27937331) B27937331
theorem B2904551 : Blo 1289963 2904551 := bstep (se 1 (by rfl) ⟨2178413, by rfl⟩ : syracuseStep 2904551 = 4356827) B4356827
theorem B2904767 : Blo 1289963 2904767 := bstep (se 1 (by rfl) ⟨2178575, by rfl⟩ : syracuseStep 2904767 = 4357151) B4357151
theorem B4903649 : Blo 1289963 4903649 := bstep (se 2 (by rfl) ⟨1838868, by rfl⟩ : syracuseStep 4903649 = 3677737) B3677737
theorem B4133663 : Blo 1289963 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B1291367 : Blo 1289963 1291367 := bstep (se 1 (by rfl) ⟨968525, by rfl⟩ : syracuseStep 1291367 = 1937051) B1937051
theorem B16536797 : Blo 1289963 16536797 := bstep (se 3 (by rfl) ⟨3100649, by rfl⟩ : syracuseStep 16536797 = 6201299) B6201299
theorem B1291487 : Blo 1289963 1291487 := bstep (se 1 (by rfl) ⟨968615, by rfl⟩ : syracuseStep 1291487 = 1937231) B1937231
theorem B14693723 : Blo 1289963 14693723 := bstep (se 1 (by rfl) ⟨11020292, by rfl⟩ : syracuseStep 14693723 = 22040585) B22040585
theorem B3724751 : Blo 1289963 3724751 := bstep (se 1 (by rfl) ⟨2793563, by rfl⟩ : syracuseStep 3724751 = 5587127) B5587127
theorem B4355639 : Blo 1289963 4355639 := bstep (se 1 (by rfl) ⟨3266729, by rfl⟩ : syracuseStep 4355639 = 6533459) B6533459
theorem B134100629 : Blo 1289963 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B2905775 : Blo 1289963 2905775 := bstep (se 1 (by rfl) ⟨2179331, by rfl⟩ : syracuseStep 2905775 = 4358663) B4358663
theorem B11032595 : Blo 1289963 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B9304831 : Blo 1289963 9304831 := bstep (se 1 (by rfl) ⟨6978623, by rfl⟩ : syracuseStep 9304831 = 13957247) B13957247
theorem B6978433 : Blo 1289963 6978433 := bstep (se 2 (by rfl) ⟨2616912, by rfl⟩ : syracuseStep 6978433 = 5233825) B5233825
theorem B6979709 : Blo 1289963 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B3269099 : Blo 1289963 3269099 := bstep (se 1 (by rfl) ⟨2451824, by rfl⟩ : syracuseStep 3269099 = 4903649) B4903649
theorem B4358825 : Blo 1289963 4358825 := bstep (se 2 (by rfl) ⟨1634559, by rfl⟩ : syracuseStep 4358825 = 3269119) B3269119
theorem B2483167 : Blo 1289963 2483167 := bstep (se 1 (by rfl) ⟨1862375, by rfl⟩ : syracuseStep 2483167 = 3724751) B3724751
theorem B89400419 : Blo 1289963 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B13961747 : Blo 1289963 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B83692115 : Blo 1289963 83692115 := bstep (se 1 (by rfl) ⟨62769086, by rfl⟩ : syracuseStep 83692115 = 125538173) B125538173
theorem B6531839 : Blo 1289963 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B1936199 : Blo 1289963 1936199 := bstep (se 1 (by rfl) ⟨1452149, by rfl⟩ : syracuseStep 1936199 = 2904299) B2904299
theorem B1936367 : Blo 1289963 1936367 := bstep (se 1 (by rfl) ⟨1452275, by rfl⟩ : syracuseStep 1936367 = 2904551) B2904551
theorem B16755769 : Blo 1289963 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B1936511 : Blo 1289963 1936511 := bstep (se 1 (by rfl) ⟨1452383, by rfl⟩ : syracuseStep 1936511 = 2904767) B2904767
theorem B13962401 : Blo 1289963 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2755775 : Blo 1289963 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B12406441 : Blo 1289963 12406441 := bstep (se 2 (by rfl) ⟨4652415, by rfl⟩ : syracuseStep 12406441 = 9304831) B9304831
theorem B2903759 : Blo 1289963 2903759 := bstep (se 1 (by rfl) ⟨2177819, by rfl⟩ : syracuseStep 2903759 = 4355639) B4355639
theorem B1937183 : Blo 1289963 1937183 := bstep (se 1 (by rfl) ⟨1452887, by rfl⟩ : syracuseStep 1937183 = 2905775) B2905775
theorem B7353287 : Blo 1289963 7353287 := bstep (se 1 (by rfl) ⟨5514965, by rfl⟩ : syracuseStep 7353287 = 11029931) B11029931
theorem B49640525 : Blo 1289963 49640525 := bstep (se 3 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 49640525 = 18615197) B18615197
theorem B12416591 : Blo 1289963 12416591 := bstep (se 1 (by rfl) ⟨9312443, by rfl⟩ : syracuseStep 12416591 = 18624887) B18624887
theorem B11024531 : Blo 1289963 11024531 := bstep (se 1 (by rfl) ⟨8268398, by rfl⟩ : syracuseStep 11024531 = 16536797) B16536797
theorem B9795815 : Blo 1289963 9795815 := bstep (se 1 (by rfl) ⟨7346861, by rfl⟩ : syracuseStep 9795815 = 14693723) B14693723
theorem B9304577 : Blo 1289963 9304577 := bstep (se 2 (by rfl) ⟨3489216, by rfl⟩ : syracuseStep 9304577 = 6978433) B6978433
theorem B3267175 : Blo 1289963 3267175 := bstep (se 1 (by rfl) ⟨2450381, by rfl⟩ : syracuseStep 3267175 = 4900763) B4900763
theorem B7355063 : Blo 1289963 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B3103687 : Blo 1289963 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B4653139 : Blo 1289963 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B2179399 : Blo 1289963 2179399 := bstep (se 1 (by rfl) ⟨1634549, by rfl⟩ : syracuseStep 2179399 = 3269099) B3269099
theorem B4138249 : Blo 1289963 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B3310889 : Blo 1289963 3310889 := bstep (se 2 (by rfl) ⟨1241583, by rfl⟩ : syracuseStep 3310889 = 2483167) B2483167
theorem B22341025 : Blo 1289963 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B7349687 : Blo 1289963 7349687 := bstep (se 1 (by rfl) ⟨5512265, by rfl⟩ : syracuseStep 7349687 = 11024531) B11024531
theorem B6530543 : Blo 1289963 6530543 := bstep (se 1 (by rfl) ⟨4897907, by rfl⟩ : syracuseStep 6530543 = 9795815) B9795815
theorem B6203051 : Blo 1289963 6203051 := bstep (se 1 (by rfl) ⟨4652288, by rfl⟩ : syracuseStep 6203051 = 9304577) B9304577
theorem B9307831 : Blo 1289963 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B9308267 : Blo 1289963 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1837183 : Blo 1289963 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B16541921 : Blo 1289963 16541921 := bstep (se 2 (by rfl) ⟨6203220, by rfl⟩ : syracuseStep 16541921 = 12406441) B12406441
theorem B1935839 : Blo 1289963 1935839 := bstep (se 1 (by rfl) ⟨1451879, by rfl⟩ : syracuseStep 1935839 = 2903759) B2903759
theorem B4902191 : Blo 1289963 4902191 := bstep (se 1 (by rfl) ⟨3676643, by rfl⟩ : syracuseStep 4902191 = 7353287) B7353287
theorem B59600279 : Blo 1289963 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B8277727 : Blo 1289963 8277727 := bstep (se 1 (by rfl) ⟨6208295, by rfl⟩ : syracuseStep 8277727 = 12416591) B12416591
theorem B4903375 : Blo 1289963 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B4354559 : Blo 1289963 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B1290799 : Blo 1289963 1290799 := bstep (se 1 (by rfl) ⟨968099, by rfl⟩ : syracuseStep 1290799 = 1936199) B1936199
theorem B1290911 : Blo 1289963 1290911 := bstep (se 1 (by rfl) ⟨968183, by rfl⟩ : syracuseStep 1290911 = 1936367) B1936367
theorem B1291007 : Blo 1289963 1291007 := bstep (se 1 (by rfl) ⟨968255, by rfl⟩ : syracuseStep 1291007 = 1936511) B1936511
theorem B1291455 : Blo 1289963 1291455 := bstep (se 1 (by rfl) ⟨968591, by rfl⟩ : syracuseStep 1291455 = 1937183) B1937183
theorem B2905883 : Blo 1289963 2905883 := bstep (se 1 (by rfl) ⟨2179412, by rfl⟩ : syracuseStep 2905883 = 4358825) B4358825
theorem B33093683 : Blo 1289963 33093683 := bstep (se 1 (by rfl) ⟨24820262, by rfl⟩ : syracuseStep 33093683 = 49640525) B49640525
theorem B4356233 : Blo 1289963 4356233 := bstep (se 2 (by rfl) ⟨1633587, by rfl⟩ : syracuseStep 4356233 = 3267175) B3267175
theorem B55794743 : Blo 1289963 55794743 := bstep (se 1 (by rfl) ⟨41846057, by rfl⟩ : syracuseStep 55794743 = 83692115) B83692115
theorem B2449577 : Blo 1289963 2449577 := bstep (se 2 (by rfl) ⟨918591, by rfl⟩ : syracuseStep 2449577 = 1837183) B1837183
theorem B6537833 : Blo 1289963 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B4899791 : Blo 1289963 4899791 := bstep (se 1 (by rfl) ⟨3674843, by rfl⟩ : syracuseStep 4899791 = 7349687) B7349687
theorem B22062455 : Blo 1289963 22062455 := bstep (se 1 (by rfl) ⟨16546841, by rfl⟩ : syracuseStep 22062455 = 33093683) B33093683
theorem B11027947 : Blo 1289963 11027947 := bstep (se 1 (by rfl) ⟨8270960, by rfl⟩ : syracuseStep 11027947 = 16541921) B16541921
theorem B29788033 : Blo 1289963 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B39733519 : Blo 1289963 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B11036969 : Blo 1289963 11036969 := bstep (se 2 (by rfl) ⟨4138863, by rfl⟩ : syracuseStep 11036969 = 8277727) B8277727
theorem B6204185 : Blo 1289963 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B2903039 : Blo 1289963 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B4353695 : Blo 1289963 4353695 := bstep (se 1 (by rfl) ⟨3265271, by rfl⟩ : syracuseStep 4353695 = 6530543) B6530543
theorem B1937255 : Blo 1289963 1937255 := bstep (se 1 (by rfl) ⟨1452941, by rfl⟩ : syracuseStep 1937255 = 2905883) B2905883
theorem B6205511 : Blo 1289963 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B2904155 : Blo 1289963 2904155 := bstep (se 1 (by rfl) ⟨2178116, by rfl⟩ : syracuseStep 2904155 = 4356233) B4356233
theorem B1290559 : Blo 1289963 1290559 := bstep (se 1 (by rfl) ⟨967919, by rfl⟩ : syracuseStep 1290559 = 1935839) B1935839
theorem B5517665 : Blo 1289963 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B37196495 : Blo 1289963 37196495 := bstep (se 1 (by rfl) ⟨27897371, by rfl⟩ : syracuseStep 37196495 = 55794743) B55794743
theorem B2905865 : Blo 1289963 2905865 := bstep (se 2 (by rfl) ⟨1089699, by rfl⟩ : syracuseStep 2905865 = 2179399) B2179399
theorem B8829037 : Blo 1289963 8829037 := bstep (se 3 (by rfl) ⟨1655444, by rfl⟩ : syracuseStep 8829037 = 3310889) B3310889
theorem B4135367 : Blo 1289963 4135367 := bstep (se 1 (by rfl) ⟨3101525, by rfl⟩ : syracuseStep 4135367 = 6203051) B6203051
theorem B3268127 : Blo 1289963 3268127 := bstep (se 1 (by rfl) ⟨2451095, by rfl⟩ : syracuseStep 3268127 = 4902191) B4902191
theorem B12410441 : Blo 1289963 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B4137007 : Blo 1289963 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B11772049 : Blo 1289963 11772049 := bstep (se 2 (by rfl) ⟨4414518, by rfl⟩ : syracuseStep 11772049 = 8829037) B8829037
theorem B3678443 : Blo 1289963 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B52978025 : Blo 1289963 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B4358555 : Blo 1289963 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B24797663 : Blo 1289963 24797663 := bstep (se 1 (by rfl) ⟨18598247, by rfl⟩ : syracuseStep 24797663 = 37196495) B37196495
theorem B7357979 : Blo 1289963 7357979 := bstep (se 1 (by rfl) ⟨5518484, by rfl⟩ : syracuseStep 7357979 = 11036969) B11036969
theorem B1935359 : Blo 1289963 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B2902463 : Blo 1289963 2902463 := bstep (se 1 (by rfl) ⟨2176847, by rfl⟩ : syracuseStep 2902463 = 4353695) B4353695
theorem B39717377 : Blo 1289963 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B1936103 : Blo 1289963 1936103 := bstep (se 1 (by rfl) ⟨1452077, by rfl⟩ : syracuseStep 1936103 = 2904155) B2904155
theorem B1633051 : Blo 1289963 1633051 := bstep (se 1 (by rfl) ⟨1224788, by rfl⟩ : syracuseStep 1633051 = 2449577) B2449577
theorem B14708303 : Blo 1289963 14708303 := bstep (se 1 (by rfl) ⟨11031227, by rfl⟩ : syracuseStep 14708303 = 22062455) B22062455
theorem B1937243 : Blo 1289963 1937243 := bstep (se 1 (by rfl) ⟨1452932, by rfl⟩ : syracuseStep 1937243 = 2905865) B2905865
theorem B2756911 : Blo 1289963 2756911 := bstep (se 1 (by rfl) ⟨2067683, by rfl⟩ : syracuseStep 2756911 = 4135367) B4135367
theorem B1291503 : Blo 1289963 1291503 := bstep (se 1 (by rfl) ⟨968627, by rfl⟩ : syracuseStep 1291503 = 1937255) B1937255
theorem B3266527 : Blo 1289963 3266527 := bstep (se 1 (by rfl) ⟨2449895, by rfl⟩ : syracuseStep 3266527 = 4899791) B4899791
theorem B4136123 : Blo 1289963 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B14703929 : Blo 1289963 14703929 := bstep (se 2 (by rfl) ⟨5513973, by rfl⟩ : syracuseStep 14703929 = 11027947) B11027947
theorem B2178751 : Blo 1289963 2178751 := bstep (se 1 (by rfl) ⟨1634063, by rfl⟩ : syracuseStep 2178751 = 3268127) B3268127
theorem B8273627 : Blo 1289963 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B15696065 : Blo 1289963 15696065 := bstep (se 2 (by rfl) ⟨5886024, by rfl⟩ : syracuseStep 15696065 = 11772049) B11772049
theorem B16531775 : Blo 1289963 16531775 := bstep (se 1 (by rfl) ⟨12398831, by rfl⟩ : syracuseStep 16531775 = 24797663) B24797663
theorem B1934975 : Blo 1289963 1934975 := bstep (se 1 (by rfl) ⟨1451231, by rfl⟩ : syracuseStep 1934975 = 2902463) B2902463
theorem B26478251 : Blo 1289963 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B5515751 : Blo 1289963 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B5516009 : Blo 1289963 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B2452295 : Blo 1289963 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B35318683 : Blo 1289963 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B1290239 : Blo 1289963 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B1290735 : Blo 1289963 1290735 := bstep (se 1 (by rfl) ⟨968051, by rfl⟩ : syracuseStep 1290735 = 1936103) B1936103
theorem B2757415 : Blo 1289963 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B9802619 : Blo 1289963 9802619 := bstep (se 1 (by rfl) ⟨7351964, by rfl⟩ : syracuseStep 9802619 = 14703929) B14703929
theorem B2905001 : Blo 1289963 2905001 := bstep (se 2 (by rfl) ⟨1089375, by rfl⟩ : syracuseStep 2905001 = 2178751) B2178751
theorem B1291495 : Blo 1289963 1291495 := bstep (se 1 (by rfl) ⟨968621, by rfl⟩ : syracuseStep 1291495 = 1937243) B1937243
theorem B4355369 : Blo 1289963 4355369 := bstep (se 2 (by rfl) ⟨1633263, by rfl⟩ : syracuseStep 4355369 = 3266527) B3266527
theorem B2905703 : Blo 1289963 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B3675881 : Blo 1289963 3675881 := bstep (se 2 (by rfl) ⟨1378455, by rfl⟩ : syracuseStep 3675881 = 2756911) B2756911
theorem B4905319 : Blo 1289963 4905319 := bstep (se 1 (by rfl) ⟨3678989, by rfl⟩ : syracuseStep 4905319 = 7357979) B7357979
theorem B2177401 : Blo 1289963 2177401 := bstep (se 2 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 2177401 = 1633051) B1633051
theorem B9805535 : Blo 1289963 9805535 := bstep (se 1 (by rfl) ⟨7354151, by rfl⟩ : syracuseStep 9805535 = 14708303) B14708303
theorem B2450587 : Blo 1289963 2450587 := bstep (se 1 (by rfl) ⟨1837940, by rfl⟩ : syracuseStep 2450587 = 3675881) B3675881
theorem B6539453 : Blo 1289963 6539453 := bstep (se 3 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 6539453 = 2452295) B2452295
theorem B11021183 : Blo 1289963 11021183 := bstep (se 1 (by rfl) ⟨8265887, by rfl⟩ : syracuseStep 11021183 = 16531775) B16531775
theorem B6540425 : Blo 1289963 6540425 := bstep (se 2 (by rfl) ⟨2452659, by rfl⟩ : syracuseStep 6540425 = 4905319) B4905319
theorem B2903201 : Blo 1289963 2903201 := bstep (se 2 (by rfl) ⟨1088700, by rfl⟩ : syracuseStep 2903201 = 2177401) B2177401
theorem B41856173 : Blo 1289963 41856173 := bstep (se 3 (by rfl) ⟨7848032, by rfl⟩ : syracuseStep 41856173 = 15696065) B15696065
theorem B1936667 : Blo 1289963 1936667 := bstep (se 1 (by rfl) ⟨1452500, by rfl⟩ : syracuseStep 1936667 = 2905001) B2905001
theorem B2903579 : Blo 1289963 2903579 := bstep (se 1 (by rfl) ⟨2177684, by rfl⟩ : syracuseStep 2903579 = 4355369) B4355369
theorem B1937135 : Blo 1289963 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B1289983 : Blo 1289963 1289983 := bstep (se 1 (by rfl) ⟨967487, by rfl⟩ : syracuseStep 1289983 = 1934975) B1934975
theorem B47091577 : Blo 1289963 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B6535079 : Blo 1289963 6535079 := bstep (se 1 (by rfl) ⟨4901309, by rfl⟩ : syracuseStep 6535079 = 9802619) B9802619
theorem B3676553 : Blo 1289963 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B17652167 : Blo 1289963 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B3677167 : Blo 1289963 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B3677339 : Blo 1289963 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B6537023 : Blo 1289963 6537023 := bstep (se 1 (by rfl) ⟨4902767, by rfl⟩ : syracuseStep 6537023 = 9805535) B9805535
theorem B4359635 : Blo 1289963 4359635 := bstep (se 1 (by rfl) ⟨3269726, by rfl⟩ : syracuseStep 4359635 = 6539453) B6539453
theorem B2451035 : Blo 1289963 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B4360283 : Blo 1289963 4360283 := bstep (se 1 (by rfl) ⟨3270212, by rfl⟩ : syracuseStep 4360283 = 6540425) B6540425
theorem B2451559 : Blo 1289963 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B1935467 : Blo 1289963 1935467 := bstep (se 1 (by rfl) ⟨1451600, by rfl⟩ : syracuseStep 1935467 = 2903201) B2903201
theorem B27904115 : Blo 1289963 27904115 := bstep (se 1 (by rfl) ⟨20928086, by rfl⟩ : syracuseStep 27904115 = 41856173) B41856173
theorem B1935719 : Blo 1289963 1935719 := bstep (se 1 (by rfl) ⟨1451789, by rfl⟩ : syracuseStep 1935719 = 2903579) B2903579
theorem B4902889 : Blo 1289963 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B11768111 : Blo 1289963 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B1291111 : Blo 1289963 1291111 := bstep (se 1 (by rfl) ⟨968333, by rfl⟩ : syracuseStep 1291111 = 1936667) B1936667
theorem B1291423 : Blo 1289963 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B62788769 : Blo 1289963 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B4356719 : Blo 1289963 4356719 := bstep (se 1 (by rfl) ⟨3267539, by rfl⟩ : syracuseStep 4356719 = 6535079) B6535079
theorem B3267449 : Blo 1289963 3267449 := bstep (se 2 (by rfl) ⟨1225293, by rfl⟩ : syracuseStep 3267449 = 2450587) B2450587
theorem B7347455 : Blo 1289963 7347455 := bstep (se 1 (by rfl) ⟨5510591, by rfl⟩ : syracuseStep 7347455 = 11021183) B11021183
theorem B4358015 : Blo 1289963 4358015 := bstep (se 1 (by rfl) ⟨3268511, by rfl⟩ : syracuseStep 4358015 = 6537023) B6537023
theorem B3268745 : Blo 1289963 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B1634023 : Blo 1289963 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B1290311 : Blo 1289963 1290311 := bstep (se 1 (by rfl) ⟨967733, by rfl⟩ : syracuseStep 1290311 = 1935467) B1935467
theorem B1290479 : Blo 1289963 1290479 := bstep (se 1 (by rfl) ⟨967859, by rfl⟩ : syracuseStep 1290479 = 1935719) B1935719
theorem B2904479 : Blo 1289963 2904479 := bstep (se 1 (by rfl) ⟨2178359, by rfl⟩ : syracuseStep 2904479 = 4356719) B4356719
theorem B2905343 : Blo 1289963 2905343 := bstep (se 1 (by rfl) ⟨2179007, by rfl⟩ : syracuseStep 2905343 = 4358015) B4358015
theorem B7845407 : Blo 1289963 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B41859179 : Blo 1289963 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B2906423 : Blo 1289963 2906423 := bstep (se 1 (by rfl) ⟨2179817, by rfl⟩ : syracuseStep 2906423 = 4359635) B4359635
theorem B2906855 : Blo 1289963 2906855 := bstep (se 1 (by rfl) ⟨2180141, by rfl⟩ : syracuseStep 2906855 = 4360283) B4360283
theorem B18602743 : Blo 1289963 18602743 := bstep (se 1 (by rfl) ⟨13952057, by rfl⟩ : syracuseStep 18602743 = 27904115) B27904115
theorem B2178299 : Blo 1289963 2178299 := bstep (se 1 (by rfl) ⟨1633724, by rfl⟩ : syracuseStep 2178299 = 3267449) B3267449
theorem B4898303 : Blo 1289963 4898303 := bstep (se 1 (by rfl) ⟨3673727, by rfl⟩ : syracuseStep 4898303 = 7347455) B7347455
theorem B6537185 : Blo 1289963 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B2179163 : Blo 1289963 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B1452199 : Blo 1289963 1452199 := bstep (se 1 (by rfl) ⟨1089149, by rfl⟩ : syracuseStep 1452199 = 2178299) B2178299
theorem B1936319 : Blo 1289963 1936319 := bstep (se 1 (by rfl) ⟨1452239, by rfl⟩ : syracuseStep 1936319 = 2904479) B2904479
theorem B1936895 : Blo 1289963 1936895 := bstep (se 1 (by rfl) ⟨1452671, by rfl⟩ : syracuseStep 1936895 = 2905343) B2905343
theorem B5230271 : Blo 1289963 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B27906119 : Blo 1289963 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B1937615 : Blo 1289963 1937615 := bstep (se 1 (by rfl) ⟨1453211, by rfl⟩ : syracuseStep 1937615 = 2906423) B2906423
theorem B1937903 : Blo 1289963 1937903 := bstep (se 1 (by rfl) ⟨1453427, by rfl⟩ : syracuseStep 1937903 = 2906855) B2906855
theorem B3265535 : Blo 1289963 3265535 := bstep (se 1 (by rfl) ⟨2449151, by rfl⟩ : syracuseStep 3265535 = 4898303) B4898303
theorem B24803657 : Blo 1289963 24803657 := bstep (se 2 (by rfl) ⟨9301371, by rfl⟩ : syracuseStep 24803657 = 18602743) B18602743
theorem B2178697 : Blo 1289963 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B4358123 : Blo 1289963 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B18604079 : Blo 1289963 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B1452775 : Blo 1289963 1452775 := bstep (se 1 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 1452775 = 2179163) B2179163
theorem B1936265 : Blo 1289963 1936265 := bstep (se 2 (by rfl) ⟨726099, by rfl⟩ : syracuseStep 1936265 = 1452199) B1452199
theorem B16535771 : Blo 1289963 16535771 := bstep (se 1 (by rfl) ⟨12401828, by rfl⟩ : syracuseStep 16535771 = 24803657) B24803657
theorem B13947389 : Blo 1289963 13947389 := bstep (se 3 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 13947389 = 5230271) B5230271
theorem B1290879 : Blo 1289963 1290879 := bstep (se 1 (by rfl) ⟨968159, by rfl⟩ : syracuseStep 1290879 = 1936319) B1936319
theorem B2904929 : Blo 1289963 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B1291263 : Blo 1289963 1291263 := bstep (se 1 (by rfl) ⟨968447, by rfl⟩ : syracuseStep 1291263 = 1936895) B1936895
theorem B2905415 : Blo 1289963 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B1291743 : Blo 1289963 1291743 := bstep (se 1 (by rfl) ⟨968807, by rfl⟩ : syracuseStep 1291743 = 1937615) B1937615
theorem B1291935 : Blo 1289963 1291935 := bstep (se 1 (by rfl) ⟨968951, by rfl⟩ : syracuseStep 1291935 = 1937903) B1937903
theorem B2177023 : Blo 1289963 2177023 := bstep (se 1 (by rfl) ⟨1632767, by rfl⟩ : syracuseStep 2177023 = 3265535) B3265535
theorem B12402719 : Blo 1289963 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B9298259 : Blo 1289963 9298259 := bstep (se 1 (by rfl) ⟨6973694, by rfl⟩ : syracuseStep 9298259 = 13947389) B13947389
theorem B2902697 : Blo 1289963 2902697 := bstep (se 2 (by rfl) ⟨1088511, by rfl⟩ : syracuseStep 2902697 = 2177023) B2177023
theorem B1936619 : Blo 1289963 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1936943 : Blo 1289963 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B1937033 : Blo 1289963 1937033 := bstep (se 2 (by rfl) ⟨726387, by rfl⟩ : syracuseStep 1937033 = 1452775) B1452775
theorem B1290843 : Blo 1289963 1290843 := bstep (se 1 (by rfl) ⟨968132, by rfl⟩ : syracuseStep 1290843 = 1936265) B1936265
theorem B11023847 : Blo 1289963 11023847 := bstep (se 1 (by rfl) ⟨8267885, by rfl⟩ : syracuseStep 11023847 = 16535771) B16535771
theorem B7349231 : Blo 1289963 7349231 := bstep (se 1 (by rfl) ⟨5511923, by rfl⟩ : syracuseStep 7349231 = 11023847) B11023847
theorem B1935131 : Blo 1289963 1935131 := bstep (se 1 (by rfl) ⟨1451348, by rfl⟩ : syracuseStep 1935131 = 2902697) B2902697
theorem B8268479 : Blo 1289963 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B1291079 : Blo 1289963 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B1291295 : Blo 1289963 1291295 := bstep (se 1 (by rfl) ⟨968471, by rfl⟩ : syracuseStep 1291295 = 1936943) B1936943
theorem B1291355 : Blo 1289963 1291355 := bstep (se 1 (by rfl) ⟨968516, by rfl⟩ : syracuseStep 1291355 = 1937033) B1937033
theorem B6198839 : Blo 1289963 6198839 := bstep (se 1 (by rfl) ⟨4649129, by rfl⟩ : syracuseStep 6198839 = 9298259) B9298259
theorem B4899487 : Blo 1289963 4899487 := bstep (se 1 (by rfl) ⟨3674615, by rfl⟩ : syracuseStep 4899487 = 7349231) B7349231
theorem B4132559 : Blo 1289963 4132559 := bstep (se 1 (by rfl) ⟨3099419, by rfl⟩ : syracuseStep 4132559 = 6198839) B6198839
theorem B1290087 : Blo 1289963 1290087 := bstep (se 1 (by rfl) ⟨967565, by rfl⟩ : syracuseStep 1290087 = 1935131) B1935131
theorem B5512319 : Blo 1289963 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B11020157 : Blo 1289963 11020157 := bstep (se 3 (by rfl) ⟨2066279, by rfl⟩ : syracuseStep 11020157 = 4132559) B4132559
theorem B6532649 : Blo 1289963 6532649 := bstep (se 2 (by rfl) ⟨2449743, by rfl⟩ : syracuseStep 6532649 = 4899487) B4899487
theorem B3674879 : Blo 1289963 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B2449919 : Blo 1289963 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B4355099 : Blo 1289963 4355099 := bstep (se 1 (by rfl) ⟨3266324, by rfl⟩ : syracuseStep 4355099 = 6532649) B6532649
theorem B7346771 : Blo 1289963 7346771 := bstep (se 1 (by rfl) ⟨5510078, by rfl⟩ : syracuseStep 7346771 = 11020157) B11020157
theorem B1633279 : Blo 1289963 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B2903399 : Blo 1289963 2903399 := bstep (se 1 (by rfl) ⟨2177549, by rfl⟩ : syracuseStep 2903399 = 4355099) B4355099
theorem B4897847 : Blo 1289963 4897847 := bstep (se 1 (by rfl) ⟨3673385, by rfl⟩ : syracuseStep 4897847 = 7346771) B7346771
theorem B1935599 : Blo 1289963 1935599 := bstep (se 1 (by rfl) ⟨1451699, by rfl⟩ : syracuseStep 1935599 = 2903399) B2903399
theorem B3265231 : Blo 1289963 3265231 := bstep (se 1 (by rfl) ⟨2448923, by rfl⟩ : syracuseStep 3265231 = 4897847) B4897847
theorem B2177705 : Blo 1289963 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B1451803 : Blo 1289963 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B4353641 : Blo 1289963 4353641 := bstep (se 2 (by rfl) ⟨1632615, by rfl⟩ : syracuseStep 4353641 = 3265231) B3265231
theorem B1290399 : Blo 1289963 1290399 := bstep (se 1 (by rfl) ⟨967799, by rfl⟩ : syracuseStep 1290399 = 1935599) B1935599
theorem B1935737 : Blo 1289963 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B2902427 : Blo 1289963 2902427 := bstep (se 1 (by rfl) ⟨2176820, by rfl⟩ : syracuseStep 2902427 = 4353641) B4353641
theorem B1934951 : Blo 1289963 1934951 := bstep (se 1 (by rfl) ⟨1451213, by rfl⟩ : syracuseStep 1934951 = 2902427) B2902427
theorem B1290491 : Blo 1289963 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B1289967 : Blo 1289963 1289967 := bstep (se 1 (by rfl) ⟨967475, by rfl⟩ : syracuseStep 1289967 = 1934951) B1934951

theorem C0 (j : ℕ) (h1 : 322490 ≤ j) (h2 : j ≤ 322990) : Blo 1289963 (4 * j + 3) := by
  interval_cases j
  · exact B1289963
  · exact B1289967
  · exact B1289971
  · exact B1289975
  · exact B1289979
  · exact B1289983
  · exact B1289987
  · exact B1289991
  · exact B1289995
  · exact B1289999
  · exact B1290003
  · exact B1290007
  · exact B1290011
  · exact B1290015
  · exact B1290019
  · exact B1290023
  · exact B1290027
  · exact B1290031
  · exact B1290035
  · exact B1290039
  · exact B1290043
  · exact B1290047
  · exact B1290051
  · exact B1290055
  · exact B1290059
  · exact B1290063
  · exact B1290067
  · exact B1290071
  · exact B1290075
  · exact B1290079
  · exact B1290083
  · exact B1290087
  · exact B1290091
  · exact B1290095
  · exact B1290099
  · exact B1290103
  · exact B1290107
  · exact B1290111
  · exact B1290115
  · exact B1290119
  · exact B1290123
  · exact B1290127
  · exact B1290131
  · exact B1290135
  · exact B1290139
  · exact B1290143
  · exact B1290147
  · exact B1290151
  · exact B1290155
  · exact B1290159
  · exact B1290163
  · exact B1290167
  · exact B1290171
  · exact B1290175
  · exact B1290179
  · exact B1290183
  · exact B1290187
  · exact B1290191
  · exact B1290195
  · exact B1290199
  · exact B1290203
  · exact B1290207
  · exact B1290211
  · exact B1290215
  · exact B1290219
  · exact B1290223
  · exact B1290227
  · exact B1290231
  · exact B1290235
  · exact B1290239
  · exact B1290243
  · exact B1290247
  · exact B1290251
  · exact B1290255
  · exact B1290259
  · exact B1290263
  · exact B1290267
  · exact B1290271
  · exact B1290275
  · exact B1290279
  · exact B1290283
  · exact B1290287
  · exact B1290291
  · exact B1290295
  · exact B1290299
  · exact B1290303
  · exact B1290307
  · exact B1290311
  · exact B1290315
  · exact B1290319
  · exact B1290323
  · exact B1290327
  · exact B1290331
  · exact B1290335
  · exact B1290339
  · exact B1290343
  · exact B1290347
  · exact B1290351
  · exact B1290355
  · exact B1290359
  · exact B1290363
  · exact B1290367
  · exact B1290371
  · exact B1290375
  · exact B1290379
  · exact B1290383
  · exact B1290387
  · exact B1290391
  · exact B1290395
  · exact B1290399
  · exact B1290403
  · exact B1290407
  · exact B1290411
  · exact B1290415
  · exact B1290419
  · exact B1290423
  · exact B1290427
  · exact B1290431
  · exact B1290435
  · exact B1290439
  · exact B1290443
  · exact B1290447
  · exact B1290451
  · exact B1290455
  · exact B1290459
  · exact B1290463
  · exact B1290467
  · exact B1290471
  · exact B1290475
  · exact B1290479
  · exact B1290483
  · exact B1290487
  · exact B1290491
  · exact B1290495
  · exact B1290499
  · exact B1290503
  · exact B1290507
  · exact B1290511
  · exact B1290515
  · exact B1290519
  · exact B1290523
  · exact B1290527
  · exact B1290531
  · exact B1290535
  · exact B1290539
  · exact B1290543
  · exact B1290547
  · exact B1290551
  · exact B1290555
  · exact B1290559
  · exact B1290563
  · exact B1290567
  · exact B1290571
  · exact B1290575
  · exact B1290579
  · exact B1290583
  · exact B1290587
  · exact B1290591
  · exact B1290595
  · exact B1290599
  · exact B1290603
  · exact B1290607
  · exact B1290611
  · exact B1290615
  · exact B1290619
  · exact B1290623
  · exact B1290627
  · exact B1290631
  · exact B1290635
  · exact B1290639
  · exact B1290643
  · exact B1290647
  · exact B1290651
  · exact B1290655
  · exact B1290659
  · exact B1290663
  · exact B1290667
  · exact B1290671
  · exact B1290675
  · exact B1290679
  · exact B1290683
  · exact B1290687
  · exact B1290691
  · exact B1290695
  · exact B1290699
  · exact B1290703
  · exact B1290707
  · exact B1290711
  · exact B1290715
  · exact B1290719
  · exact B1290723
  · exact B1290727
  · exact B1290731
  · exact B1290735
  · exact B1290739
  · exact B1290743
  · exact B1290747
  · exact B1290751
  · exact B1290755
  · exact B1290759
  · exact B1290763
  · exact B1290767
  · exact B1290771
  · exact B1290775
  · exact B1290779
  · exact B1290783
  · exact B1290787
  · exact B1290791
  · exact B1290795
  · exact B1290799
  · exact B1290803
  · exact B1290807
  · exact B1290811
  · exact B1290815
  · exact B1290819
  · exact B1290823
  · exact B1290827
  · exact B1290831
  · exact B1290835
  · exact B1290839
  · exact B1290843
  · exact B1290847
  · exact B1290851
  · exact B1290855
  · exact B1290859
  · exact B1290863
  · exact B1290867
  · exact B1290871
  · exact B1290875
  · exact B1290879
  · exact B1290883
  · exact B1290887
  · exact B1290891
  · exact B1290895
  · exact B1290899
  · exact B1290903
  · exact B1290907
  · exact B1290911
  · exact B1290915
  · exact B1290919
  · exact B1290923
  · exact B1290927
  · exact B1290931
  · exact B1290935
  · exact B1290939
  · exact B1290943
  · exact B1290947
  · exact B1290951
  · exact B1290955
  · exact B1290959
  · exact B1290963
  · exact B1290967
  · exact B1290971
  · exact B1290975
  · exact B1290979
  · exact B1290983
  · exact B1290987
  · exact B1290991
  · exact B1290995
  · exact B1290999
  · exact B1291003
  · exact B1291007
  · exact B1291011
  · exact B1291015
  · exact B1291019
  · exact B1291023
  · exact B1291027
  · exact B1291031
  · exact B1291035
  · exact B1291039
  · exact B1291043
  · exact B1291047
  · exact B1291051
  · exact B1291055
  · exact B1291059
  · exact B1291063
  · exact B1291067
  · exact B1291071
  · exact B1291075
  · exact B1291079
  · exact B1291083
  · exact B1291087
  · exact B1291091
  · exact B1291095
  · exact B1291099
  · exact B1291103
  · exact B1291107
  · exact B1291111
  · exact B1291115
  · exact B1291119
  · exact B1291123
  · exact B1291127
  · exact B1291131
  · exact B1291135
  · exact B1291139
  · exact B1291143
  · exact B1291147
  · exact B1291151
  · exact B1291155
  · exact B1291159
  · exact B1291163
  · exact B1291167
  · exact B1291171
  · exact B1291175
  · exact B1291179
  · exact B1291183
  · exact B1291187
  · exact B1291191
  · exact B1291195
  · exact B1291199
  · exact B1291203
  · exact B1291207
  · exact B1291211
  · exact B1291215
  · exact B1291219
  · exact B1291223
  · exact B1291227
  · exact B1291231
  · exact B1291235
  · exact B1291239
  · exact B1291243
  · exact B1291247
  · exact B1291251
  · exact B1291255
  · exact B1291259
  · exact B1291263
  · exact B1291267
  · exact B1291271
  · exact B1291275
  · exact B1291279
  · exact B1291283
  · exact B1291287
  · exact B1291291
  · exact B1291295
  · exact B1291299
  · exact B1291303
  · exact B1291307
  · exact B1291311
  · exact B1291315
  · exact B1291319
  · exact B1291323
  · exact B1291327
  · exact B1291331
  · exact B1291335
  · exact B1291339
  · exact B1291343
  · exact B1291347
  · exact B1291351
  · exact B1291355
  · exact B1291359
  · exact B1291363
  · exact B1291367
  · exact B1291371
  · exact B1291375
  · exact B1291379
  · exact B1291383
  · exact B1291387
  · exact B1291391
  · exact B1291395
  · exact B1291399
  · exact B1291403
  · exact B1291407
  · exact B1291411
  · exact B1291415
  · exact B1291419
  · exact B1291423
  · exact B1291427
  · exact B1291431
  · exact B1291435
  · exact B1291439
  · exact B1291443
  · exact B1291447
  · exact B1291451
  · exact B1291455
  · exact B1291459
  · exact B1291463
  · exact B1291467
  · exact B1291471
  · exact B1291475
  · exact B1291479
  · exact B1291483
  · exact B1291487
  · exact B1291491
  · exact B1291495
  · exact B1291499
  · exact B1291503
  · exact B1291507
  · exact B1291511
  · exact B1291515
  · exact B1291519
  · exact B1291523
  · exact B1291527
  · exact B1291531
  · exact B1291535
  · exact B1291539
  · exact B1291543
  · exact B1291547
  · exact B1291551
  · exact B1291555
  · exact B1291559
  · exact B1291563
  · exact B1291567
  · exact B1291571
  · exact B1291575
  · exact B1291579
  · exact B1291583
  · exact B1291587
  · exact B1291591
  · exact B1291595
  · exact B1291599
  · exact B1291603
  · exact B1291607
  · exact B1291611
  · exact B1291615
  · exact B1291619
  · exact B1291623
  · exact B1291627
  · exact B1291631
  · exact B1291635
  · exact B1291639
  · exact B1291643
  · exact B1291647
  · exact B1291651
  · exact B1291655
  · exact B1291659
  · exact B1291663
  · exact B1291667
  · exact B1291671
  · exact B1291675
  · exact B1291679
  · exact B1291683
  · exact B1291687
  · exact B1291691
  · exact B1291695
  · exact B1291699
  · exact B1291703
  · exact B1291707
  · exact B1291711
  · exact B1291715
  · exact B1291719
  · exact B1291723
  · exact B1291727
  · exact B1291731
  · exact B1291735
  · exact B1291739
  · exact B1291743
  · exact B1291747
  · exact B1291751
  · exact B1291755
  · exact B1291759
  · exact B1291763
  · exact B1291767
  · exact B1291771
  · exact B1291775
  · exact B1291779
  · exact B1291783
  · exact B1291787
  · exact B1291791
  · exact B1291795
  · exact B1291799
  · exact B1291803
  · exact B1291807
  · exact B1291811
  · exact B1291815
  · exact B1291819
  · exact B1291823
  · exact B1291827
  · exact B1291831
  · exact B1291835
  · exact B1291839
  · exact B1291843
  · exact B1291847
  · exact B1291851
  · exact B1291855
  · exact B1291859
  · exact B1291863
  · exact B1291867
  · exact B1291871
  · exact B1291875
  · exact B1291879
  · exact B1291883
  · exact B1291887
  · exact B1291891
  · exact B1291895
  · exact B1291899
  · exact B1291903
  · exact B1291907
  · exact B1291911
  · exact B1291915
  · exact B1291919
  · exact B1291923
  · exact B1291927
  · exact B1291931
  · exact B1291935
  · exact B1291939
  · exact B1291943
  · exact B1291947
  · exact B1291951
  · exact B1291955
  · exact B1291959
  · exact B1291963

theorem solution (m : ℕ) (hlo : 1289963 ≤ m) (hhi : m ≤ 1291963) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 322490 ≤ j := by omega
    have hj2 : j ≤ 322990 := by omega
    have hb : Blo 1289963 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
