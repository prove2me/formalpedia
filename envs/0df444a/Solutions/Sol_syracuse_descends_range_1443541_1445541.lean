-- Prove2me | solution 1 for syracuse_descends_range_1443541_1445541
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:57.292976+00:00
-- url     : https://prove2.me/submissions/8a591866-1b4e-4b68-bdfb-2c3cdb070e6c

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


theorem B2056213 : Blo 1443541 2056213 := bbase (se 6 (by rfl) ⟨48192, by rfl⟩ : syracuseStep 2056213 = 96385) (by norm_num)
theorem B4874309 : Blo 1443541 4874309 := bbase (se 4 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 4874309 = 913933) (by norm_num)
theorem B3252293 : Blo 1443541 3252293 := bbase (se 4 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 3252293 = 609805) (by norm_num)
theorem B3252365 : Blo 1443541 3252365 := bbase (se 3 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 3252365 = 1219637) (by norm_num)
theorem B3252437 : Blo 1443541 3252437 := bbase (se 7 (by rfl) ⟨38114, by rfl⟩ : syracuseStep 3252437 = 76229) (by norm_num)
theorem B4940021 : Blo 1443541 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B1827137 : Blo 1443541 1827137 := bbase (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) (by norm_num)
theorem B3653981 : Blo 1443541 3653981 := bbase (se 3 (by rfl) ⟨685121, by rfl⟩ : syracuseStep 3653981 = 1370243) (by norm_num)
theorem B1827193 : Blo 1443541 1827193 := bbase (se 2 (by rfl) ⟨685197, by rfl⟩ : syracuseStep 1827193 = 1370395) (by norm_num)
theorem B1647029 : Blo 1443541 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B29630933 : Blo 1443541 29630933 := bbase (se 7 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 29630933 = 694475) (by norm_num)
theorem B1827289 : Blo 1443541 1827289 := bbase (se 2 (by rfl) ⟨685233, by rfl⟩ : syracuseStep 1827289 = 1370467) (by norm_num)
theorem B4874741 : Blo 1443541 4874741 := bbase (se 5 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 4874741 = 457007) (by norm_num)
theorem B3654173 : Blo 1443541 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B1827461 : Blo 1443541 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B1827517 : Blo 1443541 1827517 := bbase (se 3 (by rfl) ⟨342659, by rfl⟩ : syracuseStep 1827517 = 685319) (by norm_num)
theorem B4113109 : Blo 1443541 4113109 := bbase (se 7 (by rfl) ⟨48200, by rfl⟩ : syracuseStep 4113109 = 96401) (by norm_num)
theorem B2196229 : Blo 1443541 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B1827613 : Blo 1443541 1827613 := bbase (se 3 (by rfl) ⟨342677, by rfl⟩ : syracuseStep 1827613 = 685355) (by norm_num)
theorem B2057005 : Blo 1443541 2057005 := bbase (se 3 (by rfl) ⟨385688, by rfl⟩ : syracuseStep 2057005 = 771377) (by norm_num)
theorem B8790869 : Blo 1443541 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B2196325 : Blo 1443541 2196325 := bbase (se 4 (by rfl) ⟨205905, by rfl⟩ : syracuseStep 2196325 = 411811) (by norm_num)
theorem B3654517 : Blo 1443541 3654517 := bbase (se 5 (by rfl) ⟨171305, by rfl⟩ : syracuseStep 3654517 = 342611) (by norm_num)
theorem B4875173 : Blo 1443541 4875173 := bbase (se 4 (by rfl) ⟨457047, by rfl⟩ : syracuseStep 4875173 = 914095) (by norm_num)
theorem B7316405 : Blo 1443541 7316405 := bbase (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) (by norm_num)
theorem B1827785 : Blo 1443541 1827785 := bbase (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) (by norm_num)
theorem B3654629 : Blo 1443541 3654629 := bbase (se 4 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 3654629 = 685243) (by norm_num)
theorem B1827841 : Blo 1443541 1827841 := bbase (se 2 (by rfl) ⟨685440, by rfl⟩ : syracuseStep 1827841 = 1370881) (by norm_num)
theorem B1827937 : Blo 1443541 1827937 := bbase (se 2 (by rfl) ⟨685476, by rfl⟩ : syracuseStep 1827937 = 1370953) (by norm_num)
theorem B2344061 : Blo 1443541 2344061 := bbase (se 3 (by rfl) ⟨439511, by rfl⟩ : syracuseStep 2344061 = 879023) (by norm_num)
theorem B2057341 : Blo 1443541 2057341 := bbase (se 3 (by rfl) ⟨385751, by rfl⟩ : syracuseStep 2057341 = 771503) (by norm_num)
theorem B6169733 : Blo 1443541 6169733 := bbase (se 4 (by rfl) ⟨578412, by rfl⟩ : syracuseStep 6169733 = 1156825) (by norm_num)
theorem B3654821 : Blo 1443541 3654821 := bbase (se 4 (by rfl) ⟨342639, by rfl⟩ : syracuseStep 3654821 = 685279) (by norm_num)
theorem B5481701 : Blo 1443541 5481701 := bbase (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) (by norm_num)
theorem B1828109 : Blo 1443541 1828109 := bbase (se 3 (by rfl) ⟨342770, by rfl⟩ : syracuseStep 1828109 = 685541) (by norm_num)
theorem B2778437 : Blo 1443541 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B1828165 : Blo 1443541 1828165 := bbase (se 4 (by rfl) ⟨171390, by rfl⟩ : syracuseStep 1828165 = 342781) (by norm_num)
theorem B7308629 : Blo 1443541 7308629 := bbase (se 12 (by rfl) ⟨2676, by rfl⟩ : syracuseStep 7308629 = 5353) (by norm_num)
theorem B6939989 : Blo 1443541 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B4875605 : Blo 1443541 4875605 := bbase (se 12 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 4875605 = 3571) (by norm_num)
theorem B2057557 : Blo 1443541 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B5203349 : Blo 1443541 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B8226197 : Blo 1443541 8226197 := bbase (se 6 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 8226197 = 385603) (by norm_num)
theorem B1828261 : Blo 1443541 1828261 := bbase (se 4 (by rfl) ⟨171399, by rfl⟩ : syracuseStep 1828261 = 342799) (by norm_num)
theorem B1951165 : Blo 1443541 1951165 := bbase (se 3 (by rfl) ⟨365843, by rfl⟩ : syracuseStep 1951165 = 731687) (by norm_num)
theorem B8455637 : Blo 1443541 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B3655165 : Blo 1443541 3655165 := bbase (se 3 (by rfl) ⟨685343, by rfl⟩ : syracuseStep 3655165 = 1370687) (by norm_num)
theorem B5481989 : Blo 1443541 5481989 := bbase (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) (by norm_num)
theorem B2197037 : Blo 1443541 2197037 := bbase (se 3 (by rfl) ⟨411944, by rfl⟩ : syracuseStep 2197037 = 823889) (by norm_num)
theorem B1828433 : Blo 1443541 1828433 := bbase (se 2 (by rfl) ⟨685662, by rfl⟩ : syracuseStep 1828433 = 1371325) (by norm_num)
theorem B3655277 : Blo 1443541 3655277 := bbase (se 3 (by rfl) ⟨685364, by rfl⟩ : syracuseStep 3655277 = 1370729) (by norm_num)
theorem B2197109 : Blo 1443541 2197109 := bbase (se 5 (by rfl) ⟨102989, by rfl⟩ : syracuseStep 2197109 = 205979) (by norm_num)
theorem B1828489 : Blo 1443541 1828489 := bbase (se 2 (by rfl) ⟨685683, by rfl⟩ : syracuseStep 1828489 = 1371367) (by norm_num)
theorem B1951381 : Blo 1443541 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B1541801 : Blo 1443541 1541801 := bbase (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) (by norm_num)
theorem B2057933 : Blo 1443541 2057933 := bbase (se 3 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 2057933 = 771725) (by norm_num)
theorem B1828585 : Blo 1443541 1828585 := bbase (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) (by norm_num)
theorem B4876037 : Blo 1443541 4876037 := bbase (se 4 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 4876037 = 914257) (by norm_num)
theorem B3655469 : Blo 1443541 3655469 := bbase (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) (by norm_num)
theorem B1828757 : Blo 1443541 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B1624009 : Blo 1443541 1624009 := bbase (se 2 (by rfl) ⟨609003, by rfl⟩ : syracuseStep 1624009 = 1218007) (by norm_num)
theorem B1828813 : Blo 1443541 1828813 := bbase (se 3 (by rfl) ⟨342902, by rfl⟩ : syracuseStep 1828813 = 685805) (by norm_num)
theorem B1624045 : Blo 1443541 1624045 := bbase (se 3 (by rfl) ⟨304508, by rfl⟩ : syracuseStep 1624045 = 609017) (by norm_num)
theorem B4630517 : Blo 1443541 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B1624081 : Blo 1443541 1624081 := bbase (se 2 (by rfl) ⟨609030, by rfl⟩ : syracuseStep 1624081 = 1218061) (by norm_num)
theorem B1828909 : Blo 1443541 1828909 := bbase (se 3 (by rfl) ⟨342920, by rfl⟩ : syracuseStep 1828909 = 685841) (by norm_num)
theorem B1624117 : Blo 1443541 1624117 := bbase (se 5 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 1624117 = 152261) (by norm_num)
theorem B53413973 : Blo 1443541 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B1624153 : Blo 1443541 1624153 := bbase (se 2 (by rfl) ⟨609057, by rfl⟩ : syracuseStep 1624153 = 1218115) (by norm_num)
theorem B1542245 : Blo 1443541 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B2312317 : Blo 1443541 2312317 := bbase (se 3 (by rfl) ⟨433559, by rfl⟩ : syracuseStep 2312317 = 867119) (by norm_num)
theorem B1624189 : Blo 1443541 1624189 := bbase (se 3 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 1624189 = 609071) (by norm_num)
theorem B3655813 : Blo 1443541 3655813 := bbase (se 4 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 3655813 = 685465) (by norm_num)
theorem B5859461 : Blo 1443541 5859461 := bbase (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) (by norm_num)
theorem B1853585 : Blo 1443541 1853585 := bbase (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) (by norm_num)
theorem B1624225 : Blo 1443541 1624225 := bbase (se 2 (by rfl) ⟨609084, by rfl⟩ : syracuseStep 1624225 = 1218169) (by norm_num)
theorem B1853605 : Blo 1443541 1853605 := bbase (se 4 (by rfl) ⟨173775, by rfl⟩ : syracuseStep 1853605 = 347551) (by norm_num)
theorem B4876469 : Blo 1443541 4876469 := bbase (se 5 (by rfl) ⟨228584, by rfl⟩ : syracuseStep 4876469 = 457169) (by norm_num)
theorem B4114613 : Blo 1443541 4114613 := bbase (se 5 (by rfl) ⟨192872, by rfl⟩ : syracuseStep 4114613 = 385745) (by norm_num)
theorem B1624261 : Blo 1443541 1624261 := bbase (se 4 (by rfl) ⟨152274, by rfl⟩ : syracuseStep 1624261 = 304549) (by norm_num)
theorem B7317701 : Blo 1443541 7317701 := bbase (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) (by norm_num)
theorem B1829081 : Blo 1443541 1829081 := bbase (se 2 (by rfl) ⟨685905, by rfl⟩ : syracuseStep 1829081 = 1371811) (by norm_num)
theorem B1624297 : Blo 1443541 1624297 := bbase (se 2 (by rfl) ⟨609111, by rfl⟩ : syracuseStep 1624297 = 1218223) (by norm_num)
theorem B3655925 : Blo 1443541 3655925 := bbase (se 5 (by rfl) ⟨171371, by rfl⟩ : syracuseStep 3655925 = 342743) (by norm_num)
theorem B1624333 : Blo 1443541 1624333 := bbase (se 3 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 1624333 = 609125) (by norm_num)
theorem B1829137 : Blo 1443541 1829137 := bbase (se 2 (by rfl) ⟨685926, by rfl⟩ : syracuseStep 1829137 = 1371853) (by norm_num)
theorem B1624369 : Blo 1443541 1624369 := bbase (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) (by norm_num)
theorem B2926901 : Blo 1443541 2926901 := bbase (se 5 (by rfl) ⟨137198, by rfl⟩ : syracuseStep 2926901 = 274397) (by norm_num)
theorem B1624405 : Blo 1443541 1624405 := bbase (se 10 (by rfl) ⟨2379, by rfl⟩ : syracuseStep 1624405 = 4759) (by norm_num)
theorem B1542493 : Blo 1443541 1542493 := bbase (se 3 (by rfl) ⟨289217, by rfl⟩ : syracuseStep 1542493 = 578435) (by norm_num)
theorem B1829233 : Blo 1443541 1829233 := bbase (se 2 (by rfl) ⟨685962, by rfl⟩ : syracuseStep 1829233 = 1371925) (by norm_num)
theorem B1624441 : Blo 1443541 1624441 := bbase (se 2 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 1624441 = 1218331) (by norm_num)
theorem B1624477 : Blo 1443541 1624477 := bbase (se 3 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 1624477 = 609179) (by norm_num)
theorem B3656117 : Blo 1443541 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B1624513 : Blo 1443541 1624513 := bbase (se 2 (by rfl) ⟨609192, by rfl⟩ : syracuseStep 1624513 = 1218385) (by norm_num)
theorem B1624549 : Blo 1443541 1624549 := bbase (se 4 (by rfl) ⟨152301, by rfl⟩ : syracuseStep 1624549 = 304603) (by norm_num)
theorem B1624585 : Blo 1443541 1624585 := bbase (se 2 (by rfl) ⟨609219, by rfl⟩ : syracuseStep 1624585 = 1218439) (by norm_num)
theorem B1829405 : Blo 1443541 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B1624621 : Blo 1443541 1624621 := bbase (se 3 (by rfl) ⟨304616, by rfl⟩ : syracuseStep 1624621 = 609233) (by norm_num)
theorem B1624657 : Blo 1443541 1624657 := bbase (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) (by norm_num)
theorem B2165333 : Blo 1443541 2165333 := bbase (se 8 (by rfl) ⟨12687, by rfl⟩ : syracuseStep 2165333 = 25375) (by norm_num)
theorem B1829461 : Blo 1443541 1829461 := bbase (se 8 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 1829461 = 21439) (by norm_num)
theorem B7309925 : Blo 1443541 7309925 := bbase (se 4 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 7309925 = 1370611) (by norm_num)
theorem B4876901 : Blo 1443541 4876901 := bbase (se 4 (by rfl) ⟨457209, by rfl⟩ : syracuseStep 4876901 = 914419) (by norm_num)
theorem B2165357 : Blo 1443541 2165357 := bbase (se 3 (by rfl) ⟨406004, by rfl⟩ : syracuseStep 2165357 = 812009) (by norm_num)
theorem B1624693 : Blo 1443541 1624693 := bbase (se 5 (by rfl) ⟨76157, by rfl⟩ : syracuseStep 1624693 = 152315) (by norm_num)
theorem B2165381 : Blo 1443541 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B6941333 : Blo 1443541 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B1624729 : Blo 1443541 1624729 := bbase (se 2 (by rfl) ⟨609273, by rfl⟩ : syracuseStep 1624729 = 1218547) (by norm_num)
theorem B2165405 : Blo 1443541 2165405 := bbase (se 3 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 2165405 = 812027) (by norm_num)
theorem B2312869 : Blo 1443541 2312869 := bbase (se 4 (by rfl) ⟨216831, by rfl⟩ : syracuseStep 2312869 = 433663) (by norm_num)
theorem B5483173 : Blo 1443541 5483173 := bbase (se 4 (by rfl) ⟨514047, by rfl⟩ : syracuseStep 5483173 = 1028095) (by norm_num)
theorem B2165429 : Blo 1443541 2165429 := bbase (se 5 (by rfl) ⟨101504, by rfl⟩ : syracuseStep 2165429 = 203009) (by norm_num)
theorem B1624765 : Blo 1443541 1624765 := bbase (se 3 (by rfl) ⟨304643, by rfl⟩ : syracuseStep 1624765 = 609287) (by norm_num)
theorem B2165453 : Blo 1443541 2165453 := bbase (se 3 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 2165453 = 812045) (by norm_num)
theorem B1624801 : Blo 1443541 1624801 := bbase (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) (by norm_num)
theorem B2165477 : Blo 1443541 2165477 := bbase (se 4 (by rfl) ⟨203013, by rfl⟩ : syracuseStep 2165477 = 406027) (by norm_num)
theorem B1854181 : Blo 1443541 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B2165501 : Blo 1443541 2165501 := bbase (se 3 (by rfl) ⟨406031, by rfl⟩ : syracuseStep 2165501 = 812063) (by norm_num)
theorem B1624837 : Blo 1443541 1624837 := bbase (se 4 (by rfl) ⟨152328, by rfl⟩ : syracuseStep 1624837 = 304657) (by norm_num)
theorem B3656461 : Blo 1443541 3656461 := bbase (se 3 (by rfl) ⟨685586, by rfl⟩ : syracuseStep 3656461 = 1371173) (by norm_num)
theorem B1542925 : Blo 1443541 1542925 := bbase (se 3 (by rfl) ⟨289298, by rfl⟩ : syracuseStep 1542925 = 578597) (by norm_num)
theorem B2165525 : Blo 1443541 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B1624873 : Blo 1443541 1624873 := bbase (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) (by norm_num)
theorem B2165549 : Blo 1443541 2165549 := bbase (se 3 (by rfl) ⟨406040, by rfl⟩ : syracuseStep 2165549 = 812081) (by norm_num)
theorem B2165573 : Blo 1443541 2165573 := bbase (se 4 (by rfl) ⟨203022, by rfl⟩ : syracuseStep 2165573 = 406045) (by norm_num)
theorem B1624909 : Blo 1443541 1624909 := bbase (se 3 (by rfl) ⟨304670, by rfl⟩ : syracuseStep 1624909 = 609341) (by norm_num)
theorem B1542997 : Blo 1443541 1542997 := bbase (se 9 (by rfl) ⟨4520, by rfl⟩ : syracuseStep 1542997 = 9041) (by norm_num)
theorem B2165597 : Blo 1443541 2165597 := bbase (se 3 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 2165597 = 812099) (by norm_num)
theorem B1624945 : Blo 1443541 1624945 := bbase (se 2 (by rfl) ⟨609354, by rfl⟩ : syracuseStep 1624945 = 1218709) (by norm_num)
theorem B2165621 : Blo 1443541 2165621 := bbase (se 5 (by rfl) ⟨101513, by rfl⟩ : syracuseStep 2165621 = 203027) (by norm_num)
theorem B3656573 : Blo 1443541 3656573 := bbase (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) (by norm_num)
theorem B2165645 : Blo 1443541 2165645 := bbase (se 3 (by rfl) ⟨406058, by rfl⟩ : syracuseStep 2165645 = 812117) (by norm_num)
theorem B1624981 : Blo 1443541 1624981 := bbase (se 6 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 1624981 = 76171) (by norm_num)
theorem B2165669 : Blo 1443541 2165669 := bbase (se 4 (by rfl) ⟨203031, by rfl⟩ : syracuseStep 2165669 = 406063) (by norm_num)
theorem B2313125 : Blo 1443541 2313125 := bbase (se 4 (by rfl) ⟨216855, by rfl⟩ : syracuseStep 2313125 = 433711) (by norm_num)
theorem B1625017 : Blo 1443541 1625017 := bbase (se 2 (by rfl) ⟨609381, by rfl⟩ : syracuseStep 1625017 = 1218763) (by norm_num)
theorem B2165693 : Blo 1443541 2165693 := bbase (se 3 (by rfl) ⟨406067, by rfl⟩ : syracuseStep 2165693 = 812135) (by norm_num)
theorem B2165717 : Blo 1443541 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B5483477 : Blo 1443541 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B2436061 : Blo 1443541 2436061 := bbase (se 3 (by rfl) ⟨456761, by rfl⟩ : syracuseStep 2436061 = 913523) (by norm_num)
theorem B1625053 : Blo 1443541 1625053 := bbase (se 3 (by rfl) ⟨304697, by rfl⟩ : syracuseStep 1625053 = 609395) (by norm_num)
theorem B2165741 : Blo 1443541 2165741 := bbase (se 3 (by rfl) ⟨406076, by rfl⟩ : syracuseStep 2165741 = 812153) (by norm_num)
theorem B1625089 : Blo 1443541 1625089 := bbase (se 2 (by rfl) ⟨609408, by rfl⟩ : syracuseStep 1625089 = 1218817) (by norm_num)
theorem B2165765 : Blo 1443541 2165765 := bbase (se 4 (by rfl) ⟨203040, by rfl⟩ : syracuseStep 2165765 = 406081) (by norm_num)
theorem B4877333 : Blo 1443541 4877333 := bbase (se 6 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 4877333 = 228625) (by norm_num)
theorem B2165789 : Blo 1443541 2165789 := bbase (se 3 (by rfl) ⟨406085, by rfl⟩ : syracuseStep 2165789 = 812171) (by norm_num)
theorem B1625125 : Blo 1443541 1625125 := bbase (se 4 (by rfl) ⟨152355, by rfl⟩ : syracuseStep 1625125 = 304711) (by norm_num)
theorem B2436149 : Blo 1443541 2436149 := bbase (se 5 (by rfl) ⟨114194, by rfl⟩ : syracuseStep 2436149 = 228389) (by norm_num)
theorem B2165813 : Blo 1443541 2165813 := bbase (se 5 (by rfl) ⟨101522, by rfl⟩ : syracuseStep 2165813 = 203045) (by norm_num)
theorem B3656765 : Blo 1443541 3656765 := bbase (se 3 (by rfl) ⟨685643, by rfl⟩ : syracuseStep 3656765 = 1371287) (by norm_num)
theorem B1625161 : Blo 1443541 1625161 := bbase (se 2 (by rfl) ⟨609435, by rfl⟩ : syracuseStep 1625161 = 1218871) (by norm_num)
theorem B2165837 : Blo 1443541 2165837 := bbase (se 3 (by rfl) ⟨406094, by rfl⟩ : syracuseStep 2165837 = 812189) (by norm_num)
theorem B2165861 : Blo 1443541 2165861 := bbase (se 4 (by rfl) ⟨203049, by rfl⟩ : syracuseStep 2165861 = 406099) (by norm_num)
theorem B1625197 : Blo 1443541 1625197 := bbase (se 3 (by rfl) ⟨304724, by rfl⟩ : syracuseStep 1625197 = 609449) (by norm_num)
theorem B2165885 : Blo 1443541 2165885 := bbase (se 3 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 2165885 = 812207) (by norm_num)
theorem B1625233 : Blo 1443541 1625233 := bbase (se 2 (by rfl) ⟨609462, by rfl⟩ : syracuseStep 1625233 = 1218925) (by norm_num)
theorem B2165909 : Blo 1443541 2165909 := bbase (se 6 (by rfl) ⟨50763, by rfl⟩ : syracuseStep 2165909 = 101527) (by norm_num)
theorem B2165933 : Blo 1443541 2165933 := bbase (se 3 (by rfl) ⟨406112, by rfl⟩ : syracuseStep 2165933 = 812225) (by norm_num)
theorem B2436277 : Blo 1443541 2436277 := bbase (se 5 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 2436277 = 228401) (by norm_num)
theorem B1625269 : Blo 1443541 1625269 := bbase (se 5 (by rfl) ⟨76184, by rfl⟩ : syracuseStep 1625269 = 152369) (by norm_num)
theorem B2165957 : Blo 1443541 2165957 := bbase (se 4 (by rfl) ⟨203058, by rfl⟩ : syracuseStep 2165957 = 406117) (by norm_num)
theorem B4943045 : Blo 1443541 4943045 := bbase (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) (by norm_num)
theorem B1625305 : Blo 1443541 1625305 := bbase (se 2 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 1625305 = 1218979) (by norm_num)
theorem B2165981 : Blo 1443541 2165981 := bbase (se 3 (by rfl) ⟨406121, by rfl⟩ : syracuseStep 2165981 = 812243) (by norm_num)
theorem B2166005 : Blo 1443541 2166005 := bbase (se 5 (by rfl) ⟨101531, by rfl⟩ : syracuseStep 2166005 = 203063) (by norm_num)
theorem B1625341 : Blo 1443541 1625341 := bbase (se 3 (by rfl) ⟨304751, by rfl⟩ : syracuseStep 1625341 = 609503) (by norm_num)
theorem B1953029 : Blo 1443541 1953029 := bbase (se 4 (by rfl) ⟨183096, by rfl⟩ : syracuseStep 1953029 = 366193) (by norm_num)
theorem B2436365 : Blo 1443541 2436365 := bbase (se 3 (by rfl) ⟨456818, by rfl⟩ : syracuseStep 2436365 = 913637) (by norm_num)
theorem B2166029 : Blo 1443541 2166029 := bbase (se 3 (by rfl) ⟨406130, by rfl⟩ : syracuseStep 2166029 = 812261) (by norm_num)
theorem B1625377 : Blo 1443541 1625377 := bbase (se 2 (by rfl) ⟨609516, by rfl⟩ : syracuseStep 1625377 = 1219033) (by norm_num)
theorem B2166053 : Blo 1443541 2166053 := bbase (se 4 (by rfl) ⟨203067, by rfl⟩ : syracuseStep 2166053 = 406135) (by norm_num)
theorem B2166077 : Blo 1443541 2166077 := bbase (se 3 (by rfl) ⟨406139, by rfl⟩ : syracuseStep 2166077 = 812279) (by norm_num)
theorem B1625413 : Blo 1443541 1625413 := bbase (se 4 (by rfl) ⟨152382, by rfl⟩ : syracuseStep 1625413 = 304765) (by norm_num)
theorem B2166101 : Blo 1443541 2166101 := bbase (se 11 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2166101 = 3173) (by norm_num)
theorem B1625449 : Blo 1443541 1625449 := bbase (se 2 (by rfl) ⟨609543, by rfl⟩ : syracuseStep 1625449 = 1219087) (by norm_num)
theorem B2166125 : Blo 1443541 2166125 := bbase (se 3 (by rfl) ⟨406148, by rfl⟩ : syracuseStep 2166125 = 812297) (by norm_num)
theorem B2166149 : Blo 1443541 2166149 := bbase (se 4 (by rfl) ⟨203076, by rfl⟩ : syracuseStep 2166149 = 406153) (by norm_num)
theorem B2436493 : Blo 1443541 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B1625485 : Blo 1443541 1625485 := bbase (se 3 (by rfl) ⟨304778, by rfl⟩ : syracuseStep 1625485 = 609557) (by norm_num)
theorem B3657109 : Blo 1443541 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B2166173 : Blo 1443541 2166173 := bbase (se 3 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 2166173 = 812315) (by norm_num)
theorem B1953181 : Blo 1443541 1953181 := bbase (se 3 (by rfl) ⟨366221, by rfl⟩ : syracuseStep 1953181 = 732443) (by norm_num)
theorem B1625521 : Blo 1443541 1625521 := bbase (se 2 (by rfl) ⟨609570, by rfl⟩ : syracuseStep 1625521 = 1219141) (by norm_num)
theorem B2166197 : Blo 1443541 2166197 := bbase (se 5 (by rfl) ⟨101540, by rfl⟩ : syracuseStep 2166197 = 203081) (by norm_num)
theorem B4877765 : Blo 1443541 4877765 := bbase (se 4 (by rfl) ⟨457290, by rfl⟩ : syracuseStep 4877765 = 914581) (by norm_num)
theorem B2166221 : Blo 1443541 2166221 := bbase (se 3 (by rfl) ⟨406166, by rfl⟩ : syracuseStep 2166221 = 812333) (by norm_num)
theorem B1625557 : Blo 1443541 1625557 := bbase (se 7 (by rfl) ⟨19049, by rfl⟩ : syracuseStep 1625557 = 38099) (by norm_num)
theorem B2436581 : Blo 1443541 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B2166245 : Blo 1443541 2166245 := bbase (se 4 (by rfl) ⟨203085, by rfl⟩ : syracuseStep 2166245 = 406171) (by norm_num)
theorem B13880821 : Blo 1443541 13880821 := bbase (se 5 (by rfl) ⟨650663, by rfl⟩ : syracuseStep 13880821 = 1301327) (by norm_num)
theorem B1625593 : Blo 1443541 1625593 := bbase (se 2 (by rfl) ⟨609597, by rfl⟩ : syracuseStep 1625593 = 1219195) (by norm_num)
theorem B3083773 : Blo 1443541 3083773 := bbase (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) (by norm_num)
theorem B2166269 : Blo 1443541 2166269 := bbase (se 3 (by rfl) ⟨406175, by rfl⟩ : syracuseStep 2166269 = 812351) (by norm_num)
theorem B3657221 : Blo 1443541 3657221 := bbase (se 4 (by rfl) ⟨342864, by rfl⟩ : syracuseStep 3657221 = 685729) (by norm_num)
theorem B2166293 : Blo 1443541 2166293 := bbase (se 6 (by rfl) ⟨50772, by rfl⟩ : syracuseStep 2166293 = 101545) (by norm_num)
theorem B1625629 : Blo 1443541 1625629 := bbase (se 3 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 1625629 = 609611) (by norm_num)
theorem B2166317 : Blo 1443541 2166317 := bbase (se 3 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 2166317 = 812369) (by norm_num)
theorem B8228405 : Blo 1443541 8228405 := bbase (se 5 (by rfl) ⟨385706, by rfl⟩ : syracuseStep 8228405 = 771413) (by norm_num)
theorem B1625665 : Blo 1443541 1625665 := bbase (se 2 (by rfl) ⟨609624, by rfl⟩ : syracuseStep 1625665 = 1219249) (by norm_num)
theorem B2166341 : Blo 1443541 2166341 := bbase (se 4 (by rfl) ⟨203094, by rfl⟩ : syracuseStep 2166341 = 406189) (by norm_num)
theorem B8343125 : Blo 1443541 8343125 := bbase (se 8 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 8343125 = 97771) (by norm_num)
theorem B2166365 : Blo 1443541 2166365 := bbase (se 3 (by rfl) ⟨406193, by rfl⟩ : syracuseStep 2166365 = 812387) (by norm_num)
theorem B2436709 : Blo 1443541 2436709 := bbase (se 4 (by rfl) ⟨228441, by rfl⟩ : syracuseStep 2436709 = 456883) (by norm_num)
theorem B2313829 : Blo 1443541 2313829 := bbase (se 4 (by rfl) ⟨216921, by rfl⟩ : syracuseStep 2313829 = 433843) (by norm_num)
theorem B1625701 : Blo 1443541 1625701 := bbase (se 4 (by rfl) ⟨152409, by rfl⟩ : syracuseStep 1625701 = 304819) (by norm_num)
theorem B2166389 : Blo 1443541 2166389 := bbase (se 5 (by rfl) ⟨101549, by rfl⟩ : syracuseStep 2166389 = 203099) (by norm_num)
theorem B1625737 : Blo 1443541 1625737 := bbase (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) (by norm_num)
theorem B2166413 : Blo 1443541 2166413 := bbase (se 3 (by rfl) ⟨406202, by rfl⟩ : syracuseStep 2166413 = 812405) (by norm_num)
theorem B2166437 : Blo 1443541 2166437 := bbase (se 4 (by rfl) ⟨203103, by rfl⟩ : syracuseStep 2166437 = 406207) (by norm_num)
theorem B1625773 : Blo 1443541 1625773 := bbase (se 3 (by rfl) ⟨304832, by rfl⟩ : syracuseStep 1625773 = 609665) (by norm_num)
theorem B1953461 : Blo 1443541 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B2436797 : Blo 1443541 2436797 := bbase (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) (by norm_num)
theorem B2166461 : Blo 1443541 2166461 := bbase (se 3 (by rfl) ⟨406211, by rfl⟩ : syracuseStep 2166461 = 812423) (by norm_num)
theorem B3657413 : Blo 1443541 3657413 := bbase (se 4 (by rfl) ⟨342882, by rfl⟩ : syracuseStep 3657413 = 685765) (by norm_num)
theorem B1625809 : Blo 1443541 1625809 := bbase (se 2 (by rfl) ⟨609678, by rfl⟩ : syracuseStep 1625809 = 1219357) (by norm_num)
theorem B2166485 : Blo 1443541 2166485 := bbase (se 7 (by rfl) ⟨25388, by rfl⟩ : syracuseStep 2166485 = 50777) (by norm_num)
theorem B4116197 : Blo 1443541 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B2166509 : Blo 1443541 2166509 := bbase (se 3 (by rfl) ⟨406220, by rfl⟩ : syracuseStep 2166509 = 812441) (by norm_num)
theorem B1625845 : Blo 1443541 1625845 := bbase (se 5 (by rfl) ⟨76211, by rfl⟩ : syracuseStep 1625845 = 152423) (by norm_num)
theorem B2166533 : Blo 1443541 2166533 := bbase (se 4 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 2166533 = 406225) (by norm_num)
theorem B9252629 : Blo 1443541 9252629 := bbase (se 6 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 9252629 = 433717) (by norm_num)
theorem B1625881 : Blo 1443541 1625881 := bbase (se 2 (by rfl) ⟨609705, by rfl⟩ : syracuseStep 1625881 = 1219411) (by norm_num)
theorem B2166557 : Blo 1443541 2166557 := bbase (se 3 (by rfl) ⟨406229, by rfl⟩ : syracuseStep 2166557 = 812459) (by norm_num)
theorem B2166581 : Blo 1443541 2166581 := bbase (se 5 (by rfl) ⟨101558, by rfl⟩ : syracuseStep 2166581 = 203117) (by norm_num)
theorem B2436925 : Blo 1443541 2436925 := bbase (se 3 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 2436925 = 913847) (by norm_num)
theorem B1625917 : Blo 1443541 1625917 := bbase (se 3 (by rfl) ⟨304859, by rfl⟩ : syracuseStep 1625917 = 609719) (by norm_num)
theorem B2166605 : Blo 1443541 2166605 := bbase (se 3 (by rfl) ⟨406238, by rfl⟩ : syracuseStep 2166605 = 812477) (by norm_num)
theorem B1625953 : Blo 1443541 1625953 := bbase (se 2 (by rfl) ⟨609732, by rfl⟩ : syracuseStep 1625953 = 1219465) (by norm_num)
theorem B3247973 : Blo 1443541 3247973 := bbase (se 4 (by rfl) ⟨304497, by rfl⟩ : syracuseStep 3247973 = 608995) (by norm_num)
theorem B2166629 : Blo 1443541 2166629 := bbase (se 4 (by rfl) ⟨203121, by rfl⟩ : syracuseStep 2166629 = 406243) (by norm_num)
theorem B3084149 : Blo 1443541 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B7311221 : Blo 1443541 7311221 := bbase (se 5 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 7311221 = 685427) (by norm_num)
theorem B4878197 : Blo 1443541 4878197 := bbase (se 5 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 4878197 = 457331) (by norm_num)
theorem B2166653 : Blo 1443541 2166653 := bbase (se 3 (by rfl) ⟨406247, by rfl⟩ : syracuseStep 2166653 = 812495) (by norm_num)
theorem B3518333 : Blo 1443541 3518333 := bbase (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) (by norm_num)
theorem B1625989 : Blo 1443541 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B2437013 : Blo 1443541 2437013 := bbase (se 6 (by rfl) ⟨57117, by rfl⟩ : syracuseStep 2437013 = 114235) (by norm_num)
theorem B2166677 : Blo 1443541 2166677 := bbase (se 6 (by rfl) ⟨50781, by rfl⟩ : syracuseStep 2166677 = 101563) (by norm_num)
theorem B1626025 : Blo 1443541 1626025 := bbase (se 2 (by rfl) ⟨609759, by rfl⟩ : syracuseStep 1626025 = 1219519) (by norm_num)
theorem B3248045 : Blo 1443541 3248045 := bbase (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) (by norm_num)
theorem B2166701 : Blo 1443541 2166701 := bbase (se 3 (by rfl) ⟨406256, by rfl⟩ : syracuseStep 2166701 = 812513) (by norm_num)
theorem B3125189 : Blo 1443541 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B2166725 : Blo 1443541 2166725 := bbase (se 4 (by rfl) ⟨203130, by rfl⟩ : syracuseStep 2166725 = 406261) (by norm_num)
theorem B3338189 : Blo 1443541 3338189 := bbase (se 3 (by rfl) ⟨625910, by rfl⟩ : syracuseStep 3338189 = 1251821) (by norm_num)
theorem B1626061 : Blo 1443541 1626061 := bbase (se 3 (by rfl) ⟨304886, by rfl⟩ : syracuseStep 1626061 = 609773) (by norm_num)
theorem B2166749 : Blo 1443541 2166749 := bbase (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) (by norm_num)
theorem B1626097 : Blo 1443541 1626097 := bbase (se 2 (by rfl) ⟨609786, by rfl⟩ : syracuseStep 1626097 = 1219573) (by norm_num)
theorem B3248117 : Blo 1443541 3248117 := bbase (se 5 (by rfl) ⟨152255, by rfl⟩ : syracuseStep 3248117 = 304511) (by norm_num)
theorem B2166773 : Blo 1443541 2166773 := bbase (se 5 (by rfl) ⟨101567, by rfl⟩ : syracuseStep 2166773 = 203135) (by norm_num)
theorem B2928629 : Blo 1443541 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B2469901 : Blo 1443541 2469901 := bbase (se 3 (by rfl) ⟨463106, by rfl⟩ : syracuseStep 2469901 = 926213) (by norm_num)
theorem B2166797 : Blo 1443541 2166797 := bbase (se 3 (by rfl) ⟨406274, by rfl⟩ : syracuseStep 2166797 = 812549) (by norm_num)
theorem B2314253 : Blo 1443541 2314253 := bbase (se 3 (by rfl) ⟨433922, by rfl⟩ : syracuseStep 2314253 = 867845) (by norm_num)
theorem B2437141 : Blo 1443541 2437141 := bbase (se 6 (by rfl) ⟨57120, by rfl⟩ : syracuseStep 2437141 = 114241) (by norm_num)
theorem B1626133 : Blo 1443541 1626133 := bbase (se 6 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 1626133 = 76225) (by norm_num)
theorem B3657757 : Blo 1443541 3657757 := bbase (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) (by norm_num)
theorem B2166821 : Blo 1443541 2166821 := bbase (se 4 (by rfl) ⟨203139, by rfl⟩ : syracuseStep 2166821 = 406279) (by norm_num)
theorem B1626169 : Blo 1443541 1626169 := bbase (se 2 (by rfl) ⟨609813, by rfl⟩ : syracuseStep 1626169 = 1219627) (by norm_num)
theorem B3248189 : Blo 1443541 3248189 := bbase (se 3 (by rfl) ⟨609035, by rfl⟩ : syracuseStep 3248189 = 1218071) (by norm_num)
theorem B2166845 : Blo 1443541 2166845 := bbase (se 3 (by rfl) ⟨406283, by rfl⟩ : syracuseStep 2166845 = 812567) (by norm_num)
theorem B2166869 : Blo 1443541 2166869 := bbase (se 8 (by rfl) ⟨12696, by rfl⟩ : syracuseStep 2166869 = 25393) (by norm_num)
theorem B1626205 : Blo 1443541 1626205 := bbase (se 3 (by rfl) ⟨304913, by rfl⟩ : syracuseStep 1626205 = 609827) (by norm_num)
theorem B2437229 : Blo 1443541 2437229 := bbase (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) (by norm_num)
theorem B2166893 : Blo 1443541 2166893 := bbase (se 3 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 2166893 = 812585) (by norm_num)
theorem B3248261 : Blo 1443541 3248261 := bbase (se 4 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 3248261 = 609049) (by norm_num)
theorem B2166917 : Blo 1443541 2166917 := bbase (se 4 (by rfl) ⟨203148, by rfl⟩ : syracuseStep 2166917 = 406297) (by norm_num)
theorem B3657869 : Blo 1443541 3657869 := bbase (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) (by norm_num)
theorem B2166941 : Blo 1443541 2166941 := bbase (se 3 (by rfl) ⟨406301, by rfl⟩ : syracuseStep 2166941 = 812603) (by norm_num)
theorem B2166965 : Blo 1443541 2166965 := bbase (se 5 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 2166965 = 203153) (by norm_num)
theorem B3248333 : Blo 1443541 3248333 := bbase (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) (by norm_num)
theorem B2166989 : Blo 1443541 2166989 := bbase (se 3 (by rfl) ⟨406310, by rfl⟩ : syracuseStep 2166989 = 812621) (by norm_num)
theorem B2167013 : Blo 1443541 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B2437357 : Blo 1443541 2437357 := bbase (se 3 (by rfl) ⟨457004, by rfl⟩ : syracuseStep 2437357 = 914009) (by norm_num)
theorem B2470133 : Blo 1443541 2470133 := bbase (se 5 (by rfl) ⟨115787, by rfl⟩ : syracuseStep 2470133 = 231575) (by norm_num)
theorem B2167037 : Blo 1443541 2167037 := bbase (se 3 (by rfl) ⟨406319, by rfl⟩ : syracuseStep 2167037 = 812639) (by norm_num)
theorem B2740493 : Blo 1443541 2740493 := bbase (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) (by norm_num)
theorem B3248405 : Blo 1443541 3248405 := bbase (se 6 (by rfl) ⟨76134, by rfl⟩ : syracuseStep 3248405 = 152269) (by norm_num)
theorem B2167061 : Blo 1443541 2167061 := bbase (se 6 (by rfl) ⟨50790, by rfl⟩ : syracuseStep 2167061 = 101581) (by norm_num)
theorem B4878629 : Blo 1443541 4878629 := bbase (se 4 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 4878629 = 914743) (by norm_num)
theorem B2167085 : Blo 1443541 2167085 := bbase (se 3 (by rfl) ⟨406328, by rfl⟩ : syracuseStep 2167085 = 812657) (by norm_num)
theorem B2314541 : Blo 1443541 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B2437445 : Blo 1443541 2437445 := bbase (se 4 (by rfl) ⟨228510, by rfl⟩ : syracuseStep 2437445 = 457021) (by norm_num)
theorem B2167109 : Blo 1443541 2167109 := bbase (se 4 (by rfl) ⟨203166, by rfl⟩ : syracuseStep 2167109 = 406333) (by norm_num)
theorem B3658061 : Blo 1443541 3658061 := bbase (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) (by norm_num)
theorem B3248477 : Blo 1443541 3248477 := bbase (se 3 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 3248477 = 1218179) (by norm_num)
theorem B2167133 : Blo 1443541 2167133 := bbase (se 3 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 2167133 = 812675) (by norm_num)
theorem B2167157 : Blo 1443541 2167157 := bbase (se 5 (by rfl) ⟨101585, by rfl⟩ : syracuseStep 2167157 = 203171) (by norm_num)
theorem B2167181 : Blo 1443541 2167181 := bbase (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) (by norm_num)
theorem B2740645 : Blo 1443541 2740645 := bbase (se 4 (by rfl) ⟨256935, by rfl⟩ : syracuseStep 2740645 = 513871) (by norm_num)
theorem B3248549 : Blo 1443541 3248549 := bbase (se 4 (by rfl) ⟨304551, by rfl⟩ : syracuseStep 3248549 = 609103) (by norm_num)
theorem B2167205 : Blo 1443541 2167205 := bbase (se 4 (by rfl) ⟨203175, by rfl⟩ : syracuseStep 2167205 = 406351) (by norm_num)
theorem B2167229 : Blo 1443541 2167229 := bbase (se 3 (by rfl) ⟨406355, by rfl⟩ : syracuseStep 2167229 = 812711) (by norm_num)
theorem B5853637 : Blo 1443541 5853637 := bbase (se 4 (by rfl) ⟨548778, by rfl⟩ : syracuseStep 5853637 = 1097557) (by norm_num)
theorem B2437573 : Blo 1443541 2437573 := bbase (se 4 (by rfl) ⟨228522, by rfl⟩ : syracuseStep 2437573 = 457045) (by norm_num)
theorem B2167253 : Blo 1443541 2167253 := bbase (se 7 (by rfl) ⟨25397, by rfl⟩ : syracuseStep 2167253 = 50795) (by norm_num)
theorem B3248621 : Blo 1443541 3248621 := bbase (se 3 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 3248621 = 1218233) (by norm_num)
theorem B2167277 : Blo 1443541 2167277 := bbase (se 3 (by rfl) ⟨406364, by rfl⟩ : syracuseStep 2167277 = 812729) (by norm_num)
theorem B2167301 : Blo 1443541 2167301 := bbase (se 4 (by rfl) ⟨203184, by rfl⟩ : syracuseStep 2167301 = 406369) (by norm_num)
theorem B2314765 : Blo 1443541 2314765 := bbase (se 3 (by rfl) ⟨434018, by rfl⟩ : syracuseStep 2314765 = 868037) (by norm_num)
theorem B2470429 : Blo 1443541 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B2437661 : Blo 1443541 2437661 := bbase (se 3 (by rfl) ⟨457061, by rfl⟩ : syracuseStep 2437661 = 914123) (by norm_num)
theorem B2167325 : Blo 1443541 2167325 := bbase (se 3 (by rfl) ⟨406373, by rfl⟩ : syracuseStep 2167325 = 812747) (by norm_num)
theorem B2601517 : Blo 1443541 2601517 := bbase (se 3 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 2601517 = 975569) (by norm_num)
theorem B3248693 : Blo 1443541 3248693 := bbase (se 5 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 3248693 = 304565) (by norm_num)
theorem B2167349 : Blo 1443541 2167349 := bbase (se 5 (by rfl) ⟨101594, by rfl⟩ : syracuseStep 2167349 = 203189) (by norm_num)
theorem B2167373 : Blo 1443541 2167373 := bbase (se 3 (by rfl) ⟨406382, by rfl⟩ : syracuseStep 2167373 = 812765) (by norm_num)
theorem B6943333 : Blo 1443541 6943333 := bbase (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) (by norm_num)
theorem B2167397 : Blo 1443541 2167397 := bbase (se 4 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 2167397 = 406387) (by norm_num)
theorem B3248765 : Blo 1443541 3248765 := bbase (se 3 (by rfl) ⟨609143, by rfl⟩ : syracuseStep 3248765 = 1218287) (by norm_num)
theorem B2167421 : Blo 1443541 2167421 := bbase (se 3 (by rfl) ⟨406391, by rfl⟩ : syracuseStep 2167421 = 812783) (by norm_num)
theorem B4625045 : Blo 1443541 4625045 := bbase (se 6 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 4625045 = 216799) (by norm_num)
theorem B2167445 : Blo 1443541 2167445 := bbase (se 6 (by rfl) ⟨50799, by rfl⟩ : syracuseStep 2167445 = 101599) (by norm_num)
theorem B2437789 : Blo 1443541 2437789 := bbase (se 3 (by rfl) ⟨457085, by rfl⟩ : syracuseStep 2437789 = 914171) (by norm_num)
theorem B5206693 : Blo 1443541 5206693 := bbase (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) (by norm_num)
theorem B3658405 : Blo 1443541 3658405 := bbase (se 4 (by rfl) ⟨342975, by rfl⟩ : syracuseStep 3658405 = 685951) (by norm_num)
theorem B2167469 : Blo 1443541 2167469 := bbase (se 3 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 2167469 = 812801) (by norm_num)
theorem B3248837 : Blo 1443541 3248837 := bbase (se 4 (by rfl) ⟨304578, by rfl⟩ : syracuseStep 3248837 = 609157) (by norm_num)
theorem B2167493 : Blo 1443541 2167493 := bbase (se 4 (by rfl) ⟨203202, by rfl⟩ : syracuseStep 2167493 = 406405) (by norm_num)
theorem B2740949 : Blo 1443541 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B2167517 : Blo 1443541 2167517 := bbase (se 3 (by rfl) ⟨406409, by rfl⟩ : syracuseStep 2167517 = 812819) (by norm_num)
theorem B7516901 : Blo 1443541 7516901 := bbase (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) (by norm_num)
theorem B2437877 : Blo 1443541 2437877 := bbase (se 5 (by rfl) ⟨114275, by rfl⟩ : syracuseStep 2437877 = 228551) (by norm_num)
theorem B2167541 : Blo 1443541 2167541 := bbase (se 5 (by rfl) ⟨101603, by rfl⟩ : syracuseStep 2167541 = 203207) (by norm_num)
theorem B1757953 : Blo 1443541 1757953 := bbase (se 2 (by rfl) ⟨659232, by rfl⟩ : syracuseStep 1757953 = 1318465) (by norm_num)
theorem B3248909 : Blo 1443541 3248909 := bbase (se 3 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 3248909 = 1218341) (by norm_num)
theorem B2167565 : Blo 1443541 2167565 := bbase (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) (by norm_num)
theorem B3658517 : Blo 1443541 3658517 := bbase (se 6 (by rfl) ⟨85746, by rfl⟩ : syracuseStep 3658517 = 171493) (by norm_num)
theorem B2167589 : Blo 1443541 2167589 := bbase (se 4 (by rfl) ⟨203211, by rfl⟩ : syracuseStep 2167589 = 406423) (by norm_num)
theorem B5206837 : Blo 1443541 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B9261877 : Blo 1443541 9261877 := bbase (se 5 (by rfl) ⟨434150, by rfl⟩ : syracuseStep 9261877 = 868301) (by norm_num)
theorem B2167613 : Blo 1443541 2167613 := bbase (se 3 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 2167613 = 812855) (by norm_num)
theorem B3248981 : Blo 1443541 3248981 := bbase (se 9 (by rfl) ⟨9518, by rfl⟩ : syracuseStep 3248981 = 19037) (by norm_num)
theorem B2167637 : Blo 1443541 2167637 := bbase (se 9 (by rfl) ⟨6350, by rfl⟩ : syracuseStep 2167637 = 12701) (by norm_num)
theorem B2167661 : Blo 1443541 2167661 := bbase (se 3 (by rfl) ⟨406436, by rfl⟩ : syracuseStep 2167661 = 812873) (by norm_num)
theorem B2438005 : Blo 1443541 2438005 := bbase (se 5 (by rfl) ⟨114281, by rfl⟩ : syracuseStep 2438005 = 228563) (by norm_num)
theorem B2167685 : Blo 1443541 2167685 := bbase (se 4 (by rfl) ⟨203220, by rfl⟩ : syracuseStep 2167685 = 406441) (by norm_num)
theorem B3249053 : Blo 1443541 3249053 := bbase (se 3 (by rfl) ⟨609197, by rfl⟩ : syracuseStep 3249053 = 1218395) (by norm_num)
theorem B2167709 : Blo 1443541 2167709 := bbase (se 3 (by rfl) ⟨406445, by rfl⟩ : syracuseStep 2167709 = 812891) (by norm_num)
theorem B2167733 : Blo 1443541 2167733 := bbase (se 5 (by rfl) ⟨101612, by rfl⟩ : syracuseStep 2167733 = 203225) (by norm_num)
theorem B2438093 : Blo 1443541 2438093 := bbase (se 3 (by rfl) ⟨457142, by rfl⟩ : syracuseStep 2438093 = 914285) (by norm_num)
theorem B2167757 : Blo 1443541 2167757 := bbase (se 3 (by rfl) ⟨406454, by rfl⟩ : syracuseStep 2167757 = 812909) (by norm_num)
theorem B3658709 : Blo 1443541 3658709 := bbase (se 7 (by rfl) ⟨42875, by rfl⟩ : syracuseStep 3658709 = 85751) (by norm_num)
theorem B3707869 : Blo 1443541 3707869 := bbase (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) (by norm_num)
theorem B3249125 : Blo 1443541 3249125 := bbase (se 4 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 3249125 = 609211) (by norm_num)
theorem B2167781 : Blo 1443541 2167781 := bbase (se 4 (by rfl) ⟨203229, by rfl⟩ : syracuseStep 2167781 = 406459) (by norm_num)
theorem B2167805 : Blo 1443541 2167805 := bbase (se 3 (by rfl) ⟨406463, by rfl⟩ : syracuseStep 2167805 = 812927) (by norm_num)
theorem B5485589 : Blo 1443541 5485589 := bbase (se 6 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 5485589 = 257137) (by norm_num)
theorem B2167829 : Blo 1443541 2167829 := bbase (se 6 (by rfl) ⟨50808, by rfl⟩ : syracuseStep 2167829 = 101617) (by norm_num)
theorem B3249197 : Blo 1443541 3249197 := bbase (se 3 (by rfl) ⟨609224, by rfl⟩ : syracuseStep 3249197 = 1218449) (by norm_num)
theorem B2167853 : Blo 1443541 2167853 := bbase (se 3 (by rfl) ⟨406472, by rfl⟩ : syracuseStep 2167853 = 812945) (by norm_num)
theorem B12334133 : Blo 1443541 12334133 := bbase (se 5 (by rfl) ⟨578162, by rfl⟩ : syracuseStep 12334133 = 1156325) (by norm_num)
theorem B2167877 : Blo 1443541 2167877 := bbase (se 4 (by rfl) ⟨203238, by rfl⟩ : syracuseStep 2167877 = 406477) (by norm_num)
theorem B6173765 : Blo 1443541 6173765 := bbase (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) (by norm_num)
theorem B2438221 : Blo 1443541 2438221 := bbase (se 3 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 2438221 = 914333) (by norm_num)
theorem B40096853 : Blo 1443541 40096853 := bbase (se 8 (by rfl) ⟨234942, by rfl⟩ : syracuseStep 40096853 = 469885) (by norm_num)
theorem B2167901 : Blo 1443541 2167901 := bbase (se 3 (by rfl) ⟨406481, by rfl⟩ : syracuseStep 2167901 = 812963) (by norm_num)
theorem B3249269 : Blo 1443541 3249269 := bbase (se 5 (by rfl) ⟨152309, by rfl⟩ : syracuseStep 3249269 = 304619) (by norm_num)
theorem B2167925 : Blo 1443541 2167925 := bbase (se 5 (by rfl) ⟨101621, by rfl⟩ : syracuseStep 2167925 = 203243) (by norm_num)
theorem B7312517 : Blo 1443541 7312517 := bbase (se 4 (by rfl) ⟨685548, by rfl⟩ : syracuseStep 7312517 = 1371097) (by norm_num)
theorem B2167949 : Blo 1443541 2167949 := bbase (se 3 (by rfl) ⟨406490, by rfl⟩ : syracuseStep 2167949 = 812981) (by norm_num)
theorem B2438309 : Blo 1443541 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B2167973 : Blo 1443541 2167973 := bbase (se 4 (by rfl) ⟨203247, by rfl⟩ : syracuseStep 2167973 = 406495) (by norm_num)
theorem B3249341 : Blo 1443541 3249341 := bbase (se 3 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 3249341 = 1218503) (by norm_num)
theorem B2167997 : Blo 1443541 2167997 := bbase (se 3 (by rfl) ⟨406499, by rfl⟩ : syracuseStep 2167997 = 812999) (by norm_num)
theorem B2168021 : Blo 1443541 2168021 := bbase (se 7 (by rfl) ⟨25406, by rfl⟩ : syracuseStep 2168021 = 50813) (by norm_num)
theorem B2168045 : Blo 1443541 2168045 := bbase (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) (by norm_num)
theorem B3249413 : Blo 1443541 3249413 := bbase (se 4 (by rfl) ⟨304632, by rfl⟩ : syracuseStep 3249413 = 609265) (by norm_num)
theorem B2168069 : Blo 1443541 2168069 := bbase (se 4 (by rfl) ⟨203256, by rfl⟩ : syracuseStep 2168069 = 406513) (by norm_num)
theorem B9385237 : Blo 1443541 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B2168093 : Blo 1443541 2168093 := bbase (se 3 (by rfl) ⟨406517, by rfl⟩ : syracuseStep 2168093 = 813035) (by norm_num)
theorem B3470629 : Blo 1443541 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B2438437 : Blo 1443541 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B5485877 : Blo 1443541 5485877 := bbase (se 5 (by rfl) ⟨257150, by rfl⟩ : syracuseStep 5485877 = 514301) (by norm_num)
theorem B2168117 : Blo 1443541 2168117 := bbase (se 5 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 2168117 = 203261) (by norm_num)
theorem B3249485 : Blo 1443541 3249485 := bbase (se 3 (by rfl) ⟨609278, by rfl⟩ : syracuseStep 3249485 = 1218557) (by norm_num)
theorem B2168141 : Blo 1443541 2168141 := bbase (se 3 (by rfl) ⟨406526, by rfl⟩ : syracuseStep 2168141 = 813053) (by norm_num)
theorem B1463653 : Blo 1443541 1463653 := bbase (se 4 (by rfl) ⟨137217, by rfl⟩ : syracuseStep 1463653 = 274435) (by norm_num)
theorem B2168165 : Blo 1443541 2168165 := bbase (se 4 (by rfl) ⟨203265, by rfl⟩ : syracuseStep 2168165 = 406531) (by norm_num)
theorem B2438525 : Blo 1443541 2438525 := bbase (se 3 (by rfl) ⟨457223, by rfl⟩ : syracuseStep 2438525 = 914447) (by norm_num)
theorem B2168189 : Blo 1443541 2168189 := bbase (se 3 (by rfl) ⟨406535, by rfl⟩ : syracuseStep 2168189 = 813071) (by norm_num)
theorem B1463701 : Blo 1443541 1463701 := bbase (se 6 (by rfl) ⟨34305, by rfl⟩ : syracuseStep 1463701 = 68611) (by norm_num)
theorem B3249557 : Blo 1443541 3249557 := bbase (se 6 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 3249557 = 152323) (by norm_num)
theorem B2168213 : Blo 1443541 2168213 := bbase (se 6 (by rfl) ⟨50817, by rfl⟩ : syracuseStep 2168213 = 101635) (by norm_num)
theorem B2168237 : Blo 1443541 2168237 := bbase (se 3 (by rfl) ⟨406544, by rfl⟩ : syracuseStep 2168237 = 813089) (by norm_num)
theorem B2741701 : Blo 1443541 2741701 := bbase (se 4 (by rfl) ⟨257034, by rfl⟩ : syracuseStep 2741701 = 514069) (by norm_num)
theorem B2168261 : Blo 1443541 2168261 := bbase (se 4 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 2168261 = 406549) (by norm_num)
theorem B3249629 : Blo 1443541 3249629 := bbase (se 3 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 3249629 = 1218611) (by norm_num)
theorem B3085789 : Blo 1443541 3085789 := bbase (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) (by norm_num)
theorem B2168285 : Blo 1443541 2168285 := bbase (se 3 (by rfl) ⟨406553, by rfl⟩ : syracuseStep 2168285 = 813107) (by norm_num)
theorem B2168309 : Blo 1443541 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B2438653 : Blo 1443541 2438653 := bbase (se 3 (by rfl) ⟨457247, by rfl⟩ : syracuseStep 2438653 = 914495) (by norm_num)
theorem B3249701 : Blo 1443541 3249701 := bbase (se 4 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 3249701 = 609319) (by norm_num)
theorem B2741845 : Blo 1443541 2741845 := bbase (se 8 (by rfl) ⟨16065, by rfl⟩ : syracuseStep 2741845 = 32131) (by norm_num)
theorem B2438741 : Blo 1443541 2438741 := bbase (se 8 (by rfl) ⟨14289, by rfl⟩ : syracuseStep 2438741 = 28579) (by norm_num)
theorem B2602597 : Blo 1443541 2602597 := bbase (se 4 (by rfl) ⟨243993, by rfl⟩ : syracuseStep 2602597 = 487987) (by norm_num)
theorem B3249773 : Blo 1443541 3249773 := bbase (se 3 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 3249773 = 1218665) (by norm_num)
theorem B3249845 : Blo 1443541 3249845 := bbase (se 5 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 3249845 = 304673) (by norm_num)
theorem B2602685 : Blo 1443541 2602685 := bbase (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) (by norm_num)
theorem B2438869 : Blo 1443541 2438869 := bbase (se 7 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 2438869 = 57161) (by norm_num)
theorem B2602741 : Blo 1443541 2602741 := bbase (se 5 (by rfl) ⟨122003, by rfl⟩ : syracuseStep 2602741 = 244007) (by norm_num)
theorem B2742005 : Blo 1443541 2742005 := bbase (se 5 (by rfl) ⟨128531, by rfl⟩ : syracuseStep 2742005 = 257063) (by norm_num)
theorem B3249917 : Blo 1443541 3249917 := bbase (se 3 (by rfl) ⟨609359, by rfl⟩ : syracuseStep 3249917 = 1218719) (by norm_num)
theorem B3471149 : Blo 1443541 3471149 := bbase (se 3 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 3471149 = 1301681) (by norm_num)
theorem B2438957 : Blo 1443541 2438957 := bbase (se 3 (by rfl) ⟨457304, by rfl⟩ : syracuseStep 2438957 = 914609) (by norm_num)
theorem B3249989 : Blo 1443541 3249989 := bbase (se 4 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 3249989 = 609373) (by norm_num)
theorem B2930509 : Blo 1443541 2930509 := bbase (se 3 (by rfl) ⟨549470, by rfl⟩ : syracuseStep 2930509 = 1098941) (by norm_num)
theorem B2742149 : Blo 1443541 2742149 := bbase (se 4 (by rfl) ⟨257076, by rfl⟩ : syracuseStep 2742149 = 514153) (by norm_num)
theorem B3250061 : Blo 1443541 3250061 := bbase (se 3 (by rfl) ⟨609386, by rfl⟩ : syracuseStep 3250061 = 1218773) (by norm_num)
theorem B3471245 : Blo 1443541 3471245 := bbase (se 3 (by rfl) ⟨650858, by rfl⟩ : syracuseStep 3471245 = 1301717) (by norm_num)
theorem B4626325 : Blo 1443541 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B2439085 : Blo 1443541 2439085 := bbase (se 3 (by rfl) ⟨457328, by rfl⟩ : syracuseStep 2439085 = 914657) (by norm_num)
theorem B2471885 : Blo 1443541 2471885 := bbase (se 3 (by rfl) ⟨463478, by rfl⟩ : syracuseStep 2471885 = 926957) (by norm_num)
theorem B4872149 : Blo 1443541 4872149 := bbase (se 7 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 4872149 = 114191) (by norm_num)
theorem B3250133 : Blo 1443541 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B6256597 : Blo 1443541 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B5560325 : Blo 1443541 5560325 := bbase (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) (by norm_num)
theorem B2439173 : Blo 1443541 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B3250205 : Blo 1443541 3250205 := bbase (se 3 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 3250205 = 1218827) (by norm_num)
theorem B3250277 : Blo 1443541 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B2439301 : Blo 1443541 2439301 := bbase (se 4 (by rfl) ⟨228684, by rfl⟩ : syracuseStep 2439301 = 457369) (by norm_num)
theorem B2742437 : Blo 1443541 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B3250349 : Blo 1443541 3250349 := bbase (se 3 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 3250349 = 1218881) (by norm_num)
theorem B3250421 : Blo 1443541 3250421 := bbase (se 5 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 3250421 = 304727) (by norm_num)
theorem B13883669 : Blo 1443541 13883669 := bbase (se 6 (by rfl) ⟨325398, by rfl⟩ : syracuseStep 13883669 = 650797) (by norm_num)
theorem B1734949 : Blo 1443541 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B8223029 : Blo 1443541 8223029 := bbase (se 5 (by rfl) ⟨385454, by rfl⟩ : syracuseStep 8223029 = 770909) (by norm_num)
theorem B1562941 : Blo 1443541 1562941 := bbase (se 3 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 1562941 = 586103) (by norm_num)
theorem B2742589 : Blo 1443541 2742589 := bbase (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) (by norm_num)
theorem B3250493 : Blo 1443541 3250493 := bbase (se 3 (by rfl) ⟨609467, by rfl⟩ : syracuseStep 3250493 = 1218935) (by norm_num)
theorem B3086677 : Blo 1443541 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B4872581 : Blo 1443541 4872581 := bbase (se 4 (by rfl) ⟨456804, by rfl⟩ : syracuseStep 4872581 = 913609) (by norm_num)
theorem B3250565 : Blo 1443541 3250565 := bbase (se 4 (by rfl) ⟨304740, by rfl⟩ : syracuseStep 3250565 = 609481) (by norm_num)
theorem B7313813 : Blo 1443541 7313813 := bbase (se 6 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 7313813 = 342835) (by norm_num)
theorem B3250637 : Blo 1443541 3250637 := bbase (se 3 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 3250637 = 1218989) (by norm_num)
theorem B5487061 : Blo 1443541 5487061 := bbase (se 7 (by rfl) ⟨64301, by rfl⟩ : syracuseStep 5487061 = 128603) (by norm_num)
theorem B4110821 : Blo 1443541 4110821 := bbase (se 4 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 4110821 = 770779) (by norm_num)
theorem B3250709 : Blo 1443541 3250709 := bbase (se 6 (by rfl) ⟨76188, by rfl⟩ : syracuseStep 3250709 = 152377) (by norm_num)
theorem B3250781 : Blo 1443541 3250781 := bbase (se 3 (by rfl) ⟨609521, by rfl⟩ : syracuseStep 3250781 = 1219043) (by norm_num)
theorem B2742893 : Blo 1443541 2742893 := bbase (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) (by norm_num)
theorem B4111013 : Blo 1443541 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B3250853 : Blo 1443541 3250853 := bbase (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) (by norm_num)
theorem B3250925 : Blo 1443541 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B5487365 : Blo 1443541 5487365 := bbase (se 4 (by rfl) ⟨514440, by rfl⟩ : syracuseStep 5487365 = 1028881) (by norm_num)
theorem B1563425 : Blo 1443541 1563425 := bbase (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) (by norm_num)
theorem B1465129 : Blo 1443541 1465129 := bbase (se 2 (by rfl) ⟨549423, by rfl⟩ : syracuseStep 1465129 = 1098847) (by norm_num)
theorem B4873013 : Blo 1443541 4873013 := bbase (se 5 (by rfl) ⟨228422, by rfl⟩ : syracuseStep 4873013 = 456845) (by norm_num)
theorem B3250997 : Blo 1443541 3250997 := bbase (se 5 (by rfl) ⟨152390, by rfl⟩ : syracuseStep 3250997 = 304781) (by norm_num)
theorem B6257477 : Blo 1443541 6257477 := bbase (se 4 (by rfl) ⟨586638, by rfl⟩ : syracuseStep 6257477 = 1173277) (by norm_num)
theorem B3087173 : Blo 1443541 3087173 := bbase (se 4 (by rfl) ⟨289422, by rfl⟩ : syracuseStep 3087173 = 578845) (by norm_num)
theorem B3169109 : Blo 1443541 3169109 := bbase (se 9 (by rfl) ⟨9284, by rfl⟩ : syracuseStep 3169109 = 18569) (by norm_num)
theorem B3251069 : Blo 1443541 3251069 := bbase (se 3 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 3251069 = 1219151) (by norm_num)
theorem B9255829 : Blo 1443541 9255829 := bbase (se 6 (by rfl) ⟨216933, by rfl⟩ : syracuseStep 9255829 = 433867) (by norm_num)
theorem B6167461 : Blo 1443541 6167461 := bbase (se 4 (by rfl) ⟨578199, by rfl⟩ : syracuseStep 6167461 = 1156399) (by norm_num)
theorem B6167477 : Blo 1443541 6167477 := bbase (se 5 (by rfl) ⟨289100, by rfl⟩ : syracuseStep 6167477 = 578201) (by norm_num)
theorem B3251141 : Blo 1443541 3251141 := bbase (se 4 (by rfl) ⟨304794, by rfl⟩ : syracuseStep 3251141 = 609589) (by norm_num)
theorem B3251213 : Blo 1443541 3251213 := bbase (se 3 (by rfl) ⟨609602, by rfl⟩ : syracuseStep 3251213 = 1219205) (by norm_num)
theorem B10976309 : Blo 1443541 10976309 := bbase (se 5 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 10976309 = 1029029) (by norm_num)
theorem B1543369 : Blo 1443541 1543369 := bbase (se 2 (by rfl) ⟨578763, by rfl⟩ : syracuseStep 1543369 = 1157527) (by norm_num)
theorem B3251285 : Blo 1443541 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B20831381 : Blo 1443541 20831381 := bbase (se 6 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 20831381 = 976471) (by norm_num)
theorem B3251357 : Blo 1443541 3251357 := bbase (se 3 (by rfl) ⟨609629, by rfl⟩ : syracuseStep 3251357 = 1219259) (by norm_num)
theorem B3472589 : Blo 1443541 3472589 := bbase (se 3 (by rfl) ⟨651110, by rfl⟩ : syracuseStep 3472589 = 1302221) (by norm_num)
theorem B4873445 : Blo 1443541 4873445 := bbase (se 4 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 4873445 = 913771) (by norm_num)
theorem B4627685 : Blo 1443541 4627685 := bbase (se 4 (by rfl) ⟨433845, by rfl⟩ : syracuseStep 4627685 = 867691) (by norm_num)
theorem B3251429 : Blo 1443541 3251429 := bbase (se 4 (by rfl) ⟨304821, by rfl⟩ : syracuseStep 3251429 = 609643) (by norm_num)
theorem B2604269 : Blo 1443541 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B2817301 : Blo 1443541 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B2055461 : Blo 1443541 2055461 := bbase (se 4 (by rfl) ⟨192699, by rfl⟩ : syracuseStep 2055461 = 385399) (by norm_num)
theorem B3251501 : Blo 1443541 3251501 := bbase (se 3 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 3251501 = 1219313) (by norm_num)
theorem B1735997 : Blo 1443541 1735997 := bbase (se 3 (by rfl) ⟨325499, by rfl⟩ : syracuseStep 1735997 = 650999) (by norm_num)
theorem B15621461 : Blo 1443541 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B2743645 : Blo 1443541 2743645 := bbase (se 3 (by rfl) ⟨514433, by rfl⟩ : syracuseStep 2743645 = 1028867) (by norm_num)
theorem B4627813 : Blo 1443541 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B3251573 : Blo 1443541 3251573 := bbase (se 5 (by rfl) ⟨152417, by rfl⟩ : syracuseStep 3251573 = 304835) (by norm_num)
theorem B3251645 : Blo 1443541 3251645 := bbase (se 3 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 3251645 = 1219367) (by norm_num)
theorem B8224213 : Blo 1443541 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B10968533 : Blo 1443541 10968533 := bbase (se 7 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 10968533 = 257075) (by norm_num)
theorem B2538973 : Blo 1443541 2538973 := bbase (se 3 (by rfl) ⟨476057, by rfl⟩ : syracuseStep 2538973 = 952115) (by norm_num)
theorem B2743789 : Blo 1443541 2743789 := bbase (se 3 (by rfl) ⟨514460, by rfl⟩ : syracuseStep 2743789 = 1028921) (by norm_num)
theorem B3251717 : Blo 1443541 3251717 := bbase (se 4 (by rfl) ⟨304848, by rfl⟩ : syracuseStep 3251717 = 609697) (by norm_num)
theorem B3251789 : Blo 1443541 3251789 := bbase (se 3 (by rfl) ⟨609710, by rfl⟩ : syracuseStep 3251789 = 1219421) (by norm_num)
theorem B4628069 : Blo 1443541 4628069 := bbase (se 4 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 4628069 = 867763) (by norm_num)
theorem B4112005 : Blo 1443541 4112005 := bbase (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) (by norm_num)
theorem B2743949 : Blo 1443541 2743949 := bbase (se 3 (by rfl) ⟨514490, by rfl⟩ : syracuseStep 2743949 = 1028981) (by norm_num)
theorem B4873877 : Blo 1443541 4873877 := bbase (se 6 (by rfl) ⟨114231, by rfl⟩ : syracuseStep 4873877 = 228463) (by norm_num)
theorem B3251861 : Blo 1443541 3251861 := bbase (se 6 (by rfl) ⟨76215, by rfl⟩ : syracuseStep 3251861 = 152431) (by norm_num)
theorem B1736353 : Blo 1443541 1736353 := bbase (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) (by norm_num)
theorem B7315109 : Blo 1443541 7315109 := bbase (se 4 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 7315109 = 1371583) (by norm_num)
theorem B2637517 : Blo 1443541 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B3251933 : Blo 1443541 3251933 := bbase (se 3 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 3251933 = 1219475) (by norm_num)
theorem B2744093 : Blo 1443541 2744093 := bbase (se 3 (by rfl) ⟨514517, by rfl⟩ : syracuseStep 2744093 = 1029035) (by norm_num)
theorem B3252005 : Blo 1443541 3252005 := bbase (se 4 (by rfl) ⟨304875, by rfl⟩ : syracuseStep 3252005 = 609751) (by norm_num)
theorem B52748117 : Blo 1443541 52748117 := bbase (se 9 (by rfl) ⟨154535, by rfl⟩ : syracuseStep 52748117 = 309071) (by norm_num)
theorem B1736545 : Blo 1443541 1736545 := bbase (se 2 (by rfl) ⟨651204, by rfl⟩ : syracuseStep 1736545 = 1302409) (by norm_num)
theorem B3252077 : Blo 1443541 3252077 := bbase (se 3 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 3252077 = 1219529) (by norm_num)
theorem B8339381 : Blo 1443541 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B3252149 : Blo 1443541 3252149 := bbase (se 5 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 3252149 = 304889) (by norm_num)
theorem B12337109 : Blo 1443541 12337109 := bbase (se 7 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 12337109 = 289151) (by norm_num)
theorem B3252221 : Blo 1443541 3252221 := bbase (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) (by norm_num)
theorem B3293201 : Blo 1443541 3293201 := bstep (se 2 (by rfl) ⟨1234950, by rfl⟩ : syracuseStep 3293201 = 2469901) B2469901
theorem B3293347 : Blo 1443541 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B1646755 : Blo 1443541 1646755 := bstep (se 1 (by rfl) ⟨1235066, by rfl⟩ : syracuseStep 1646755 = 2470133) B2470133
theorem B4874417 : Blo 1443541 4874417 := bstep (se 2 (by rfl) ⟨1827906, by rfl⟩ : syracuseStep 4874417 = 3655813) B3655813
theorem B3252401 : Blo 1443541 3252401 := bstep (se 2 (by rfl) ⟨1219650, by rfl⟩ : syracuseStep 3252401 = 2439301) B2439301
theorem B3252419 : Blo 1443541 3252419 := bstep (se 1 (by rfl) ⟨2439314, by rfl⟩ : syracuseStep 3252419 = 4878629) B4878629
theorem B1827299 : Blo 1443541 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B13181453 : Blo 1443541 13181453 := bstep (se 3 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 13181453 = 4943045) B4943045
theorem B3654193 : Blo 1443541 3654193 := bstep (se 2 (by rfl) ⟨1370322, by rfl⟩ : syracuseStep 3654193 = 2740645) B2740645
theorem B7316081 : Blo 1443541 7316081 := bstep (se 2 (by rfl) ⟨2743530, by rfl⟩ : syracuseStep 7316081 = 5487061) B5487061
theorem B7307981 : Blo 1443541 7307981 := bstep (se 3 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 7307981 = 2740493) B2740493
theorem B4874957 : Blo 1443541 4874957 := bstep (se 3 (by rfl) ⟨914054, by rfl⟩ : syracuseStep 4874957 = 1828109) B1828109
theorem B3293905 : Blo 1443541 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B79086293 : Blo 1443541 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B26731235 : Blo 1443541 26731235 := bstep (se 1 (by rfl) ⟨20048426, by rfl⟩ : syracuseStep 26731235 = 40096853) B40096853
theorem B4113155 : Blo 1443541 4113155 := bstep (se 1 (by rfl) ⟨3084866, by rfl⟩ : syracuseStep 4113155 = 6169733) B6169733
theorem B4875011 : Blo 1443541 4875011 := bstep (se 1 (by rfl) ⟨3656258, by rfl⟩ : syracuseStep 4875011 = 7312517) B7312517
theorem B5481229 : Blo 1443541 5481229 := bstep (se 3 (by rfl) ⟨1027730, by rfl⟩ : syracuseStep 5481229 = 2055461) B2055461
theorem B9257777 : Blo 1443541 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B3654467 : Blo 1443541 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B4629325 : Blo 1443541 4629325 := bstep (se 3 (by rfl) ⟨867998, by rfl⟩ : syracuseStep 4629325 = 1735997) B1735997
theorem B3654659 : Blo 1443541 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B4875281 : Blo 1443541 4875281 := bstep (se 2 (by rfl) ⟨1828230, by rfl⟩ : syracuseStep 4875281 = 3656461) B3656461
theorem B2057233 : Blo 1443541 2057233 := bstep (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) B1542925
theorem B16450613 : Blo 1443541 16450613 := bstep (se 5 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 16450613 = 1542245) B1542245
theorem B2057329 : Blo 1443541 2057329 := bstep (se 2 (by rfl) ⟨771498, by rfl⟩ : syracuseStep 2057329 = 1542997) B1542997
theorem B4392077 : Blo 1443541 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1828003 : Blo 1443541 1828003 := bstep (se 1 (by rfl) ⟨1371002, by rfl⟩ : syracuseStep 1828003 = 2742005) B2742005
theorem B1828099 : Blo 1443541 1828099 := bstep (se 1 (by rfl) ⟨1371074, by rfl⟩ : syracuseStep 1828099 = 2742149) B2742149
theorem B1647923 : Blo 1443541 1647923 := bstep (se 1 (by rfl) ⟨1235942, by rfl⟩ : syracuseStep 1647923 = 2471885) B2471885
theorem B5482019 : Blo 1443541 5482019 := bstep (se 1 (by rfl) ⟨4111514, by rfl⟩ : syracuseStep 5482019 = 8223029) B8223029
theorem B4875821 : Blo 1443541 4875821 := bstep (se 3 (by rfl) ⟨914216, by rfl⟩ : syracuseStep 4875821 = 1828433) B1828433
theorem B4875875 : Blo 1443541 4875875 := bstep (se 1 (by rfl) ⟨3656906, by rfl⟩ : syracuseStep 4875875 = 7313813) B7313813
theorem B2057825 : Blo 1443541 2057825 := bstep (se 2 (by rfl) ⟨771684, by rfl⟩ : syracuseStep 2057825 = 1543369) B1543369
theorem B1443555 : Blo 1443541 1443555 := bstep (se 1 (by rfl) ⟨1082666, by rfl⟩ : syracuseStep 1443555 = 2165333) B2165333
theorem B1443571 : Blo 1443541 1443571 := bstep (se 1 (by rfl) ⟨1082678, by rfl⟩ : syracuseStep 1443571 = 2165357) B2165357
theorem B1828595 : Blo 1443541 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B1443587 : Blo 1443541 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B10962701 : Blo 1443541 10962701 := bstep (se 3 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 10962701 = 4111013) B4111013
theorem B1443603 : Blo 1443541 1443603 := bstep (se 1 (by rfl) ⟨1082702, by rfl⟩ : syracuseStep 1443603 = 2165405) B2165405
theorem B1443619 : Blo 1443541 1443619 := bstep (se 1 (by rfl) ⟨1082714, by rfl⟩ : syracuseStep 1443619 = 2165429) B2165429
theorem B1951537 : Blo 1443541 1951537 := bstep (se 2 (by rfl) ⟨731826, by rfl⟩ : syracuseStep 1951537 = 1463653) B1463653
theorem B6170417 : Blo 1443541 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B1443635 : Blo 1443541 1443635 := bstep (se 1 (by rfl) ⟨1082726, by rfl⟩ : syracuseStep 1443635 = 2165453) B2165453
theorem B1443651 : Blo 1443541 1443651 := bstep (se 1 (by rfl) ⟨1082738, by rfl⟩ : syracuseStep 1443651 = 2165477) B2165477
theorem B8226629 : Blo 1443541 8226629 := bstep (se 4 (by rfl) ⟨771246, by rfl⟩ : syracuseStep 8226629 = 1542493) B1542493
theorem B1443667 : Blo 1443541 1443667 := bstep (se 1 (by rfl) ⟨1082750, by rfl⟩ : syracuseStep 1443667 = 2165501) B2165501
theorem B1443683 : Blo 1443541 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B4876145 : Blo 1443541 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B1443699 : Blo 1443541 1443699 := bstep (se 1 (by rfl) ⟨1082774, by rfl⟩ : syracuseStep 1443699 = 2165549) B2165549
theorem B1443715 : Blo 1443541 1443715 := bstep (se 1 (by rfl) ⟨1082786, by rfl⟩ : syracuseStep 1443715 = 2165573) B2165573
theorem B1443731 : Blo 1443541 1443731 := bstep (se 1 (by rfl) ⟨1082798, by rfl⟩ : syracuseStep 1443731 = 2165597) B2165597
theorem B1443747 : Blo 1443541 1443747 := bstep (se 1 (by rfl) ⟨1082810, by rfl⟩ : syracuseStep 1443747 = 2165621) B2165621
theorem B3655601 : Blo 1443541 3655601 := bstep (se 2 (by rfl) ⟨1370850, by rfl⟩ : syracuseStep 3655601 = 2741701) B2741701
theorem B1443763 : Blo 1443541 1443763 := bstep (se 1 (by rfl) ⟨1082822, by rfl⟩ : syracuseStep 1443763 = 2165645) B2165645
theorem B1443779 : Blo 1443541 1443779 := bstep (se 1 (by rfl) ⟨1082834, by rfl⟩ : syracuseStep 1443779 = 2165669) B2165669
theorem B1542083 : Blo 1443541 1542083 := bstep (se 1 (by rfl) ⟨1156562, by rfl⟩ : syracuseStep 1542083 = 2313125) B2313125
theorem B3385297 : Blo 1443541 3385297 := bstep (se 2 (by rfl) ⟨1269486, by rfl⟩ : syracuseStep 3385297 = 2538973) B2538973
theorem B4114385 : Blo 1443541 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B1443795 : Blo 1443541 1443795 := bstep (se 1 (by rfl) ⟨1082846, by rfl⟩ : syracuseStep 1443795 = 2165693) B2165693
theorem B1443811 : Blo 1443541 1443811 := bstep (se 1 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 1443811 = 2165717) B2165717
theorem B3655651 : Blo 1443541 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B18507761 : Blo 1443541 18507761 := bstep (se 2 (by rfl) ⟨6940410, by rfl⟩ : syracuseStep 18507761 = 13880821) B13880821
theorem B1443827 : Blo 1443541 1443827 := bstep (se 1 (by rfl) ⟨1082870, by rfl⟩ : syracuseStep 1443827 = 2165741) B2165741
theorem B1443843 : Blo 1443541 1443843 := bstep (se 1 (by rfl) ⟨1082882, by rfl⟩ : syracuseStep 1443843 = 2165765) B2165765
theorem B1443859 : Blo 1443541 1443859 := bstep (se 1 (by rfl) ⟨1082894, by rfl⟩ : syracuseStep 1443859 = 2165789) B2165789
theorem B1624099 : Blo 1443541 1624099 := bstep (se 1 (by rfl) ⟨1218074, by rfl⟩ : syracuseStep 1624099 = 2436149) B2436149
theorem B1443875 : Blo 1443541 1443875 := bstep (se 1 (by rfl) ⟨1082906, by rfl⟩ : syracuseStep 1443875 = 2165813) B2165813
theorem B7317539 : Blo 1443541 7317539 := bstep (se 1 (by rfl) ⟨5488154, by rfl⟩ : syracuseStep 7317539 = 10976309) B10976309
theorem B1443891 : Blo 1443541 1443891 := bstep (se 1 (by rfl) ⟨1082918, by rfl⟩ : syracuseStep 1443891 = 2165837) B2165837
theorem B1443907 : Blo 1443541 1443907 := bstep (se 1 (by rfl) ⟨1082930, by rfl⟩ : syracuseStep 1443907 = 2165861) B2165861
theorem B1443923 : Blo 1443541 1443923 := bstep (se 1 (by rfl) ⟨1082942, by rfl⟩ : syracuseStep 1443923 = 2165885) B2165885
theorem B1443939 : Blo 1443541 1443939 := bstep (se 1 (by rfl) ⟨1082954, by rfl⟩ : syracuseStep 1443939 = 2165909) B2165909
theorem B13887587 : Blo 1443541 13887587 := bstep (se 1 (by rfl) ⟨10415690, by rfl⟩ : syracuseStep 13887587 = 20831381) B20831381
theorem B3655793 : Blo 1443541 3655793 := bstep (se 2 (by rfl) ⟨1370922, by rfl⟩ : syracuseStep 3655793 = 2741845) B2741845
theorem B1443955 : Blo 1443541 1443955 := bstep (se 1 (by rfl) ⟨1082966, by rfl⟩ : syracuseStep 1443955 = 2165933) B2165933
theorem B1443971 : Blo 1443541 1443971 := bstep (se 1 (by rfl) ⟨1082978, by rfl⟩ : syracuseStep 1443971 = 2165957) B2165957
theorem B1443987 : Blo 1443541 1443987 := bstep (se 1 (by rfl) ⟨1082990, by rfl⟩ : syracuseStep 1443987 = 2165981) B2165981
theorem B1444003 : Blo 1443541 1444003 := bstep (se 1 (by rfl) ⟨1083002, by rfl⟩ : syracuseStep 1444003 = 2166005) B2166005
theorem B5482673 : Blo 1443541 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B1624243 : Blo 1443541 1624243 := bstep (se 1 (by rfl) ⟨1218182, by rfl⟩ : syracuseStep 1624243 = 2436365) B2436365
theorem B1444019 : Blo 1443541 1444019 := bstep (se 1 (by rfl) ⟨1083014, by rfl⟩ : syracuseStep 1444019 = 2166029) B2166029
theorem B1444035 : Blo 1443541 1444035 := bstep (se 1 (by rfl) ⟨1083026, by rfl⟩ : syracuseStep 1444035 = 2166053) B2166053
theorem B1444051 : Blo 1443541 1444051 := bstep (se 1 (by rfl) ⟨1083038, by rfl⟩ : syracuseStep 1444051 = 2166077) B2166077
theorem B1444067 : Blo 1443541 1444067 := bstep (se 1 (by rfl) ⟨1083050, by rfl⟩ : syracuseStep 1444067 = 2166101) B2166101
theorem B10414307 : Blo 1443541 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B1444083 : Blo 1443541 1444083 := bstep (se 1 (by rfl) ⟨1083062, by rfl⟩ : syracuseStep 1444083 = 2166125) B2166125
theorem B1444099 : Blo 1443541 1444099 := bstep (se 1 (by rfl) ⟨1083074, by rfl⟩ : syracuseStep 1444099 = 2166149) B2166149
theorem B3516689 : Blo 1443541 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B1444115 : Blo 1443541 1444115 := bstep (se 1 (by rfl) ⟨1083086, by rfl⟩ : syracuseStep 1444115 = 2166173) B2166173
theorem B1444131 : Blo 1443541 1444131 := bstep (se 1 (by rfl) ⟨1083098, by rfl⟩ : syracuseStep 1444131 = 2166197) B2166197
theorem B1444147 : Blo 1443541 1444147 := bstep (se 1 (by rfl) ⟨1083110, by rfl⟩ : syracuseStep 1444147 = 2166221) B2166221
theorem B1624387 : Blo 1443541 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B1444163 : Blo 1443541 1444163 := bstep (se 1 (by rfl) ⟨1083122, by rfl⟩ : syracuseStep 1444163 = 2166245) B2166245
theorem B1444179 : Blo 1443541 1444179 := bstep (se 1 (by rfl) ⟨1083134, by rfl⟩ : syracuseStep 1444179 = 2166269) B2166269
theorem B1444195 : Blo 1443541 1444195 := bstep (se 1 (by rfl) ⟨1083146, by rfl⟩ : syracuseStep 1444195 = 2166293) B2166293
theorem B1444211 : Blo 1443541 1444211 := bstep (se 1 (by rfl) ⟨1083158, by rfl⟩ : syracuseStep 1444211 = 2166317) B2166317
theorem B1444227 : Blo 1443541 1444227 := bstep (se 1 (by rfl) ⟨1083170, by rfl⟩ : syracuseStep 1444227 = 2166341) B2166341
theorem B4876685 : Blo 1443541 4876685 := bstep (se 3 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 4876685 = 1828757) B1828757
theorem B1444243 : Blo 1443541 1444243 := bstep (se 1 (by rfl) ⟨1083182, by rfl⟩ : syracuseStep 1444243 = 2166365) B2166365
theorem B1444259 : Blo 1443541 1444259 := bstep (se 1 (by rfl) ⟨1083194, by rfl⟩ : syracuseStep 1444259 = 2166389) B2166389
theorem B1444275 : Blo 1443541 1444275 := bstep (se 1 (by rfl) ⟨1083206, by rfl⟩ : syracuseStep 1444275 = 2166413) B2166413
theorem B1829299 : Blo 1443541 1829299 := bstep (se 1 (by rfl) ⟨1371974, by rfl⟩ : syracuseStep 1829299 = 2743949) B2743949
theorem B1444291 : Blo 1443541 1444291 := bstep (se 1 (by rfl) ⟨1083218, by rfl⟩ : syracuseStep 1444291 = 2166437) B2166437
theorem B4876739 : Blo 1443541 4876739 := bstep (se 1 (by rfl) ⟨3657554, by rfl⟩ : syracuseStep 4876739 = 7315109) B7315109
theorem B1624531 : Blo 1443541 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B1444307 : Blo 1443541 1444307 := bstep (se 1 (by rfl) ⟨1083230, by rfl⟩ : syracuseStep 1444307 = 2166461) B2166461
theorem B1444323 : Blo 1443541 1444323 := bstep (se 1 (by rfl) ⟨1083242, by rfl⟩ : syracuseStep 1444323 = 2166485) B2166485
theorem B1444339 : Blo 1443541 1444339 := bstep (se 1 (by rfl) ⟨1083254, by rfl⟩ : syracuseStep 1444339 = 2166509) B2166509
theorem B1444355 : Blo 1443541 1444355 := bstep (se 1 (by rfl) ⟨1083266, by rfl⟩ : syracuseStep 1444355 = 2166533) B2166533
theorem B8333837 : Blo 1443541 8333837 := bstep (se 3 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 8333837 = 3125189) B3125189
theorem B1444371 : Blo 1443541 1444371 := bstep (se 1 (by rfl) ⟨1083278, by rfl⟩ : syracuseStep 1444371 = 2166557) B2166557
theorem B1829395 : Blo 1443541 1829395 := bstep (se 1 (by rfl) ⟨1372046, by rfl⟩ : syracuseStep 1829395 = 2744093) B2744093
theorem B1444387 : Blo 1443541 1444387 := bstep (se 1 (by rfl) ⟨1083290, by rfl⟩ : syracuseStep 1444387 = 2166581) B2166581
theorem B1444403 : Blo 1443541 1444403 := bstep (se 1 (by rfl) ⟨1083302, by rfl⟩ : syracuseStep 1444403 = 2166605) B2166605
theorem B2165315 : Blo 1443541 2165315 := bstep (se 1 (by rfl) ⟨1623986, by rfl⟩ : syracuseStep 2165315 = 3247973) B3247973
theorem B1444419 : Blo 1443541 1444419 := bstep (se 1 (by rfl) ⟨1083314, by rfl⟩ : syracuseStep 1444419 = 2166629) B2166629
theorem B1444435 : Blo 1443541 1444435 := bstep (se 1 (by rfl) ⟨1083326, by rfl⟩ : syracuseStep 1444435 = 2166653) B2166653
theorem B2345555 : Blo 1443541 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B2165345 : Blo 1443541 2165345 := bstep (se 2 (by rfl) ⟨812004, by rfl⟩ : syracuseStep 2165345 = 1624009) B1624009
theorem B1624675 : Blo 1443541 1624675 := bstep (se 1 (by rfl) ⟨1218506, by rfl⟩ : syracuseStep 1624675 = 2437013) B2437013
theorem B1444451 : Blo 1443541 1444451 := bstep (se 1 (by rfl) ⟨1083338, by rfl⟩ : syracuseStep 1444451 = 2166677) B2166677
theorem B8342129 : Blo 1443541 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B2165363 : Blo 1443541 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B1444467 : Blo 1443541 1444467 := bstep (se 1 (by rfl) ⟨1083350, by rfl⟩ : syracuseStep 1444467 = 2166701) B2166701
theorem B1444483 : Blo 1443541 1444483 := bstep (se 1 (by rfl) ⟨1083362, by rfl⟩ : syracuseStep 1444483 = 2166725) B2166725
theorem B2165393 : Blo 1443541 2165393 := bstep (se 2 (by rfl) ⟨812022, by rfl⟩ : syracuseStep 2165393 = 1624045) B1624045
theorem B1444499 : Blo 1443541 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B2165411 : Blo 1443541 2165411 := bstep (se 1 (by rfl) ⟨1624058, by rfl⟩ : syracuseStep 2165411 = 3248117) B3248117
theorem B1444515 : Blo 1443541 1444515 := bstep (se 1 (by rfl) ⟨1083386, by rfl⟩ : syracuseStep 1444515 = 2166773) B2166773
theorem B1952419 : Blo 1443541 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B1444531 : Blo 1443541 1444531 := bstep (se 1 (by rfl) ⟨1083398, by rfl⟩ : syracuseStep 1444531 = 2166797) B2166797
theorem B1542835 : Blo 1443541 1542835 := bstep (se 1 (by rfl) ⟨1157126, by rfl⟩ : syracuseStep 1542835 = 2314253) B2314253
theorem B2165441 : Blo 1443541 2165441 := bstep (se 2 (by rfl) ⟨812040, by rfl⟩ : syracuseStep 2165441 = 1624081) B1624081
theorem B1444547 : Blo 1443541 1444547 := bstep (se 1 (by rfl) ⟨1083410, by rfl⟩ : syracuseStep 1444547 = 2166821) B2166821
theorem B4877009 : Blo 1443541 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B2165459 : Blo 1443541 2165459 := bstep (se 1 (by rfl) ⟨1624094, by rfl⟩ : syracuseStep 2165459 = 3248189) B3248189
theorem B1444563 : Blo 1443541 1444563 := bstep (se 1 (by rfl) ⟨1083422, by rfl⟩ : syracuseStep 1444563 = 2166845) B2166845
theorem B1444579 : Blo 1443541 1444579 := bstep (se 1 (by rfl) ⟨1083434, by rfl⟩ : syracuseStep 1444579 = 2166869) B2166869
theorem B2165489 : Blo 1443541 2165489 := bstep (se 2 (by rfl) ⟨812058, by rfl⟩ : syracuseStep 2165489 = 1624117) B1624117
theorem B1624819 : Blo 1443541 1624819 := bstep (se 1 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 1624819 = 2437229) B2437229
theorem B1444595 : Blo 1443541 1444595 := bstep (se 1 (by rfl) ⟨1083446, by rfl⟩ : syracuseStep 1444595 = 2166893) B2166893
theorem B2165507 : Blo 1443541 2165507 := bstep (se 1 (by rfl) ⟨1624130, by rfl⟩ : syracuseStep 2165507 = 3248261) B3248261
theorem B1444611 : Blo 1443541 1444611 := bstep (se 1 (by rfl) ⟨1083458, by rfl⟩ : syracuseStep 1444611 = 2166917) B2166917
theorem B1444627 : Blo 1443541 1444627 := bstep (se 1 (by rfl) ⟨1083470, by rfl⟩ : syracuseStep 1444627 = 2166941) B2166941
theorem B2165537 : Blo 1443541 2165537 := bstep (se 2 (by rfl) ⟨812076, by rfl⟩ : syracuseStep 2165537 = 1624153) B1624153
theorem B1444643 : Blo 1443541 1444643 := bstep (se 1 (by rfl) ⟨1083482, by rfl⟩ : syracuseStep 1444643 = 2166965) B2166965
theorem B2165555 : Blo 1443541 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B1444659 : Blo 1443541 1444659 := bstep (se 1 (by rfl) ⟨1083494, by rfl⟩ : syracuseStep 1444659 = 2166989) B2166989
theorem B1444675 : Blo 1443541 1444675 := bstep (se 1 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 1444675 = 2167013) B2167013
theorem B2165585 : Blo 1443541 2165585 := bstep (se 2 (by rfl) ⟨812094, by rfl⟩ : syracuseStep 2165585 = 1624189) B1624189
theorem B1444691 : Blo 1443541 1444691 := bstep (se 1 (by rfl) ⟨1083518, by rfl⟩ : syracuseStep 1444691 = 2167037) B2167037
theorem B2165603 : Blo 1443541 2165603 := bstep (se 1 (by rfl) ⟨1624202, by rfl⟩ : syracuseStep 2165603 = 3248405) B3248405
theorem B1444707 : Blo 1443541 1444707 := bstep (se 1 (by rfl) ⟨1083530, by rfl⟩ : syracuseStep 1444707 = 2167061) B2167061
theorem B1444723 : Blo 1443541 1444723 := bstep (se 1 (by rfl) ⟨1083542, by rfl⟩ : syracuseStep 1444723 = 2167085) B2167085
theorem B2165633 : Blo 1443541 2165633 := bstep (se 2 (by rfl) ⟨812112, by rfl⟩ : syracuseStep 2165633 = 1624225) B1624225
theorem B1624963 : Blo 1443541 1624963 := bstep (se 1 (by rfl) ⟨1218722, by rfl⟩ : syracuseStep 1624963 = 2437445) B2437445
theorem B1444739 : Blo 1443541 1444739 := bstep (se 1 (by rfl) ⟨1083554, by rfl⟩ : syracuseStep 1444739 = 2167109) B2167109
theorem B2435987 : Blo 1443541 2435987 := bstep (se 1 (by rfl) ⟨1826990, by rfl⟩ : syracuseStep 2435987 = 3653981) B3653981
theorem B2165651 : Blo 1443541 2165651 := bstep (se 1 (by rfl) ⟨1624238, by rfl⟩ : syracuseStep 2165651 = 3248477) B3248477
theorem B1444755 : Blo 1443541 1444755 := bstep (se 1 (by rfl) ⟨1083566, by rfl⟩ : syracuseStep 1444755 = 2167133) B2167133
theorem B1444771 : Blo 1443541 1444771 := bstep (se 1 (by rfl) ⟨1083578, by rfl⟩ : syracuseStep 1444771 = 2167157) B2167157
theorem B2165681 : Blo 1443541 2165681 := bstep (se 2 (by rfl) ⟨812130, by rfl⟩ : syracuseStep 2165681 = 1624261) B1624261
theorem B1444787 : Blo 1443541 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B2165699 : Blo 1443541 2165699 := bstep (se 1 (by rfl) ⟨1624274, by rfl⟩ : syracuseStep 2165699 = 3248549) B3248549
theorem B1444803 : Blo 1443541 1444803 := bstep (se 1 (by rfl) ⟨1083602, by rfl⟩ : syracuseStep 1444803 = 2167205) B2167205
theorem B1444819 : Blo 1443541 1444819 := bstep (se 1 (by rfl) ⟨1083614, by rfl⟩ : syracuseStep 1444819 = 2167229) B2167229
theorem B2165729 : Blo 1443541 2165729 := bstep (se 2 (by rfl) ⟨812148, by rfl⟩ : syracuseStep 2165729 = 1624297) B1624297
theorem B19753955 : Blo 1443541 19753955 := bstep (se 1 (by rfl) ⟨14815466, by rfl⟩ : syracuseStep 19753955 = 29630933) B29630933
theorem B1444835 : Blo 1443541 1444835 := bstep (se 1 (by rfl) ⟨1083626, by rfl⟩ : syracuseStep 1444835 = 2167253) B2167253
theorem B2165747 : Blo 1443541 2165747 := bstep (se 1 (by rfl) ⟨1624310, by rfl⟩ : syracuseStep 2165747 = 3248621) B3248621
theorem B1444851 : Blo 1443541 1444851 := bstep (se 1 (by rfl) ⟨1083638, by rfl⟩ : syracuseStep 1444851 = 2167277) B2167277
theorem B1444867 : Blo 1443541 1444867 := bstep (se 1 (by rfl) ⟨1083650, by rfl⟩ : syracuseStep 1444867 = 2167301) B2167301
theorem B2165777 : Blo 1443541 2165777 := bstep (se 2 (by rfl) ⟨812166, by rfl⟩ : syracuseStep 2165777 = 1624333) B1624333
theorem B2436115 : Blo 1443541 2436115 := bstep (se 1 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 2436115 = 3654173) B3654173
theorem B1625107 : Blo 1443541 1625107 := bstep (se 1 (by rfl) ⟨1218830, by rfl⟩ : syracuseStep 1625107 = 2437661) B2437661
theorem B1444883 : Blo 1443541 1444883 := bstep (se 1 (by rfl) ⟨1083662, by rfl⟩ : syracuseStep 1444883 = 2167325) B2167325
theorem B2165795 : Blo 1443541 2165795 := bstep (se 1 (by rfl) ⟨1624346, by rfl⟩ : syracuseStep 2165795 = 3248693) B3248693
theorem B1444899 : Blo 1443541 1444899 := bstep (se 1 (by rfl) ⟨1083674, by rfl⟩ : syracuseStep 1444899 = 2167349) B2167349
theorem B1444915 : Blo 1443541 1444915 := bstep (se 1 (by rfl) ⟨1083686, by rfl⟩ : syracuseStep 1444915 = 2167373) B2167373
theorem B2165825 : Blo 1443541 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B1444931 : Blo 1443541 1444931 := bstep (se 1 (by rfl) ⟨1083698, by rfl⟩ : syracuseStep 1444931 = 2167397) B2167397
theorem B3656785 : Blo 1443541 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B2165843 : Blo 1443541 2165843 := bstep (se 1 (by rfl) ⟨1624382, by rfl⟩ : syracuseStep 2165843 = 3248765) B3248765
theorem B1444947 : Blo 1443541 1444947 := bstep (se 1 (by rfl) ⟨1083710, by rfl⟩ : syracuseStep 1444947 = 2167421) B2167421
theorem B3083363 : Blo 1443541 3083363 := bstep (se 1 (by rfl) ⟨2312522, by rfl⟩ : syracuseStep 3083363 = 4625045) B4625045
theorem B1444963 : Blo 1443541 1444963 := bstep (se 1 (by rfl) ⟨1083722, by rfl⟩ : syracuseStep 1444963 = 2167445) B2167445
theorem B2165873 : Blo 1443541 2165873 := bstep (se 2 (by rfl) ⟨812202, by rfl⟩ : syracuseStep 2165873 = 1624405) B1624405
theorem B1444979 : Blo 1443541 1444979 := bstep (se 1 (by rfl) ⟨1083734, by rfl⟩ : syracuseStep 1444979 = 2167469) B2167469
theorem B2165891 : Blo 1443541 2165891 := bstep (se 1 (by rfl) ⟨1624418, by rfl⟩ : syracuseStep 2165891 = 3248837) B3248837
theorem B1444995 : Blo 1443541 1444995 := bstep (se 1 (by rfl) ⟨1083746, by rfl⟩ : syracuseStep 1444995 = 2167493) B2167493
theorem B1445011 : Blo 1443541 1445011 := bstep (se 1 (by rfl) ⟨1083758, by rfl⟩ : syracuseStep 1445011 = 2167517) B2167517
theorem B2436257 : Blo 1443541 2436257 := bstep (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) B1827193
theorem B2165921 : Blo 1443541 2165921 := bstep (se 2 (by rfl) ⟨812220, by rfl⟩ : syracuseStep 2165921 = 1624441) B1624441
theorem B1625251 : Blo 1443541 1625251 := bstep (se 1 (by rfl) ⟨1218938, by rfl⟩ : syracuseStep 1625251 = 2437877) B2437877
theorem B1445027 : Blo 1443541 1445027 := bstep (se 1 (by rfl) ⟨1083770, by rfl⟩ : syracuseStep 1445027 = 2167541) B2167541
theorem B2165939 : Blo 1443541 2165939 := bstep (se 1 (by rfl) ⟨1624454, by rfl⟩ : syracuseStep 2165939 = 3248909) B3248909
theorem B1445043 : Blo 1443541 1445043 := bstep (se 1 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 1445043 = 2167565) B2167565
theorem B1445059 : Blo 1443541 1445059 := bstep (se 1 (by rfl) ⟨1083794, by rfl⟩ : syracuseStep 1445059 = 2167589) B2167589
theorem B12340421 : Blo 1443541 12340421 := bstep (se 4 (by rfl) ⟨1156914, by rfl⟩ : syracuseStep 12340421 = 2313829) B2313829
theorem B2165969 : Blo 1443541 2165969 := bstep (se 2 (by rfl) ⟨812238, by rfl⟩ : syracuseStep 2165969 = 1624477) B1624477
theorem B1445075 : Blo 1443541 1445075 := bstep (se 1 (by rfl) ⟨1083806, by rfl⟩ : syracuseStep 1445075 = 2167613) B2167613
theorem B9260237 : Blo 1443541 9260237 := bstep (se 3 (by rfl) ⟨1736294, by rfl⟩ : syracuseStep 9260237 = 3472589) B3472589
theorem B2165987 : Blo 1443541 2165987 := bstep (se 1 (by rfl) ⟨1624490, by rfl⟩ : syracuseStep 2165987 = 3248981) B3248981
theorem B1445091 : Blo 1443541 1445091 := bstep (se 1 (by rfl) ⟨1083818, by rfl⟩ : syracuseStep 1445091 = 2167637) B2167637
theorem B1445107 : Blo 1443541 1445107 := bstep (se 1 (by rfl) ⟨1083830, by rfl⟩ : syracuseStep 1445107 = 2167661) B2167661
theorem B4877549 : Blo 1443541 4877549 := bstep (se 3 (by rfl) ⟨914540, by rfl⟩ : syracuseStep 4877549 = 1829081) B1829081
theorem B2166017 : Blo 1443541 2166017 := bstep (se 2 (by rfl) ⟨812256, by rfl⟩ : syracuseStep 2166017 = 1624513) B1624513
theorem B1445123 : Blo 1443541 1445123 := bstep (se 1 (by rfl) ⟨1083842, by rfl⟩ : syracuseStep 1445123 = 2167685) B2167685
theorem B2166035 : Blo 1443541 2166035 := bstep (se 1 (by rfl) ⟨1624526, by rfl⟩ : syracuseStep 2166035 = 3249053) B3249053
theorem B1445139 : Blo 1443541 1445139 := bstep (se 1 (by rfl) ⟨1083854, by rfl⟩ : syracuseStep 1445139 = 2167709) B2167709
theorem B2436385 : Blo 1443541 2436385 := bstep (se 2 (by rfl) ⟨913644, by rfl⟩ : syracuseStep 2436385 = 1827289) B1827289
theorem B1445155 : Blo 1443541 1445155 := bstep (se 1 (by rfl) ⟨1083866, by rfl⟩ : syracuseStep 1445155 = 2167733) B2167733
theorem B4877603 : Blo 1443541 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B2166065 : Blo 1443541 2166065 := bstep (se 2 (by rfl) ⟨812274, by rfl⟩ : syracuseStep 2166065 = 1624549) B1624549
theorem B1625395 : Blo 1443541 1625395 := bstep (se 1 (by rfl) ⟨1219046, by rfl⟩ : syracuseStep 1625395 = 2438093) B2438093
theorem B1445171 : Blo 1443541 1445171 := bstep (se 1 (by rfl) ⟨1083878, by rfl⟩ : syracuseStep 1445171 = 2167757) B2167757
theorem B2436419 : Blo 1443541 2436419 := bstep (se 1 (by rfl) ⟨1827314, by rfl⟩ : syracuseStep 2436419 = 3654629) B3654629
theorem B2166083 : Blo 1443541 2166083 := bstep (se 1 (by rfl) ⟨1624562, by rfl⟩ : syracuseStep 2166083 = 3249125) B3249125
theorem B12332357 : Blo 1443541 12332357 := bstep (se 4 (by rfl) ⟨1156158, by rfl⟩ : syracuseStep 12332357 = 2312317) B2312317
theorem B1445187 : Blo 1443541 1445187 := bstep (se 1 (by rfl) ⟨1083890, by rfl⟩ : syracuseStep 1445187 = 2167781) B2167781
theorem B1445203 : Blo 1443541 1445203 := bstep (se 1 (by rfl) ⟨1083902, by rfl⟩ : syracuseStep 1445203 = 2167805) B2167805
theorem B2166113 : Blo 1443541 2166113 := bstep (se 2 (by rfl) ⟨812292, by rfl⟩ : syracuseStep 2166113 = 1624585) B1624585
theorem B3657059 : Blo 1443541 3657059 := bstep (se 1 (by rfl) ⟨2742794, by rfl⟩ : syracuseStep 3657059 = 5485589) B5485589
theorem B1445219 : Blo 1443541 1445219 := bstep (se 1 (by rfl) ⟨1083914, by rfl⟩ : syracuseStep 1445219 = 2167829) B2167829
theorem B2166131 : Blo 1443541 2166131 := bstep (se 1 (by rfl) ⟨1624598, by rfl⟩ : syracuseStep 2166131 = 3249197) B3249197
theorem B1445235 : Blo 1443541 1445235 := bstep (se 1 (by rfl) ⟨1083926, by rfl⟩ : syracuseStep 1445235 = 2167853) B2167853
theorem B1445251 : Blo 1443541 1445251 := bstep (se 1 (by rfl) ⟨1083938, by rfl⟩ : syracuseStep 1445251 = 2167877) B2167877
theorem B4115843 : Blo 1443541 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B3468689 : Blo 1443541 3468689 := bstep (se 2 (by rfl) ⟨1300758, by rfl⟩ : syracuseStep 3468689 = 2601517) B2601517
theorem B2166161 : Blo 1443541 2166161 := bstep (se 2 (by rfl) ⟨812310, by rfl⟩ : syracuseStep 2166161 = 1624621) B1624621
theorem B1445267 : Blo 1443541 1445267 := bstep (se 1 (by rfl) ⟨1083950, by rfl⟩ : syracuseStep 1445267 = 2167901) B2167901
theorem B2166179 : Blo 1443541 2166179 := bstep (se 1 (by rfl) ⟨1624634, by rfl⟩ : syracuseStep 2166179 = 3249269) B3249269
theorem B1445283 : Blo 1443541 1445283 := bstep (se 1 (by rfl) ⟨1083962, by rfl⟩ : syracuseStep 1445283 = 2167925) B2167925
theorem B1445299 : Blo 1443541 1445299 := bstep (se 1 (by rfl) ⟨1083974, by rfl⟩ : syracuseStep 1445299 = 2167949) B2167949
theorem B2166209 : Blo 1443541 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B2436547 : Blo 1443541 2436547 := bstep (se 1 (by rfl) ⟨1827410, by rfl⟩ : syracuseStep 2436547 = 3654821) B3654821
theorem B1625539 : Blo 1443541 1625539 := bstep (se 1 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 1625539 = 2438309) B2438309
theorem B10407365 : Blo 1443541 10407365 := bstep (se 4 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 10407365 = 1951381) B1951381
theorem B1445315 : Blo 1443541 1445315 := bstep (se 1 (by rfl) ⟨1083986, by rfl⟩ : syracuseStep 1445315 = 2167973) B2167973
theorem B6172109 : Blo 1443541 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B2166227 : Blo 1443541 2166227 := bstep (se 1 (by rfl) ⟨1624670, by rfl⟩ : syracuseStep 2166227 = 3249341) B3249341
theorem B1445331 : Blo 1443541 1445331 := bstep (se 1 (by rfl) ⟨1083998, by rfl⟩ : syracuseStep 1445331 = 2167997) B2167997
theorem B1445347 : Blo 1443541 1445347 := bstep (se 1 (by rfl) ⟨1084010, by rfl⟩ : syracuseStep 1445347 = 2168021) B2168021
theorem B2166257 : Blo 1443541 2166257 := bstep (se 2 (by rfl) ⟨812346, by rfl⟩ : syracuseStep 2166257 = 1624693) B1624693
theorem B1445363 : Blo 1443541 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B2166275 : Blo 1443541 2166275 := bstep (se 1 (by rfl) ⟨1624706, by rfl⟩ : syracuseStep 2166275 = 3249413) B3249413
theorem B1445379 : Blo 1443541 1445379 := bstep (se 1 (by rfl) ⟨1084034, by rfl⟩ : syracuseStep 1445379 = 2168069) B2168069
theorem B7409165 : Blo 1443541 7409165 := bstep (se 3 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 7409165 = 2778437) B2778437
theorem B1445395 : Blo 1443541 1445395 := bstep (se 1 (by rfl) ⟨1084046, by rfl⟩ : syracuseStep 1445395 = 2168093) B2168093
theorem B2166305 : Blo 1443541 2166305 := bstep (se 2 (by rfl) ⟨812364, by rfl⟩ : syracuseStep 2166305 = 1624729) B1624729
theorem B3657251 : Blo 1443541 3657251 := bstep (se 1 (by rfl) ⟨2742938, by rfl⟩ : syracuseStep 3657251 = 5485877) B5485877
theorem B1445411 : Blo 1443541 1445411 := bstep (se 1 (by rfl) ⟨1084058, by rfl⟩ : syracuseStep 1445411 = 2168117) B2168117
theorem B3083825 : Blo 1443541 3083825 := bstep (se 2 (by rfl) ⟨1156434, by rfl⟩ : syracuseStep 3083825 = 2312869) B2312869
theorem B7310897 : Blo 1443541 7310897 := bstep (se 2 (by rfl) ⟨2741586, by rfl⟩ : syracuseStep 7310897 = 5483173) B5483173
theorem B2166323 : Blo 1443541 2166323 := bstep (se 1 (by rfl) ⟨1624742, by rfl⟩ : syracuseStep 2166323 = 3249485) B3249485
theorem B6942257 : Blo 1443541 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B4877873 : Blo 1443541 4877873 := bstep (se 2 (by rfl) ⟨1829202, by rfl⟩ : syracuseStep 4877873 = 3658405) B3658405
theorem B1445427 : Blo 1443541 1445427 := bstep (se 1 (by rfl) ⟨1084070, by rfl⟩ : syracuseStep 1445427 = 2168141) B2168141
theorem B1445443 : Blo 1443541 1445443 := bstep (se 1 (by rfl) ⟨1084082, by rfl⟩ : syracuseStep 1445443 = 2168165) B2168165
theorem B2436689 : Blo 1443541 2436689 := bstep (se 2 (by rfl) ⟨913758, by rfl⟩ : syracuseStep 2436689 = 1827517) B1827517
theorem B2166353 : Blo 1443541 2166353 := bstep (se 2 (by rfl) ⟨812382, by rfl⟩ : syracuseStep 2166353 = 1624765) B1624765
theorem B1625683 : Blo 1443541 1625683 := bstep (se 1 (by rfl) ⟨1219262, by rfl⟩ : syracuseStep 1625683 = 2438525) B2438525
theorem B1445459 : Blo 1443541 1445459 := bstep (se 1 (by rfl) ⟨1084094, by rfl⟩ : syracuseStep 1445459 = 2168189) B2168189
theorem B3468899 : Blo 1443541 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B2166371 : Blo 1443541 2166371 := bstep (se 1 (by rfl) ⟨1624778, by rfl⟩ : syracuseStep 2166371 = 3249557) B3249557
theorem B5484131 : Blo 1443541 5484131 := bstep (se 1 (by rfl) ⟨4113098, by rfl⟩ : syracuseStep 5484131 = 8226197) B8226197
theorem B1445475 : Blo 1443541 1445475 := bstep (se 1 (by rfl) ⟨1084106, by rfl⟩ : syracuseStep 1445475 = 2168213) B2168213
theorem B5484145 : Blo 1443541 5484145 := bstep (se 2 (by rfl) ⟨2056554, by rfl⟩ : syracuseStep 5484145 = 4113109) B4113109
theorem B1445491 : Blo 1443541 1445491 := bstep (se 1 (by rfl) ⟨1084118, by rfl⟩ : syracuseStep 1445491 = 2168237) B2168237
theorem B2166401 : Blo 1443541 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1445507 : Blo 1443541 1445507 := bstep (se 1 (by rfl) ⟨1084130, by rfl⟩ : syracuseStep 1445507 = 2168261) B2168261
theorem B2166419 : Blo 1443541 2166419 := bstep (se 1 (by rfl) ⟨1624814, by rfl⟩ : syracuseStep 2166419 = 3249629) B3249629
theorem B1445523 : Blo 1443541 1445523 := bstep (se 1 (by rfl) ⟨1084142, by rfl⟩ : syracuseStep 1445523 = 2168285) B2168285
theorem B1445539 : Blo 1443541 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B2166449 : Blo 1443541 2166449 := bstep (se 2 (by rfl) ⟨812418, by rfl⟩ : syracuseStep 2166449 = 1624837) B1624837
theorem B2928305 : Blo 1443541 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B2166467 : Blo 1443541 2166467 := bstep (se 1 (by rfl) ⟨1624850, by rfl⟩ : syracuseStep 2166467 = 3249701) B3249701
theorem B2436817 : Blo 1443541 2436817 := bstep (se 2 (by rfl) ⟨913806, by rfl⟩ : syracuseStep 2436817 = 1827613) B1827613
theorem B2166497 : Blo 1443541 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1625827 : Blo 1443541 1625827 := bstep (se 1 (by rfl) ⟨1219370, by rfl⟩ : syracuseStep 1625827 = 2438741) B2438741
theorem B1953505 : Blo 1443541 1953505 := bstep (se 2 (by rfl) ⟨732564, by rfl⟩ : syracuseStep 1953505 = 1465129) B1465129
theorem B6942449 : Blo 1443541 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B12349169 : Blo 1443541 12349169 := bstep (se 2 (by rfl) ⟨4630938, by rfl⟩ : syracuseStep 12349169 = 9261877) B9261877
theorem B2436851 : Blo 1443541 2436851 := bstep (se 1 (by rfl) ⟨1827638, by rfl⟩ : syracuseStep 2436851 = 3655277) B3655277
theorem B2166515 : Blo 1443541 2166515 := bstep (se 1 (by rfl) ⟨1624886, by rfl⟩ : syracuseStep 2166515 = 3249773) B3249773
theorem B2166545 : Blo 1443541 2166545 := bstep (se 2 (by rfl) ⟨812454, by rfl⟩ : syracuseStep 2166545 = 1624909) B1624909
theorem B2166563 : Blo 1443541 2166563 := bstep (se 1 (by rfl) ⟨1624922, by rfl⟩ : syracuseStep 2166563 = 3249845) B3249845
theorem B2166593 : Blo 1443541 2166593 := bstep (se 2 (by rfl) ⟨812472, by rfl⟩ : syracuseStep 2166593 = 1624945) B1624945
theorem B2166611 : Blo 1443541 2166611 := bstep (se 1 (by rfl) ⟨1624958, by rfl⟩ : syracuseStep 2166611 = 3249917) B3249917
theorem B2166641 : Blo 1443541 2166641 := bstep (se 2 (by rfl) ⟨812490, by rfl⟩ : syracuseStep 2166641 = 1624981) B1624981
theorem B12341105 : Blo 1443541 12341105 := bstep (se 2 (by rfl) ⟨4627914, by rfl⟩ : syracuseStep 12341105 = 9255829) B9255829
theorem B2436979 : Blo 1443541 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B2314099 : Blo 1443541 2314099 := bstep (se 1 (by rfl) ⟨1735574, by rfl⟩ : syracuseStep 2314099 = 3471149) B3471149
theorem B1625971 : Blo 1443541 1625971 := bstep (se 1 (by rfl) ⟨1219478, by rfl⟩ : syracuseStep 1625971 = 2438957) B2438957
theorem B2166659 : Blo 1443541 2166659 := bstep (se 1 (by rfl) ⟨1624994, by rfl⟩ : syracuseStep 2166659 = 3249989) B3249989
theorem B22548365 : Blo 1443541 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B2166689 : Blo 1443541 2166689 := bstep (se 2 (by rfl) ⟨812508, by rfl⟩ : syracuseStep 2166689 = 1625017) B1625017
theorem B2166707 : Blo 1443541 2166707 := bstep (se 1 (by rfl) ⟨1625030, by rfl⟩ : syracuseStep 2166707 = 3250061) B3250061
theorem B2314163 : Blo 1443541 2314163 := bstep (se 1 (by rfl) ⟨1735622, by rfl⟩ : syracuseStep 2314163 = 3471245) B3471245
theorem B3248081 : Blo 1443541 3248081 := bstep (se 2 (by rfl) ⟨1218030, by rfl⟩ : syracuseStep 3248081 = 2436061) B2436061
theorem B2166737 : Blo 1443541 2166737 := bstep (se 2 (by rfl) ⟨812526, by rfl⟩ : syracuseStep 2166737 = 1625053) B1625053
theorem B4943825 : Blo 1443541 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B3248099 : Blo 1443541 3248099 := bstep (se 1 (by rfl) ⟨2436074, by rfl⟩ : syracuseStep 3248099 = 4872149) B4872149
theorem B2166755 : Blo 1443541 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B2437121 : Blo 1443541 2437121 := bstep (se 2 (by rfl) ⟨913920, by rfl⟩ : syracuseStep 2437121 = 1827841) B1827841
theorem B2166785 : Blo 1443541 2166785 := bstep (se 2 (by rfl) ⟨812544, by rfl⟩ : syracuseStep 2166785 = 1625089) B1625089
theorem B3706883 : Blo 1443541 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B1626115 : Blo 1443541 1626115 := bstep (se 1 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 1626115 = 2439173) B2439173
theorem B9375749 : Blo 1443541 9375749 := bstep (se 4 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 9375749 = 1757953) B1757953
theorem B2166803 : Blo 1443541 2166803 := bstep (se 1 (by rfl) ⟨1625102, by rfl⟩ : syracuseStep 2166803 = 3250205) B3250205
theorem B2166833 : Blo 1443541 2166833 := bstep (se 2 (by rfl) ⟨812562, by rfl⟩ : syracuseStep 2166833 = 1625125) B1625125
theorem B2166851 : Blo 1443541 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B4878413 : Blo 1443541 4878413 := bstep (se 3 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 4878413 = 1829405) B1829405
theorem B2166881 : Blo 1443541 2166881 := bstep (se 2 (by rfl) ⟨812580, by rfl⟩ : syracuseStep 2166881 = 1625161) B1625161
theorem B2166899 : Blo 1443541 2166899 := bstep (se 1 (by rfl) ⟨1625174, by rfl⟩ : syracuseStep 2166899 = 3250349) B3250349
theorem B2437249 : Blo 1443541 2437249 := bstep (se 2 (by rfl) ⟨913968, by rfl⟩ : syracuseStep 2437249 = 1827937) B1827937
theorem B4878467 : Blo 1443541 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B2166929 : Blo 1443541 2166929 := bstep (se 2 (by rfl) ⟨812598, by rfl⟩ : syracuseStep 2166929 = 1625197) B1625197
theorem B2437283 : Blo 1443541 2437283 := bstep (se 1 (by rfl) ⟨1827962, by rfl⟩ : syracuseStep 2437283 = 3655925) B3655925
theorem B2166947 : Blo 1443541 2166947 := bstep (se 1 (by rfl) ⟨1625210, by rfl⟩ : syracuseStep 2166947 = 3250421) B3250421
theorem B2166977 : Blo 1443541 2166977 := bstep (se 2 (by rfl) ⟨812616, by rfl⟩ : syracuseStep 2166977 = 1625233) B1625233
theorem B9253061 : Blo 1443541 9253061 := bstep (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) B1734949
theorem B2166995 : Blo 1443541 2166995 := bstep (se 1 (by rfl) ⟨1625246, by rfl⟩ : syracuseStep 2166995 = 3250493) B3250493
theorem B3248369 : Blo 1443541 3248369 := bstep (se 2 (by rfl) ⟨1218138, by rfl⟩ : syracuseStep 3248369 = 2436277) B2436277
theorem B2167025 : Blo 1443541 2167025 := bstep (se 2 (by rfl) ⟨812634, by rfl⟩ : syracuseStep 2167025 = 1625269) B1625269
theorem B3248387 : Blo 1443541 3248387 := bstep (se 1 (by rfl) ⟨2436290, by rfl⟩ : syracuseStep 3248387 = 4872581) B4872581
theorem B2167043 : Blo 1443541 2167043 := bstep (se 1 (by rfl) ⟨1625282, by rfl⟩ : syracuseStep 2167043 = 3250565) B3250565
theorem B2167073 : Blo 1443541 2167073 := bstep (se 2 (by rfl) ⟨812652, by rfl⟩ : syracuseStep 2167073 = 1625305) B1625305
theorem B2437411 : Blo 1443541 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B2167091 : Blo 1443541 2167091 := bstep (se 1 (by rfl) ⟨1625318, by rfl⟩ : syracuseStep 2167091 = 3250637) B3250637
theorem B2740547 : Blo 1443541 2740547 := bstep (se 1 (by rfl) ⟨2055410, by rfl⟩ : syracuseStep 2740547 = 4110821) B4110821
theorem B8335685 : Blo 1443541 8335685 := bstep (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) B1562941
theorem B2167121 : Blo 1443541 2167121 := bstep (se 2 (by rfl) ⟨812670, by rfl⟩ : syracuseStep 2167121 = 1625341) B1625341
theorem B2167139 : Blo 1443541 2167139 := bstep (se 1 (by rfl) ⟨1625354, by rfl⟩ : syracuseStep 2167139 = 3250709) B3250709
theorem B3756401 : Blo 1443541 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B12513649 : Blo 1443541 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B2167169 : Blo 1443541 2167169 := bstep (se 2 (by rfl) ⟨812688, by rfl⟩ : syracuseStep 2167169 = 1625377) B1625377
theorem B18510221 : Blo 1443541 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B2167187 : Blo 1443541 2167187 := bstep (se 1 (by rfl) ⟨1625390, by rfl⟩ : syracuseStep 2167187 = 3250781) B3250781
theorem B2437553 : Blo 1443541 2437553 := bstep (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) B1828165
theorem B2167217 : Blo 1443541 2167217 := bstep (se 2 (by rfl) ⟨812706, by rfl⟩ : syracuseStep 2167217 = 1625413) B1625413
theorem B2167235 : Blo 1443541 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B16462277 : Blo 1443541 16462277 := bstep (se 4 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 16462277 = 3086677) B3086677
theorem B3658193 : Blo 1443541 3658193 := bstep (se 2 (by rfl) ⟨1371822, by rfl⟩ : syracuseStep 3658193 = 2743645) B2743645
theorem B2167265 : Blo 1443541 2167265 := bstep (se 2 (by rfl) ⟨812724, by rfl⟩ : syracuseStep 2167265 = 1625449) B1625449
theorem B2167283 : Blo 1443541 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B3658243 : Blo 1443541 3658243 := bstep (se 1 (by rfl) ⟨2743682, by rfl⟩ : syracuseStep 3658243 = 5487365) B5487365
theorem B3248657 : Blo 1443541 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B2167313 : Blo 1443541 2167313 := bstep (se 2 (by rfl) ⟨812742, by rfl⟩ : syracuseStep 2167313 = 1625485) B1625485
theorem B3248675 : Blo 1443541 3248675 := bstep (se 1 (by rfl) ⟨2436506, by rfl⟩ : syracuseStep 3248675 = 4873013) B4873013
theorem B2167331 : Blo 1443541 2167331 := bstep (se 1 (by rfl) ⟨1625498, by rfl⟩ : syracuseStep 2167331 = 3250997) B3250997
theorem B2437681 : Blo 1443541 2437681 := bstep (se 2 (by rfl) ⟨914130, by rfl⟩ : syracuseStep 2437681 = 1828261) B1828261
theorem B2167361 : Blo 1443541 2167361 := bstep (se 2 (by rfl) ⟨812760, by rfl⟩ : syracuseStep 2167361 = 1625521) B1625521
theorem B2601553 : Blo 1443541 2601553 := bstep (se 2 (by rfl) ⟨975582, by rfl⟩ : syracuseStep 2601553 = 1951165) B1951165
theorem B2437715 : Blo 1443541 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B2167379 : Blo 1443541 2167379 := bstep (se 1 (by rfl) ⟨1625534, by rfl⟩ : syracuseStep 2167379 = 3251069) B3251069
theorem B10965617 : Blo 1443541 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B2167409 : Blo 1443541 2167409 := bstep (se 2 (by rfl) ⟨812778, by rfl⟩ : syracuseStep 2167409 = 1625557) B1625557
theorem B2167427 : Blo 1443541 2167427 := bstep (se 1 (by rfl) ⟨1625570, by rfl⟩ : syracuseStep 2167427 = 3251141) B3251141
theorem B3658385 : Blo 1443541 3658385 := bstep (se 2 (by rfl) ⟨1371894, by rfl⟩ : syracuseStep 3658385 = 2743789) B2743789
theorem B2167457 : Blo 1443541 2167457 := bstep (se 2 (by rfl) ⟨812796, by rfl⟩ : syracuseStep 2167457 = 1625593) B1625593
theorem B2167475 : Blo 1443541 2167475 := bstep (se 1 (by rfl) ⟨1625606, by rfl⟩ : syracuseStep 2167475 = 3251213) B3251213
theorem B2167505 : Blo 1443541 2167505 := bstep (se 2 (by rfl) ⟨812814, by rfl⟩ : syracuseStep 2167505 = 1625629) B1625629
theorem B2437843 : Blo 1443541 2437843 := bstep (se 1 (by rfl) ⟨1828382, by rfl⟩ : syracuseStep 2437843 = 3656765) B3656765
theorem B2167523 : Blo 1443541 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B2167553 : Blo 1443541 2167553 := bstep (se 2 (by rfl) ⟨812832, by rfl⟩ : syracuseStep 2167553 = 1625665) B1625665
theorem B2167571 : Blo 1443541 2167571 := bstep (se 1 (by rfl) ⟨1625678, by rfl⟩ : syracuseStep 2167571 = 3251357) B3251357
theorem B3248945 : Blo 1443541 3248945 := bstep (se 2 (by rfl) ⟨1218354, by rfl⟩ : syracuseStep 3248945 = 2436709) B2436709
theorem B3470129 : Blo 1443541 3470129 := bstep (se 2 (by rfl) ⟨1301298, by rfl⟩ : syracuseStep 3470129 = 2602597) B2602597
theorem B2167601 : Blo 1443541 2167601 := bstep (se 2 (by rfl) ⟨812850, by rfl⟩ : syracuseStep 2167601 = 1625701) B1625701
theorem B3248963 : Blo 1443541 3248963 := bstep (se 1 (by rfl) ⟨2436722, by rfl⟩ : syracuseStep 3248963 = 4873445) B4873445
theorem B3085123 : Blo 1443541 3085123 := bstep (se 1 (by rfl) ⟨2313842, by rfl⟩ : syracuseStep 3085123 = 4627685) B4627685
theorem B2167619 : Blo 1443541 2167619 := bstep (se 1 (by rfl) ⟨1625714, by rfl⟩ : syracuseStep 2167619 = 3251429) B3251429
theorem B2437985 : Blo 1443541 2437985 := bstep (se 2 (by rfl) ⟨914244, by rfl⟩ : syracuseStep 2437985 = 1828489) B1828489
theorem B2167649 : Blo 1443541 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B2167667 : Blo 1443541 2167667 := bstep (se 1 (by rfl) ⟨1625750, by rfl⟩ : syracuseStep 2167667 = 3251501) B3251501
theorem B2315137 : Blo 1443541 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B23442317 : Blo 1443541 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B2167697 : Blo 1443541 2167697 := bstep (se 2 (by rfl) ⟨812886, by rfl⟩ : syracuseStep 2167697 = 1625773) B1625773
theorem B2167715 : Blo 1443541 2167715 := bstep (se 1 (by rfl) ⟨1625786, by rfl⟩ : syracuseStep 2167715 = 3251573) B3251573
theorem B2167745 : Blo 1443541 2167745 := bstep (se 2 (by rfl) ⟨812904, by rfl⟩ : syracuseStep 2167745 = 1625809) B1625809
theorem B2167763 : Blo 1443541 2167763 := bstep (se 1 (by rfl) ⟨1625822, by rfl⟩ : syracuseStep 2167763 = 3251645) B3251645
theorem B2438113 : Blo 1443541 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B7312355 : Blo 1443541 7312355 := bstep (se 1 (by rfl) ⟨5484266, by rfl⟩ : syracuseStep 7312355 = 10968533) B10968533
theorem B3470321 : Blo 1443541 3470321 := bstep (se 2 (by rfl) ⟨1301370, by rfl⟩ : syracuseStep 3470321 = 2602741) B2602741
theorem B2167793 : Blo 1443541 2167793 := bstep (se 2 (by rfl) ⟨812922, by rfl⟩ : syracuseStep 2167793 = 1625845) B1625845
theorem B2438147 : Blo 1443541 2438147 := bstep (se 1 (by rfl) ⟨1828610, by rfl⟩ : syracuseStep 2438147 = 3657221) B3657221
theorem B2167811 : Blo 1443541 2167811 := bstep (se 1 (by rfl) ⟨1625858, by rfl⟩ : syracuseStep 2167811 = 3251717) B3251717
theorem B2167841 : Blo 1443541 2167841 := bstep (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) B1625881
theorem B5485603 : Blo 1443541 5485603 := bstep (se 1 (by rfl) ⟨4114202, by rfl⟩ : syracuseStep 5485603 = 8228405) B8228405
theorem B2167859 : Blo 1443541 2167859 := bstep (se 1 (by rfl) ⟨1625894, by rfl⟩ : syracuseStep 2167859 = 3251789) B3251789
theorem B3085379 : Blo 1443541 3085379 := bstep (se 1 (by rfl) ⟨2314034, by rfl⟩ : syracuseStep 3085379 = 4628069) B4628069
theorem B3249233 : Blo 1443541 3249233 := bstep (se 2 (by rfl) ⟨1218462, by rfl⟩ : syracuseStep 3249233 = 2436925) B2436925
theorem B2167889 : Blo 1443541 2167889 := bstep (se 2 (by rfl) ⟨812958, by rfl⟩ : syracuseStep 2167889 = 1625917) B1625917
theorem B3249251 : Blo 1443541 3249251 := bstep (se 1 (by rfl) ⟨2436938, by rfl⟩ : syracuseStep 3249251 = 4873877) B4873877
theorem B2167907 : Blo 1443541 2167907 := bstep (se 1 (by rfl) ⟨1625930, by rfl⟩ : syracuseStep 2167907 = 3251861) B3251861
theorem B2167937 : Blo 1443541 2167937 := bstep (se 2 (by rfl) ⟨812976, by rfl⟩ : syracuseStep 2167937 = 1625953) B1625953
theorem B2315393 : Blo 1443541 2315393 := bstep (se 2 (by rfl) ⟨868272, by rfl⟩ : syracuseStep 2315393 = 1736545) B1736545
theorem B2438275 : Blo 1443541 2438275 := bstep (se 1 (by rfl) ⟨1828706, by rfl⟩ : syracuseStep 2438275 = 3657413) B3657413
theorem B2167955 : Blo 1443541 2167955 := bstep (se 1 (by rfl) ⟨1625966, by rfl⟩ : syracuseStep 2167955 = 3251933) B3251933
theorem B2167985 : Blo 1443541 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B2168003 : Blo 1443541 2168003 := bstep (se 1 (by rfl) ⟨1626002, by rfl⟩ : syracuseStep 2168003 = 3252005) B3252005
theorem B2168033 : Blo 1443541 2168033 := bstep (se 2 (by rfl) ⟨813012, by rfl⟩ : syracuseStep 2168033 = 1626025) B1626025
theorem B35165411 : Blo 1443541 35165411 := bstep (se 1 (by rfl) ⟨26374058, by rfl⟩ : syracuseStep 35165411 = 52748117) B52748117
theorem B2168051 : Blo 1443541 2168051 := bstep (se 1 (by rfl) ⟨1626038, by rfl⟩ : syracuseStep 2168051 = 3252077) B3252077
theorem B2438417 : Blo 1443541 2438417 := bstep (se 2 (by rfl) ⟨914406, by rfl⟩ : syracuseStep 2438417 = 1828813) B1828813
theorem B2168081 : Blo 1443541 2168081 := bstep (se 2 (by rfl) ⟨813030, by rfl⟩ : syracuseStep 2168081 = 1626061) B1626061
theorem B5559587 : Blo 1443541 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B2168099 : Blo 1443541 2168099 := bstep (se 1 (by rfl) ⟨1626074, by rfl⟩ : syracuseStep 2168099 = 3252149) B3252149
theorem B2225459 : Blo 1443541 2225459 := bstep (se 1 (by rfl) ⟨1669094, by rfl⟩ : syracuseStep 2225459 = 3338189) B3338189
theorem B2168129 : Blo 1443541 2168129 := bstep (se 2 (by rfl) ⟨813048, by rfl⟩ : syracuseStep 2168129 = 1626097) B1626097
theorem B2168147 : Blo 1443541 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B2741617 : Blo 1443541 2741617 := bstep (se 2 (by rfl) ⟨1028106, by rfl⟩ : syracuseStep 2741617 = 2056213) B2056213
theorem B3249521 : Blo 1443541 3249521 := bstep (se 2 (by rfl) ⟨1218570, by rfl⟩ : syracuseStep 3249521 = 2437141) B2437141
theorem B2168177 : Blo 1443541 2168177 := bstep (se 2 (by rfl) ⟨813066, by rfl⟩ : syracuseStep 2168177 = 1626133) B1626133
theorem B3249539 : Blo 1443541 3249539 := bstep (se 1 (by rfl) ⟨2437154, by rfl⟩ : syracuseStep 3249539 = 4874309) B4874309
theorem B2168195 : Blo 1443541 2168195 := bstep (se 1 (by rfl) ⟨1626146, by rfl⟩ : syracuseStep 2168195 = 3252293) B3252293
theorem B2438545 : Blo 1443541 2438545 := bstep (se 2 (by rfl) ⟨914454, by rfl⟩ : syracuseStep 2438545 = 1828909) B1828909
theorem B2168225 : Blo 1443541 2168225 := bstep (se 2 (by rfl) ⟨813084, by rfl⟩ : syracuseStep 2168225 = 1626169) B1626169
theorem B2438579 : Blo 1443541 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B2168243 : Blo 1443541 2168243 := bstep (se 1 (by rfl) ⟨1626182, by rfl⟩ : syracuseStep 2168243 = 3252365) B3252365
theorem B2168273 : Blo 1443541 2168273 := bstep (se 2 (by rfl) ⟨813102, by rfl⟩ : syracuseStep 2168273 = 1626205) B1626205
theorem B2168291 : Blo 1443541 2168291 := bstep (se 1 (by rfl) ⟨1626218, by rfl⟩ : syracuseStep 2168291 = 3252437) B3252437
theorem B2438707 : Blo 1443541 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B3249809 : Blo 1443541 3249809 := bstep (se 2 (by rfl) ⟨1218678, by rfl⟩ : syracuseStep 3249809 = 2437357) B2437357
theorem B3249827 : Blo 1443541 3249827 := bstep (se 1 (by rfl) ⟨2437370, by rfl⟩ : syracuseStep 3249827 = 4874741) B4874741
theorem B16676533 : Blo 1443541 16676533 := bstep (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) B1563425
theorem B2438849 : Blo 1443541 2438849 := bstep (se 2 (by rfl) ⟨914568, by rfl⟩ : syracuseStep 2438849 = 1829137) B1829137
theorem B7313165 : Blo 1443541 7313165 := bstep (se 3 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 7313165 = 2742437) B2742437
theorem B31225621 : Blo 1443541 31225621 := bstep (se 6 (by rfl) ⟨731850, by rfl⟩ : syracuseStep 31225621 = 1463701) B1463701
theorem B2438977 : Blo 1443541 2438977 := bstep (se 2 (by rfl) ⟨914616, by rfl⟩ : syracuseStep 2438977 = 1829233) B1829233
theorem B5011267 : Blo 1443541 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B2439011 : Blo 1443541 2439011 := bstep (se 1 (by rfl) ⟨1829258, by rfl⟩ : syracuseStep 2439011 = 3658517) B3658517
theorem B7804849 : Blo 1443541 7804849 := bstep (se 2 (by rfl) ⟨2926818, by rfl⟩ : syracuseStep 7804849 = 5853637) B5853637
theorem B3250097 : Blo 1443541 3250097 := bstep (se 2 (by rfl) ⟨1218786, by rfl⟩ : syracuseStep 3250097 = 2437573) B2437573
theorem B3250115 : Blo 1443541 3250115 := bstep (se 1 (by rfl) ⟨2437586, by rfl⟩ : syracuseStep 3250115 = 4875173) B4875173
theorem B6944717 : Blo 1443541 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B2439139 : Blo 1443541 2439139 := bstep (se 1 (by rfl) ⟨1829354, by rfl⟩ : syracuseStep 2439139 = 3658709) B3658709
theorem B5208077 : Blo 1443541 5208077 := bstep (se 3 (by rfl) ⟨976514, by rfl⟩ : syracuseStep 5208077 = 1953029) B1953029
theorem B3086353 : Blo 1443541 3086353 := bstep (se 2 (by rfl) ⟨1157382, by rfl⟩ : syracuseStep 3086353 = 2314765) B2314765
theorem B8222755 : Blo 1443541 8222755 := bstep (se 1 (by rfl) ⟨6167066, by rfl⟩ : syracuseStep 8222755 = 12334133) B12334133
theorem B1562707 : Blo 1443541 1562707 := bstep (se 1 (by rfl) ⟨1172030, by rfl⟩ : syracuseStep 1562707 = 2344061) B2344061
theorem B2439281 : Blo 1443541 2439281 := bstep (se 2 (by rfl) ⟨914730, by rfl⟩ : syracuseStep 2439281 = 1829461) B1829461
theorem B7805069 : Blo 1443541 7805069 := bstep (se 3 (by rfl) ⟨1463450, by rfl⟩ : syracuseStep 7805069 = 2926901) B2926901
theorem B4872365 : Blo 1443541 4872365 := bstep (se 3 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 4872365 = 1827137) B1827137
theorem B9885893 : Blo 1443541 9885893 := bstep (se 4 (by rfl) ⟨926802, by rfl⟩ : syracuseStep 9885893 = 1853605) B1853605
theorem B3250385 : Blo 1443541 3250385 := bstep (se 2 (by rfl) ⟨1218894, by rfl⟩ : syracuseStep 3250385 = 2437789) B2437789
theorem B4872419 : Blo 1443541 4872419 := bstep (se 1 (by rfl) ⟨3654314, by rfl⟩ : syracuseStep 4872419 = 7308629) B7308629
theorem B4626659 : Blo 1443541 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B3250403 : Blo 1443541 3250403 := bstep (se 1 (by rfl) ⟨2437802, by rfl⟩ : syracuseStep 3250403 = 4875605) B4875605
theorem B2472241 : Blo 1443541 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B1464691 : Blo 1443541 1464691 := bstep (se 1 (by rfl) ⟨1098518, by rfl⟩ : syracuseStep 1464691 = 2197037) B2197037
theorem B2742673 : Blo 1443541 2742673 := bstep (se 2 (by rfl) ⟨1028502, by rfl⟩ : syracuseStep 2742673 = 2057005) B2057005
theorem B1464739 : Blo 1443541 1464739 := bstep (se 1 (by rfl) ⟨1098554, by rfl⟩ : syracuseStep 1464739 = 2197109) B2197109
theorem B1735123 : Blo 1443541 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B4872689 : Blo 1443541 4872689 := bstep (se 2 (by rfl) ⟨1827258, by rfl⟩ : syracuseStep 4872689 = 3654517) B3654517
theorem B3250673 : Blo 1443541 3250673 := bstep (se 2 (by rfl) ⟨1219002, by rfl⟩ : syracuseStep 3250673 = 2438005) B2438005
theorem B3250691 : Blo 1443541 3250691 := bstep (se 1 (by rfl) ⟨2438018, by rfl⟩ : syracuseStep 3250691 = 4876037) B4876037
theorem B8223281 : Blo 1443541 8223281 := bstep (se 2 (by rfl) ⟨3083730, by rfl⟩ : syracuseStep 8223281 = 6167461) B6167461
theorem B3087011 : Blo 1443541 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B35609315 : Blo 1443541 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B3906307 : Blo 1443541 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B3250961 : Blo 1443541 3250961 := bstep (se 2 (by rfl) ⟨1219110, by rfl⟩ : syracuseStep 3250961 = 2438221) B2438221
theorem B3250979 : Blo 1443541 3250979 := bstep (se 1 (by rfl) ⟨2438234, by rfl⟩ : syracuseStep 3250979 = 4876469) B4876469
theorem B2743075 : Blo 1443541 2743075 := bstep (se 1 (by rfl) ⟨2057306, by rfl⟩ : syracuseStep 2743075 = 4114613) B4114613
theorem B2743121 : Blo 1443541 2743121 := bstep (se 2 (by rfl) ⟨1028670, by rfl⟩ : syracuseStep 2743121 = 2057341) B2057341
theorem B9255779 : Blo 1443541 9255779 := bstep (se 1 (by rfl) ⟨6941834, by rfl⟩ : syracuseStep 9255779 = 13883669) B13883669
theorem B4873229 : Blo 1443541 4873229 := bstep (se 3 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 4873229 = 1827461) B1827461
theorem B4627505 : Blo 1443541 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B3251249 : Blo 1443541 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B4873283 : Blo 1443541 4873283 := bstep (se 1 (by rfl) ⟨3654962, by rfl⟩ : syracuseStep 4873283 = 7309925) B7309925
theorem B3251267 : Blo 1443541 3251267 := bstep (se 1 (by rfl) ⟨2438450, by rfl⟩ : syracuseStep 3251267 = 4876901) B4876901
theorem B15629381 : Blo 1443541 15629381 := bstep (se 4 (by rfl) ⟨1465254, by rfl⟩ : syracuseStep 15629381 = 2930509) B2930509
theorem B4111469 : Blo 1443541 4111469 := bstep (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) B1541801
theorem B2743409 : Blo 1443541 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B5209229 : Blo 1443541 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B11713733 : Blo 1443541 11713733 := bstep (se 4 (by rfl) ⟨1098162, by rfl⟩ : syracuseStep 11713733 = 2196325) B2196325
theorem B5487821 : Blo 1443541 5487821 := bstep (se 3 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 5487821 = 2057933) B2057933
theorem B2604241 : Blo 1443541 2604241 := bstep (se 2 (by rfl) ⟨976590, by rfl⟩ : syracuseStep 2604241 = 1953181) B1953181
theorem B2112739 : Blo 1443541 2112739 := bstep (se 1 (by rfl) ⟨1584554, by rfl⟩ : syracuseStep 2112739 = 3169109) B3169109
theorem B4111651 : Blo 1443541 4111651 := bstep (se 1 (by rfl) ⟨3083738, by rfl⟩ : syracuseStep 4111651 = 6167477) B6167477
theorem B4111697 : Blo 1443541 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B4873553 : Blo 1443541 4873553 := bstep (se 2 (by rfl) ⟨1827582, by rfl⟩ : syracuseStep 4873553 = 3655165) B3655165
theorem B3251537 : Blo 1443541 3251537 := bstep (se 2 (by rfl) ⟨1219326, by rfl⟩ : syracuseStep 3251537 = 2438653) B2438653
theorem B3251555 : Blo 1443541 3251555 := bstep (se 1 (by rfl) ⟨2438666, by rfl⟩ : syracuseStep 3251555 = 4877333) B4877333
theorem B24673733 : Blo 1443541 24673733 := bstep (se 4 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 24673733 = 4626325) B4626325
theorem B16686605 : Blo 1443541 16686605 := bstep (se 3 (by rfl) ⟨3128738, by rfl⟩ : syracuseStep 16686605 = 6257477) B6257477
theorem B8232461 : Blo 1443541 8232461 := bstep (se 3 (by rfl) ⟨1543586, by rfl⟩ : syracuseStep 8232461 = 3087173) B3087173
theorem B3251825 : Blo 1443541 3251825 := bstep (se 2 (by rfl) ⟨1219434, by rfl⟩ : syracuseStep 3251825 = 2438869) B2438869
theorem B3251843 : Blo 1443541 3251843 := bstep (se 1 (by rfl) ⟨2438882, by rfl⟩ : syracuseStep 3251843 = 4877765) B4877765
theorem B5562083 : Blo 1443541 5562083 := bstep (se 1 (by rfl) ⟨4171562, by rfl⟩ : syracuseStep 5562083 = 8343125) B8343125
theorem B2744131 : Blo 1443541 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B6168419 : Blo 1443541 6168419 := bstep (se 1 (by rfl) ⟨4626314, by rfl⟩ : syracuseStep 6168419 = 9252629) B9252629
theorem B4874093 : Blo 1443541 4874093 := bstep (se 3 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 4874093 = 1827785) B1827785
theorem B3252113 : Blo 1443541 3252113 := bstep (se 2 (by rfl) ⟨1219542, by rfl⟩ : syracuseStep 3252113 = 2439085) B2439085
theorem B2056099 : Blo 1443541 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B4874147 : Blo 1443541 4874147 := bstep (se 1 (by rfl) ⟨3655610, by rfl⟩ : syracuseStep 4874147 = 7311221) B7311221
theorem B3252131 : Blo 1443541 3252131 := bstep (se 1 (by rfl) ⟨2439098, by rfl⟩ : syracuseStep 3252131 = 4878197) B4878197
theorem B8224739 : Blo 1443541 8224739 := bstep (se 1 (by rfl) ⟨6168554, by rfl⟩ : syracuseStep 8224739 = 12337109) B12337109
theorem B6250499 : Blo 1443541 6250499 := bstep (se 1 (by rfl) ⟨4687874, by rfl⟩ : syracuseStep 6250499 = 9375749) B9375749
theorem B2195467 : Blo 1443541 2195467 := bstep (se 1 (by rfl) ⟨1646600, by rfl⟩ : syracuseStep 2195467 = 3293201) B3293201
theorem B3252275 : Blo 1443541 3252275 := bstep (se 1 (by rfl) ⟨2439206, by rfl⟩ : syracuseStep 3252275 = 4878413) B4878413
theorem B3252311 : Blo 1443541 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B6168707 : Blo 1443541 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B1827031 : Blo 1443541 1827031 := bstep (se 1 (by rfl) ⟨1370273, by rfl⟩ : syracuseStep 1827031 = 2740547) B2740547
theorem B4391129 : Blo 1443541 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B7315757 : Blo 1443541 7315757 := bstep (se 3 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 7315757 = 2743409) B2743409
theorem B52724195 : Blo 1443541 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B26362381 : Blo 1443541 26362381 := bstep (se 3 (by rfl) ⟨4942946, by rfl⟩ : syracuseStep 26362381 = 9885893) B9885893
theorem B12337757 : Blo 1443541 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B4874903 : Blo 1443541 4874903 := bstep (se 1 (by rfl) ⟨3656177, by rfl⟩ : syracuseStep 4874903 = 7312355) B7312355
theorem B2056919 : Blo 1443541 2056919 := bstep (se 1 (by rfl) ⟨1542689, by rfl⟩ : syracuseStep 2056919 = 3085379) B3085379
theorem B1483639 : Blo 1443541 1483639 := bstep (se 1 (by rfl) ⟨1112729, by rfl⟩ : syracuseStep 1483639 = 2225459) B2225459
theorem B2057113 : Blo 1443541 2057113 := bstep (se 2 (by rfl) ⟨771417, by rfl⟩ : syracuseStep 2057113 = 1542835) B1542835
theorem B4391873 : Blo 1443541 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B88941509 : Blo 1443541 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B7308305 : Blo 1443541 7308305 := bstep (se 2 (by rfl) ⟨2740614, by rfl⟩ : syracuseStep 7308305 = 5481229) B5481229
theorem B3654679 : Blo 1443541 3654679 := bstep (se 1 (by rfl) ⟨2741009, by rfl⟩ : syracuseStep 3654679 = 5482019) B5482019
theorem B4113497 : Blo 1443541 4113497 := bstep (se 2 (by rfl) ⟨1542561, by rfl⟩ : syracuseStep 4113497 = 3085123) B3085123
theorem B7308467 : Blo 1443541 7308467 := bstep (se 1 (by rfl) ⟨5481350, by rfl⟩ : syracuseStep 7308467 = 10962701) B10962701
theorem B4875443 : Blo 1443541 4875443 := bstep (se 1 (by rfl) ⟨3656582, by rfl⟩ : syracuseStep 4875443 = 7313165) B7313165
theorem B4113611 : Blo 1443541 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B4629811 : Blo 1443541 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B12338507 : Blo 1443541 12338507 := bstep (se 1 (by rfl) ⟨9253880, by rfl⟩ : syracuseStep 12338507 = 18507761) B18507761
theorem B9258391 : Blo 1443541 9258391 := bstep (se 1 (by rfl) ⟨6943793, by rfl⟩ : syracuseStep 9258391 = 13887587) B13887587
theorem B5203379 : Blo 1443541 5203379 := bstep (se 1 (by rfl) ⟨3902534, by rfl⟩ : syracuseStep 5203379 = 7805069) B7805069
theorem B4875713 : Blo 1443541 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B3655115 : Blo 1443541 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B2344459 : Blo 1443541 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B5555891 : Blo 1443541 5555891 := bstep (se 1 (by rfl) ⟨4166918, by rfl⟩ : syracuseStep 5555891 = 8333837) B8333837
theorem B5482187 : Blo 1443541 5482187 := bstep (se 1 (by rfl) ⟨4111640, by rfl⟩ : syracuseStep 5482187 = 8223281) B8223281
theorem B1443543 : Blo 1443541 1443543 := bstep (se 1 (by rfl) ⟨1082657, by rfl⟩ : syracuseStep 1443543 = 2165315) B2165315
theorem B5482201 : Blo 1443541 5482201 := bstep (se 2 (by rfl) ⟨2055825, by rfl⟩ : syracuseStep 5482201 = 4111651) B4111651
theorem B1443563 : Blo 1443541 1443563 := bstep (se 1 (by rfl) ⟨1082672, by rfl⟩ : syracuseStep 1443563 = 2165345) B2165345
theorem B1443575 : Blo 1443541 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B1443595 : Blo 1443541 1443595 := bstep (se 1 (by rfl) ⟨1082696, by rfl⟩ : syracuseStep 1443595 = 2165393) B2165393
theorem B1443607 : Blo 1443541 1443607 := bstep (se 1 (by rfl) ⟨1082705, by rfl⟩ : syracuseStep 1443607 = 2165411) B2165411
theorem B1443627 : Blo 1443541 1443627 := bstep (se 1 (by rfl) ⟨1082720, by rfl⟩ : syracuseStep 1443627 = 2165441) B2165441
theorem B1443639 : Blo 1443541 1443639 := bstep (se 1 (by rfl) ⟨1082729, by rfl⟩ : syracuseStep 1443639 = 2165459) B2165459
theorem B3655489 : Blo 1443541 3655489 := bstep (se 2 (by rfl) ⟨1370808, by rfl⟩ : syracuseStep 3655489 = 2741617) B2741617
theorem B1443659 : Blo 1443541 1443659 := bstep (se 1 (by rfl) ⟨1082744, by rfl⟩ : syracuseStep 1443659 = 2165489) B2165489
theorem B1443671 : Blo 1443541 1443671 := bstep (se 1 (by rfl) ⟨1082753, by rfl⟩ : syracuseStep 1443671 = 2165507) B2165507
theorem B1443691 : Blo 1443541 1443691 := bstep (se 1 (by rfl) ⟨1082768, by rfl⟩ : syracuseStep 1443691 = 2165537) B2165537
theorem B1443703 : Blo 1443541 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B1443723 : Blo 1443541 1443723 := bstep (se 1 (by rfl) ⟨1082792, by rfl⟩ : syracuseStep 1443723 = 2165585) B2165585
theorem B1828747 : Blo 1443541 1828747 := bstep (se 1 (by rfl) ⟨1371560, by rfl⟩ : syracuseStep 1828747 = 2743121) B2743121
theorem B1443735 : Blo 1443541 1443735 := bstep (se 1 (by rfl) ⟨1082801, by rfl⟩ : syracuseStep 1443735 = 2165603) B2165603
theorem B6170519 : Blo 1443541 6170519 := bstep (se 1 (by rfl) ⟨4627889, by rfl⟩ : syracuseStep 6170519 = 9255779) B9255779
theorem B1443755 : Blo 1443541 1443755 := bstep (se 1 (by rfl) ⟨1082816, by rfl⟩ : syracuseStep 1443755 = 2165633) B2165633
theorem B1623991 : Blo 1443541 1623991 := bstep (se 1 (by rfl) ⟨1217993, by rfl⟩ : syracuseStep 1623991 = 2435987) B2435987
theorem B1443767 : Blo 1443541 1443767 := bstep (se 1 (by rfl) ⟨1082825, by rfl⟩ : syracuseStep 1443767 = 2165651) B2165651
theorem B1443787 : Blo 1443541 1443787 := bstep (se 1 (by rfl) ⟨1082840, by rfl⟩ : syracuseStep 1443787 = 2165681) B2165681
theorem B1443799 : Blo 1443541 1443799 := bstep (se 1 (by rfl) ⟨1082849, by rfl⟩ : syracuseStep 1443799 = 2165699) B2165699
theorem B4876253 : Blo 1443541 4876253 := bstep (se 3 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 4876253 = 1828595) B1828595
theorem B1443819 : Blo 1443541 1443819 := bstep (se 1 (by rfl) ⟨1082864, by rfl⟩ : syracuseStep 1443819 = 2165729) B2165729
theorem B1443831 : Blo 1443541 1443831 := bstep (se 1 (by rfl) ⟨1082873, by rfl⟩ : syracuseStep 1443831 = 2165747) B2165747
theorem B1443851 : Blo 1443541 1443851 := bstep (se 1 (by rfl) ⟨1082888, by rfl⟩ : syracuseStep 1443851 = 2165777) B2165777
theorem B1443863 : Blo 1443541 1443863 := bstep (se 1 (by rfl) ⟨1082897, by rfl⟩ : syracuseStep 1443863 = 2165795) B2165795
theorem B1443883 : Blo 1443541 1443883 := bstep (se 1 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 1443883 = 2165825) B2165825
theorem B1443895 : Blo 1443541 1443895 := bstep (se 1 (by rfl) ⟨1082921, by rfl⟩ : syracuseStep 1443895 = 2165843) B2165843
theorem B1443915 : Blo 1443541 1443915 := bstep (se 1 (by rfl) ⟨1082936, by rfl⟩ : syracuseStep 1443915 = 2165873) B2165873
theorem B1443927 : Blo 1443541 1443927 := bstep (se 1 (by rfl) ⟨1082945, by rfl⟩ : syracuseStep 1443927 = 2165891) B2165891
theorem B1624171 : Blo 1443541 1624171 := bstep (se 1 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 1624171 = 2436257) B2436257
theorem B1443947 : Blo 1443541 1443947 := bstep (se 1 (by rfl) ⟨1082960, by rfl⟩ : syracuseStep 1443947 = 2165921) B2165921
theorem B1443959 : Blo 1443541 1443959 := bstep (se 1 (by rfl) ⟨1082969, by rfl⟩ : syracuseStep 1443959 = 2165939) B2165939
theorem B7809155 : Blo 1443541 7809155 := bstep (se 1 (by rfl) ⟨5856866, by rfl⟩ : syracuseStep 7809155 = 11713733) B11713733
theorem B8226947 : Blo 1443541 8226947 := bstep (se 1 (by rfl) ⟨6170210, by rfl⟩ : syracuseStep 8226947 = 12340421) B12340421
theorem B1443979 : Blo 1443541 1443979 := bstep (se 1 (by rfl) ⟨1082984, by rfl⟩ : syracuseStep 1443979 = 2165969) B2165969
theorem B1443991 : Blo 1443541 1443991 := bstep (se 1 (by rfl) ⟨1082993, by rfl⟩ : syracuseStep 1443991 = 2165987) B2165987
theorem B1444011 : Blo 1443541 1444011 := bstep (se 1 (by rfl) ⟨1083008, by rfl⟩ : syracuseStep 1444011 = 2166017) B2166017
theorem B1444023 : Blo 1443541 1444023 := bstep (se 1 (by rfl) ⟨1083017, by rfl⟩ : syracuseStep 1444023 = 2166035) B2166035
theorem B1444043 : Blo 1443541 1444043 := bstep (se 1 (by rfl) ⟨1083032, by rfl⟩ : syracuseStep 1444043 = 2166065) B2166065
theorem B1624279 : Blo 1443541 1624279 := bstep (se 1 (by rfl) ⟨1218209, by rfl⟩ : syracuseStep 1624279 = 2436419) B2436419
theorem B1444055 : Blo 1443541 1444055 := bstep (se 1 (by rfl) ⟨1083041, by rfl⟩ : syracuseStep 1444055 = 2166083) B2166083
theorem B1444075 : Blo 1443541 1444075 := bstep (se 1 (by rfl) ⟨1083056, by rfl⟩ : syracuseStep 1444075 = 2166113) B2166113
theorem B1444087 : Blo 1443541 1444087 := bstep (se 1 (by rfl) ⟨1083065, by rfl⟩ : syracuseStep 1444087 = 2166131) B2166131
theorem B2312459 : Blo 1443541 2312459 := bstep (se 1 (by rfl) ⟨1734344, by rfl⟩ : syracuseStep 2312459 = 3468689) B3468689
theorem B1444107 : Blo 1443541 1444107 := bstep (se 1 (by rfl) ⟨1083080, by rfl⟩ : syracuseStep 1444107 = 2166161) B2166161
theorem B1444119 : Blo 1443541 1444119 := bstep (se 1 (by rfl) ⟨1083089, by rfl⟩ : syracuseStep 1444119 = 2166179) B2166179
theorem B1444139 : Blo 1443541 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B4114739 : Blo 1443541 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B1444151 : Blo 1443541 1444151 := bstep (se 1 (by rfl) ⟨1083113, by rfl⟩ : syracuseStep 1444151 = 2166227) B2166227
theorem B1444171 : Blo 1443541 1444171 := bstep (se 1 (by rfl) ⟨1083128, by rfl⟩ : syracuseStep 1444171 = 2166257) B2166257
theorem B1444183 : Blo 1443541 1444183 := bstep (se 1 (by rfl) ⟨1083137, by rfl⟩ : syracuseStep 1444183 = 2166275) B2166275
theorem B1444203 : Blo 1443541 1444203 := bstep (se 1 (by rfl) ⟨1083152, by rfl⟩ : syracuseStep 1444203 = 2166305) B2166305
theorem B41634161 : Blo 1443541 41634161 := bstep (se 2 (by rfl) ⟨15612810, by rfl⟩ : syracuseStep 41634161 = 31225621) B31225621
theorem B1444215 : Blo 1443541 1444215 := bstep (se 1 (by rfl) ⟨1083161, by rfl⟩ : syracuseStep 1444215 = 2166323) B2166323
theorem B1624459 : Blo 1443541 1624459 := bstep (se 1 (by rfl) ⟨1218344, by rfl⟩ : syracuseStep 1624459 = 2436689) B2436689
theorem B1444235 : Blo 1443541 1444235 := bstep (se 1 (by rfl) ⟨1083176, by rfl⟩ : syracuseStep 1444235 = 2166353) B2166353
theorem B2312599 : Blo 1443541 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B1444247 : Blo 1443541 1444247 := bstep (se 1 (by rfl) ⟨1083185, by rfl⟩ : syracuseStep 1444247 = 2166371) B2166371
theorem B3656087 : Blo 1443541 3656087 := bstep (se 1 (by rfl) ⟨2742065, by rfl⟩ : syracuseStep 3656087 = 5484131) B5484131
theorem B1444267 : Blo 1443541 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B1444279 : Blo 1443541 1444279 := bstep (se 1 (by rfl) ⟨1083209, by rfl⟩ : syracuseStep 1444279 = 2166419) B2166419
theorem B1444299 : Blo 1443541 1444299 := bstep (se 1 (by rfl) ⟨1083224, by rfl⟩ : syracuseStep 1444299 = 2166449) B2166449
theorem B1952203 : Blo 1443541 1952203 := bstep (se 1 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 1952203 = 2928305) B2928305
theorem B1444311 : Blo 1443541 1444311 := bstep (se 1 (by rfl) ⟨1083233, by rfl⟩ : syracuseStep 1444311 = 2166467) B2166467
theorem B1444331 : Blo 1443541 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B1624567 : Blo 1443541 1624567 := bstep (se 1 (by rfl) ⟨1218425, by rfl⟩ : syracuseStep 1624567 = 2436851) B2436851
theorem B1444343 : Blo 1443541 1444343 := bstep (se 1 (by rfl) ⟨1083257, by rfl⟩ : syracuseStep 1444343 = 2166515) B2166515
theorem B1444363 : Blo 1443541 1444363 := bstep (se 1 (by rfl) ⟨1083272, by rfl⟩ : syracuseStep 1444363 = 2166545) B2166545
theorem B1444375 : Blo 1443541 1444375 := bstep (se 1 (by rfl) ⟨1083281, by rfl⟩ : syracuseStep 1444375 = 2166563) B2166563
theorem B1444395 : Blo 1443541 1444395 := bstep (se 1 (by rfl) ⟨1083296, by rfl⟩ : syracuseStep 1444395 = 2166593) B2166593
theorem B1444407 : Blo 1443541 1444407 := bstep (se 1 (by rfl) ⟨1083305, by rfl⟩ : syracuseStep 1444407 = 2166611) B2166611
theorem B10406465 : Blo 1443541 10406465 := bstep (se 2 (by rfl) ⟨3902424, by rfl⟩ : syracuseStep 10406465 = 7804849) B7804849
theorem B1444427 : Blo 1443541 1444427 := bstep (se 1 (by rfl) ⟨1083320, by rfl⟩ : syracuseStep 1444427 = 2166641) B2166641
theorem B8227403 : Blo 1443541 8227403 := bstep (se 1 (by rfl) ⟨6170552, by rfl⟩ : syracuseStep 8227403 = 12341105) B12341105
theorem B1444439 : Blo 1443541 1444439 := bstep (se 1 (by rfl) ⟨1083329, by rfl⟩ : syracuseStep 1444439 = 2166659) B2166659
theorem B1444459 : Blo 1443541 1444459 := bstep (se 1 (by rfl) ⟨1083344, by rfl⟩ : syracuseStep 1444459 = 2166689) B2166689
theorem B1444471 : Blo 1443541 1444471 := bstep (se 1 (by rfl) ⟨1083353, by rfl⟩ : syracuseStep 1444471 = 2166707) B2166707
theorem B1542775 : Blo 1443541 1542775 := bstep (se 1 (by rfl) ⟨1157081, by rfl⟩ : syracuseStep 1542775 = 2314163) B2314163
theorem B2165387 : Blo 1443541 2165387 := bstep (se 1 (by rfl) ⟨1624040, by rfl⟩ : syracuseStep 2165387 = 3248081) B3248081
theorem B1444491 : Blo 1443541 1444491 := bstep (se 1 (by rfl) ⟨1083368, by rfl⟩ : syracuseStep 1444491 = 2166737) B2166737
theorem B3295883 : Blo 1443541 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B2165399 : Blo 1443541 2165399 := bstep (se 1 (by rfl) ⟨1624049, by rfl⟩ : syracuseStep 2165399 = 3248099) B3248099
theorem B5483159 : Blo 1443541 5483159 := bstep (se 1 (by rfl) ⟨4112369, by rfl⟩ : syracuseStep 5483159 = 8224739) B8224739
theorem B1444503 : Blo 1443541 1444503 := bstep (se 1 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 1444503 = 2166755) B2166755
theorem B1624747 : Blo 1443541 1624747 := bstep (se 1 (by rfl) ⟨1218560, by rfl⟩ : syracuseStep 1624747 = 2437121) B2437121
theorem B1444523 : Blo 1443541 1444523 := bstep (se 1 (by rfl) ⟨1083392, by rfl⟩ : syracuseStep 1444523 = 2166785) B2166785
theorem B1444535 : Blo 1443541 1444535 := bstep (se 1 (by rfl) ⟨1083401, by rfl⟩ : syracuseStep 1444535 = 2166803) B2166803
theorem B4115137 : Blo 1443541 4115137 := bstep (se 2 (by rfl) ⟨1543176, by rfl⟩ : syracuseStep 4115137 = 3086353) B3086353
theorem B1444555 : Blo 1443541 1444555 := bstep (se 1 (by rfl) ⟨1083416, by rfl⟩ : syracuseStep 1444555 = 2166833) B2166833
theorem B1444567 : Blo 1443541 1444567 := bstep (se 1 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 1444567 = 2166851) B2166851
theorem B2165465 : Blo 1443541 2165465 := bstep (se 2 (by rfl) ⟨812049, by rfl⟩ : syracuseStep 2165465 = 1624099) B1624099
theorem B10963673 : Blo 1443541 10963673 := bstep (se 2 (by rfl) ⟨4111377, by rfl⟩ : syracuseStep 10963673 = 8222755) B8222755
theorem B1444587 : Blo 1443541 1444587 := bstep (se 1 (by rfl) ⟨1083440, by rfl⟩ : syracuseStep 1444587 = 2166881) B2166881
theorem B1444599 : Blo 1443541 1444599 := bstep (se 1 (by rfl) ⟨1083449, by rfl⟩ : syracuseStep 1444599 = 2166899) B2166899
theorem B1444619 : Blo 1443541 1444619 := bstep (se 1 (by rfl) ⟨1083464, by rfl⟩ : syracuseStep 1444619 = 2166929) B2166929
theorem B1624855 : Blo 1443541 1624855 := bstep (se 1 (by rfl) ⟨1218641, by rfl⟩ : syracuseStep 1624855 = 2437283) B2437283
theorem B1444631 : Blo 1443541 1444631 := bstep (se 1 (by rfl) ⟨1083473, by rfl⟩ : syracuseStep 1444631 = 2166947) B2166947
theorem B2083609 : Blo 1443541 2083609 := bstep (se 2 (by rfl) ⟨781353, by rfl⟩ : syracuseStep 2083609 = 1562707) B1562707
theorem B1444651 : Blo 1443541 1444651 := bstep (se 1 (by rfl) ⟨1083488, by rfl⟩ : syracuseStep 1444651 = 2166977) B2166977
theorem B1444663 : Blo 1443541 1444663 := bstep (se 1 (by rfl) ⟨1083497, by rfl⟩ : syracuseStep 1444663 = 2166995) B2166995
theorem B2165579 : Blo 1443541 2165579 := bstep (se 1 (by rfl) ⟨1624184, by rfl⟩ : syracuseStep 2165579 = 3248369) B3248369
theorem B1444683 : Blo 1443541 1444683 := bstep (se 1 (by rfl) ⟨1083512, by rfl⟩ : syracuseStep 1444683 = 2167025) B2167025
theorem B2165591 : Blo 1443541 2165591 := bstep (se 1 (by rfl) ⟨1624193, by rfl⟩ : syracuseStep 2165591 = 3248387) B3248387
theorem B1444695 : Blo 1443541 1444695 := bstep (se 1 (by rfl) ⟨1083521, by rfl⟩ : syracuseStep 1444695 = 2167043) B2167043
theorem B1444715 : Blo 1443541 1444715 := bstep (se 1 (by rfl) ⟨1083536, by rfl⟩ : syracuseStep 1444715 = 2167073) B2167073
theorem B1444727 : Blo 1443541 1444727 := bstep (se 1 (by rfl) ⟨1083545, by rfl⟩ : syracuseStep 1444727 = 2167091) B2167091
theorem B5557123 : Blo 1443541 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B1444747 : Blo 1443541 1444747 := bstep (se 1 (by rfl) ⟨1083560, by rfl⟩ : syracuseStep 1444747 = 2167121) B2167121
theorem B1444759 : Blo 1443541 1444759 := bstep (se 1 (by rfl) ⟨1083569, by rfl⟩ : syracuseStep 1444759 = 2167139) B2167139
theorem B2165657 : Blo 1443541 2165657 := bstep (se 2 (by rfl) ⟨812121, by rfl⟩ : syracuseStep 2165657 = 1624243) B1624243
theorem B1444779 : Blo 1443541 1444779 := bstep (se 1 (by rfl) ⟨1083584, by rfl⟩ : syracuseStep 1444779 = 2167169) B2167169
theorem B12340147 : Blo 1443541 12340147 := bstep (se 1 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 12340147 = 18510221) B18510221
theorem B1444791 : Blo 1443541 1444791 := bstep (se 1 (by rfl) ⟨1083593, by rfl⟩ : syracuseStep 1444791 = 2167187) B2167187
theorem B1625035 : Blo 1443541 1625035 := bstep (se 1 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 1625035 = 2437553) B2437553
theorem B1444811 : Blo 1443541 1444811 := bstep (se 1 (by rfl) ⟨1083608, by rfl⟩ : syracuseStep 1444811 = 2167217) B2167217
theorem B1444823 : Blo 1443541 1444823 := bstep (se 1 (by rfl) ⟨1083617, by rfl⟩ : syracuseStep 1444823 = 2167235) B2167235
theorem B1444843 : Blo 1443541 1444843 := bstep (se 1 (by rfl) ⟨1083632, by rfl⟩ : syracuseStep 1444843 = 2167265) B2167265
theorem B1444855 : Blo 1443541 1444855 := bstep (se 1 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 1444855 = 2167283) B2167283
theorem B2165771 : Blo 1443541 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B1444875 : Blo 1443541 1444875 := bstep (se 1 (by rfl) ⟨1083656, by rfl⟩ : syracuseStep 1444875 = 2167313) B2167313
theorem B2165783 : Blo 1443541 2165783 := bstep (se 1 (by rfl) ⟨1624337, by rfl⟩ : syracuseStep 2165783 = 3248675) B3248675
theorem B1444887 : Blo 1443541 1444887 := bstep (se 1 (by rfl) ⟨1083665, by rfl⟩ : syracuseStep 1444887 = 2167331) B2167331
theorem B1444907 : Blo 1443541 1444907 := bstep (se 1 (by rfl) ⟨1083680, by rfl⟩ : syracuseStep 1444907 = 2167361) B2167361
theorem B1625143 : Blo 1443541 1625143 := bstep (se 1 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 1625143 = 2437715) B2437715
theorem B1444919 : Blo 1443541 1444919 := bstep (se 1 (by rfl) ⟨1083689, by rfl⟩ : syracuseStep 1444919 = 2167379) B2167379
theorem B3296321 : Blo 1443541 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B7310411 : Blo 1443541 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B1444939 : Blo 1443541 1444939 := bstep (se 1 (by rfl) ⟨1083704, by rfl⟩ : syracuseStep 1444939 = 2167409) B2167409
theorem B4877387 : Blo 1443541 4877387 := bstep (se 1 (by rfl) ⟨3658040, by rfl⟩ : syracuseStep 4877387 = 7316081) B7316081
theorem B1444951 : Blo 1443541 1444951 := bstep (se 1 (by rfl) ⟨1083713, by rfl⟩ : syracuseStep 1444951 = 2167427) B2167427
theorem B2165849 : Blo 1443541 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B1444971 : Blo 1443541 1444971 := bstep (se 1 (by rfl) ⟨1083728, by rfl⟩ : syracuseStep 1444971 = 2167457) B2167457
theorem B1444983 : Blo 1443541 1444983 := bstep (se 1 (by rfl) ⟨1083737, by rfl⟩ : syracuseStep 1444983 = 2167475) B2167475
theorem B1445003 : Blo 1443541 1445003 := bstep (se 1 (by rfl) ⟨1083752, by rfl⟩ : syracuseStep 1445003 = 2167505) B2167505
theorem B1445015 : Blo 1443541 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B17820823 : Blo 1443541 17820823 := bstep (se 1 (by rfl) ⟨13365617, by rfl⟩ : syracuseStep 17820823 = 26731235) B26731235
theorem B1952921 : Blo 1443541 1952921 := bstep (se 2 (by rfl) ⟨732345, by rfl⟩ : syracuseStep 1952921 = 1464691) B1464691
theorem B1445035 : Blo 1443541 1445035 := bstep (se 1 (by rfl) ⟨1083776, by rfl⟩ : syracuseStep 1445035 = 2167553) B2167553
theorem B1445047 : Blo 1443541 1445047 := bstep (se 1 (by rfl) ⟨1083785, by rfl⟩ : syracuseStep 1445047 = 2167571) B2167571
theorem B3656897 : Blo 1443541 3656897 := bstep (se 2 (by rfl) ⟨1371336, by rfl⟩ : syracuseStep 3656897 = 2742673) B2742673
theorem B2165963 : Blo 1443541 2165963 := bstep (se 1 (by rfl) ⟨1624472, by rfl⟩ : syracuseStep 2165963 = 3248945) B3248945
theorem B2313419 : Blo 1443541 2313419 := bstep (se 1 (by rfl) ⟨1735064, by rfl⟩ : syracuseStep 2313419 = 3470129) B3470129
theorem B6171851 : Blo 1443541 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B1445067 : Blo 1443541 1445067 := bstep (se 1 (by rfl) ⟨1083800, by rfl⟩ : syracuseStep 1445067 = 2167601) B2167601
theorem B2436311 : Blo 1443541 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B2165975 : Blo 1443541 2165975 := bstep (se 1 (by rfl) ⟨1624481, by rfl⟩ : syracuseStep 2165975 = 3248963) B3248963
theorem B1445079 : Blo 1443541 1445079 := bstep (se 1 (by rfl) ⟨1083809, by rfl⟩ : syracuseStep 1445079 = 2167619) B2167619
theorem B1625323 : Blo 1443541 1625323 := bstep (se 1 (by rfl) ⟨1218992, by rfl⟩ : syracuseStep 1625323 = 2437985) B2437985
theorem B1445099 : Blo 1443541 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B1445111 : Blo 1443541 1445111 := bstep (se 1 (by rfl) ⟨1083833, by rfl⟩ : syracuseStep 1445111 = 2167667) B2167667
theorem B10972421 : Blo 1443541 10972421 := bstep (se 4 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 10972421 = 2057329) B2057329
theorem B1445131 : Blo 1443541 1445131 := bstep (se 1 (by rfl) ⟨1083848, by rfl⟩ : syracuseStep 1445131 = 2167697) B2167697
theorem B1445143 : Blo 1443541 1445143 := bstep (se 1 (by rfl) ⟨1083857, by rfl⟩ : syracuseStep 1445143 = 2167715) B2167715
theorem B2166041 : Blo 1443541 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B2313497 : Blo 1443541 2313497 := bstep (se 2 (by rfl) ⟨867561, by rfl⟩ : syracuseStep 2313497 = 1735123) B1735123
theorem B1445163 : Blo 1443541 1445163 := bstep (se 1 (by rfl) ⟨1083872, by rfl⟩ : syracuseStep 1445163 = 2167745) B2167745
theorem B1445175 : Blo 1443541 1445175 := bstep (se 1 (by rfl) ⟨1083881, by rfl⟩ : syracuseStep 1445175 = 2167763) B2167763
theorem B1445195 : Blo 1443541 1445195 := bstep (se 1 (by rfl) ⟨1083896, by rfl⟩ : syracuseStep 1445195 = 2167793) B2167793
theorem B2436439 : Blo 1443541 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B1625431 : Blo 1443541 1625431 := bstep (se 1 (by rfl) ⟨1219073, by rfl⟩ : syracuseStep 1625431 = 2438147) B2438147
theorem B1445207 : Blo 1443541 1445207 := bstep (se 1 (by rfl) ⟨1083905, by rfl⟩ : syracuseStep 1445207 = 2167811) B2167811
theorem B4877657 : Blo 1443541 4877657 := bstep (se 2 (by rfl) ⟨1829121, by rfl⟩ : syracuseStep 4877657 = 3658243) B3658243
theorem B1445227 : Blo 1443541 1445227 := bstep (se 1 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 1445227 = 2167841) B2167841
theorem B1445239 : Blo 1443541 1445239 := bstep (se 1 (by rfl) ⟨1083929, by rfl⟩ : syracuseStep 1445239 = 2167859) B2167859
theorem B2166155 : Blo 1443541 2166155 := bstep (se 1 (by rfl) ⟨1624616, by rfl⟩ : syracuseStep 2166155 = 3249233) B3249233
theorem B1445259 : Blo 1443541 1445259 := bstep (se 1 (by rfl) ⟨1083944, by rfl⟩ : syracuseStep 1445259 = 2167889) B2167889
theorem B35130773 : Blo 1443541 35130773 := bstep (se 6 (by rfl) ⟨823377, by rfl⟩ : syracuseStep 35130773 = 1646755) B1646755
theorem B2166167 : Blo 1443541 2166167 := bstep (se 1 (by rfl) ⟨1624625, by rfl⟩ : syracuseStep 2166167 = 3249251) B3249251
theorem B31247765 : Blo 1443541 31247765 := bstep (se 6 (by rfl) ⟨732369, by rfl⟩ : syracuseStep 31247765 = 1464739) B1464739
theorem B1445271 : Blo 1443541 1445271 := bstep (se 1 (by rfl) ⟨1083953, by rfl⟩ : syracuseStep 1445271 = 2167907) B2167907
theorem B1445291 : Blo 1443541 1445291 := bstep (se 1 (by rfl) ⟨1083968, by rfl⟩ : syracuseStep 1445291 = 2167937) B2167937
theorem B1543595 : Blo 1443541 1543595 := bstep (se 1 (by rfl) ⟨1157696, by rfl⟩ : syracuseStep 1543595 = 2315393) B2315393
theorem B1445303 : Blo 1443541 1445303 := bstep (se 1 (by rfl) ⟨1083977, by rfl⟩ : syracuseStep 1445303 = 2167955) B2167955
theorem B3468737 : Blo 1443541 3468737 := bstep (se 2 (by rfl) ⟨1300776, by rfl⟩ : syracuseStep 3468737 = 2601553) B2601553
theorem B1445323 : Blo 1443541 1445323 := bstep (se 1 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 1445323 = 2167985) B2167985
theorem B1445335 : Blo 1443541 1445335 := bstep (se 1 (by rfl) ⟨1084001, by rfl⟩ : syracuseStep 1445335 = 2168003) B2168003
theorem B2166233 : Blo 1443541 2166233 := bstep (se 2 (by rfl) ⟨812337, by rfl⟩ : syracuseStep 2166233 = 1624675) B1624675
theorem B4394461 : Blo 1443541 4394461 := bstep (se 3 (by rfl) ⟨823961, by rfl⟩ : syracuseStep 4394461 = 1647923) B1647923
theorem B1445355 : Blo 1443541 1445355 := bstep (se 1 (by rfl) ⟨1084016, by rfl⟩ : syracuseStep 1445355 = 2168033) B2168033
theorem B1445367 : Blo 1443541 1445367 := bstep (se 1 (by rfl) ⟨1084025, by rfl⟩ : syracuseStep 1445367 = 2168051) B2168051
theorem B1625611 : Blo 1443541 1625611 := bstep (se 1 (by rfl) ⟨1219208, by rfl⟩ : syracuseStep 1625611 = 2438417) B2438417
theorem B1445387 : Blo 1443541 1445387 := bstep (se 1 (by rfl) ⟨1084040, by rfl⟩ : syracuseStep 1445387 = 2168081) B2168081
theorem B3706391 : Blo 1443541 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B1445399 : Blo 1443541 1445399 := bstep (se 1 (by rfl) ⟨1084049, by rfl⟩ : syracuseStep 1445399 = 2168099) B2168099
theorem B1445419 : Blo 1443541 1445419 := bstep (se 1 (by rfl) ⟨1084064, by rfl⟩ : syracuseStep 1445419 = 2168129) B2168129
theorem B1445431 : Blo 1443541 1445431 := bstep (se 1 (by rfl) ⟨1084073, by rfl⟩ : syracuseStep 1445431 = 2168147) B2168147
theorem B2166347 : Blo 1443541 2166347 := bstep (se 1 (by rfl) ⟨1624760, by rfl⟩ : syracuseStep 2166347 = 3249521) B3249521
theorem B1445451 : Blo 1443541 1445451 := bstep (se 1 (by rfl) ⟨1084088, by rfl⟩ : syracuseStep 1445451 = 2168177) B2168177
theorem B2166359 : Blo 1443541 2166359 := bstep (se 1 (by rfl) ⟨1624769, by rfl⟩ : syracuseStep 2166359 = 3249539) B3249539
theorem B1445463 : Blo 1443541 1445463 := bstep (se 1 (by rfl) ⟨1084097, by rfl⟩ : syracuseStep 1445463 = 2168195) B2168195
theorem B1445483 : Blo 1443541 1445483 := bstep (se 1 (by rfl) ⟨1084112, by rfl⟩ : syracuseStep 1445483 = 2168225) B2168225
theorem B1625719 : Blo 1443541 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B1445495 : Blo 1443541 1445495 := bstep (se 1 (by rfl) ⟨1084121, by rfl⟩ : syracuseStep 1445495 = 2168243) B2168243
theorem B1445515 : Blo 1443541 1445515 := bstep (se 1 (by rfl) ⟨1084136, by rfl⟩ : syracuseStep 1445515 = 2168273) B2168273
theorem B1445527 : Blo 1443541 1445527 := bstep (se 1 (by rfl) ⟨1084145, by rfl⟩ : syracuseStep 1445527 = 2168291) B2168291
theorem B2166425 : Blo 1443541 2166425 := bstep (se 2 (by rfl) ⟨812409, by rfl⟩ : syracuseStep 2166425 = 1624819) B1624819
theorem B3657433 : Blo 1443541 3657433 := bstep (se 2 (by rfl) ⟨1371537, by rfl⟩ : syracuseStep 3657433 = 2743075) B2743075
theorem B2166539 : Blo 1443541 2166539 := bstep (se 1 (by rfl) ⟨1624904, by rfl⟩ : syracuseStep 2166539 = 3249809) B3249809
theorem B6172433 : Blo 1443541 6172433 := bstep (se 2 (by rfl) ⟨2314662, by rfl⟩ : syracuseStep 6172433 = 4629325) B4629325
theorem B2166551 : Blo 1443541 2166551 := bstep (se 1 (by rfl) ⟨1624913, by rfl⟩ : syracuseStep 2166551 = 3249827) B3249827
theorem B1625899 : Blo 1443541 1625899 := bstep (se 1 (by rfl) ⟨1219424, by rfl⟩ : syracuseStep 1625899 = 2438849) B2438849
theorem B2166617 : Blo 1443541 2166617 := bstep (se 2 (by rfl) ⟨812481, by rfl⟩ : syracuseStep 2166617 = 1624963) B1624963
theorem B5484419 : Blo 1443541 5484419 := bstep (se 1 (by rfl) ⟨4113314, by rfl⟩ : syracuseStep 5484419 = 8226629) B8226629
theorem B1626007 : Blo 1443541 1626007 := bstep (se 1 (by rfl) ⟨1219505, by rfl⟩ : syracuseStep 1626007 = 2439011) B2439011
theorem B2437067 : Blo 1443541 2437067 := bstep (se 1 (by rfl) ⟨1827800, by rfl⟩ : syracuseStep 2437067 = 3655601) B3655601
theorem B2166731 : Blo 1443541 2166731 := bstep (se 1 (by rfl) ⟨1625048, by rfl⟩ : syracuseStep 2166731 = 3250097) B3250097
theorem B2166743 : Blo 1443541 2166743 := bstep (se 1 (by rfl) ⟨1625057, by rfl⟩ : syracuseStep 2166743 = 3250115) B3250115
theorem B4878359 : Blo 1443541 4878359 := bstep (se 1 (by rfl) ⟨3658769, by rfl⟩ : syracuseStep 4878359 = 7317539) B7317539
theorem B3248153 : Blo 1443541 3248153 := bstep (se 2 (by rfl) ⟨1218057, by rfl⟩ : syracuseStep 3248153 = 2436115) B2436115
theorem B2166809 : Blo 1443541 2166809 := bstep (se 2 (by rfl) ⟨812553, by rfl⟩ : syracuseStep 2166809 = 1625107) B1625107
theorem B2437195 : Blo 1443541 2437195 := bstep (se 1 (by rfl) ⟨1827896, by rfl⟩ : syracuseStep 2437195 = 3655793) B3655793
theorem B1626187 : Blo 1443541 1626187 := bstep (se 1 (by rfl) ⟨1219640, by rfl⟩ : syracuseStep 1626187 = 2439281) B2439281
theorem B3248243 : Blo 1443541 3248243 := bstep (se 1 (by rfl) ⟨2436182, by rfl⟩ : syracuseStep 3248243 = 4872365) B4872365
theorem B2166923 : Blo 1443541 2166923 := bstep (se 1 (by rfl) ⟨1625192, by rfl⟩ : syracuseStep 2166923 = 3250385) B3250385
theorem B3248279 : Blo 1443541 3248279 := bstep (se 1 (by rfl) ⟨2436209, by rfl⟩ : syracuseStep 3248279 = 4872419) B4872419
theorem B2166935 : Blo 1443541 2166935 := bstep (se 1 (by rfl) ⟨1625201, by rfl⟩ : syracuseStep 2166935 = 3250403) B3250403
theorem B6942871 : Blo 1443541 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B2437337 : Blo 1443541 2437337 := bstep (se 2 (by rfl) ⟨914001, by rfl⟩ : syracuseStep 2437337 = 1828003) B1828003
theorem B2167001 : Blo 1443541 2167001 := bstep (se 2 (by rfl) ⟨812625, by rfl⟩ : syracuseStep 2167001 = 1625251) B1625251
theorem B6254813 : Blo 1443541 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B22245677 : Blo 1443541 22245677 := bstep (se 3 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 22245677 = 8342129) B8342129
theorem B3248459 : Blo 1443541 3248459 := bstep (se 1 (by rfl) ⟨2436344, by rfl⟩ : syracuseStep 3248459 = 4872689) B4872689
theorem B2167115 : Blo 1443541 2167115 := bstep (se 1 (by rfl) ⟨1625336, by rfl⟩ : syracuseStep 2167115 = 3250673) B3250673
theorem B2167127 : Blo 1443541 2167127 := bstep (se 1 (by rfl) ⟨1625345, by rfl⟩ : syracuseStep 2167127 = 3250691) B3250691
theorem B2437465 : Blo 1443541 2437465 := bstep (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) B1828099
theorem B3248513 : Blo 1443541 3248513 := bstep (se 2 (by rfl) ⟨1218192, by rfl⟩ : syracuseStep 3248513 = 2436385) B2436385
theorem B2167193 : Blo 1443541 2167193 := bstep (se 2 (by rfl) ⟨812697, by rfl⟩ : syracuseStep 2167193 = 1625395) B1625395
theorem B2167307 : Blo 1443541 2167307 := bstep (se 1 (by rfl) ⟨1625480, by rfl⟩ : syracuseStep 2167307 = 3250961) B3250961
theorem B2167319 : Blo 1443541 2167319 := bstep (se 1 (by rfl) ⟨1625489, by rfl⟩ : syracuseStep 2167319 = 3250979) B3250979
theorem B3248729 : Blo 1443541 3248729 := bstep (se 2 (by rfl) ⟨1218273, by rfl⟩ : syracuseStep 3248729 = 2436547) B2436547
theorem B2167385 : Blo 1443541 2167385 := bstep (se 2 (by rfl) ⟨812769, by rfl⟩ : syracuseStep 2167385 = 1625539) B1625539
theorem B94958173 : Blo 1443541 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B13169303 : Blo 1443541 13169303 := bstep (se 1 (by rfl) ⟨9876977, by rfl⟩ : syracuseStep 13169303 = 19753955) B19753955
theorem B3248819 : Blo 1443541 3248819 := bstep (se 1 (by rfl) ⟨2436614, by rfl⟩ : syracuseStep 3248819 = 4873229) B4873229
theorem B3085003 : Blo 1443541 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B2167499 : Blo 1443541 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B3248855 : Blo 1443541 3248855 := bstep (se 1 (by rfl) ⟨2436641, by rfl⟩ : syracuseStep 3248855 = 4873283) B4873283
theorem B2167511 : Blo 1443541 2167511 := bstep (se 1 (by rfl) ⟨1625633, by rfl⟩ : syracuseStep 2167511 = 3251267) B3251267
theorem B2740979 : Blo 1443541 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B2167577 : Blo 1443541 2167577 := bstep (se 2 (by rfl) ⟨812841, by rfl⟩ : syracuseStep 2167577 = 1625683) B1625683
theorem B6173491 : Blo 1443541 6173491 := bstep (se 1 (by rfl) ⟨4630118, by rfl⟩ : syracuseStep 6173491 = 9260237) B9260237
theorem B3658547 : Blo 1443541 3658547 := bstep (se 1 (by rfl) ⟨2743910, by rfl⟩ : syracuseStep 3658547 = 5487821) B5487821
theorem B7312193 : Blo 1443541 7312193 := bstep (se 2 (by rfl) ⟨2742072, by rfl⟩ : syracuseStep 7312193 = 5484145) B5484145
theorem B8221571 : Blo 1443541 8221571 := bstep (se 1 (by rfl) ⟨6166178, by rfl⟩ : syracuseStep 8221571 = 12332357) B12332357
theorem B2741131 : Blo 1443541 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B3249035 : Blo 1443541 3249035 := bstep (se 1 (by rfl) ⟨2436776, by rfl⟩ : syracuseStep 3249035 = 4873553) B4873553
theorem B2167691 : Blo 1443541 2167691 := bstep (se 1 (by rfl) ⟨1625768, by rfl⟩ : syracuseStep 2167691 = 3251537) B3251537
theorem B2438039 : Blo 1443541 2438039 := bstep (se 1 (by rfl) ⟨1828529, by rfl⟩ : syracuseStep 2438039 = 3657059) B3657059
theorem B2167703 : Blo 1443541 2167703 := bstep (se 1 (by rfl) ⟨1625777, by rfl⟩ : syracuseStep 2167703 = 3251555) B3251555
theorem B3249089 : Blo 1443541 3249089 := bstep (se 2 (by rfl) ⟨1218408, by rfl⟩ : syracuseStep 3249089 = 2436817) B2436817
theorem B2167769 : Blo 1443541 2167769 := bstep (se 2 (by rfl) ⟨812913, by rfl⟩ : syracuseStep 2167769 = 1625827) B1625827
theorem B2438167 : Blo 1443541 2438167 := bstep (se 1 (by rfl) ⟨1828625, by rfl⟩ : syracuseStep 2438167 = 3657251) B3657251
theorem B2602049 : Blo 1443541 2602049 := bstep (se 2 (by rfl) ⟨975768, by rfl⟩ : syracuseStep 2602049 = 1951537) B1951537
theorem B2167883 : Blo 1443541 2167883 := bstep (se 1 (by rfl) ⟨1625912, by rfl⟩ : syracuseStep 2167883 = 3251825) B3251825
theorem B6681689 : Blo 1443541 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B2167895 : Blo 1443541 2167895 := bstep (se 1 (by rfl) ⟨1625921, by rfl⟩ : syracuseStep 2167895 = 3251843) B3251843
theorem B3658841 : Blo 1443541 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B3708055 : Blo 1443541 3708055 := bstep (se 1 (by rfl) ⟨2781041, by rfl⟩ : syracuseStep 3708055 = 5562083) B5562083
theorem B3249305 : Blo 1443541 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B3085465 : Blo 1443541 3085465 := bstep (se 2 (by rfl) ⟨1157049, by rfl⟩ : syracuseStep 3085465 = 2314099) B2314099
theorem B2167961 : Blo 1443541 2167961 := bstep (se 2 (by rfl) ⟨812985, by rfl⟩ : syracuseStep 2167961 = 1625971) B1625971
theorem B2741465 : Blo 1443541 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B3249395 : Blo 1443541 3249395 := bstep (se 1 (by rfl) ⟨2437046, by rfl⟩ : syracuseStep 3249395 = 4874093) B4874093
theorem B2168075 : Blo 1443541 2168075 := bstep (se 1 (by rfl) ⟨1626056, by rfl⟩ : syracuseStep 2168075 = 3252113) B3252113
theorem B3249431 : Blo 1443541 3249431 := bstep (se 1 (by rfl) ⟨2437073, by rfl⟩ : syracuseStep 3249431 = 4874147) B4874147
theorem B2168087 : Blo 1443541 2168087 := bstep (se 1 (by rfl) ⟨1626065, by rfl⟩ : syracuseStep 2168087 = 3252131) B3252131
theorem B9254189 : Blo 1443541 9254189 := bstep (se 3 (by rfl) ⟨1735160, by rfl⟩ : syracuseStep 9254189 = 3470321) B3470321
theorem B2471255 : Blo 1443541 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B2168153 : Blo 1443541 2168153 := bstep (se 2 (by rfl) ⟨813057, by rfl⟩ : syracuseStep 2168153 = 1626115) B1626115
theorem B3249611 : Blo 1443541 3249611 := bstep (se 1 (by rfl) ⟨2437208, by rfl⟩ : syracuseStep 3249611 = 4874417) B4874417
theorem B2168267 : Blo 1443541 2168267 := bstep (se 1 (by rfl) ⟨1626200, by rfl⟩ : syracuseStep 2168267 = 3252401) B3252401
theorem B2168279 : Blo 1443541 2168279 := bstep (se 1 (by rfl) ⟨1626209, by rfl⟩ : syracuseStep 2168279 = 3252419) B3252419
theorem B3249665 : Blo 1443541 3249665 := bstep (se 2 (by rfl) ⟨1218624, by rfl⟩ : syracuseStep 3249665 = 2437249) B2437249
theorem B2504267 : Blo 1443541 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B10974851 : Blo 1443541 10974851 := bstep (se 1 (by rfl) ⟨8231138, by rfl⟩ : syracuseStep 10974851 = 16462277) B16462277
theorem B2438795 : Blo 1443541 2438795 := bstep (se 1 (by rfl) ⟨1829096, by rfl⟩ : syracuseStep 2438795 = 3658193) B3658193
theorem B8787635 : Blo 1443541 8787635 := bstep (se 1 (by rfl) ⟨6590726, by rfl⟩ : syracuseStep 8787635 = 13181453) B13181453
theorem B11712205 : Blo 1443541 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B13891277 : Blo 1443541 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B3249881 : Blo 1443541 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B2438923 : Blo 1443541 2438923 := bstep (se 1 (by rfl) ⟨1829192, by rfl⟩ : syracuseStep 2438923 = 3658385) B3658385
theorem B4871987 : Blo 1443541 4871987 := bstep (se 1 (by rfl) ⟨3653990, by rfl⟩ : syracuseStep 4871987 = 7307981) B7307981
theorem B3249971 : Blo 1443541 3249971 := bstep (se 1 (by rfl) ⟨2437478, by rfl⟩ : syracuseStep 3249971 = 4874957) B4874957
theorem B16684865 : Blo 1443541 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B2742103 : Blo 1443541 2742103 := bstep (se 1 (by rfl) ⟨2056577, by rfl⟩ : syracuseStep 2742103 = 4113155) B4113155
theorem B3250007 : Blo 1443541 3250007 := bstep (se 1 (by rfl) ⟨2437505, by rfl⟩ : syracuseStep 3250007 = 4875011) B4875011
theorem B2439065 : Blo 1443541 2439065 := bstep (se 2 (by rfl) ⟨914649, by rfl⟩ : syracuseStep 2439065 = 1829299) B1829299
theorem B15628211 : Blo 1443541 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B3250187 : Blo 1443541 3250187 := bstep (se 1 (by rfl) ⟨2437640, by rfl⟩ : syracuseStep 3250187 = 4875281) B4875281
theorem B2439193 : Blo 1443541 2439193 := bstep (se 2 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 2439193 = 1829395) B1829395
theorem B10967075 : Blo 1443541 10967075 := bstep (se 1 (by rfl) ⟨8225306, by rfl⟩ : syracuseStep 10967075 = 16450613) B16450613
theorem B4872257 : Blo 1443541 4872257 := bstep (se 2 (by rfl) ⟨1827096, by rfl⟩ : syracuseStep 4872257 = 3654193) B3654193
theorem B3250241 : Blo 1443541 3250241 := bstep (se 2 (by rfl) ⟨1218840, by rfl⟩ : syracuseStep 3250241 = 2437681) B2437681
theorem B23443607 : Blo 1443541 23443607 := bstep (se 1 (by rfl) ⟨17582705, by rfl⟩ : syracuseStep 23443607 = 35165411) B35165411
theorem B2603225 : Blo 1443541 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B3250457 : Blo 1443541 3250457 := bstep (se 2 (by rfl) ⟨1218921, by rfl⟩ : syracuseStep 3250457 = 2437843) B2437843
theorem B5208409 : Blo 1443541 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B3250547 : Blo 1443541 3250547 := bstep (se 1 (by rfl) ⟨2437910, by rfl⟩ : syracuseStep 3250547 = 4875821) B4875821
theorem B3250583 : Blo 1443541 3250583 := bstep (se 1 (by rfl) ⟨2437937, by rfl⟩ : syracuseStep 3250583 = 4875875) B4875875
theorem B3086849 : Blo 1443541 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B3250763 : Blo 1443541 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B4872797 : Blo 1443541 4872797 := bstep (se 3 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 4872797 = 1827299) B1827299
theorem B3250817 : Blo 1443541 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B2742923 : Blo 1443541 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B3472051 : Blo 1443541 3472051 := bstep (se 1 (by rfl) ⟨2604038, by rfl⟩ : syracuseStep 3472051 = 5208077) B5208077
theorem B2742977 : Blo 1443541 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B19757773 : Blo 1443541 19757773 := bstep (se 3 (by rfl) ⟨3704582, by rfl⟩ : syracuseStep 19757773 = 7409165) B7409165
theorem B44497613 : Blo 1443541 44497613 := bstep (se 3 (by rfl) ⟨8343302, by rfl⟩ : syracuseStep 44497613 = 16686605) B16686605
theorem B7314137 : Blo 1443541 7314137 := bstep (se 2 (by rfl) ⟨2742801, by rfl⟩ : syracuseStep 7314137 = 5485603) B5485603
theorem B3251033 : Blo 1443541 3251033 := bstep (se 2 (by rfl) ⟨1219137, by rfl⟩ : syracuseStep 3251033 = 2438275) B2438275
theorem B5487533 : Blo 1443541 5487533 := bstep (se 3 (by rfl) ⟨1028912, by rfl⟩ : syracuseStep 5487533 = 2057825) B2057825
theorem B3251123 : Blo 1443541 3251123 := bstep (se 1 (by rfl) ⟨2438342, by rfl⟩ : syracuseStep 3251123 = 4876685) B4876685
theorem B3472321 : Blo 1443541 3472321 := bstep (se 2 (by rfl) ⟨1302120, by rfl⟩ : syracuseStep 3472321 = 2604241) B2604241
theorem B3251159 : Blo 1443541 3251159 := bstep (se 1 (by rfl) ⟨2438369, by rfl⟩ : syracuseStep 3251159 = 4876739) B4876739
theorem B8232029 : Blo 1443541 8232029 := bstep (se 3 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 8232029 = 3087011) B3087011
theorem B3251339 : Blo 1443541 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B3251393 : Blo 1443541 3251393 := bstep (se 2 (by rfl) ⟨1219272, by rfl⟩ : syracuseStep 3251393 = 2438545) B2438545
theorem B18513197 : Blo 1443541 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B10419587 : Blo 1443541 10419587 := bstep (se 1 (by rfl) ⟨7814690, by rfl⟩ : syracuseStep 10419587 = 15629381) B15629381
theorem B45071765 : Blo 1443541 45071765 := bstep (se 6 (by rfl) ⟨1056369, by rfl⟩ : syracuseStep 45071765 = 2112739) B2112739
theorem B2055575 : Blo 1443541 2055575 := bstep (se 1 (by rfl) ⟨1541681, by rfl⟩ : syracuseStep 2055575 = 3083363) B3083363
theorem B3251609 : Blo 1443541 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B3251699 : Blo 1443541 3251699 := bstep (se 1 (by rfl) ⟨2438774, by rfl⟩ : syracuseStep 3251699 = 4877549) B4877549
theorem B3251735 : Blo 1443541 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B2743895 : Blo 1443541 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B2604673 : Blo 1443541 2604673 := bstep (se 2 (by rfl) ⟨976752, by rfl⟩ : syracuseStep 2604673 = 1953505) B1953505
theorem B6938243 : Blo 1443541 6938243 := bstep (se 1 (by rfl) ⟨5203682, by rfl⟩ : syracuseStep 6938243 = 10407365) B10407365
theorem B16449155 : Blo 1443541 16449155 := bstep (se 1 (by rfl) ⟨12336866, by rfl⟩ : syracuseStep 16449155 = 24673733) B24673733
theorem B5488307 : Blo 1443541 5488307 := bstep (se 1 (by rfl) ⟨4116230, by rfl⟩ : syracuseStep 5488307 = 8232461) B8232461
theorem B2055883 : Blo 1443541 2055883 := bstep (se 1 (by rfl) ⟨1541912, by rfl⟩ : syracuseStep 2055883 = 3083825) B3083825
theorem B4873931 : Blo 1443541 4873931 := bstep (se 1 (by rfl) ⟨3655448, by rfl⟩ : syracuseStep 4873931 = 7310897) B7310897
theorem B4628171 : Blo 1443541 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B3251915 : Blo 1443541 3251915 := bstep (se 1 (by rfl) ⟨2438936, by rfl⟩ : syracuseStep 3251915 = 4877873) B4877873
theorem B3251969 : Blo 1443541 3251969 := bstep (se 2 (by rfl) ⟨1219488, by rfl⟩ : syracuseStep 3251969 = 2438977) B2438977
theorem B8232779 : Blo 1443541 8232779 := bstep (se 1 (by rfl) ⟨6174584, by rfl⟩ : syracuseStep 8232779 = 12349169) B12349169
theorem B4112221 : Blo 1443541 4112221 := bstep (se 3 (by rfl) ⟨771041, by rfl⟩ : syracuseStep 4112221 = 1542083) B1542083
theorem B4112279 : Blo 1443541 4112279 := bstep (se 1 (by rfl) ⟨3084209, by rfl⟩ : syracuseStep 4112279 = 6168419) B6168419
theorem B15032243 : Blo 1443541 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B4513729 : Blo 1443541 4513729 := bstep (se 2 (by rfl) ⟨1692648, by rfl⟩ : syracuseStep 4513729 = 3385297) B3385297
theorem B4874201 : Blo 1443541 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B3252185 : Blo 1443541 3252185 := bstep (se 2 (by rfl) ⟨1219569, by rfl⟩ : syracuseStep 3252185 = 2439139) B2439139
theorem B3252239 : Blo 1443541 3252239 := bstep (se 1 (by rfl) ⟨2439179, by rfl⟩ : syracuseStep 3252239 = 4878359) B4878359
theorem B3252257 : Blo 1443541 3252257 := bstep (se 2 (by rfl) ⟨1219596, by rfl⟩ : syracuseStep 3252257 = 2439193) B2439193
theorem B4112471 : Blo 1443541 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B4169875 : Blo 1443541 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B6938797 : Blo 1443541 6938797 := bstep (se 3 (by rfl) ⟨1301024, by rfl⟩ : syracuseStep 6938797 = 2602049) B2602049
theorem B9257161 : Blo 1443541 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B8225171 : Blo 1443541 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B6169117 : Blo 1443541 6169117 := bstep (se 3 (by rfl) ⟨1156709, by rfl⟩ : syracuseStep 6169117 = 2313419) B2313419
theorem B4874795 : Blo 1443541 4874795 := bstep (se 1 (by rfl) ⟨3656096, by rfl⟩ : syracuseStep 4874795 = 7312193) B7312193
theorem B5481047 : Blo 1443541 5481047 := bstep (se 1 (by rfl) ⟨4110785, by rfl⟩ : syracuseStep 5481047 = 8221571) B8221571
theorem B59294339 : Blo 1443541 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B2057033 : Blo 1443541 2057033 := bstep (se 2 (by rfl) ⟨771387, by rfl⟩ : syracuseStep 2057033 = 1542775) B1542775
theorem B6169459 : Blo 1443541 6169459 := bstep (se 1 (by rfl) ⟨4627094, by rfl⟩ : syracuseStep 6169459 = 9254189) B9254189
theorem B8225671 : Blo 1443541 8225671 := bstep (se 1 (by rfl) ⟨6169253, by rfl⟩ : syracuseStep 8225671 = 12338507) B12338507
theorem B1647503 : Blo 1443541 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B4629401 : Blo 1443541 4629401 := bstep (se 2 (by rfl) ⟨1736025, by rfl⟩ : syracuseStep 4629401 = 3472051) B3472051
theorem B4113337 : Blo 1443541 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B2778145 : Blo 1443541 2778145 := bstep (se 2 (by rfl) ⟨1041804, by rfl⟩ : syracuseStep 2778145 = 2083609) B2083609
theorem B5481533 : Blo 1443541 5481533 := bstep (se 3 (by rfl) ⟨1027787, by rfl⟩ : syracuseStep 5481533 = 2055575) B2055575
theorem B7316567 : Blo 1443541 7316567 := bstep (se 1 (by rfl) ⟨5487425, by rfl⟩ : syracuseStep 7316567 = 10974851) B10974851
theorem B5858423 : Blo 1443541 5858423 := bstep (se 1 (by rfl) ⟨4393817, by rfl⟩ : syracuseStep 5858423 = 8787635) B8787635
theorem B3654791 : Blo 1443541 3654791 := bstep (se 1 (by rfl) ⟨2741093, by rfl⟩ : syracuseStep 3654791 = 5482187) B5482187
theorem B3654841 : Blo 1443541 3654841 := bstep (se 2 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 3654841 = 2741131) B2741131
theorem B4629761 : Blo 1443541 4629761 := bstep (se 2 (by rfl) ⟨1736160, by rfl⟩ : syracuseStep 4629761 = 3472321) B3472321
theorem B4113679 : Blo 1443541 4113679 := bstep (se 1 (by rfl) ⟨3085259, by rfl⟩ : syracuseStep 4113679 = 6170519) B6170519
theorem B1541639 : Blo 1443541 1541639 := bstep (se 1 (by rfl) ⟨1156229, by rfl⟩ : syracuseStep 1541639 = 2312459) B2312459
theorem B4113953 : Blo 1443541 4113953 := bstep (se 2 (by rfl) ⟨1542732, by rfl⟩ : syracuseStep 4113953 = 3085465) B3085465
theorem B7317053 : Blo 1443541 7317053 := bstep (se 3 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 7317053 = 2743895) B2743895
theorem B27756107 : Blo 1443541 27756107 := bstep (se 1 (by rfl) ⟨20817080, by rfl⟩ : syracuseStep 27756107 = 41634161) B41634161
theorem B2057899 : Blo 1443541 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1443591 : Blo 1443541 1443591 := bstep (se 1 (by rfl) ⟨1082693, by rfl⟩ : syracuseStep 1443591 = 2165387) B2165387
theorem B2197255 : Blo 1443541 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B1443599 : Blo 1443541 1443599 := bstep (se 1 (by rfl) ⟨1082699, by rfl⟩ : syracuseStep 1443599 = 2165399) B2165399
theorem B3655439 : Blo 1443541 3655439 := bstep (se 1 (by rfl) ⟨2741579, by rfl⟩ : syracuseStep 3655439 = 5483159) B5483159
theorem B1828651 : Blo 1443541 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B1443643 : Blo 1443541 1443643 := bstep (se 1 (by rfl) ⟨1082732, by rfl⟩ : syracuseStep 1443643 = 2165465) B2165465
theorem B7309115 : Blo 1443541 7309115 := bstep (se 1 (by rfl) ⟨5481836, by rfl⟩ : syracuseStep 7309115 = 10963673) B10963673
theorem B4876091 : Blo 1443541 4876091 := bstep (se 1 (by rfl) ⟨3657068, by rfl⟩ : syracuseStep 4876091 = 7314137) B7314137
theorem B1443719 : Blo 1443541 1443719 := bstep (se 1 (by rfl) ⟨1082789, by rfl⟩ : syracuseStep 1443719 = 2165579) B2165579
theorem B1443727 : Blo 1443541 1443727 := bstep (se 1 (by rfl) ⟨1082795, by rfl⟩ : syracuseStep 1443727 = 2165591) B2165591
theorem B1443771 : Blo 1443541 1443771 := bstep (se 1 (by rfl) ⟨1082828, by rfl⟩ : syracuseStep 1443771 = 2165657) B2165657
theorem B5859281 : Blo 1443541 5859281 := bstep (se 2 (by rfl) ⟨2197230, by rfl⟩ : syracuseStep 5859281 = 4394461) B4394461
theorem B7309277 : Blo 1443541 7309277 := bstep (se 3 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 7309277 = 2740979) B2740979
theorem B1443847 : Blo 1443541 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B1443855 : Blo 1443541 1443855 := bstep (se 1 (by rfl) ⟨1082891, by rfl⟩ : syracuseStep 1443855 = 2165783) B2165783
theorem B2197547 : Blo 1443541 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B1443899 : Blo 1443541 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B1443975 : Blo 1443541 1443975 := bstep (se 1 (by rfl) ⟨1082981, by rfl⟩ : syracuseStep 1443975 = 2165963) B2165963
theorem B4114567 : Blo 1443541 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B1624207 : Blo 1443541 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B1443983 : Blo 1443541 1443983 := bstep (se 1 (by rfl) ⟨1082987, by rfl⟩ : syracuseStep 1443983 = 2165975) B2165975
theorem B1444027 : Blo 1443541 1444027 := bstep (se 1 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 1444027 = 2166041) B2166041
theorem B1542331 : Blo 1443541 1542331 := bstep (se 1 (by rfl) ⟨1156748, by rfl⟩ : syracuseStep 1542331 = 2313497) B2313497
theorem B1444103 : Blo 1443541 1444103 := bstep (se 1 (by rfl) ⟨1083077, by rfl⟩ : syracuseStep 1444103 = 2166155) B2166155
theorem B1444111 : Blo 1443541 1444111 := bstep (se 1 (by rfl) ⟨1083083, by rfl⟩ : syracuseStep 1444111 = 2166167) B2166167
theorem B15616273 : Blo 1443541 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B7309601 : Blo 1443541 7309601 := bstep (se 2 (by rfl) ⟨2741100, by rfl⟩ : syracuseStep 7309601 = 5482201) B5482201
theorem B4876577 : Blo 1443541 4876577 := bstep (se 2 (by rfl) ⟨1828716, by rfl⟩ : syracuseStep 4876577 = 3657433) B3657433
theorem B2312491 : Blo 1443541 2312491 := bstep (se 1 (by rfl) ⟨1734368, by rfl⟩ : syracuseStep 2312491 = 3468737) B3468737
theorem B1444155 : Blo 1443541 1444155 := bstep (se 1 (by rfl) ⟨1083116, by rfl⟩ : syracuseStep 1444155 = 2166233) B2166233
theorem B1444231 : Blo 1443541 1444231 := bstep (se 1 (by rfl) ⟨1083173, by rfl⟩ : syracuseStep 1444231 = 2166347) B2166347
theorem B1444239 : Blo 1443541 1444239 := bstep (se 1 (by rfl) ⟨1083179, by rfl⟩ : syracuseStep 1444239 = 2166359) B2166359
theorem B1444283 : Blo 1443541 1444283 := bstep (se 1 (by rfl) ⟨1083212, by rfl⟩ : syracuseStep 1444283 = 2166425) B2166425
theorem B3656137 : Blo 1443541 3656137 := bstep (se 2 (by rfl) ⟨1371051, by rfl⟩ : syracuseStep 3656137 = 2742103) B2742103
theorem B5482961 : Blo 1443541 5482961 := bstep (se 2 (by rfl) ⟨2056110, by rfl⟩ : syracuseStep 5482961 = 4112221) B4112221
theorem B1444359 : Blo 1443541 1444359 := bstep (se 1 (by rfl) ⟨1083269, by rfl⟩ : syracuseStep 1444359 = 2166539) B2166539
theorem B4114955 : Blo 1443541 4114955 := bstep (se 1 (by rfl) ⟨3086216, by rfl⟩ : syracuseStep 4114955 = 6172433) B6172433
theorem B1444367 : Blo 1443541 1444367 := bstep (se 1 (by rfl) ⟨1083275, by rfl⟩ : syracuseStep 1444367 = 2166551) B2166551
theorem B1444411 : Blo 1443541 1444411 := bstep (se 1 (by rfl) ⟨1083308, by rfl⟩ : syracuseStep 1444411 = 2166617) B2166617
theorem B2165321 : Blo 1443541 2165321 := bstep (se 2 (by rfl) ⟨811995, by rfl⟩ : syracuseStep 2165321 = 1623991) B1623991
theorem B3656279 : Blo 1443541 3656279 := bstep (se 1 (by rfl) ⟨2742209, by rfl⟩ : syracuseStep 3656279 = 5484419) B5484419
theorem B10021495 : Blo 1443541 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B1624711 : Blo 1443541 1624711 := bstep (se 1 (by rfl) ⟨1218533, by rfl⟩ : syracuseStep 1624711 = 2437067) B2437067
theorem B1444487 : Blo 1443541 1444487 := bstep (se 1 (by rfl) ⟨1083365, by rfl⟩ : syracuseStep 1444487 = 2166731) B2166731
theorem B1444495 : Blo 1443541 1444495 := bstep (se 1 (by rfl) ⟨1083371, by rfl⟩ : syracuseStep 1444495 = 2166743) B2166743
theorem B2165435 : Blo 1443541 2165435 := bstep (se 1 (by rfl) ⟨1624076, by rfl⟩ : syracuseStep 2165435 = 3248153) B3248153
theorem B1444539 : Blo 1443541 1444539 := bstep (se 1 (by rfl) ⟨1083404, by rfl⟩ : syracuseStep 1444539 = 2166809) B2166809
theorem B11709157 : Blo 1443541 11709157 := bstep (se 4 (by rfl) ⟨1097733, by rfl⟩ : syracuseStep 11709157 = 2195467) B2195467
theorem B2165495 : Blo 1443541 2165495 := bstep (se 1 (by rfl) ⟨1624121, by rfl⟩ : syracuseStep 2165495 = 3248243) B3248243
theorem B1444615 : Blo 1443541 1444615 := bstep (se 1 (by rfl) ⟨1083461, by rfl⟩ : syracuseStep 1444615 = 2166923) B2166923
theorem B2165519 : Blo 1443541 2165519 := bstep (se 1 (by rfl) ⟨1624139, by rfl⟩ : syracuseStep 2165519 = 3248279) B3248279
theorem B1444623 : Blo 1443541 1444623 := bstep (se 1 (by rfl) ⟨1083467, by rfl⟩ : syracuseStep 1444623 = 2166935) B2166935
theorem B2165561 : Blo 1443541 2165561 := bstep (se 2 (by rfl) ⟨812085, by rfl⟩ : syracuseStep 2165561 = 1624171) B1624171
theorem B1624891 : Blo 1443541 1624891 := bstep (se 1 (by rfl) ⟨1218668, by rfl⟩ : syracuseStep 1624891 = 2437337) B2437337
theorem B1444667 : Blo 1443541 1444667 := bstep (se 1 (by rfl) ⟨1083500, by rfl⟩ : syracuseStep 1444667 = 2167001) B2167001
theorem B14830451 : Blo 1443541 14830451 := bstep (se 1 (by rfl) ⟨11122838, by rfl⟩ : syracuseStep 14830451 = 22245677) B22245677
theorem B4877171 : Blo 1443541 4877171 := bstep (se 1 (by rfl) ⟨3657878, by rfl⟩ : syracuseStep 4877171 = 7315757) B7315757
theorem B2165639 : Blo 1443541 2165639 := bstep (se 1 (by rfl) ⟨1624229, by rfl⟩ : syracuseStep 2165639 = 3248459) B3248459
theorem B1444743 : Blo 1443541 1444743 := bstep (se 1 (by rfl) ⟨1083557, by rfl⟩ : syracuseStep 1444743 = 2167115) B2167115
theorem B1444751 : Blo 1443541 1444751 := bstep (se 1 (by rfl) ⟨1083563, by rfl⟩ : syracuseStep 1444751 = 2167127) B2167127
theorem B2165675 : Blo 1443541 2165675 := bstep (se 1 (by rfl) ⟨1624256, by rfl⟩ : syracuseStep 2165675 = 3248513) B3248513
theorem B1444795 : Blo 1443541 1444795 := bstep (se 1 (by rfl) ⟨1083596, by rfl⟩ : syracuseStep 1444795 = 2167193) B2167193
theorem B2436041 : Blo 1443541 2436041 := bstep (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) B1827031
theorem B2165705 : Blo 1443541 2165705 := bstep (se 2 (by rfl) ⟨812139, by rfl⟩ : syracuseStep 2165705 = 1624279) B1624279
theorem B1444871 : Blo 1443541 1444871 := bstep (se 1 (by rfl) ⟨1083653, by rfl⟩ : syracuseStep 1444871 = 2167307) B2167307
theorem B1444879 : Blo 1443541 1444879 := bstep (se 1 (by rfl) ⟨1083659, by rfl⟩ : syracuseStep 1444879 = 2167319) B2167319
theorem B2165819 : Blo 1443541 2165819 := bstep (se 1 (by rfl) ⟨1624364, by rfl⟩ : syracuseStep 2165819 = 3248729) B3248729
theorem B1444923 : Blo 1443541 1444923 := bstep (se 1 (by rfl) ⟨1083692, by rfl⟩ : syracuseStep 1444923 = 2167385) B2167385
theorem B62516285 : Blo 1443541 62516285 := bstep (se 3 (by rfl) ⟨11721803, by rfl⟩ : syracuseStep 62516285 = 23443607) B23443607
theorem B2165879 : Blo 1443541 2165879 := bstep (se 1 (by rfl) ⟨1624409, by rfl⟩ : syracuseStep 2165879 = 3248819) B3248819
theorem B1444999 : Blo 1443541 1444999 := bstep (se 1 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 1444999 = 2167499) B2167499
theorem B2165903 : Blo 1443541 2165903 := bstep (se 1 (by rfl) ⟨1624427, by rfl⟩ : syracuseStep 2165903 = 3248855) B3248855
theorem B1445007 : Blo 1443541 1445007 := bstep (se 1 (by rfl) ⟨1083755, by rfl⟩ : syracuseStep 1445007 = 2167511) B2167511
theorem B2165945 : Blo 1443541 2165945 := bstep (se 2 (by rfl) ⟨812229, by rfl⟩ : syracuseStep 2165945 = 1624459) B1624459
theorem B1445051 : Blo 1443541 1445051 := bstep (se 1 (by rfl) ⟨1083788, by rfl⟩ : syracuseStep 1445051 = 2167577) B2167577
theorem B3083465 : Blo 1443541 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B11709677 : Blo 1443541 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B7310573 : Blo 1443541 7310573 := bstep (se 3 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 7310573 = 2741465) B2741465
theorem B6941933 : Blo 1443541 6941933 := bstep (se 3 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 6941933 = 2603225) B2603225
theorem B2166023 : Blo 1443541 2166023 := bstep (se 1 (by rfl) ⟨1624517, by rfl⟩ : syracuseStep 2166023 = 3249035) B3249035
theorem B1445127 : Blo 1443541 1445127 := bstep (se 1 (by rfl) ⟨1083845, by rfl⟩ : syracuseStep 1445127 = 2167691) B2167691
theorem B1625359 : Blo 1443541 1625359 := bstep (se 1 (by rfl) ⟨1219019, by rfl⟩ : syracuseStep 1625359 = 2438039) B2438039
theorem B1445135 : Blo 1443541 1445135 := bstep (se 1 (by rfl) ⟨1083851, by rfl⟩ : syracuseStep 1445135 = 2167703) B2167703
theorem B2166059 : Blo 1443541 2166059 := bstep (se 1 (by rfl) ⟨1624544, by rfl⟩ : syracuseStep 2166059 = 3249089) B3249089
theorem B2927915 : Blo 1443541 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B1445179 : Blo 1443541 1445179 := bstep (se 1 (by rfl) ⟨1083884, by rfl⟩ : syracuseStep 1445179 = 2167769) B2167769
theorem B2166089 : Blo 1443541 2166089 := bstep (se 2 (by rfl) ⟨812283, by rfl⟩ : syracuseStep 2166089 = 1624567) B1624567
theorem B1445255 : Blo 1443541 1445255 := bstep (se 1 (by rfl) ⟨1083941, by rfl⟩ : syracuseStep 1445255 = 2167883) B2167883
theorem B1445263 : Blo 1443541 1445263 := bstep (se 1 (by rfl) ⟨1083947, by rfl⟩ : syracuseStep 1445263 = 2167895) B2167895
theorem B2166203 : Blo 1443541 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B1445307 : Blo 1443541 1445307 := bstep (se 1 (by rfl) ⟨1083980, by rfl⟩ : syracuseStep 1445307 = 2167961) B2167961
theorem B126610897 : Blo 1443541 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B2166263 : Blo 1443541 2166263 := bstep (se 1 (by rfl) ⟨1624697, by rfl⟩ : syracuseStep 2166263 = 3249395) B3249395
theorem B1445383 : Blo 1443541 1445383 := bstep (se 1 (by rfl) ⟨1084037, by rfl⟩ : syracuseStep 1445383 = 2168075) B2168075
theorem B2166287 : Blo 1443541 2166287 := bstep (se 1 (by rfl) ⟨1624715, by rfl⟩ : syracuseStep 2166287 = 3249431) B3249431
theorem B1445391 : Blo 1443541 1445391 := bstep (se 1 (by rfl) ⟨1084043, by rfl⟩ : syracuseStep 1445391 = 2168087) B2168087
theorem B2166329 : Blo 1443541 2166329 := bstep (se 2 (by rfl) ⟨812373, by rfl⟩ : syracuseStep 2166329 = 1624747) B1624747
theorem B1445435 : Blo 1443541 1445435 := bstep (se 1 (by rfl) ⟨1084076, by rfl⟩ : syracuseStep 1445435 = 2168153) B2168153
theorem B3468919 : Blo 1443541 3468919 := bstep (se 1 (by rfl) ⟨2601689, by rfl⟩ : syracuseStep 3468919 = 5203379) B5203379
theorem B2436743 : Blo 1443541 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B2166407 : Blo 1443541 2166407 := bstep (se 1 (by rfl) ⟨1624805, by rfl⟩ : syracuseStep 2166407 = 3249611) B3249611
theorem B1445511 : Blo 1443541 1445511 := bstep (se 1 (by rfl) ⟨1084133, by rfl⟩ : syracuseStep 1445511 = 2168267) B2168267
theorem B1445519 : Blo 1443541 1445519 := bstep (se 1 (by rfl) ⟨1084139, by rfl⟩ : syracuseStep 1445519 = 2168279) B2168279
theorem B2166443 : Blo 1443541 2166443 := bstep (se 1 (by rfl) ⟨1624832, by rfl⟩ : syracuseStep 2166443 = 3249665) B3249665
theorem B2166473 : Blo 1443541 2166473 := bstep (se 2 (by rfl) ⟨812427, by rfl⟩ : syracuseStep 2166473 = 1624855) B1624855
theorem B1625863 : Blo 1443541 1625863 := bstep (se 1 (by rfl) ⟨1219397, by rfl⟩ : syracuseStep 1625863 = 2438795) B2438795
theorem B4116253 : Blo 1443541 4116253 := bstep (se 3 (by rfl) ⟨771797, by rfl⟩ : syracuseStep 4116253 = 1543595) B1543595
theorem B2166587 : Blo 1443541 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B7409497 : Blo 1443541 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B3247991 : Blo 1443541 3247991 := bstep (se 1 (by rfl) ⟨2435993, by rfl⟩ : syracuseStep 3247991 = 4871987) B4871987
theorem B2166647 : Blo 1443541 2166647 := bstep (se 1 (by rfl) ⟨1624985, by rfl⟩ : syracuseStep 2166647 = 3249971) B3249971
theorem B2166671 : Blo 1443541 2166671 := bstep (se 1 (by rfl) ⟨1625003, by rfl⟩ : syracuseStep 2166671 = 3250007) B3250007
theorem B16453529 : Blo 1443541 16453529 := bstep (se 2 (by rfl) ⟨6170073, by rfl⟩ : syracuseStep 16453529 = 12340147) B12340147
theorem B2166713 : Blo 1443541 2166713 := bstep (se 2 (by rfl) ⟨812517, by rfl⟩ : syracuseStep 2166713 = 1625035) B1625035
theorem B1626043 : Blo 1443541 1626043 := bstep (se 1 (by rfl) ⟨1219532, by rfl⟩ : syracuseStep 1626043 = 2439065) B2439065
theorem B2166791 : Blo 1443541 2166791 := bstep (se 1 (by rfl) ⟨1625093, by rfl⟩ : syracuseStep 2166791 = 3250187) B3250187
theorem B7311383 : Blo 1443541 7311383 := bstep (se 1 (by rfl) ⟨5483537, by rfl⟩ : syracuseStep 7311383 = 10967075) B10967075
theorem B3248171 : Blo 1443541 3248171 := bstep (se 1 (by rfl) ⟨2436128, by rfl⟩ : syracuseStep 3248171 = 4872257) B4872257
theorem B2166827 : Blo 1443541 2166827 := bstep (se 1 (by rfl) ⟨1625120, by rfl⟩ : syracuseStep 2166827 = 3250241) B3250241
theorem B2166857 : Blo 1443541 2166857 := bstep (se 2 (by rfl) ⟨812571, by rfl⟩ : syracuseStep 2166857 = 1625143) B1625143
theorem B5206103 : Blo 1443541 5206103 := bstep (se 1 (by rfl) ⟨3904577, by rfl⟩ : syracuseStep 5206103 = 7809155) B7809155
theorem B5484631 : Blo 1443541 5484631 := bstep (se 1 (by rfl) ⟨4113473, by rfl⟩ : syracuseStep 5484631 = 8226947) B8226947
theorem B2166971 : Blo 1443541 2166971 := bstep (se 1 (by rfl) ⟨1625228, by rfl⟩ : syracuseStep 2166971 = 3250457) B3250457
theorem B4944073 : Blo 1443541 4944073 := bstep (se 2 (by rfl) ⟨1854027, by rfl⟩ : syracuseStep 4944073 = 3708055) B3708055
theorem B23761097 : Blo 1443541 23761097 := bstep (se 2 (by rfl) ⟨8910411, by rfl⟩ : syracuseStep 23761097 = 17820823) B17820823
theorem B2167031 : Blo 1443541 2167031 := bstep (se 1 (by rfl) ⟨1625273, by rfl⟩ : syracuseStep 2167031 = 3250547) B3250547
theorem B2437391 : Blo 1443541 2437391 := bstep (se 1 (by rfl) ⟨1828043, by rfl⟩ : syracuseStep 2437391 = 3656087) B3656087
theorem B2167055 : Blo 1443541 2167055 := bstep (se 1 (by rfl) ⟨1625291, by rfl⟩ : syracuseStep 2167055 = 3250583) B3250583
theorem B2167097 : Blo 1443541 2167097 := bstep (se 2 (by rfl) ⟨812661, by rfl⟩ : syracuseStep 2167097 = 1625323) B1625323
theorem B5484935 : Blo 1443541 5484935 := bstep (se 1 (by rfl) ⟨4113701, by rfl⟩ : syracuseStep 5484935 = 8227403) B8227403
theorem B2167175 : Blo 1443541 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B3248531 : Blo 1443541 3248531 := bstep (se 1 (by rfl) ⟨2436398, by rfl⟩ : syracuseStep 3248531 = 4872797) B4872797
theorem B6173081 : Blo 1443541 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B2167211 : Blo 1443541 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B3248585 : Blo 1443541 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B2167241 : Blo 1443541 2167241 := bstep (se 2 (by rfl) ⟨812715, by rfl⟩ : syracuseStep 2167241 = 1625431) B1625431
theorem B14815709 : Blo 1443541 14815709 := bstep (se 3 (by rfl) ⟨2777945, by rfl⟩ : syracuseStep 14815709 = 5555891) B5555891
theorem B2167355 : Blo 1443541 2167355 := bstep (se 1 (by rfl) ⟨1625516, by rfl⟩ : syracuseStep 2167355 = 3251033) B3251033
theorem B5485117 : Blo 1443541 5485117 := bstep (se 3 (by rfl) ⟨1028459, by rfl⟩ : syracuseStep 5485117 = 2056919) B2056919
theorem B3658355 : Blo 1443541 3658355 := bstep (se 1 (by rfl) ⟨2743766, by rfl⟩ : syracuseStep 3658355 = 5487533) B5487533
theorem B2167415 : Blo 1443541 2167415 := bstep (se 1 (by rfl) ⟨1625561, by rfl⟩ : syracuseStep 2167415 = 3251123) B3251123
theorem B2167439 : Blo 1443541 2167439 := bstep (se 1 (by rfl) ⟨1625579, by rfl⟩ : syracuseStep 2167439 = 3251159) B3251159
theorem B3125945 : Blo 1443541 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B2167481 : Blo 1443541 2167481 := bstep (se 2 (by rfl) ⟨812805, by rfl⟩ : syracuseStep 2167481 = 1625611) B1625611
theorem B2167559 : Blo 1443541 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B2437931 : Blo 1443541 2437931 := bstep (se 1 (by rfl) ⟨1828448, by rfl⟩ : syracuseStep 2437931 = 3656897) B3656897
theorem B2167595 : Blo 1443541 2167595 := bstep (se 1 (by rfl) ⟨1625696, by rfl⟩ : syracuseStep 2167595 = 3251393) B3251393
theorem B2167625 : Blo 1443541 2167625 := bstep (se 2 (by rfl) ⟨812859, by rfl⟩ : syracuseStep 2167625 = 1625719) B1625719
theorem B12342131 : Blo 1443541 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B2741177 : Blo 1443541 2741177 := bstep (se 2 (by rfl) ⟨1027941, by rfl⟩ : syracuseStep 2741177 = 2055883) B2055883
theorem B2167739 : Blo 1443541 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B2167799 : Blo 1443541 2167799 := bstep (se 1 (by rfl) ⟨1625849, by rfl⟩ : syracuseStep 2167799 = 3251699) B3251699
theorem B2470927 : Blo 1443541 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B2167823 : Blo 1443541 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B2167865 : Blo 1443541 2167865 := bstep (se 2 (by rfl) ⟨812949, by rfl⟩ : syracuseStep 2167865 = 1625899) B1625899
theorem B4625495 : Blo 1443541 4625495 := bstep (se 1 (by rfl) ⟨3469121, by rfl⟩ : syracuseStep 4625495 = 6938243) B6938243
theorem B10966103 : Blo 1443541 10966103 := bstep (se 1 (by rfl) ⟨8224577, by rfl⟩ : syracuseStep 10966103 = 16449155) B16449155
theorem B3658871 : Blo 1443541 3658871 := bstep (se 1 (by rfl) ⟨2744153, by rfl⟩ : syracuseStep 3658871 = 5488307) B5488307
theorem B3249287 : Blo 1443541 3249287 := bstep (se 1 (by rfl) ⟨2436965, by rfl⟩ : syracuseStep 3249287 = 4873931) B4873931
theorem B3085447 : Blo 1443541 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B2167943 : Blo 1443541 2167943 := bstep (se 1 (by rfl) ⟨1625957, by rfl⟩ : syracuseStep 2167943 = 3251915) B3251915
theorem B2167979 : Blo 1443541 2167979 := bstep (se 1 (by rfl) ⟨1625984, by rfl⟩ : syracuseStep 2167979 = 3251969) B3251969
theorem B2438329 : Blo 1443541 2438329 := bstep (se 2 (by rfl) ⟨914373, by rfl⟩ : syracuseStep 2438329 = 1828747) B1828747
theorem B2168009 : Blo 1443541 2168009 := bstep (se 2 (by rfl) ⟨813003, by rfl⟩ : syracuseStep 2168009 = 1626007) B1626007
theorem B6018305 : Blo 1443541 6018305 := bstep (se 2 (by rfl) ⟨2256864, by rfl⟩ : syracuseStep 6018305 = 4513729) B4513729
theorem B2741519 : Blo 1443541 2741519 := bstep (se 1 (by rfl) ⟨2056139, by rfl⟩ : syracuseStep 2741519 = 4112279) B4112279
theorem B3249467 : Blo 1443541 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B2168123 : Blo 1443541 2168123 := bstep (se 1 (by rfl) ⟨1626092, by rfl⟩ : syracuseStep 2168123 = 3252185) B3252185
theorem B4166999 : Blo 1443541 4166999 := bstep (se 1 (by rfl) ⟨3125249, by rfl⟩ : syracuseStep 4166999 = 6250499) B6250499
theorem B2168183 : Blo 1443541 2168183 := bstep (se 1 (by rfl) ⟨1626137, by rfl⟩ : syracuseStep 2168183 = 3252275) B3252275
theorem B2168207 : Blo 1443541 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B3249593 : Blo 1443541 3249593 := bstep (se 2 (by rfl) ⟨1218597, by rfl⟩ : syracuseStep 3249593 = 2437195) B2437195
theorem B2168249 : Blo 1443541 2168249 := bstep (se 2 (by rfl) ⟨813093, by rfl⟩ : syracuseStep 2168249 = 1626187) B1626187
theorem B35149463 : Blo 1443541 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B5207789 : Blo 1443541 5207789 := bstep (se 3 (by rfl) ⟨976460, by rfl⟩ : syracuseStep 5207789 = 1952921) B1952921
theorem B8779535 : Blo 1443541 8779535 := bstep (se 1 (by rfl) ⟨6584651, by rfl⟩ : syracuseStep 8779535 = 13169303) B13169303
theorem B3249935 : Blo 1443541 3249935 := bstep (se 1 (by rfl) ⟨2437451, by rfl⟩ : syracuseStep 3249935 = 4874903) B4874903
theorem B3249953 : Blo 1443541 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B6944545 : Blo 1443541 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B2439031 : Blo 1443541 2439031 := bstep (se 1 (by rfl) ⟨1829273, by rfl⟩ : syracuseStep 2439031 = 3658547) B3658547
theorem B2602937 : Blo 1443541 2602937 := bstep (se 2 (by rfl) ⟨976101, by rfl⟩ : syracuseStep 2602937 = 1952203) B1952203
theorem B4872203 : Blo 1443541 4872203 := bstep (se 1 (by rfl) ⟨3654152, by rfl⟩ : syracuseStep 4872203 = 7308305) B7308305
theorem B35149841 : Blo 1443541 35149841 := bstep (se 2 (by rfl) ⟨13181190, by rfl⟩ : syracuseStep 35149841 = 26362381) B26362381
theorem B2742331 : Blo 1443541 2742331 := bstep (se 1 (by rfl) ⟨2056748, by rfl⟩ : syracuseStep 2742331 = 4113497) B4113497
theorem B4454459 : Blo 1443541 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B2439227 : Blo 1443541 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B4872311 : Blo 1443541 4872311 := bstep (se 1 (by rfl) ⟨3654233, by rfl⟩ : syracuseStep 4872311 = 7308467) B7308467
theorem B3250295 : Blo 1443541 3250295 := bstep (se 1 (by rfl) ⟨2437721, by rfl⟩ : syracuseStep 3250295 = 4875443) B4875443
theorem B2742407 : Blo 1443541 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B5486849 : Blo 1443541 5486849 := bstep (se 2 (by rfl) ⟨2057568, by rfl⟩ : syracuseStep 5486849 = 4115137) B4115137
theorem B26343697 : Blo 1443541 26343697 := bstep (se 2 (by rfl) ⟨9878886, by rfl⟩ : syracuseStep 26343697 = 19757773) B19757773
theorem B3250475 : Blo 1443541 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B1669511 : Blo 1443541 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B8231321 : Blo 1443541 8231321 := bstep (se 2 (by rfl) ⟨3086745, by rfl⟩ : syracuseStep 8231321 = 6173491) B6173491
theorem B2742817 : Blo 1443541 2742817 := bstep (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) B2057113
theorem B11123243 : Blo 1443541 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B10418807 : Blo 1443541 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B3250835 : Blo 1443541 3250835 := bstep (se 1 (by rfl) ⟨2438126, by rfl⟩ : syracuseStep 3250835 = 4876253) B4876253
theorem B4872905 : Blo 1443541 4872905 := bstep (se 2 (by rfl) ⟨1827339, by rfl⟩ : syracuseStep 4872905 = 3654679) B3654679
theorem B3250889 : Blo 1443541 3250889 := bstep (se 2 (by rfl) ⟨1219083, by rfl⟩ : syracuseStep 3250889 = 2438167) B2438167
theorem B2743159 : Blo 1443541 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B7314461 : Blo 1443541 7314461 := bstep (se 3 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 7314461 = 2742923) B2742923
theorem B6937643 : Blo 1443541 6937643 := bstep (se 1 (by rfl) ⟨5203232, by rfl⟩ : syracuseStep 6937643 = 10406465) B10406465
theorem B12344521 : Blo 1443541 12344521 := bstep (se 2 (by rfl) ⟨4629195, by rfl⟩ : syracuseStep 12344521 = 9258391) B9258391
theorem B118660301 : Blo 1443541 118660301 := bstep (se 3 (by rfl) ⟨22248806, by rfl⟩ : syracuseStep 118660301 = 44497613) B44497613
theorem B37043405 : Blo 1443541 37043405 := bstep (se 3 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 37043405 = 13891277) B13891277
theorem B7912741 : Blo 1443541 7912741 := bstep (se 4 (by rfl) ⟨741819, by rfl⟩ : syracuseStep 7912741 = 1483639) B1483639
theorem B4873607 : Blo 1443541 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B3251591 : Blo 1443541 3251591 := bstep (se 1 (by rfl) ⟨2438693, by rfl⟩ : syracuseStep 3251591 = 4877387) B4877387
theorem B5488019 : Blo 1443541 5488019 := bstep (se 1 (by rfl) ⟨4116014, by rfl⟩ : syracuseStep 5488019 = 8232029) B8232029
theorem B3472897 : Blo 1443541 3472897 := bstep (se 2 (by rfl) ⟨1302336, by rfl⟩ : syracuseStep 3472897 = 2604673) B2604673
theorem B7314947 : Blo 1443541 7314947 := bstep (se 1 (by rfl) ⟨5486210, by rfl⟩ : syracuseStep 7314947 = 10972421) B10972421
theorem B3251771 : Blo 1443541 3251771 := bstep (se 1 (by rfl) ⟨2438828, by rfl⟩ : syracuseStep 3251771 = 4877657) B4877657
theorem B6946391 : Blo 1443541 6946391 := bstep (se 1 (by rfl) ⟨5209793, by rfl⟩ : syracuseStep 6946391 = 10419587) B10419587
theorem B23420515 : Blo 1443541 23420515 := bstep (se 1 (by rfl) ⟨17565386, by rfl⟩ : syracuseStep 23420515 = 35130773) B35130773
theorem B30047843 : Blo 1443541 30047843 := bstep (se 1 (by rfl) ⟨22535882, by rfl⟩ : syracuseStep 30047843 = 45071765) B45071765
theorem B20831843 : Blo 1443541 20831843 := bstep (se 1 (by rfl) ⟨15623882, by rfl⟩ : syracuseStep 20831843 = 31247765) B31247765
theorem B3251897 : Blo 1443541 3251897 := bstep (se 2 (by rfl) ⟨1219461, by rfl⟩ : syracuseStep 3251897 = 2438923) B2438923
theorem B4873985 : Blo 1443541 4873985 := bstep (se 2 (by rfl) ⟨1827744, by rfl⟩ : syracuseStep 4873985 = 3655489) B3655489
theorem B5488519 : Blo 1443541 5488519 := bstep (se 1 (by rfl) ⟨4116389, by rfl⟩ : syracuseStep 5488519 = 8232779) B8232779
theorem B4874255 : Blo 1443541 4874255 := bstep (se 1 (by rfl) ⟨3655691, by rfl⟩ : syracuseStep 4874255 = 7311383) B7311383
theorem B2056441 : Blo 1443541 2056441 := bstep (se 2 (by rfl) ⟨771165, by rfl⟩ : syracuseStep 2056441 = 1542331) B1542331
theorem B3654031 : Blo 1443541 3654031 := bstep (se 1 (by rfl) ⟨2740523, by rfl⟩ : syracuseStep 3654031 = 5481047) B5481047
theorem B4874849 : Blo 1443541 4874849 := bstep (se 2 (by rfl) ⟨1828068, by rfl⟩ : syracuseStep 4874849 = 3656137) B3656137
theorem B1827451 : Blo 1443541 1827451 := bstep (se 1 (by rfl) ⟨1370588, by rfl⟩ : syracuseStep 1827451 = 2741177) B2741177
theorem B8225489 : Blo 1443541 8225489 := bstep (se 2 (by rfl) ⟨3084558, by rfl⟩ : syracuseStep 8225489 = 6169117) B6169117
theorem B3654355 : Blo 1443541 3654355 := bstep (se 1 (by rfl) ⟨2740766, by rfl⟩ : syracuseStep 3654355 = 5481533) B5481533
theorem B13361993 : Blo 1443541 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B1827679 : Blo 1443541 1827679 := bstep (se 1 (by rfl) ⟨1370759, by rfl⟩ : syracuseStep 1827679 = 2741519) B2741519
theorem B2777999 : Blo 1443541 2777999 := bstep (se 1 (by rfl) ⟨2083499, by rfl⟩ : syracuseStep 2777999 = 4166999) B4166999
theorem B8225945 : Blo 1443541 8225945 := bstep (se 2 (by rfl) ⟨3084729, by rfl⟩ : syracuseStep 8225945 = 6169459) B6169459
theorem B3294569 : Blo 1443541 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B1828271 : Blo 1443541 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B17573365 : Blo 1443541 17573365 := bstep (se 5 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 17573365 = 1647503) B1647503
theorem B4113929 : Blo 1443541 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B16459361 : Blo 1443541 16459361 := bstep (se 2 (by rfl) ⟨6172260, by rfl⟩ : syracuseStep 16459361 = 12344521) B12344521
theorem B3655307 : Blo 1443541 3655307 := bstep (se 1 (by rfl) ⟨2741480, by rfl⟩ : syracuseStep 3655307 = 5482961) B5482961
theorem B7415495 : Blo 1443541 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B1443547 : Blo 1443541 1443547 := bstep (se 1 (by rfl) ⟨1082660, by rfl⟩ : syracuseStep 1443547 = 2165321) B2165321
theorem B1443623 : Blo 1443541 1443623 := bstep (se 1 (by rfl) ⟨1082717, by rfl⟩ : syracuseStep 1443623 = 2165435) B2165435
theorem B1443663 : Blo 1443541 1443663 := bstep (se 1 (by rfl) ⟨1082747, by rfl⟩ : syracuseStep 1443663 = 2165495) B2165495
theorem B1443679 : Blo 1443541 1443679 := bstep (se 1 (by rfl) ⟨1082759, by rfl⟩ : syracuseStep 1443679 = 2165519) B2165519
theorem B1443707 : Blo 1443541 1443707 := bstep (se 1 (by rfl) ⟨1082780, by rfl⟩ : syracuseStep 1443707 = 2165561) B2165561
theorem B1443759 : Blo 1443541 1443759 := bstep (se 1 (by rfl) ⟨1082819, by rfl⟩ : syracuseStep 1443759 = 2165639) B2165639
theorem B168814529 : Blo 1443541 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B1443783 : Blo 1443541 1443783 := bstep (se 1 (by rfl) ⟨1082837, by rfl⟩ : syracuseStep 1443783 = 2165675) B2165675
theorem B1624027 : Blo 1443541 1624027 := bstep (se 1 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 1624027 = 2436041) B2436041
theorem B1443803 : Blo 1443541 1443803 := bstep (se 1 (by rfl) ⟨1082852, by rfl⟩ : syracuseStep 1443803 = 2165705) B2165705
theorem B4630529 : Blo 1443541 4630529 := bstep (se 2 (by rfl) ⟨1736448, by rfl⟩ : syracuseStep 4630529 = 3472897) B3472897
theorem B4876307 : Blo 1443541 4876307 := bstep (se 1 (by rfl) ⟨3657230, by rfl⟩ : syracuseStep 4876307 = 7314461) B7314461
theorem B1443879 : Blo 1443541 1443879 := bstep (se 1 (by rfl) ⟨1082909, by rfl⟩ : syracuseStep 1443879 = 2165819) B2165819
theorem B1443919 : Blo 1443541 1443919 := bstep (se 1 (by rfl) ⟨1082939, by rfl⟩ : syracuseStep 1443919 = 2165879) B2165879
theorem B1443935 : Blo 1443541 1443935 := bstep (se 1 (by rfl) ⟨1082951, by rfl⟩ : syracuseStep 1443935 = 2165903) B2165903
theorem B1443963 : Blo 1443541 1443963 := bstep (se 1 (by rfl) ⟨1082972, by rfl⟩ : syracuseStep 1443963 = 2165945) B2165945
theorem B1444015 : Blo 1443541 1444015 := bstep (se 1 (by rfl) ⟨1083011, by rfl⟩ : syracuseStep 1444015 = 2166023) B2166023
theorem B1444039 : Blo 1443541 1444039 := bstep (se 1 (by rfl) ⟨1083029, by rfl⟩ : syracuseStep 1444039 = 2166059) B2166059
theorem B1951943 : Blo 1443541 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B1444059 : Blo 1443541 1444059 := bstep (se 1 (by rfl) ⟨1083044, by rfl⟩ : syracuseStep 1444059 = 2166089) B2166089
theorem B1444135 : Blo 1443541 1444135 := bstep (se 1 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 1444135 = 2166203) B2166203
theorem B1444175 : Blo 1443541 1444175 := bstep (se 1 (by rfl) ⟨1083131, by rfl⟩ : syracuseStep 1444175 = 2166263) B2166263
theorem B4876631 : Blo 1443541 4876631 := bstep (se 1 (by rfl) ⟨3657473, by rfl⟩ : syracuseStep 4876631 = 7314947) B7314947
theorem B1444191 : Blo 1443541 1444191 := bstep (se 1 (by rfl) ⟨1083143, by rfl⟩ : syracuseStep 1444191 = 2166287) B2166287
theorem B1444219 : Blo 1443541 1444219 := bstep (se 1 (by rfl) ⟨1083164, by rfl⟩ : syracuseStep 1444219 = 2166329) B2166329
theorem B9259393 : Blo 1443541 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B4630927 : Blo 1443541 4630927 := bstep (se 1 (by rfl) ⟨3473195, by rfl⟩ : syracuseStep 4630927 = 6946391) B6946391
theorem B20031895 : Blo 1443541 20031895 := bstep (se 1 (by rfl) ⟨15023921, by rfl⟩ : syracuseStep 20031895 = 30047843) B30047843
theorem B13887895 : Blo 1443541 13887895 := bstep (se 1 (by rfl) ⟨10415921, by rfl⟩ : syracuseStep 13887895 = 20831843) B20831843
theorem B1624495 : Blo 1443541 1624495 := bstep (se 1 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 1624495 = 2436743) B2436743
theorem B1444271 : Blo 1443541 1444271 := bstep (se 1 (by rfl) ⟨1083203, by rfl⟩ : syracuseStep 1444271 = 2166407) B2166407
theorem B1444295 : Blo 1443541 1444295 := bstep (se 1 (by rfl) ⟨1083221, by rfl⟩ : syracuseStep 1444295 = 2166443) B2166443
theorem B1444315 : Blo 1443541 1444315 := bstep (se 1 (by rfl) ⟨1083236, by rfl⟩ : syracuseStep 1444315 = 2166473) B2166473
theorem B7318025 : Blo 1443541 7318025 := bstep (se 2 (by rfl) ⟨2744259, by rfl⟩ : syracuseStep 7318025 = 5488519) B5488519
theorem B1444391 : Blo 1443541 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B2165327 : Blo 1443541 2165327 := bstep (se 1 (by rfl) ⟨1623995, by rfl⟩ : syracuseStep 2165327 = 3247991) B3247991
theorem B1444431 : Blo 1443541 1444431 := bstep (se 1 (by rfl) ⟨1083323, by rfl⟩ : syracuseStep 1444431 = 2166647) B2166647
theorem B1444447 : Blo 1443541 1444447 := bstep (se 1 (by rfl) ⟨1083335, by rfl⟩ : syracuseStep 1444447 = 2166671) B2166671
theorem B1444475 : Blo 1443541 1444475 := bstep (se 1 (by rfl) ⟨1083356, by rfl⟩ : syracuseStep 1444475 = 2166713) B2166713
theorem B1444527 : Blo 1443541 1444527 := bstep (se 1 (by rfl) ⟨1083395, by rfl⟩ : syracuseStep 1444527 = 2166791) B2166791
theorem B64195253 : Blo 1443541 64195253 := bstep (se 5 (by rfl) ⟨3009152, by rfl⟩ : syracuseStep 64195253 = 6018305) B6018305
theorem B2165447 : Blo 1443541 2165447 := bstep (se 1 (by rfl) ⟨1624085, by rfl⟩ : syracuseStep 2165447 = 3248171) B3248171
theorem B1444551 : Blo 1443541 1444551 := bstep (se 1 (by rfl) ⟨1083413, by rfl⟩ : syracuseStep 1444551 = 2166827) B2166827
theorem B1444571 : Blo 1443541 1444571 := bstep (se 1 (by rfl) ⟨1083428, by rfl⟩ : syracuseStep 1444571 = 2166857) B2166857
theorem B3656441 : Blo 1443541 3656441 := bstep (se 2 (by rfl) ⟨1371165, by rfl⟩ : syracuseStep 3656441 = 2742331) B2742331
theorem B1444647 : Blo 1443541 1444647 := bstep (se 1 (by rfl) ⟨1083485, by rfl⟩ : syracuseStep 1444647 = 2166971) B2166971
theorem B1444687 : Blo 1443541 1444687 := bstep (se 1 (by rfl) ⟨1083515, by rfl⟩ : syracuseStep 1444687 = 2167031) B2167031
theorem B1624927 : Blo 1443541 1624927 := bstep (se 1 (by rfl) ⟨1218695, by rfl⟩ : syracuseStep 1624927 = 2437391) B2437391
theorem B1444703 : Blo 1443541 1444703 := bstep (se 1 (by rfl) ⟨1083527, by rfl⟩ : syracuseStep 1444703 = 2167055) B2167055
theorem B2165609 : Blo 1443541 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B1444731 : Blo 1443541 1444731 := bstep (se 1 (by rfl) ⟨1083548, by rfl⟩ : syracuseStep 1444731 = 2167097) B2167097
theorem B9251729 : Blo 1443541 9251729 := bstep (se 2 (by rfl) ⟨3469398, by rfl⟩ : syracuseStep 9251729 = 6938797) B6938797
theorem B3656623 : Blo 1443541 3656623 := bstep (se 1 (by rfl) ⟨2742467, by rfl⟩ : syracuseStep 3656623 = 5484935) B5484935
theorem B1444783 : Blo 1443541 1444783 := bstep (se 1 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 1444783 = 2167175) B2167175
theorem B2165687 : Blo 1443541 2165687 := bstep (se 1 (by rfl) ⟨1624265, by rfl⟩ : syracuseStep 2165687 = 3248531) B3248531
theorem B5483447 : Blo 1443541 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B4115387 : Blo 1443541 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B1444807 : Blo 1443541 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B2165723 : Blo 1443541 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B1444827 : Blo 1443541 1444827 := bstep (se 1 (by rfl) ⟨1083620, by rfl⟩ : syracuseStep 1444827 = 2167241) B2167241
theorem B1444903 : Blo 1443541 1444903 := bstep (se 1 (by rfl) ⟨1083677, by rfl⟩ : syracuseStep 1444903 = 2167355) B2167355
theorem B3083321 : Blo 1443541 3083321 := bstep (se 2 (by rfl) ⟨1156245, by rfl⟩ : syracuseStep 3083321 = 2312491) B2312491
theorem B1444943 : Blo 1443541 1444943 := bstep (se 1 (by rfl) ⟨1083707, by rfl⟩ : syracuseStep 1444943 = 2167415) B2167415
theorem B39529559 : Blo 1443541 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B1444959 : Blo 1443541 1444959 := bstep (se 1 (by rfl) ⟨1083719, by rfl⟩ : syracuseStep 1444959 = 2167439) B2167439
theorem B2083963 : Blo 1443541 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B1444987 : Blo 1443541 1444987 := bstep (se 1 (by rfl) ⟨1083740, by rfl⟩ : syracuseStep 1444987 = 2167481) B2167481
theorem B1445039 : Blo 1443541 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B1625287 : Blo 1443541 1625287 := bstep (se 1 (by rfl) ⟨1218965, by rfl⟩ : syracuseStep 1625287 = 2437931) B2437931
theorem B1445063 : Blo 1443541 1445063 := bstep (se 1 (by rfl) ⟨1083797, by rfl⟩ : syracuseStep 1445063 = 2167595) B2167595
theorem B1445083 : Blo 1443541 1445083 := bstep (se 1 (by rfl) ⟨1083812, by rfl⟩ : syracuseStep 1445083 = 2167625) B2167625
theorem B8228087 : Blo 1443541 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B1445159 : Blo 1443541 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B1445199 : Blo 1443541 1445199 := bstep (se 1 (by rfl) ⟨1083899, by rfl⟩ : syracuseStep 1445199 = 2167799) B2167799
theorem B1445215 : Blo 1443541 1445215 := bstep (se 1 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 1445215 = 2167823) B2167823
theorem B1445243 : Blo 1443541 1445243 := bstep (se 1 (by rfl) ⟨1083932, by rfl⟩ : syracuseStep 1445243 = 2167865) B2167865
theorem B3657089 : Blo 1443541 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B3083663 : Blo 1443541 3083663 := bstep (se 1 (by rfl) ⟨2312747, by rfl⟩ : syracuseStep 3083663 = 4625495) B4625495
theorem B7310735 : Blo 1443541 7310735 := bstep (se 1 (by rfl) ⟨5483051, by rfl⟩ : syracuseStep 7310735 = 10966103) B10966103
theorem B4877711 : Blo 1443541 4877711 := bstep (se 1 (by rfl) ⟨3658283, by rfl⟩ : syracuseStep 4877711 = 7316567) B7316567
theorem B2436527 : Blo 1443541 2436527 := bstep (se 1 (by rfl) ⟨1827395, by rfl⟩ : syracuseStep 2436527 = 3654791) B3654791
theorem B2166191 : Blo 1443541 2166191 := bstep (se 1 (by rfl) ⟨1624643, by rfl⟩ : syracuseStep 2166191 = 3249287) B3249287
theorem B1445295 : Blo 1443541 1445295 := bstep (se 1 (by rfl) ⟨1083971, by rfl⟩ : syracuseStep 1445295 = 2167943) B2167943
theorem B1445319 : Blo 1443541 1445319 := bstep (se 1 (by rfl) ⟨1083989, by rfl⟩ : syracuseStep 1445319 = 2167979) B2167979
theorem B1445339 : Blo 1443541 1445339 := bstep (se 1 (by rfl) ⟨1084004, by rfl⟩ : syracuseStep 1445339 = 2168009) B2168009
theorem B2166281 : Blo 1443541 2166281 := bstep (se 2 (by rfl) ⟨812355, by rfl⟩ : syracuseStep 2166281 = 1624711) B1624711
theorem B2166311 : Blo 1443541 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B1445415 : Blo 1443541 1445415 := bstep (se 1 (by rfl) ⟨1084061, by rfl⟩ : syracuseStep 1445415 = 2168123) B2168123
theorem B1445455 : Blo 1443541 1445455 := bstep (se 1 (by rfl) ⟨1084091, by rfl⟩ : syracuseStep 1445455 = 2168183) B2168183
theorem B1445471 : Blo 1443541 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B2166395 : Blo 1443541 2166395 := bstep (se 1 (by rfl) ⟨1624796, by rfl⟩ : syracuseStep 2166395 = 3249593) B3249593
theorem B1445499 : Blo 1443541 1445499 := bstep (se 1 (by rfl) ⟨1084124, by rfl⟩ : syracuseStep 1445499 = 2168249) B2168249
theorem B4452029 : Blo 1443541 4452029 := bstep (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) B1669511
theorem B4878035 : Blo 1443541 4878035 := bstep (se 1 (by rfl) ⟨3658526, by rfl⟩ : syracuseStep 4878035 = 7317053) B7317053
theorem B2166521 : Blo 1443541 2166521 := bstep (se 2 (by rfl) ⟨812445, by rfl⟩ : syracuseStep 2166521 = 1624891) B1624891
theorem B23432975 : Blo 1443541 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B3657545 : Blo 1443541 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B5853023 : Blo 1443541 5853023 := bstep (se 1 (by rfl) ⟨4389767, by rfl⟩ : syracuseStep 5853023 = 8779535) B8779535
theorem B2436959 : Blo 1443541 2436959 := bstep (se 1 (by rfl) ⟨1827719, by rfl⟩ : syracuseStep 2436959 = 3655439) B3655439
theorem B2166623 : Blo 1443541 2166623 := bstep (se 1 (by rfl) ⟨1624967, by rfl⟩ : syracuseStep 2166623 = 3249935) B3249935
theorem B2166635 : Blo 1443541 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B5484449 : Blo 1443541 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B3248135 : Blo 1443541 3248135 := bstep (se 1 (by rfl) ⟨2436101, by rfl⟩ : syracuseStep 3248135 = 4872203) B4872203
theorem B23433227 : Blo 1443541 23433227 := bstep (se 1 (by rfl) ⟨17574920, by rfl⟩ : syracuseStep 23433227 = 35149841) B35149841
theorem B2969639 : Blo 1443541 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B1626151 : Blo 1443541 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B3248207 : Blo 1443541 3248207 := bstep (se 1 (by rfl) ⟨2436155, by rfl⟩ : syracuseStep 3248207 = 4872311) B4872311
theorem B2166863 : Blo 1443541 2166863 := bstep (se 1 (by rfl) ⟨1625147, by rfl⟩ : syracuseStep 2166863 = 3250295) B3250295
theorem B3657899 : Blo 1443541 3657899 := bstep (se 1 (by rfl) ⟨2743424, by rfl⟩ : syracuseStep 3657899 = 5486849) B5486849
theorem B2166983 : Blo 1443541 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B5484905 : Blo 1443541 5484905 := bstep (se 2 (by rfl) ⟨2056839, by rfl⟩ : syracuseStep 5484905 = 4113679) B4113679
theorem B2167145 : Blo 1443541 2167145 := bstep (se 2 (by rfl) ⟨812679, by rfl⟩ : syracuseStep 2167145 = 1625359) B1625359
theorem B2437519 : Blo 1443541 2437519 := bstep (se 1 (by rfl) ⟨1828139, by rfl⟩ : syracuseStep 2437519 = 3656279) B3656279
theorem B2167223 : Blo 1443541 2167223 := bstep (se 1 (by rfl) ⟨1625417, by rfl⟩ : syracuseStep 2167223 = 3250835) B3250835
theorem B3248603 : Blo 1443541 3248603 := bstep (se 1 (by rfl) ⟨2436452, by rfl⟩ : syracuseStep 3248603 = 4872905) B4872905
theorem B2167259 : Blo 1443541 2167259 := bstep (se 1 (by rfl) ⟨1625444, by rfl⟩ : syracuseStep 2167259 = 3250889) B3250889
theorem B4625095 : Blo 1443541 4625095 := bstep (se 1 (by rfl) ⟨3468821, by rfl⟩ : syracuseStep 4625095 = 6937643) B6937643
theorem B41677523 : Blo 1443541 41677523 := bstep (se 1 (by rfl) ⟨31258142, by rfl⟩ : syracuseStep 41677523 = 62516285) B62516285
theorem B79106867 : Blo 1443541 79106867 := bstep (se 1 (by rfl) ⟨59330150, by rfl⟩ : syracuseStep 79106867 = 118660301) B118660301
theorem B24695603 : Blo 1443541 24695603 := bstep (se 1 (by rfl) ⟨18521702, by rfl⟩ : syracuseStep 24695603 = 37043405) B37043405
theorem B4625225 : Blo 1443541 4625225 := bstep (se 2 (by rfl) ⟨1734459, by rfl⟩ : syracuseStep 4625225 = 3468919) B3468919
theorem B5485421 : Blo 1443541 5485421 := bstep (se 3 (by rfl) ⟨1028516, by rfl⟩ : syracuseStep 5485421 = 2057033) B2057033
theorem B3249071 : Blo 1443541 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B2167727 : Blo 1443541 2167727 := bstep (se 1 (by rfl) ⟨1625795, by rfl⟩ : syracuseStep 2167727 = 3251591) B3251591
theorem B3658679 : Blo 1443541 3658679 := bstep (se 1 (by rfl) ⟨2744009, by rfl⟩ : syracuseStep 3658679 = 5488019) B5488019
theorem B2929673 : Blo 1443541 2929673 := bstep (se 2 (by rfl) ⟨1098627, by rfl⟩ : syracuseStep 2929673 = 2197255) B2197255
theorem B2167817 : Blo 1443541 2167817 := bstep (se 2 (by rfl) ⟨812931, by rfl⟩ : syracuseStep 2167817 = 1625863) B1625863
theorem B2167847 : Blo 1443541 2167847 := bstep (se 1 (by rfl) ⟨1625885, by rfl⟩ : syracuseStep 2167847 = 3251771) B3251771
theorem B2438201 : Blo 1443541 2438201 := bstep (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) B1828651
theorem B2167931 : Blo 1443541 2167931 := bstep (se 1 (by rfl) ⟨1625948, by rfl⟩ : syracuseStep 2167931 = 3251897) B3251897
theorem B3249323 : Blo 1443541 3249323 := bstep (se 1 (by rfl) ⟨2436992, by rfl⟩ : syracuseStep 3249323 = 4873985) B4873985
theorem B2168057 : Blo 1443541 2168057 := bstep (se 2 (by rfl) ⟨813021, by rfl⟩ : syracuseStep 2168057 = 1626043) B1626043
theorem B2168159 : Blo 1443541 2168159 := bstep (se 1 (by rfl) ⟨1626119, by rfl⟩ : syracuseStep 2168159 = 3252239) B3252239
theorem B2168171 : Blo 1443541 2168171 := bstep (se 1 (by rfl) ⟨1626128, by rfl⟩ : syracuseStep 2168171 = 3252257) B3252257
theorem B3470735 : Blo 1443541 3470735 := bstep (se 1 (by rfl) ⟨2603051, by rfl⟩ : syracuseStep 3470735 = 5206103) B5206103
theorem B7312841 : Blo 1443541 7312841 := bstep (se 2 (by rfl) ⟨2742315, by rfl⟩ : syracuseStep 7312841 = 5484631) B5484631
theorem B15840731 : Blo 1443541 15840731 := bstep (se 1 (by rfl) ⟨11880548, by rfl⟩ : syracuseStep 15840731 = 23761097) B23761097
theorem B14816773 : Blo 1443541 14816773 := bstep (se 4 (by rfl) ⟨1389072, by rfl⟩ : syracuseStep 14816773 = 2778145) B2778145
theorem B5486089 : Blo 1443541 5486089 := bstep (se 2 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 5486089 = 4114567) B4114567
theorem B5559833 : Blo 1443541 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B10966589 : Blo 1443541 10966589 := bstep (se 3 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 10966589 = 4112471) B4112471
theorem B12342881 : Blo 1443541 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B6592097 : Blo 1443541 6592097 := bstep (se 2 (by rfl) ⟨2472036, by rfl⟩ : syracuseStep 6592097 = 4944073) B4944073
theorem B9877139 : Blo 1443541 9877139 := bstep (se 1 (by rfl) ⟨7407854, by rfl⟩ : syracuseStep 9877139 = 14815709) B14815709
theorem B35124929 : Blo 1443541 35124929 := bstep (se 2 (by rfl) ⟨13171848, by rfl⟩ : syracuseStep 35124929 = 26343697) B26343697
theorem B20821697 : Blo 1443541 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B3249863 : Blo 1443541 3249863 := bstep (se 1 (by rfl) ⟨2437397, by rfl⟩ : syracuseStep 3249863 = 4874795) B4874795
theorem B2438903 : Blo 1443541 2438903 := bstep (se 1 (by rfl) ⟨1829177, by rfl⟩ : syracuseStep 2438903 = 3658355) B3658355
theorem B8222573 : Blo 1443541 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B3086267 : Blo 1443541 3086267 := bstep (se 1 (by rfl) ⟨2314700, by rfl⟩ : syracuseStep 3086267 = 4629401) B4629401
theorem B3905615 : Blo 1443541 3905615 := bstep (se 1 (by rfl) ⟨2929211, by rfl⟩ : syracuseStep 3905615 = 5858423) B5858423
theorem B2439247 : Blo 1443541 2439247 := bstep (se 1 (by rfl) ⟨1829435, by rfl⟩ : syracuseStep 2439247 = 3658871) B3658871
theorem B7313489 : Blo 1443541 7313489 := bstep (se 2 (by rfl) ⟨2742558, by rfl⟩ : syracuseStep 7313489 = 5485117) B5485117
theorem B3086507 : Blo 1443541 3086507 := bstep (se 1 (by rfl) ⟨2314880, by rfl⟩ : syracuseStep 3086507 = 4629761) B4629761
theorem B15612209 : Blo 1443541 15612209 := bstep (se 2 (by rfl) ⟨5854578, by rfl⟩ : syracuseStep 15612209 = 11709157) B11709157
theorem B2742635 : Blo 1443541 2742635 := bstep (se 1 (by rfl) ⟨2056976, by rfl⟩ : syracuseStep 2742635 = 4113953) B4113953
theorem B18504071 : Blo 1443541 18504071 := bstep (se 1 (by rfl) ⟨13878053, by rfl⟩ : syracuseStep 18504071 = 27756107) B27756107
theorem B3471859 : Blo 1443541 3471859 := bstep (se 1 (by rfl) ⟨2603894, by rfl⟩ : syracuseStep 3471859 = 5207789) B5207789
theorem B10967561 : Blo 1443541 10967561 := bstep (se 2 (by rfl) ⟨4112835, by rfl⟩ : syracuseStep 10967561 = 8225671) B8225671
theorem B4872743 : Blo 1443541 4872743 := bstep (se 1 (by rfl) ⟨3654557, by rfl⟩ : syracuseStep 4872743 = 7309115) B7309115
theorem B3250727 : Blo 1443541 3250727 := bstep (se 1 (by rfl) ⟨2438045, by rfl⟩ : syracuseStep 3250727 = 4876091) B4876091
theorem B1735291 : Blo 1443541 1735291 := bstep (se 1 (by rfl) ⟨1301468, by rfl⟩ : syracuseStep 1735291 = 2602937) B2602937
theorem B3906187 : Blo 1443541 3906187 := bstep (se 1 (by rfl) ⟨2929640, by rfl⟩ : syracuseStep 3906187 = 5859281) B5859281
theorem B4872851 : Blo 1443541 4872851 := bstep (se 1 (by rfl) ⟨3654638, by rfl⟩ : syracuseStep 4872851 = 7309277) B7309277
theorem B4111037 : Blo 1443541 4111037 := bstep (se 3 (by rfl) ⟨770819, by rfl⟩ : syracuseStep 4111037 = 1541639) B1541639
theorem B1465031 : Blo 1443541 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B4873067 : Blo 1443541 4873067 := bstep (se 1 (by rfl) ⟨3654800, by rfl⟩ : syracuseStep 4873067 = 7309601) B7309601
theorem B3251051 : Blo 1443541 3251051 := bstep (se 1 (by rfl) ⟨2438288, by rfl⟩ : syracuseStep 3251051 = 4876577) B4876577
theorem B4873121 : Blo 1443541 4873121 := bstep (se 2 (by rfl) ⟨1827420, by rfl⟩ : syracuseStep 4873121 = 3654841) B3654841
theorem B3251105 : Blo 1443541 3251105 := bstep (se 2 (by rfl) ⟨1219164, by rfl⟩ : syracuseStep 3251105 = 2438329) B2438329
theorem B5487547 : Blo 1443541 5487547 := bstep (se 1 (by rfl) ⟨4115660, by rfl⟩ : syracuseStep 5487547 = 8231321) B8231321
theorem B2743303 : Blo 1443541 2743303 := bstep (se 1 (by rfl) ⟨2057477, by rfl⟩ : syracuseStep 2743303 = 4114955) B4114955
theorem B10550321 : Blo 1443541 10550321 := bstep (se 2 (by rfl) ⟨3956370, by rfl⟩ : syracuseStep 10550321 = 7912741) B7912741
theorem B6945871 : Blo 1443541 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B9886967 : Blo 1443541 9886967 := bstep (se 1 (by rfl) ⟨7415225, by rfl⟩ : syracuseStep 9886967 = 14830451) B14830451
theorem B3251447 : Blo 1443541 3251447 := bstep (se 1 (by rfl) ⟨2438585, by rfl⟩ : syracuseStep 3251447 = 4877171) B4877171
theorem B31227353 : Blo 1443541 31227353 := bstep (se 2 (by rfl) ⟨11710257, by rfl⟩ : syracuseStep 31227353 = 23420515) B23420515
theorem B7806451 : Blo 1443541 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B4873715 : Blo 1443541 4873715 := bstep (se 1 (by rfl) ⟨3655286, by rfl⟩ : syracuseStep 4873715 = 7310573) B7310573
theorem B4627955 : Blo 1443541 4627955 := bstep (se 1 (by rfl) ⟨3470966, by rfl⟩ : syracuseStep 4627955 = 6941933) B6941933
theorem B2743865 : Blo 1443541 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B5488337 : Blo 1443541 5488337 := bstep (se 2 (by rfl) ⟨2058126, by rfl⟩ : syracuseStep 5488337 = 4116253) B4116253
theorem B9879329 : Blo 1443541 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B3252041 : Blo 1443541 3252041 := bstep (se 2 (by rfl) ⟨1219515, by rfl⟩ : syracuseStep 3252041 = 2439031) B2439031
theorem B10969019 : Blo 1443541 10969019 := bstep (se 1 (by rfl) ⟨8226764, by rfl⟩ : syracuseStep 10969019 = 16453529) B16453529
theorem B15622151 : Blo 1443541 15622151 := bstep (se 1 (by rfl) ⟨11716613, by rfl⟩ : syracuseStep 15622151 = 23433227) B23433227
theorem B3252329 : Blo 1443541 3252329 := bstep (se 2 (by rfl) ⟨1219623, by rfl⟩ : syracuseStep 3252329 = 2439247) B2439247
theorem B12345857 : Blo 1443541 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B4629145 : Blo 1443541 4629145 := bstep (se 2 (by rfl) ⟨1735929, by rfl⟩ : syracuseStep 4629145 = 3471859) B3471859
theorem B20832997 : Blo 1443541 20832997 := bstep (se 4 (by rfl) ⟨1953093, by rfl⟩ : syracuseStep 20832997 = 3906187) B3906187
theorem B2196379 : Blo 1443541 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B4875227 : Blo 1443541 4875227 := bstep (se 1 (by rfl) ⟨3656420, by rfl⟩ : syracuseStep 4875227 = 7312841) B7312841
theorem B4875389 : Blo 1443541 4875389 := bstep (se 3 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 4875389 = 1828271) B1828271
theorem B4875497 : Blo 1443541 4875497 := bstep (se 2 (by rfl) ⟨1828311, by rfl⟩ : syracuseStep 4875497 = 3656623) B3656623
theorem B5481715 : Blo 1443541 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B7316729 : Blo 1443541 7316729 := bstep (se 2 (by rfl) ⟨2743773, by rfl⟩ : syracuseStep 7316729 = 5487547) B5487547
theorem B112543019 : Blo 1443541 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B10970477 : Blo 1443541 10970477 := bstep (se 3 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 10970477 = 4113929) B4113929
theorem B4875659 : Blo 1443541 4875659 := bstep (se 1 (by rfl) ⟨3656744, by rfl⟩ : syracuseStep 4875659 = 7313489) B7313489
theorem B2057671 : Blo 1443541 2057671 := bstep (se 1 (by rfl) ⟨1543253, by rfl⟩ : syracuseStep 2057671 = 3086507) B3086507
theorem B2778617 : Blo 1443541 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B1828423 : Blo 1443541 1828423 := bstep (se 1 (by rfl) ⟨1371317, by rfl⟩ : syracuseStep 1828423 = 2742635) B2742635
theorem B1443551 : Blo 1443541 1443551 := bstep (se 1 (by rfl) ⟨1082663, by rfl⟩ : syracuseStep 1443551 = 2165327) B2165327
theorem B42796835 : Blo 1443541 42796835 := bstep (se 1 (by rfl) ⟨32097626, by rfl⟩ : syracuseStep 42796835 = 64195253) B64195253
theorem B1443631 : Blo 1443541 1443631 := bstep (se 1 (by rfl) ⟨1082723, by rfl⟩ : syracuseStep 1443631 = 2165447) B2165447
theorem B1443739 : Blo 1443541 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B1443791 : Blo 1443541 1443791 := bstep (se 1 (by rfl) ⟨1082843, by rfl⟩ : syracuseStep 1443791 = 2165687) B2165687
theorem B3655631 : Blo 1443541 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B1443815 : Blo 1443541 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B23431153 : Blo 1443541 23431153 := bstep (se 2 (by rfl) ⟨8786682, by rfl⟩ : syracuseStep 23431153 = 17573365) B17573365
theorem B1624351 : Blo 1443541 1624351 := bstep (se 1 (by rfl) ⟨1218263, by rfl⟩ : syracuseStep 1624351 = 2436527) B2436527
theorem B1444127 : Blo 1443541 1444127 := bstep (se 1 (by rfl) ⟨1083095, by rfl⟩ : syracuseStep 1444127 = 2166191) B2166191
theorem B20818235 : Blo 1443541 20818235 := bstep (se 1 (by rfl) ⟨15613676, by rfl⟩ : syracuseStep 20818235 = 31227353) B31227353
theorem B1444187 : Blo 1443541 1444187 := bstep (se 1 (by rfl) ⟨1083140, by rfl⟩ : syracuseStep 1444187 = 2166281) B2166281
theorem B1444207 : Blo 1443541 1444207 := bstep (se 1 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 1444207 = 2166311) B2166311
theorem B1829243 : Blo 1443541 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B7407997 : Blo 1443541 7407997 := bstep (se 3 (by rfl) ⟨1388999, by rfl⟩ : syracuseStep 7407997 = 2777999) B2777999
theorem B1444263 : Blo 1443541 1444263 := bstep (se 1 (by rfl) ⟨1083197, by rfl⟩ : syracuseStep 1444263 = 2166395) B2166395
theorem B2968019 : Blo 1443541 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B1444347 : Blo 1443541 1444347 := bstep (se 1 (by rfl) ⟨1083260, by rfl⟩ : syracuseStep 1444347 = 2166521) B2166521
theorem B3902015 : Blo 1443541 3902015 := bstep (se 1 (by rfl) ⟨2926511, by rfl⟩ : syracuseStep 3902015 = 5853023) B5853023
theorem B1624639 : Blo 1443541 1624639 := bstep (se 1 (by rfl) ⟨1218479, by rfl⟩ : syracuseStep 1624639 = 2436959) B2436959
theorem B1444415 : Blo 1443541 1444415 := bstep (se 1 (by rfl) ⟨1083311, by rfl⟩ : syracuseStep 1444415 = 2166623) B2166623
theorem B1444423 : Blo 1443541 1444423 := bstep (se 1 (by rfl) ⟨1083317, by rfl⟩ : syracuseStep 1444423 = 2166635) B2166635
theorem B3656299 : Blo 1443541 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B2165369 : Blo 1443541 2165369 := bstep (se 2 (by rfl) ⟨812013, by rfl⟩ : syracuseStep 2165369 = 1624027) B1624027
theorem B2165423 : Blo 1443541 2165423 := bstep (se 1 (by rfl) ⟨1624067, by rfl⟩ : syracuseStep 2165423 = 3248135) B3248135
theorem B79022789 : Blo 1443541 79022789 := bstep (se 4 (by rfl) ⟨7408386, by rfl⟩ : syracuseStep 79022789 = 14816773) B14816773
theorem B2165471 : Blo 1443541 2165471 := bstep (se 1 (by rfl) ⟨1624103, by rfl⟩ : syracuseStep 2165471 = 3248207) B3248207
theorem B1444575 : Blo 1443541 1444575 := bstep (se 1 (by rfl) ⟨1083431, by rfl⟩ : syracuseStep 1444575 = 2166863) B2166863
theorem B1444655 : Blo 1443541 1444655 := bstep (se 1 (by rfl) ⟨1083491, by rfl⟩ : syracuseStep 1444655 = 2166983) B2166983
theorem B10414973 : Blo 1443541 10414973 := bstep (se 3 (by rfl) ⟨1952807, by rfl⟩ : syracuseStep 10414973 = 3905615) B3905615
theorem B3656603 : Blo 1443541 3656603 := bstep (se 1 (by rfl) ⟨2742452, by rfl⟩ : syracuseStep 3656603 = 5484905) B5484905
theorem B1444763 : Blo 1443541 1444763 := bstep (se 1 (by rfl) ⟨1083572, by rfl⟩ : syracuseStep 1444763 = 2167145) B2167145
theorem B1444815 : Blo 1443541 1444815 := bstep (se 1 (by rfl) ⟨1083611, by rfl⟩ : syracuseStep 1444815 = 2167223) B2167223
theorem B2165735 : Blo 1443541 2165735 := bstep (se 1 (by rfl) ⟨1624301, by rfl⟩ : syracuseStep 2165735 = 3248603) B3248603
theorem B1444839 : Blo 1443541 1444839 := bstep (se 1 (by rfl) ⟨1083629, by rfl⟩ : syracuseStep 1444839 = 2167259) B2167259
theorem B5483659 : Blo 1443541 5483659 := bstep (se 1 (by rfl) ⟨4112744, by rfl⟩ : syracuseStep 5483659 = 8225489) B8225489
theorem B5205181 : Blo 1443541 5205181 := bstep (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) B1951943
theorem B26709193 : Blo 1443541 26709193 := bstep (se 2 (by rfl) ⟨10015947, by rfl⟩ : syracuseStep 26709193 = 20031895) B20031895
theorem B18517193 : Blo 1443541 18517193 := bstep (se 2 (by rfl) ⟨6943947, by rfl⟩ : syracuseStep 18517193 = 13887895) B13887895
theorem B3083483 : Blo 1443541 3083483 := bstep (se 1 (by rfl) ⟨2312612, by rfl⟩ : syracuseStep 3083483 = 4625225) B4625225
theorem B8907995 : Blo 1443541 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B2165993 : Blo 1443541 2165993 := bstep (se 2 (by rfl) ⟨812247, by rfl⟩ : syracuseStep 2165993 = 1624495) B1624495
theorem B3656947 : Blo 1443541 3656947 := bstep (se 1 (by rfl) ⟨2742710, by rfl⟩ : syracuseStep 3656947 = 5485421) B5485421
theorem B2166047 : Blo 1443541 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B1445151 : Blo 1443541 1445151 := bstep (se 1 (by rfl) ⟨1083863, by rfl⟩ : syracuseStep 1445151 = 2167727) B2167727
theorem B1953115 : Blo 1443541 1953115 := bstep (se 1 (by rfl) ⟨1464836, by rfl⟩ : syracuseStep 1953115 = 2929673) B2929673
theorem B1445211 : Blo 1443541 1445211 := bstep (se 1 (by rfl) ⟨1083908, by rfl⟩ : syracuseStep 1445211 = 2167817) B2167817
theorem B1445231 : Blo 1443541 1445231 := bstep (se 1 (by rfl) ⟨1083923, by rfl⟩ : syracuseStep 1445231 = 2167847) B2167847
theorem B1625467 : Blo 1443541 1625467 := bstep (se 1 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 1625467 = 2438201) B2438201
theorem B1445287 : Blo 1443541 1445287 := bstep (se 1 (by rfl) ⟨1083965, by rfl⟩ : syracuseStep 1445287 = 2167931) B2167931
theorem B5483963 : Blo 1443541 5483963 := bstep (se 1 (by rfl) ⟨4112972, by rfl⟩ : syracuseStep 5483963 = 8225945) B8225945
theorem B2166215 : Blo 1443541 2166215 := bstep (se 1 (by rfl) ⟨1624661, by rfl⟩ : syracuseStep 2166215 = 3249323) B3249323
theorem B2436601 : Blo 1443541 2436601 := bstep (se 2 (by rfl) ⟨913725, by rfl⟩ : syracuseStep 2436601 = 1827451) B1827451
theorem B2313721 : Blo 1443541 2313721 := bstep (se 2 (by rfl) ⟨867645, by rfl⟩ : syracuseStep 2313721 = 1735291) B1735291
theorem B1445371 : Blo 1443541 1445371 := bstep (se 1 (by rfl) ⟨1084028, by rfl⟩ : syracuseStep 1445371 = 2168057) B2168057
theorem B1445439 : Blo 1443541 1445439 := bstep (se 1 (by rfl) ⟨1084079, by rfl⟩ : syracuseStep 1445439 = 2168159) B2168159
theorem B1445447 : Blo 1443541 1445447 := bstep (se 1 (by rfl) ⟨1084085, by rfl⟩ : syracuseStep 1445447 = 2168171) B2168171
theorem B3706555 : Blo 1443541 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B7311059 : Blo 1443541 7311059 := bstep (se 1 (by rfl) ⟨5483294, by rfl⟩ : syracuseStep 7311059 = 10966589) B10966589
theorem B8228587 : Blo 1443541 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B10972907 : Blo 1443541 10972907 := bstep (se 1 (by rfl) ⟨8229680, by rfl⟩ : syracuseStep 10972907 = 16459361) B16459361
theorem B4394731 : Blo 1443541 4394731 := bstep (se 1 (by rfl) ⟨3296048, by rfl⟩ : syracuseStep 4394731 = 6592097) B6592097
theorem B2436871 : Blo 1443541 2436871 := bstep (se 1 (by rfl) ⟨1827653, by rfl⟩ : syracuseStep 2436871 = 3655307) B3655307
theorem B2436905 : Blo 1443541 2436905 := bstep (se 2 (by rfl) ⟨913839, by rfl⟩ : syracuseStep 2436905 = 1827679) B1827679
theorem B2166569 : Blo 1443541 2166569 := bstep (se 2 (by rfl) ⟨812463, by rfl⟩ : syracuseStep 2166569 = 1624927) B1624927
theorem B23416619 : Blo 1443541 23416619 := bstep (se 1 (by rfl) ⟨17562464, by rfl⟩ : syracuseStep 23416619 = 35124929) B35124929
theorem B13881131 : Blo 1443541 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B2166575 : Blo 1443541 2166575 := bstep (se 1 (by rfl) ⟨1624931, by rfl⟩ : syracuseStep 2166575 = 3249863) B3249863
theorem B4943663 : Blo 1443541 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B1625935 : Blo 1443541 1625935 := bstep (se 1 (by rfl) ⟨1219451, by rfl⟩ : syracuseStep 1625935 = 2438903) B2438903
theorem B42241949 : Blo 1443541 42241949 := bstep (se 3 (by rfl) ⟨7920365, by rfl⟩ : syracuseStep 42241949 = 15840731) B15840731
theorem B3657737 : Blo 1443541 3657737 := bstep (se 2 (by rfl) ⟨1371651, by rfl⟩ : syracuseStep 3657737 = 2743303) B2743303
theorem B9261161 : Blo 1443541 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B10408139 : Blo 1443541 10408139 := bstep (se 1 (by rfl) ⟨7806104, by rfl⟩ : syracuseStep 10408139 = 15612209) B15612209
theorem B2167049 : Blo 1443541 2167049 := bstep (se 2 (by rfl) ⟨812643, by rfl⟩ : syracuseStep 2167049 = 1625287) B1625287
theorem B7311707 : Blo 1443541 7311707 := bstep (se 1 (by rfl) ⟨5483780, by rfl⟩ : syracuseStep 7311707 = 10967561) B10967561
theorem B4878683 : Blo 1443541 4878683 := bstep (se 1 (by rfl) ⟨3659012, by rfl⟩ : syracuseStep 4878683 = 7318025) B7318025
theorem B3248495 : Blo 1443541 3248495 := bstep (se 1 (by rfl) ⟨2436371, by rfl⟩ : syracuseStep 3248495 = 4872743) B4872743
theorem B2167151 : Blo 1443541 2167151 := bstep (se 1 (by rfl) ⟨1625363, by rfl⟩ : syracuseStep 2167151 = 3250727) B3250727
theorem B3248567 : Blo 1443541 3248567 := bstep (se 1 (by rfl) ⟨2436425, by rfl⟩ : syracuseStep 3248567 = 4872851) B4872851
theorem B2740691 : Blo 1443541 2740691 := bstep (se 1 (by rfl) ⟨2055518, by rfl⟩ : syracuseStep 2740691 = 4111037) B4111037
theorem B2437627 : Blo 1443541 2437627 := bstep (se 1 (by rfl) ⟨1828220, by rfl⟩ : syracuseStep 2437627 = 3656441) B3656441
theorem B3248711 : Blo 1443541 3248711 := bstep (se 1 (by rfl) ⟨2436533, by rfl⟩ : syracuseStep 3248711 = 4873067) B4873067
theorem B2167367 : Blo 1443541 2167367 := bstep (se 1 (by rfl) ⟨1625525, by rfl⟩ : syracuseStep 2167367 = 3251051) B3251051
theorem B3248747 : Blo 1443541 3248747 := bstep (se 1 (by rfl) ⟨2436560, by rfl⟩ : syracuseStep 3248747 = 4873121) B4873121
theorem B2167403 : Blo 1443541 2167403 := bstep (se 1 (by rfl) ⟨1625552, by rfl⟩ : syracuseStep 2167403 = 3251105) B3251105
theorem B10408601 : Blo 1443541 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B7033547 : Blo 1443541 7033547 := bstep (se 1 (by rfl) ⟨5275160, by rfl⟩ : syracuseStep 7033547 = 10550321) B10550321
theorem B5485391 : Blo 1443541 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B6591311 : Blo 1443541 6591311 := bstep (se 1 (by rfl) ⟨4943483, by rfl⟩ : syracuseStep 6591311 = 9886967) B9886967
theorem B2167631 : Blo 1443541 2167631 := bstep (se 1 (by rfl) ⟨1625723, by rfl⟩ : syracuseStep 2167631 = 3251447) B3251447
theorem B2438059 : Blo 1443541 2438059 := bstep (se 1 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 2438059 = 3657089) B3657089
theorem B3249143 : Blo 1443541 3249143 := bstep (se 1 (by rfl) ⟨2436857, by rfl⟩ : syracuseStep 3249143 = 4873715) B4873715
theorem B3085303 : Blo 1443541 3085303 := bstep (se 1 (by rfl) ⟨2313977, by rfl⟩ : syracuseStep 3085303 = 4627955) B4627955
theorem B3658891 : Blo 1443541 3658891 := bstep (se 1 (by rfl) ⟨2744168, by rfl⟩ : syracuseStep 3658891 = 5488337) B5488337
theorem B8230045 : Blo 1443541 8230045 := bstep (se 3 (by rfl) ⟨1543133, by rfl⟩ : syracuseStep 8230045 = 3086267) B3086267
theorem B10974365 : Blo 1443541 10974365 := bstep (se 3 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 10974365 = 4115387) B4115387
theorem B2438363 : Blo 1443541 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B2168027 : Blo 1443541 2168027 := bstep (se 1 (by rfl) ⟨1626020, by rfl⟩ : syracuseStep 2168027 = 3252041) B3252041
theorem B7312679 : Blo 1443541 7312679 := bstep (se 1 (by rfl) ⟨5484509, by rfl⟩ : syracuseStep 7312679 = 10969019) B10969019
theorem B3249503 : Blo 1443541 3249503 := bstep (se 1 (by rfl) ⟨2437127, by rfl⟩ : syracuseStep 3249503 = 4874255) B4874255
theorem B1979759 : Blo 1443541 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B2168201 : Blo 1443541 2168201 := bstep (se 2 (by rfl) ⟨813075, by rfl⟩ : syracuseStep 2168201 = 1626151) B1626151
theorem B2438599 : Blo 1443541 2438599 := bstep (se 1 (by rfl) ⟨1828949, by rfl⟩ : syracuseStep 2438599 = 3657899) B3657899
theorem B2741921 : Blo 1443541 2741921 := bstep (se 2 (by rfl) ⟨1028220, by rfl⟩ : syracuseStep 2741921 = 2056441) B2056441
theorem B3249899 : Blo 1443541 3249899 := bstep (se 1 (by rfl) ⟨2437424, by rfl⟩ : syracuseStep 3249899 = 4874849) B4874849
theorem B27785015 : Blo 1443541 27785015 := bstep (se 1 (by rfl) ⟨20838761, by rfl⟩ : syracuseStep 27785015 = 41677523) B41677523
theorem B4872041 : Blo 1443541 4872041 := bstep (se 2 (by rfl) ⟨1827015, by rfl⟩ : syracuseStep 4872041 = 3654031) B3654031
theorem B3250025 : Blo 1443541 3250025 := bstep (se 2 (by rfl) ⟨1218759, by rfl⟩ : syracuseStep 3250025 = 2437519) B2437519
theorem B6174569 : Blo 1443541 6174569 := bstep (se 2 (by rfl) ⟨2315463, by rfl⟩ : syracuseStep 6174569 = 4630927) B4630927
theorem B52737911 : Blo 1443541 52737911 := bstep (se 1 (by rfl) ⟨39553433, by rfl⟩ : syracuseStep 52737911 = 79106867) B79106867
theorem B16463735 : Blo 1443541 16463735 := bstep (se 1 (by rfl) ⟨12347801, by rfl⟩ : syracuseStep 16463735 = 24695603) B24695603
theorem B2439119 : Blo 1443541 2439119 := bstep (se 1 (by rfl) ⟨1829339, by rfl⟩ : syracuseStep 2439119 = 3658679) B3658679
theorem B6166793 : Blo 1443541 6166793 := bstep (se 2 (by rfl) ⟨2312547, by rfl⟩ : syracuseStep 6166793 = 4625095) B4625095
theorem B4872473 : Blo 1443541 4872473 := bstep (se 2 (by rfl) ⟨1827177, by rfl⟩ : syracuseStep 4872473 = 3654355) B3654355
theorem B9255293 : Blo 1443541 9255293 := bstep (se 3 (by rfl) ⟨1735367, by rfl⟩ : syracuseStep 9255293 = 3470735) B3470735
theorem B6584759 : Blo 1443541 6584759 := bstep (se 1 (by rfl) ⟨4938569, by rfl⟩ : syracuseStep 6584759 = 9877139) B9877139
theorem B3087019 : Blo 1443541 3087019 := bstep (se 1 (by rfl) ⟨2315264, by rfl⟩ : syracuseStep 3087019 = 4630529) B4630529
theorem B3250871 : Blo 1443541 3250871 := bstep (se 1 (by rfl) ⟨2438153, by rfl⟩ : syracuseStep 3250871 = 4876307) B4876307
theorem B3251087 : Blo 1443541 3251087 := bstep (se 1 (by rfl) ⟨2438315, by rfl⟩ : syracuseStep 3251087 = 4876631) B4876631
theorem B12336047 : Blo 1443541 12336047 := bstep (se 1 (by rfl) ⟨9252035, by rfl⟩ : syracuseStep 12336047 = 18504071) B18504071
theorem B3906749 : Blo 1443541 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B6167819 : Blo 1443541 6167819 := bstep (se 1 (by rfl) ⟨4625864, by rfl⟩ : syracuseStep 6167819 = 9251729) B9251729
theorem B7314785 : Blo 1443541 7314785 := bstep (se 2 (by rfl) ⟨2743044, by rfl⟩ : syracuseStep 7314785 = 5486089) B5486089
theorem B2055547 : Blo 1443541 2055547 := bstep (se 1 (by rfl) ⟨1541660, by rfl⟩ : syracuseStep 2055547 = 3083321) B3083321
theorem B26353039 : Blo 1443541 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B2055775 : Blo 1443541 2055775 := bstep (se 1 (by rfl) ⟨1541831, by rfl⟩ : syracuseStep 2055775 = 3083663) B3083663
theorem B4873823 : Blo 1443541 4873823 := bstep (se 1 (by rfl) ⟨3655367, by rfl⟩ : syracuseStep 4873823 = 7310735) B7310735
theorem B3251807 : Blo 1443541 3251807 := bstep (se 1 (by rfl) ⟨2438855, by rfl⟩ : syracuseStep 3251807 = 4877711) B4877711
theorem B3252023 : Blo 1443541 3252023 := bstep (se 1 (by rfl) ⟨2439017, by rfl⟩ : syracuseStep 3252023 = 4878035) B4878035
theorem B15621983 : Blo 1443541 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B6586219 : Blo 1443541 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B6938759 : Blo 1443541 6938759 := bstep (se 1 (by rfl) ⟨5204069, by rfl⟩ : syracuseStep 6938759 = 10408139) B10408139
theorem B4874471 : Blo 1443541 4874471 := bstep (se 1 (by rfl) ⟨3655853, by rfl⟩ : syracuseStep 4874471 = 7311707) B7311707
theorem B3252455 : Blo 1443541 3252455 := bstep (se 1 (by rfl) ⟨2439341, by rfl⟩ : syracuseStep 3252455 = 4878683) B4878683
theorem B1827127 : Blo 1443541 1827127 := bstep (se 1 (by rfl) ⟨1370345, by rfl⟩ : syracuseStep 1827127 = 2740691) B2740691
theorem B6939067 : Blo 1443541 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B7316243 : Blo 1443541 7316243 := bstep (se 1 (by rfl) ⟨5487182, by rfl⟩ : syracuseStep 7316243 = 10974365) B10974365
theorem B4875065 : Blo 1443541 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B4875119 : Blo 1443541 4875119 := bstep (se 1 (by rfl) ⟨3656339, by rfl⟩ : syracuseStep 4875119 = 7312679) B7312679
theorem B1852411 : Blo 1443541 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B1827947 : Blo 1443541 1827947 := bstep (se 1 (by rfl) ⟨1370960, by rfl⟩ : syracuseStep 1827947 = 2741921) B2741921
theorem B18523343 : Blo 1443541 18523343 := bstep (se 1 (by rfl) ⟨13892507, by rfl⟩ : syracuseStep 18523343 = 27785015) B27785015
theorem B4113737 : Blo 1443541 4113737 := bstep (se 2 (by rfl) ⟨1542651, by rfl⟩ : syracuseStep 4113737 = 3085303) B3085303
theorem B13878823 : Blo 1443541 13878823 := bstep (se 1 (by rfl) ⟨10409117, by rfl⟩ : syracuseStep 13878823 = 20818235) B20818235
theorem B6940241 : Blo 1443541 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B6170195 : Blo 1443541 6170195 := bstep (se 1 (by rfl) ⟨4627646, by rfl⟩ : syracuseStep 6170195 = 9255293) B9255293
theorem B35612257 : Blo 1443541 35612257 := bstep (se 2 (by rfl) ⟨13354596, by rfl⟩ : syracuseStep 35612257 = 26709193) B26709193
theorem B7308953 : Blo 1443541 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B4875929 : Blo 1443541 4875929 := bstep (se 2 (by rfl) ⟨1828473, by rfl⟩ : syracuseStep 4875929 = 3656947) B3656947
theorem B1443579 : Blo 1443541 1443579 := bstep (se 1 (by rfl) ⟨1082684, by rfl⟩ : syracuseStep 1443579 = 2165369) B2165369
theorem B1443615 : Blo 1443541 1443615 := bstep (se 1 (by rfl) ⟨1082711, by rfl⟩ : syracuseStep 1443615 = 2165423) B2165423
theorem B1443647 : Blo 1443541 1443647 := bstep (se 1 (by rfl) ⟨1082735, by rfl⟩ : syracuseStep 1443647 = 2165471) B2165471
theorem B35137385 : Blo 1443541 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B1443823 : Blo 1443541 1443823 := bstep (se 1 (by rfl) ⟨1082867, by rfl⟩ : syracuseStep 1443823 = 2165735) B2165735
theorem B1443995 : Blo 1443541 1443995 := bstep (se 1 (by rfl) ⟨1082996, by rfl⟩ : syracuseStep 1443995 = 2165993) B2165993
theorem B1444031 : Blo 1443541 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B4876523 : Blo 1443541 4876523 := bstep (se 1 (by rfl) ⟨3657392, by rfl⟩ : syracuseStep 4876523 = 7314785) B7314785
theorem B4942073 : Blo 1443541 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3655975 : Blo 1443541 3655975 := bstep (se 1 (by rfl) ⟨2741981, by rfl⟩ : syracuseStep 3655975 = 5483963) B5483963
theorem B1444143 : Blo 1443541 1444143 := bstep (se 1 (by rfl) ⟨1083107, by rfl⟩ : syracuseStep 1444143 = 2166215) B2166215
theorem B10971449 : Blo 1443541 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B5859641 : Blo 1443541 5859641 := bstep (se 2 (by rfl) ⟨2197365, by rfl⟩ : syracuseStep 5859641 = 4394731) B4394731
theorem B1624603 : Blo 1443541 1624603 := bstep (se 1 (by rfl) ⟨1218452, by rfl⟩ : syracuseStep 1624603 = 2436905) B2436905
theorem B1444379 : Blo 1443541 1444379 := bstep (se 1 (by rfl) ⟨1083284, by rfl⟩ : syracuseStep 1444379 = 2166569) B2166569
theorem B1444383 : Blo 1443541 1444383 := bstep (se 1 (by rfl) ⟨1083287, by rfl⟩ : syracuseStep 1444383 = 2166575) B2166575
theorem B3295775 : Blo 1443541 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B10414655 : Blo 1443541 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B41659069 : Blo 1443541 41659069 := bstep (se 3 (by rfl) ⟨7811075, by rfl⟩ : syracuseStep 41659069 = 15622151) B15622151
theorem B1444699 : Blo 1443541 1444699 := bstep (se 1 (by rfl) ⟨1083524, by rfl⟩ : syracuseStep 1444699 = 2167049) B2167049
theorem B2165663 : Blo 1443541 2165663 := bstep (se 1 (by rfl) ⟨1624247, by rfl⟩ : syracuseStep 2165663 = 3248495) B3248495
theorem B1444767 : Blo 1443541 1444767 := bstep (se 1 (by rfl) ⟨1083575, by rfl⟩ : syracuseStep 1444767 = 2167151) B2167151
theorem B2165711 : Blo 1443541 2165711 := bstep (se 1 (by rfl) ⟨1624283, by rfl⟩ : syracuseStep 2165711 = 3248567) B3248567
theorem B2165801 : Blo 1443541 2165801 := bstep (se 2 (by rfl) ⟨812175, by rfl⟩ : syracuseStep 2165801 = 1624351) B1624351
theorem B2165807 : Blo 1443541 2165807 := bstep (se 1 (by rfl) ⟨1624355, by rfl⟩ : syracuseStep 2165807 = 3248711) B3248711
theorem B1444911 : Blo 1443541 1444911 := bstep (se 1 (by rfl) ⟨1083683, by rfl⟩ : syracuseStep 1444911 = 2167367) B2167367
theorem B2165831 : Blo 1443541 2165831 := bstep (se 1 (by rfl) ⟨1624373, by rfl⟩ : syracuseStep 2165831 = 3248747) B3248747
theorem B1444935 : Blo 1443541 1444935 := bstep (se 1 (by rfl) ⟨1083701, by rfl⟩ : syracuseStep 1444935 = 2167403) B2167403
theorem B4689031 : Blo 1443541 4689031 := bstep (se 1 (by rfl) ⟨3516773, by rfl⟩ : syracuseStep 4689031 = 7033547) B7033547
theorem B3656927 : Blo 1443541 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B4394207 : Blo 1443541 4394207 := bstep (se 1 (by rfl) ⟨3295655, by rfl⟩ : syracuseStep 4394207 = 6591311) B6591311
theorem B1445087 : Blo 1443541 1445087 := bstep (se 1 (by rfl) ⟨1083815, by rfl⟩ : syracuseStep 1445087 = 2167631) B2167631
theorem B2166095 : Blo 1443541 2166095 := bstep (se 1 (by rfl) ⟨1624571, by rfl⟩ : syracuseStep 2166095 = 3249143) B3249143
theorem B16444781 : Blo 1443541 16444781 := bstep (se 3 (by rfl) ⟨3083396, by rfl⟩ : syracuseStep 16444781 = 6166793) B6166793
theorem B2166185 : Blo 1443541 2166185 := bstep (se 2 (by rfl) ⟨812319, by rfl⟩ : syracuseStep 2166185 = 1624639) B1624639
theorem B1625575 : Blo 1443541 1625575 := bstep (se 1 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 1625575 = 2438363) B2438363
theorem B1445351 : Blo 1443541 1445351 := bstep (se 1 (by rfl) ⟨1084013, by rfl⟩ : syracuseStep 1445351 = 2168027) B2168027
theorem B4877819 : Blo 1443541 4877819 := bstep (se 1 (by rfl) ⟨3658364, by rfl⟩ : syracuseStep 4877819 = 7316729) B7316729
theorem B6172193 : Blo 1443541 6172193 := bstep (se 2 (by rfl) ⟨2314572, by rfl⟩ : syracuseStep 6172193 = 4629145) B4629145
theorem B4116025 : Blo 1443541 4116025 := bstep (se 2 (by rfl) ⟨1543509, by rfl⟩ : syracuseStep 4116025 = 3087019) B3087019
theorem B2166335 : Blo 1443541 2166335 := bstep (se 1 (by rfl) ⟨1624751, by rfl⟩ : syracuseStep 2166335 = 3249503) B3249503
theorem B1445467 : Blo 1443541 1445467 := bstep (se 1 (by rfl) ⟨1084100, by rfl⟩ : syracuseStep 1445467 = 2168201) B2168201
theorem B5279357 : Blo 1443541 5279357 := bstep (se 3 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 5279357 = 1979759) B1979759
theorem B4877981 : Blo 1443541 4877981 := bstep (se 3 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 4877981 = 1829243) B1829243
theorem B2166599 : Blo 1443541 2166599 := bstep (se 1 (by rfl) ⟨1624949, by rfl⟩ : syracuseStep 2166599 = 3249899) B3249899
theorem B3248027 : Blo 1443541 3248027 := bstep (se 1 (by rfl) ⟨2436020, by rfl⟩ : syracuseStep 3248027 = 4872041) B4872041
theorem B2166683 : Blo 1443541 2166683 := bstep (se 1 (by rfl) ⟨1625012, by rfl⟩ : syracuseStep 2166683 = 3250025) B3250025
theorem B4116379 : Blo 1443541 4116379 := bstep (se 1 (by rfl) ⟨3087284, by rfl⟩ : syracuseStep 4116379 = 6174569) B6174569
theorem B2437087 : Blo 1443541 2437087 := bstep (se 1 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 2437087 = 3655631) B3655631
theorem B1626079 : Blo 1443541 1626079 := bstep (se 1 (by rfl) ⟨1219559, by rfl⟩ : syracuseStep 1626079 = 2439119) B2439119
theorem B7311545 : Blo 1443541 7311545 := bstep (se 2 (by rfl) ⟨2741829, by rfl⟩ : syracuseStep 7311545 = 5483659) B5483659
theorem B4878521 : Blo 1443541 4878521 := bstep (se 2 (by rfl) ⟨1829445, by rfl⟩ : syracuseStep 4878521 = 3658891) B3658891
theorem B3248315 : Blo 1443541 3248315 := bstep (se 1 (by rfl) ⟨2436236, by rfl⟩ : syracuseStep 3248315 = 4872473) B4872473
theorem B10973393 : Blo 1443541 10973393 := bstep (se 2 (by rfl) ⟨4115022, by rfl⟩ : syracuseStep 10973393 = 8230045) B8230045
theorem B1978679 : Blo 1443541 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B2601343 : Blo 1443541 2601343 := bstep (se 1 (by rfl) ⟨1951007, by rfl⟩ : syracuseStep 2601343 = 3902015) B3902015
theorem B2167247 : Blo 1443541 2167247 := bstep (se 1 (by rfl) ⟨1625435, by rfl⟩ : syracuseStep 2167247 = 3250871) B3250871
theorem B10416613 : Blo 1443541 10416613 := bstep (se 4 (by rfl) ⟨976557, by rfl⟩ : syracuseStep 10416613 = 1953115) B1953115
theorem B2740729 : Blo 1443541 2740729 := bstep (se 2 (by rfl) ⟨1027773, by rfl⟩ : syracuseStep 2740729 = 2055547) B2055547
theorem B2167289 : Blo 1443541 2167289 := bstep (se 2 (by rfl) ⟨812733, by rfl⟩ : syracuseStep 2167289 = 1625467) B1625467
theorem B6943315 : Blo 1443541 6943315 := bstep (se 1 (by rfl) ⟨5207486, by rfl⟩ : syracuseStep 6943315 = 10414973) B10414973
theorem B2167391 : Blo 1443541 2167391 := bstep (se 1 (by rfl) ⟨1625543, by rfl⟩ : syracuseStep 2167391 = 3251087) B3251087
theorem B2437735 : Blo 1443541 2437735 := bstep (se 1 (by rfl) ⟨1828301, by rfl⟩ : syracuseStep 2437735 = 3656603) B3656603
theorem B3248801 : Blo 1443541 3248801 := bstep (se 2 (by rfl) ⟨1218300, by rfl⟩ : syracuseStep 3248801 = 2436601) B2436601
theorem B3084961 : Blo 1443541 3084961 := bstep (se 2 (by rfl) ⟨1156860, by rfl⟩ : syracuseStep 3084961 = 2313721) B2313721
theorem B2437897 : Blo 1443541 2437897 := bstep (se 2 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 2437897 = 1828423) B1828423
theorem B62444317 : Blo 1443541 62444317 := bstep (se 3 (by rfl) ⟨11708309, by rfl⟩ : syracuseStep 62444317 = 23416619) B23416619
theorem B2741033 : Blo 1443541 2741033 := bstep (se 2 (by rfl) ⟨1027887, by rfl⟩ : syracuseStep 2741033 = 2055775) B2055775
theorem B3249161 : Blo 1443541 3249161 := bstep (se 2 (by rfl) ⟨1218435, by rfl⟩ : syracuseStep 3249161 = 2436871) B2436871
theorem B3249215 : Blo 1443541 3249215 := bstep (se 1 (by rfl) ⟨2436911, by rfl⟩ : syracuseStep 3249215 = 4873823) B4873823
theorem B2167871 : Blo 1443541 2167871 := bstep (se 1 (by rfl) ⟨1625903, by rfl⟩ : syracuseStep 2167871 = 3251807) B3251807
theorem B2167913 : Blo 1443541 2167913 := bstep (se 2 (by rfl) ⟨812967, by rfl⟩ : syracuseStep 2167913 = 1625935) B1625935
theorem B9254087 : Blo 1443541 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B2168015 : Blo 1443541 2168015 := bstep (se 1 (by rfl) ⟨1626011, by rfl⟩ : syracuseStep 2168015 = 3252023) B3252023
theorem B28161299 : Blo 1443541 28161299 := bstep (se 1 (by rfl) ⟨21120974, by rfl⟩ : syracuseStep 28161299 = 42241949) B42241949
theorem B31241537 : Blo 1443541 31241537 := bstep (se 2 (by rfl) ⟨11715576, by rfl⟩ : syracuseStep 31241537 = 23431153) B23431153
theorem B2438491 : Blo 1443541 2438491 := bstep (se 1 (by rfl) ⟨1828868, by rfl⟩ : syracuseStep 2438491 = 3657737) B3657737
theorem B6174107 : Blo 1443541 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B2168219 : Blo 1443541 2168219 := bstep (se 1 (by rfl) ⟨1626164, by rfl⟩ : syracuseStep 2168219 = 3252329) B3252329
theorem B8230571 : Blo 1443541 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B10417997 : Blo 1443541 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B23754653 : Blo 1443541 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B3250151 : Blo 1443541 3250151 := bstep (se 1 (by rfl) ⟨2437613, by rfl⟩ : syracuseStep 3250151 = 4875227) B4875227
theorem B3250169 : Blo 1443541 3250169 := bstep (se 2 (by rfl) ⟨1218813, by rfl⟩ : syracuseStep 3250169 = 2437627) B2437627
theorem B3250259 : Blo 1443541 3250259 := bstep (se 1 (by rfl) ⟨2437694, by rfl⟩ : syracuseStep 3250259 = 4875389) B4875389
theorem B3250331 : Blo 1443541 3250331 := bstep (se 1 (by rfl) ⟨2437748, by rfl⟩ : syracuseStep 3250331 = 4875497) B4875497
theorem B75028679 : Blo 1443541 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B7313651 : Blo 1443541 7313651 := bstep (se 1 (by rfl) ⟨5485238, by rfl⟩ : syracuseStep 7313651 = 10970477) B10970477
theorem B3250439 : Blo 1443541 3250439 := bstep (se 1 (by rfl) ⟨2437829, by rfl⟩ : syracuseStep 3250439 = 4875659) B4875659
theorem B27777329 : Blo 1443541 27777329 := bstep (se 2 (by rfl) ⟨10416498, by rfl⟩ : syracuseStep 27777329 = 20832997) B20832997
theorem B28531223 : Blo 1443541 28531223 := bstep (se 1 (by rfl) ⟨21398417, by rfl⟩ : syracuseStep 28531223 = 42796835) B42796835
theorem B3250745 : Blo 1443541 3250745 := bstep (se 2 (by rfl) ⟨1219029, by rfl⟩ : syracuseStep 3250745 = 2438059) B2438059
theorem B35158607 : Blo 1443541 35158607 := bstep (se 1 (by rfl) ⟨26368955, by rfl⟩ : syracuseStep 35158607 = 52737911) B52737911
theorem B10975823 : Blo 1443541 10975823 := bstep (se 1 (by rfl) ⟨8231867, by rfl⟩ : syracuseStep 10975823 = 16463735) B16463735
theorem B4389839 : Blo 1443541 4389839 := bstep (se 1 (by rfl) ⟨3292379, by rfl⟩ : syracuseStep 4389839 = 6584759) B6584759
theorem B52681859 : Blo 1443541 52681859 := bstep (se 1 (by rfl) ⟨39511394, by rfl⟩ : syracuseStep 52681859 = 79022789) B79022789
theorem B3251465 : Blo 1443541 3251465 := bstep (se 2 (by rfl) ⟨1219299, by rfl⟩ : syracuseStep 3251465 = 2438599) B2438599
theorem B2743561 : Blo 1443541 2743561 := bstep (se 2 (by rfl) ⟨1028835, by rfl⟩ : syracuseStep 2743561 = 2057671) B2057671
theorem B8224031 : Blo 1443541 8224031 := bstep (se 1 (by rfl) ⟨6168023, by rfl⟩ : syracuseStep 8224031 = 12336047) B12336047
theorem B39509317 : Blo 1443541 39509317 := bstep (se 4 (by rfl) ⟨3703998, by rfl⟩ : syracuseStep 39509317 = 7407997) B7407997
theorem B12344795 : Blo 1443541 12344795 := bstep (se 1 (by rfl) ⟨9258596, by rfl⟩ : syracuseStep 12344795 = 18517193) B18517193
theorem B11714021 : Blo 1443541 11714021 := bstep (se 4 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 11714021 = 2196379) B2196379
theorem B2055655 : Blo 1443541 2055655 := bstep (se 1 (by rfl) ⟨1541741, by rfl⟩ : syracuseStep 2055655 = 3083483) B3083483
theorem B4111879 : Blo 1443541 4111879 := bstep (se 1 (by rfl) ⟨3083909, by rfl⟩ : syracuseStep 4111879 = 6167819) B6167819
theorem B4874039 : Blo 1443541 4874039 := bstep (se 1 (by rfl) ⟨3655529, by rfl⟩ : syracuseStep 4874039 = 7311059) B7311059
theorem B8781625 : Blo 1443541 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B7315271 : Blo 1443541 7315271 := bstep (se 1 (by rfl) ⟨5486453, by rfl⟩ : syracuseStep 7315271 = 10972907) B10972907
theorem B4874363 : Blo 1443541 4874363 := bstep (se 1 (by rfl) ⟨3655772, by rfl⟩ : syracuseStep 4874363 = 7311545) B7311545
theorem B3252347 : Blo 1443541 3252347 := bstep (se 1 (by rfl) ⟨2439260, by rfl⟩ : syracuseStep 3252347 = 4878521) B4878521
theorem B7315595 : Blo 1443541 7315595 := bstep (se 1 (by rfl) ⟨5486696, by rfl⟩ : syracuseStep 7315595 = 10973393) B10973393
theorem B4874525 : Blo 1443541 4874525 := bstep (se 3 (by rfl) ⟨913973, by rfl⟩ : syracuseStep 4874525 = 1827947) B1827947
theorem B4874633 : Blo 1443541 4874633 := bstep (se 2 (by rfl) ⟨1827987, by rfl⟩ : syracuseStep 4874633 = 3655975) B3655975
theorem B1827355 : Blo 1443541 1827355 := bstep (se 1 (by rfl) ⟨1370516, by rfl⟩ : syracuseStep 1827355 = 2741033) B2741033
theorem B3654305 : Blo 1443541 3654305 := bstep (se 2 (by rfl) ⟨1370364, by rfl⟩ : syracuseStep 3654305 = 2740729) B2740729
theorem B9257753 : Blo 1443541 9257753 := bstep (se 2 (by rfl) ⟨3471657, by rfl⟩ : syracuseStep 9257753 = 6943315) B6943315
theorem B6169391 : Blo 1443541 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B5276477 : Blo 1443541 5276477 := bstep (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) B1978679
theorem B4113281 : Blo 1443541 4113281 := bstep (se 2 (by rfl) ⟨1542480, by rfl⟩ : syracuseStep 4113281 = 3084961) B3084961
theorem B4113463 : Blo 1443541 4113463 := bstep (se 1 (by rfl) ⟨3085097, by rfl⟩ : syracuseStep 4113463 = 6170195) B6170195
theorem B15836435 : Blo 1443541 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B4875767 : Blo 1443541 4875767 := bstep (se 1 (by rfl) ⟨3656825, by rfl⟩ : syracuseStep 4875767 = 7313651) B7313651
theorem B6252041 : Blo 1443541 6252041 := bstep (se 2 (by rfl) ⟨2344515, by rfl⟩ : syracuseStep 6252041 = 4689031) B4689031
theorem B23439071 : Blo 1443541 23439071 := bstep (se 1 (by rfl) ⟨17579303, by rfl⟩ : syracuseStep 23439071 = 35158607) B35158607
theorem B7317215 : Blo 1443541 7317215 := bstep (se 1 (by rfl) ⟨5487911, by rfl⟩ : syracuseStep 7317215 = 10975823) B10975823
theorem B1443775 : Blo 1443541 1443775 := bstep (se 1 (by rfl) ⟨1082831, by rfl⟩ : syracuseStep 1443775 = 2165663) B2165663
theorem B2926559 : Blo 1443541 2926559 := bstep (se 1 (by rfl) ⟨2194919, by rfl⟩ : syracuseStep 2926559 = 4389839) B4389839
theorem B1443807 : Blo 1443541 1443807 := bstep (se 1 (by rfl) ⟨1082855, by rfl⟩ : syracuseStep 1443807 = 2165711) B2165711
theorem B5482505 : Blo 1443541 5482505 := bstep (se 2 (by rfl) ⟨2055939, by rfl⟩ : syracuseStep 5482505 = 4111879) B4111879
theorem B1443867 : Blo 1443541 1443867 := bstep (se 1 (by rfl) ⟨1082900, by rfl⟩ : syracuseStep 1443867 = 2165801) B2165801
theorem B1443871 : Blo 1443541 1443871 := bstep (se 1 (by rfl) ⟨1082903, by rfl⟩ : syracuseStep 1443871 = 2165807) B2165807
theorem B1443887 : Blo 1443541 1443887 := bstep (se 1 (by rfl) ⟨1082915, by rfl⟩ : syracuseStep 1443887 = 2165831) B2165831
theorem B35121239 : Blo 1443541 35121239 := bstep (se 1 (by rfl) ⟨26340929, by rfl⟩ : syracuseStep 35121239 = 52681859) B52681859
theorem B47483009 : Blo 1443541 47483009 := bstep (se 2 (by rfl) ⟨17806128, by rfl⟩ : syracuseStep 47483009 = 35612257) B35612257
theorem B5482687 : Blo 1443541 5482687 := bstep (se 1 (by rfl) ⟨4112015, by rfl⟩ : syracuseStep 5482687 = 8224031) B8224031
theorem B27781325 : Blo 1443541 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B1444063 : Blo 1443541 1444063 := bstep (se 1 (by rfl) ⟨1083047, by rfl⟩ : syracuseStep 1444063 = 2166095) B2166095
theorem B10963187 : Blo 1443541 10963187 := bstep (se 1 (by rfl) ⟨8222390, by rfl⟩ : syracuseStep 10963187 = 16444781) B16444781
theorem B1444123 : Blo 1443541 1444123 := bstep (se 1 (by rfl) ⟨1083092, by rfl⟩ : syracuseStep 1444123 = 2166185) B2166185
theorem B7809347 : Blo 1443541 7809347 := bstep (se 1 (by rfl) ⟨5857010, by rfl⟩ : syracuseStep 7809347 = 11714021) B11714021
theorem B4114795 : Blo 1443541 4114795 := bstep (se 1 (by rfl) ⟨3086096, by rfl⟩ : syracuseStep 4114795 = 6172193) B6172193
theorem B1444223 : Blo 1443541 1444223 := bstep (se 1 (by rfl) ⟨1083167, by rfl⟩ : syracuseStep 1444223 = 2166335) B2166335
theorem B11708833 : Blo 1443541 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B1444399 : Blo 1443541 1444399 := bstep (se 1 (by rfl) ⟨1083299, by rfl⟩ : syracuseStep 1444399 = 2166599) B2166599
theorem B4876847 : Blo 1443541 4876847 := bstep (se 1 (by rfl) ⟨3657635, by rfl⟩ : syracuseStep 4876847 = 7315271) B7315271
theorem B2165351 : Blo 1443541 2165351 := bstep (se 1 (by rfl) ⟨1624013, by rfl⟩ : syracuseStep 2165351 = 3248027) B3248027
theorem B1444455 : Blo 1443541 1444455 := bstep (se 1 (by rfl) ⟨1083341, by rfl⟩ : syracuseStep 1444455 = 2166683) B2166683
theorem B2165543 : Blo 1443541 2165543 := bstep (se 1 (by rfl) ⟨1624157, by rfl⟩ : syracuseStep 2165543 = 3248315) B3248315
theorem B1444831 : Blo 1443541 1444831 := bstep (se 1 (by rfl) ⟨1083623, by rfl⟩ : syracuseStep 1444831 = 2167247) B2167247
theorem B1444859 : Blo 1443541 1444859 := bstep (se 1 (by rfl) ⟨1083644, by rfl⟩ : syracuseStep 1444859 = 2167289) B2167289
theorem B1444927 : Blo 1443541 1444927 := bstep (se 1 (by rfl) ⟨1083695, by rfl⟩ : syracuseStep 1444927 = 2167391) B2167391
theorem B2436169 : Blo 1443541 2436169 := bstep (se 2 (by rfl) ⟨913563, by rfl⟩ : syracuseStep 2436169 = 1827127) B1827127
theorem B2165867 : Blo 1443541 2165867 := bstep (se 1 (by rfl) ⟨1624400, by rfl⟩ : syracuseStep 2165867 = 3248801) B3248801
theorem B3468457 : Blo 1443541 3468457 := bstep (se 2 (by rfl) ⟨1300671, by rfl⟩ : syracuseStep 3468457 = 2601343) B2601343
theorem B4877495 : Blo 1443541 4877495 := bstep (se 1 (by rfl) ⟨3658121, by rfl⟩ : syracuseStep 4877495 = 7316243) B7316243
theorem B9252089 : Blo 1443541 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B11717885 : Blo 1443541 11717885 := bstep (se 3 (by rfl) ⟨2197103, by rfl⟩ : syracuseStep 11717885 = 4394207) B4394207
theorem B13888817 : Blo 1443541 13888817 := bstep (se 2 (by rfl) ⟨5208306, by rfl⟩ : syracuseStep 13888817 = 10416613) B10416613
theorem B2166107 : Blo 1443541 2166107 := bstep (se 1 (by rfl) ⟨1624580, by rfl⟩ : syracuseStep 2166107 = 3249161) B3249161
theorem B2166137 : Blo 1443541 2166137 := bstep (se 2 (by rfl) ⟨812301, by rfl⟩ : syracuseStep 2166137 = 1624603) B1624603
theorem B2166143 : Blo 1443541 2166143 := bstep (se 1 (by rfl) ⟨1624607, by rfl⟩ : syracuseStep 2166143 = 3249215) B3249215
theorem B1445247 : Blo 1443541 1445247 := bstep (se 1 (by rfl) ⟨1083935, by rfl⟩ : syracuseStep 1445247 = 2167871) B2167871
theorem B1445275 : Blo 1443541 1445275 := bstep (se 1 (by rfl) ⟨1083956, by rfl⟩ : syracuseStep 1445275 = 2167913) B2167913
theorem B1445343 : Blo 1443541 1445343 := bstep (se 1 (by rfl) ⟨1084007, by rfl⟩ : syracuseStep 1445343 = 2168015) B2168015
theorem B12348895 : Blo 1443541 12348895 := bstep (se 1 (by rfl) ⟨9261671, by rfl⟩ : syracuseStep 12348895 = 18523343) B18523343
theorem B20827691 : Blo 1443541 20827691 := bstep (se 1 (by rfl) ⟨15620768, by rfl⟩ : syracuseStep 20827691 = 31241537) B31241537
theorem B55545425 : Blo 1443541 55545425 := bstep (se 2 (by rfl) ⟨20829534, by rfl⟩ : syracuseStep 55545425 = 41659069) B41659069
theorem B4116071 : Blo 1443541 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B1445479 : Blo 1443541 1445479 := bstep (se 1 (by rfl) ⟨1084109, by rfl⟩ : syracuseStep 1445479 = 2168219) B2168219
theorem B83259089 : Blo 1443541 83259089 := bstep (se 2 (by rfl) ⟨31222158, by rfl⟩ : syracuseStep 83259089 = 62444317) B62444317
theorem B23424923 : Blo 1443541 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B2166767 : Blo 1443541 2166767 := bstep (se 1 (by rfl) ⟨1625075, by rfl⟩ : syracuseStep 2166767 = 3250151) B3250151
theorem B2469881 : Blo 1443541 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B2166779 : Blo 1443541 2166779 := bstep (se 1 (by rfl) ⟨1625084, by rfl⟩ : syracuseStep 2166779 = 3250169) B3250169
theorem B2166839 : Blo 1443541 2166839 := bstep (se 1 (by rfl) ⟨1625129, by rfl⟩ : syracuseStep 2166839 = 3250259) B3250259
theorem B2166887 : Blo 1443541 2166887 := bstep (se 1 (by rfl) ⟨1625165, by rfl⟩ : syracuseStep 2166887 = 3250331) B3250331
theorem B2166959 : Blo 1443541 2166959 := bstep (se 1 (by rfl) ⟨1625219, by rfl⟩ : syracuseStep 2166959 = 3250439) B3250439
theorem B18518219 : Blo 1443541 18518219 := bstep (se 1 (by rfl) ⟨13888664, by rfl⟩ : syracuseStep 18518219 = 27777329) B27777329
theorem B3658081 : Blo 1443541 3658081 := bstep (se 2 (by rfl) ⟨1371780, by rfl⟩ : syracuseStep 3658081 = 2743561) B2743561
theorem B2167163 : Blo 1443541 2167163 := bstep (se 1 (by rfl) ⟨1625372, by rfl⟩ : syracuseStep 2167163 = 3250745) B3250745
theorem B6943103 : Blo 1443541 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B52679089 : Blo 1443541 52679089 := bstep (se 2 (by rfl) ⟨19754658, by rfl⟩ : syracuseStep 52679089 = 39509317) B39509317
theorem B2740873 : Blo 1443541 2740873 := bstep (se 2 (by rfl) ⟨1027827, by rfl⟩ : syracuseStep 2740873 = 2055655) B2055655
theorem B2167433 : Blo 1443541 2167433 := bstep (se 2 (by rfl) ⟨812787, by rfl⟩ : syracuseStep 2167433 = 1625575) B1625575
theorem B2437951 : Blo 1443541 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B2167643 : Blo 1443541 2167643 := bstep (se 1 (by rfl) ⟨1625732, by rfl⟩ : syracuseStep 2167643 = 3251465) B3251465
theorem B8229863 : Blo 1443541 8229863 := bstep (se 1 (by rfl) ⟨6172397, by rfl⟩ : syracuseStep 8229863 = 12344795) B12344795
theorem B3519571 : Blo 1443541 3519571 := bstep (se 1 (by rfl) ⟨2639678, by rfl⟩ : syracuseStep 3519571 = 5279357) B5279357
theorem B3249359 : Blo 1443541 3249359 := bstep (se 1 (by rfl) ⟨2437019, by rfl⟩ : syracuseStep 3249359 = 4874039) B4874039
theorem B3249449 : Blo 1443541 3249449 := bstep (se 2 (by rfl) ⟨1218543, by rfl⟩ : syracuseStep 3249449 = 2437087) B2437087
theorem B2168105 : Blo 1443541 2168105 := bstep (se 2 (by rfl) ⟨813039, by rfl⟩ : syracuseStep 2168105 = 1626079) B1626079
theorem B4625839 : Blo 1443541 4625839 := bstep (se 1 (by rfl) ⟨3469379, by rfl⟩ : syracuseStep 4625839 = 6938759) B6938759
theorem B3249647 : Blo 1443541 3249647 := bstep (se 1 (by rfl) ⟨2437235, by rfl⟩ : syracuseStep 3249647 = 4874471) B4874471
theorem B2168303 : Blo 1443541 2168303 := bstep (se 1 (by rfl) ⟨1626227, by rfl⟩ : syracuseStep 2168303 = 3252455) B3252455
theorem B3250043 : Blo 1443541 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B3250079 : Blo 1443541 3250079 := bstep (se 1 (by rfl) ⟨2437559, by rfl⟩ : syracuseStep 3250079 = 4875119) B4875119
theorem B13178861 : Blo 1443541 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B3250313 : Blo 1443541 3250313 := bstep (se 2 (by rfl) ⟨1218867, by rfl⟩ : syracuseStep 3250313 = 2437735) B2437735
theorem B18774199 : Blo 1443541 18774199 := bstep (se 1 (by rfl) ⟨14080649, by rfl⟩ : syracuseStep 18774199 = 28161299) B28161299
theorem B2742491 : Blo 1443541 2742491 := bstep (se 1 (by rfl) ⟨2056868, by rfl⟩ : syracuseStep 2742491 = 4113737) B4113737
theorem B3250529 : Blo 1443541 3250529 := bstep (se 2 (by rfl) ⟨1218948, by rfl⟩ : syracuseStep 3250529 = 2437897) B2437897
theorem B4626827 : Blo 1443541 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B4872635 : Blo 1443541 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B3250619 : Blo 1443541 3250619 := bstep (se 1 (by rfl) ⟨2437964, by rfl⟩ : syracuseStep 3250619 = 4875929) B4875929
theorem B5487047 : Blo 1443541 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B8788733 : Blo 1443541 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B50019119 : Blo 1443541 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B3251015 : Blo 1443541 3251015 := bstep (se 1 (by rfl) ⟨2438261, by rfl⟩ : syracuseStep 3251015 = 4876523) B4876523
theorem B7314299 : Blo 1443541 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B3906427 : Blo 1443541 3906427 := bstep (se 1 (by rfl) ⟨2929820, by rfl⟩ : syracuseStep 3906427 = 5859641) B5859641
theorem B19020815 : Blo 1443541 19020815 := bstep (se 1 (by rfl) ⟨14265611, by rfl⟩ : syracuseStep 19020815 = 28531223) B28531223
theorem B3251321 : Blo 1443541 3251321 := bstep (se 2 (by rfl) ⟨1219245, by rfl⟩ : syracuseStep 3251321 = 2438491) B2438491
theorem B18505097 : Blo 1443541 18505097 := bstep (se 2 (by rfl) ⟨6939411, by rfl⟩ : syracuseStep 18505097 = 13878823) B13878823
theorem B5488033 : Blo 1443541 5488033 := bstep (se 2 (by rfl) ⟨2058012, by rfl⟩ : syracuseStep 5488033 = 4116025) B4116025
theorem B3251879 : Blo 1443541 3251879 := bstep (se 1 (by rfl) ⟨2438909, by rfl⟩ : syracuseStep 3251879 = 4877819) B4877819
theorem B3251987 : Blo 1443541 3251987 := bstep (se 1 (by rfl) ⟨2438990, by rfl⟩ : syracuseStep 3251987 = 4877981) B4877981
theorem B5488505 : Blo 1443541 5488505 := bstep (se 2 (by rfl) ⟨2058189, by rfl⟩ : syracuseStep 5488505 = 4116379) B4116379
theorem B12345479 : Blo 1443541 12345479 := bstep (se 1 (by rfl) ⟨9259109, by rfl⟩ : syracuseStep 12345479 = 18518219) B18518219
theorem B4628735 : Blo 1443541 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B4112927 : Blo 1443541 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B70238785 : Blo 1443541 70238785 := bstep (se 2 (by rfl) ⟨26339544, by rfl⟩ : syracuseStep 70238785 = 52679089) B52679089
theorem B3654497 : Blo 1443541 3654497 := bstep (se 2 (by rfl) ⟨1370436, by rfl⟩ : syracuseStep 3654497 = 2740873) B2740873
theorem B1951039 : Blo 1443541 1951039 := bstep (se 1 (by rfl) ⟨1463279, by rfl⟩ : syracuseStep 1951039 = 2926559) B2926559
theorem B3655003 : Blo 1443541 3655003 := bstep (se 1 (by rfl) ⟨2741252, by rfl⟩ : syracuseStep 3655003 = 5482505) B5482505
theorem B23414159 : Blo 1443541 23414159 := bstep (se 1 (by rfl) ⟨17560619, by rfl⟩ : syracuseStep 23414159 = 35121239) B35121239
theorem B31655339 : Blo 1443541 31655339 := bstep (se 1 (by rfl) ⟨23741504, by rfl⟩ : syracuseStep 31655339 = 47483009) B47483009
theorem B1828327 : Blo 1443541 1828327 := bstep (se 1 (by rfl) ⟨1371245, by rfl⟩ : syracuseStep 1828327 = 2742491) B2742491
theorem B7308791 : Blo 1443541 7308791 := bstep (se 1 (by rfl) ⟨5481593, by rfl⟩ : syracuseStep 7308791 = 10963187) B10963187
theorem B1443567 : Blo 1443541 1443567 := bstep (se 1 (by rfl) ⟨1082675, by rfl⟩ : syracuseStep 1443567 = 2165351) B2165351
theorem B5859155 : Blo 1443541 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B1443695 : Blo 1443541 1443695 := bstep (se 1 (by rfl) ⟨1082771, by rfl⟩ : syracuseStep 1443695 = 2165543) B2165543
theorem B7317377 : Blo 1443541 7317377 := bstep (se 2 (by rfl) ⟨2744016, by rfl⟩ : syracuseStep 7317377 = 5488033) B5488033
theorem B4876199 : Blo 1443541 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B1443911 : Blo 1443541 1443911 := bstep (se 1 (by rfl) ⟨1082933, by rfl⟩ : syracuseStep 1443911 = 2165867) B2165867
theorem B9259211 : Blo 1443541 9259211 := bstep (se 1 (by rfl) ⟨6944408, by rfl⟩ : syracuseStep 9259211 = 13888817) B13888817
theorem B1444071 : Blo 1443541 1444071 := bstep (se 1 (by rfl) ⟨1083053, by rfl⟩ : syracuseStep 1444071 = 2166107) B2166107
theorem B1444091 : Blo 1443541 1444091 := bstep (se 1 (by rfl) ⟨1083068, by rfl⟩ : syracuseStep 1444091 = 2166137) B2166137
theorem B1444095 : Blo 1443541 1444095 := bstep (se 1 (by rfl) ⟨1083071, by rfl⟩ : syracuseStep 1444095 = 2166143) B2166143
theorem B37030283 : Blo 1443541 37030283 := bstep (se 1 (by rfl) ⟨27772712, by rfl⟩ : syracuseStep 37030283 = 55545425) B55545425
theorem B62466461 : Blo 1443541 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B1444511 : Blo 1443541 1444511 := bstep (se 1 (by rfl) ⟨1083383, by rfl⟩ : syracuseStep 1444511 = 2166767) B2166767
theorem B1444519 : Blo 1443541 1444519 := bstep (se 1 (by rfl) ⟨1083389, by rfl⟩ : syracuseStep 1444519 = 2166779) B2166779
theorem B1444559 : Blo 1443541 1444559 := bstep (se 1 (by rfl) ⟨1083419, by rfl⟩ : syracuseStep 1444559 = 2166839) B2166839
theorem B1444591 : Blo 1443541 1444591 := bstep (se 1 (by rfl) ⟨1083443, by rfl⟩ : syracuseStep 1444591 = 2166887) B2166887
theorem B4877063 : Blo 1443541 4877063 := bstep (se 1 (by rfl) ⟨3657797, by rfl⟩ : syracuseStep 4877063 = 7315595) B7315595
theorem B1444639 : Blo 1443541 1444639 := bstep (se 1 (by rfl) ⟨1083479, by rfl⟩ : syracuseStep 1444639 = 2166959) B2166959
theorem B7310249 : Blo 1443541 7310249 := bstep (se 2 (by rfl) ⟨2741343, by rfl⟩ : syracuseStep 7310249 = 5482687) B5482687
theorem B1444775 : Blo 1443541 1444775 := bstep (se 1 (by rfl) ⟨1083581, by rfl⟩ : syracuseStep 1444775 = 2167163) B2167163
theorem B1444955 : Blo 1443541 1444955 := bstep (se 1 (by rfl) ⟨1083716, by rfl⟩ : syracuseStep 1444955 = 2167433) B2167433
theorem B2436203 : Blo 1443541 2436203 := bstep (se 1 (by rfl) ⟨1827152, by rfl⟩ : syracuseStep 2436203 = 3654305) B3654305
theorem B4877441 : Blo 1443541 4877441 := bstep (se 2 (by rfl) ⟨1829040, by rfl⟩ : syracuseStep 4877441 = 3658081) B3658081
theorem B6171835 : Blo 1443541 6171835 := bstep (se 1 (by rfl) ⟨4628876, by rfl⟩ : syracuseStep 6171835 = 9257753) B9257753
theorem B3517651 : Blo 1443541 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B1445095 : Blo 1443541 1445095 := bstep (se 1 (by rfl) ⟨1083821, by rfl⟩ : syracuseStep 1445095 = 2167643) B2167643
theorem B2436473 : Blo 1443541 2436473 := bstep (se 2 (by rfl) ⟨913677, by rfl⟩ : syracuseStep 2436473 = 1827355) B1827355
theorem B2166239 : Blo 1443541 2166239 := bstep (se 1 (by rfl) ⟨1624679, by rfl⟩ : syracuseStep 2166239 = 3249359) B3249359
theorem B2166299 : Blo 1443541 2166299 := bstep (se 1 (by rfl) ⟨1624724, by rfl⟩ : syracuseStep 2166299 = 3249449) B3249449
theorem B1445403 : Blo 1443541 1445403 := bstep (se 1 (by rfl) ⟨1084052, by rfl⟩ : syracuseStep 1445403 = 2168105) B2168105
theorem B2166431 : Blo 1443541 2166431 := bstep (se 1 (by rfl) ⟨1624823, by rfl⟩ : syracuseStep 2166431 = 3249647) B3249647
theorem B1445535 : Blo 1443541 1445535 := bstep (se 1 (by rfl) ⟨1084151, by rfl⟩ : syracuseStep 1445535 = 2168303) B2168303
theorem B15626047 : Blo 1443541 15626047 := bstep (se 1 (by rfl) ⟨11719535, by rfl⟩ : syracuseStep 15626047 = 23439071) B23439071
theorem B4878143 : Blo 1443541 4878143 := bstep (se 1 (by rfl) ⟨3658607, by rfl⟩ : syracuseStep 4878143 = 7317215) B7317215
theorem B2166695 : Blo 1443541 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B2166719 : Blo 1443541 2166719 := bstep (se 1 (by rfl) ⟨1625039, by rfl⟩ : syracuseStep 2166719 = 3250079) B3250079
theorem B8785907 : Blo 1443541 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B5484617 : Blo 1443541 5484617 := bstep (se 2 (by rfl) ⟨2056731, by rfl⟩ : syracuseStep 5484617 = 4113463) B4113463
theorem B2166875 : Blo 1443541 2166875 := bstep (se 1 (by rfl) ⟨1625156, by rfl⟩ : syracuseStep 2166875 = 3250313) B3250313
theorem B3248225 : Blo 1443541 3248225 := bstep (se 2 (by rfl) ⟨1218084, by rfl⟩ : syracuseStep 3248225 = 2436169) B2436169
theorem B5206231 : Blo 1443541 5206231 := bstep (se 1 (by rfl) ⟨3904673, by rfl⟩ : syracuseStep 5206231 = 7809347) B7809347
theorem B4624609 : Blo 1443541 4624609 := bstep (se 2 (by rfl) ⟨1734228, by rfl⟩ : syracuseStep 4624609 = 3468457) B3468457
theorem B2167019 : Blo 1443541 2167019 := bstep (se 1 (by rfl) ⟨1625264, by rfl⟩ : syracuseStep 2167019 = 3250529) B3250529
theorem B3084551 : Blo 1443541 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B3248423 : Blo 1443541 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B2167079 : Blo 1443541 2167079 := bstep (se 1 (by rfl) ⟨1625309, by rfl⟩ : syracuseStep 2167079 = 3250619) B3250619
theorem B3658031 : Blo 1443541 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B33346079 : Blo 1443541 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B2167343 : Blo 1443541 2167343 := bstep (se 1 (by rfl) ⟨1625507, by rfl⟩ : syracuseStep 2167343 = 3251015) B3251015
theorem B2167547 : Blo 1443541 2167547 := bstep (se 1 (by rfl) ⟨1625660, by rfl⟩ : syracuseStep 2167547 = 3251321) B3251321
theorem B7811923 : Blo 1443541 7811923 := bstep (se 1 (by rfl) ⟨5858942, by rfl⟩ : syracuseStep 7811923 = 11717885) B11717885
theorem B2167919 : Blo 1443541 2167919 := bstep (se 1 (by rfl) ⟨1625939, by rfl⟩ : syracuseStep 2167919 = 3251879) B3251879
theorem B55506059 : Blo 1443541 55506059 := bstep (se 1 (by rfl) ⟨41629544, by rfl⟩ : syracuseStep 55506059 = 83259089) B83259089
theorem B2167991 : Blo 1443541 2167991 := bstep (se 1 (by rfl) ⟨1625993, by rfl⟩ : syracuseStep 2167991 = 3251987) B3251987
theorem B3659003 : Blo 1443541 3659003 := bstep (se 1 (by rfl) ⟨2744252, by rfl⟩ : syracuseStep 3659003 = 5488505) B5488505
theorem B3249575 : Blo 1443541 3249575 := bstep (se 1 (by rfl) ⟨2437181, by rfl⟩ : syracuseStep 3249575 = 4874363) B4874363
theorem B2168231 : Blo 1443541 2168231 := bstep (se 1 (by rfl) ⟨1626173, by rfl⟩ : syracuseStep 2168231 = 3252347) B3252347
theorem B3249683 : Blo 1443541 3249683 := bstep (se 1 (by rfl) ⟨2437262, by rfl⟩ : syracuseStep 3249683 = 4874525) B4874525
theorem B3249755 : Blo 1443541 3249755 := bstep (se 1 (by rfl) ⟨2437316, by rfl⟩ : syracuseStep 3249755 = 4874633) B4874633
theorem B5486393 : Blo 1443541 5486393 := bstep (se 2 (by rfl) ⟨2057397, by rfl⟩ : syracuseStep 5486393 = 4114795) B4114795
theorem B15611777 : Blo 1443541 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B2742187 : Blo 1443541 2742187 := bstep (se 1 (by rfl) ⟨2056640, by rfl⟩ : syracuseStep 2742187 = 4113281) B4113281
theorem B5486575 : Blo 1443541 5486575 := bstep (se 1 (by rfl) ⟨4114931, by rfl⟩ : syracuseStep 5486575 = 8229863) B8229863
theorem B10557623 : Blo 1443541 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B100129061 : Blo 1443541 100129061 := bstep (se 4 (by rfl) ⟨9387099, by rfl⟩ : syracuseStep 100129061 = 18774199) B18774199
theorem B3250511 : Blo 1443541 3250511 := bstep (se 1 (by rfl) ⟨2437883, by rfl⟩ : syracuseStep 3250511 = 4875767) B4875767
theorem B4168027 : Blo 1443541 4168027 := bstep (se 1 (by rfl) ⟨3126020, by rfl⟩ : syracuseStep 4168027 = 6252041) B6252041
theorem B3250601 : Blo 1443541 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B5208569 : Blo 1443541 5208569 := bstep (se 2 (by rfl) ⟨1953213, by rfl⟩ : syracuseStep 5208569 = 3906427) B3906427
theorem B4692761 : Blo 1443541 4692761 := bstep (se 2 (by rfl) ⟨1759785, by rfl⟩ : syracuseStep 4692761 = 3519571) B3519571
theorem B18520883 : Blo 1443541 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B3251231 : Blo 1443541 3251231 := bstep (se 1 (by rfl) ⟨2438423, by rfl⟩ : syracuseStep 3251231 = 4876847) B4876847
theorem B6167785 : Blo 1443541 6167785 := bstep (se 2 (by rfl) ⟨2312919, by rfl⟩ : syracuseStep 6167785 = 4625839) B4625839
theorem B16465193 : Blo 1443541 16465193 := bstep (se 2 (by rfl) ⟨6174447, by rfl⟩ : syracuseStep 16465193 = 12348895) B12348895
theorem B12680543 : Blo 1443541 12680543 := bstep (se 1 (by rfl) ⟨9510407, by rfl⟩ : syracuseStep 12680543 = 19020815) B19020815
theorem B3251663 : Blo 1443541 3251663 := bstep (se 1 (by rfl) ⟨2438747, by rfl⟩ : syracuseStep 3251663 = 4877495) B4877495
theorem B6168059 : Blo 1443541 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B12336731 : Blo 1443541 12336731 := bstep (se 1 (by rfl) ⟨9252548, by rfl⟩ : syracuseStep 12336731 = 18505097) B18505097
theorem B13885127 : Blo 1443541 13885127 := bstep (se 1 (by rfl) ⟨10413845, by rfl⟩ : syracuseStep 13885127 = 20827691) B20827691
theorem B2744047 : Blo 1443541 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B1646587 : Blo 1443541 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B2056367 : Blo 1443541 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B24691229 : Blo 1443541 24691229 := bstep (se 3 (by rfl) ⟨4629605, by rfl⟩ : syracuseStep 24691229 = 9259211) B9259211
theorem B93651713 : Blo 1443541 93651713 := bstep (se 2 (by rfl) ⟨35119392, by rfl⟩ : syracuseStep 93651713 = 70238785) B70238785
theorem B37004039 : Blo 1443541 37004039 := bstep (se 1 (by rfl) ⟨27753029, by rfl⟩ : syracuseStep 37004039 = 55506059) B55506059
theorem B21103559 : Blo 1443541 21103559 := bstep (se 1 (by rfl) ⟨15827669, by rfl⟩ : syracuseStep 21103559 = 31655339) B31655339
theorem B18760805 : Blo 1443541 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B7038415 : Blo 1443541 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B10405541 : Blo 1443541 10405541 := bstep (se 4 (by rfl) ⟨975519, by rfl⟩ : syracuseStep 10405541 = 1951039) B1951039
theorem B12347255 : Blo 1443541 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B1624135 : Blo 1443541 1624135 := bstep (se 1 (by rfl) ⟨1218101, by rfl⟩ : syracuseStep 1624135 = 2436203) B2436203
theorem B1624315 : Blo 1443541 1624315 := bstep (se 1 (by rfl) ⟨1218236, by rfl⟩ : syracuseStep 1624315 = 2436473) B2436473
theorem B1444159 : Blo 1443541 1444159 := bstep (se 1 (by rfl) ⟨1083119, by rfl⟩ : syracuseStep 1444159 = 2166239) B2166239
theorem B1444199 : Blo 1443541 1444199 := bstep (se 1 (by rfl) ⟨1083149, by rfl⟩ : syracuseStep 1444199 = 2166299) B2166299
theorem B20834729 : Blo 1443541 20834729 := bstep (se 2 (by rfl) ⟨7813023, by rfl⟩ : syracuseStep 20834729 = 15626047) B15626047
theorem B1444287 : Blo 1443541 1444287 := bstep (se 1 (by rfl) ⟨1083215, by rfl⟩ : syracuseStep 1444287 = 2166431) B2166431
theorem B3656249 : Blo 1443541 3656249 := bstep (se 2 (by rfl) ⟨1371093, by rfl⟩ : syracuseStep 3656249 = 2742187) B2742187
theorem B1444463 : Blo 1443541 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B1444479 : Blo 1443541 1444479 := bstep (se 1 (by rfl) ⟨1083359, by rfl⟩ : syracuseStep 1444479 = 2166719) B2166719
theorem B3656411 : Blo 1443541 3656411 := bstep (se 1 (by rfl) ⟨2742308, by rfl⟩ : syracuseStep 3656411 = 5484617) B5484617
theorem B1444583 : Blo 1443541 1444583 := bstep (se 1 (by rfl) ⟨1083437, by rfl⟩ : syracuseStep 1444583 = 2166875) B2166875
theorem B2165483 : Blo 1443541 2165483 := bstep (se 1 (by rfl) ⟨1624112, by rfl⟩ : syracuseStep 2165483 = 3248225) B3248225
theorem B1444679 : Blo 1443541 1444679 := bstep (se 1 (by rfl) ⟨1083509, by rfl⟩ : syracuseStep 1444679 = 2167019) B2167019
theorem B2165615 : Blo 1443541 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B1444719 : Blo 1443541 1444719 := bstep (se 1 (by rfl) ⟨1083539, by rfl⟩ : syracuseStep 1444719 = 2167079) B2167079
theorem B6941641 : Blo 1443541 6941641 := bstep (se 2 (by rfl) ⟨2603115, by rfl⟩ : syracuseStep 6941641 = 5206231) B5206231
theorem B1444895 : Blo 1443541 1444895 := bstep (se 1 (by rfl) ⟨1083671, by rfl⟩ : syracuseStep 1444895 = 2167343) B2167343
theorem B5557369 : Blo 1443541 5557369 := bstep (se 2 (by rfl) ⟨2084013, by rfl⟩ : syracuseStep 5557369 = 4168027) B4168027
theorem B1445031 : Blo 1443541 1445031 := bstep (se 1 (by rfl) ⟨1083773, by rfl⟩ : syracuseStep 1445031 = 2167547) B2167547
theorem B2436331 : Blo 1443541 2436331 := bstep (se 1 (by rfl) ⟨1827248, by rfl⟩ : syracuseStep 2436331 = 3654497) B3654497
theorem B1445279 : Blo 1443541 1445279 := bstep (se 1 (by rfl) ⟨1083959, by rfl⟩ : syracuseStep 1445279 = 2167919) B2167919
theorem B1445327 : Blo 1443541 1445327 := bstep (se 1 (by rfl) ⟨1083995, by rfl⟩ : syracuseStep 1445327 = 2167991) B2167991
theorem B15609439 : Blo 1443541 15609439 := bstep (se 1 (by rfl) ⟨11707079, by rfl⟩ : syracuseStep 15609439 = 23414159) B23414159
theorem B2166383 : Blo 1443541 2166383 := bstep (se 1 (by rfl) ⟨1624787, by rfl⟩ : syracuseStep 2166383 = 3249575) B3249575
theorem B1445487 : Blo 1443541 1445487 := bstep (se 1 (by rfl) ⟨1084115, by rfl⟩ : syracuseStep 1445487 = 2168231) B2168231
theorem B2166455 : Blo 1443541 2166455 := bstep (se 1 (by rfl) ⟨1624841, by rfl⟩ : syracuseStep 2166455 = 3249683) B3249683
theorem B2166503 : Blo 1443541 2166503 := bstep (se 1 (by rfl) ⟨1624877, by rfl⟩ : syracuseStep 2166503 = 3249755) B3249755
theorem B10415897 : Blo 1443541 10415897 := bstep (se 2 (by rfl) ⟨3905961, by rfl⟩ : syracuseStep 10415897 = 7811923) B7811923
theorem B3657595 : Blo 1443541 3657595 := bstep (se 1 (by rfl) ⟨2743196, by rfl⟩ : syracuseStep 3657595 = 5486393) B5486393
theorem B10407851 : Blo 1443541 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B4878251 : Blo 1443541 4878251 := bstep (se 1 (by rfl) ⟨3658688, by rfl⟩ : syracuseStep 4878251 = 7317377) B7317377
theorem B66752707 : Blo 1443541 66752707 := bstep (se 1 (by rfl) ⟨50064530, by rfl⟩ : syracuseStep 66752707 = 100129061) B100129061
theorem B2167007 : Blo 1443541 2167007 := bstep (se 1 (by rfl) ⟨1625255, by rfl⟩ : syracuseStep 2167007 = 3250511) B3250511
theorem B8229113 : Blo 1443541 8229113 := bstep (se 2 (by rfl) ⟨3085917, by rfl⟩ : syracuseStep 8229113 = 6171835) B6171835
theorem B24686855 : Blo 1443541 24686855 := bstep (se 1 (by rfl) ⟨18515141, by rfl⟩ : syracuseStep 24686855 = 37030283) B37030283
theorem B41644307 : Blo 1443541 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B2167067 : Blo 1443541 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B2437769 : Blo 1443541 2437769 := bstep (se 2 (by rfl) ⟨914163, by rfl⟩ : syracuseStep 2437769 = 1828327) B1828327
theorem B2167487 : Blo 1443541 2167487 := bstep (se 1 (by rfl) ⟨1625615, by rfl⟩ : syracuseStep 2167487 = 3251231) B3251231
theorem B2167775 : Blo 1443541 2167775 := bstep (se 1 (by rfl) ⟨1625831, by rfl⟩ : syracuseStep 2167775 = 3251663) B3251663
theorem B3658729 : Blo 1443541 3658729 := bstep (se 2 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 3658729 = 2744047) B2744047
theorem B8230319 : Blo 1443541 8230319 := bstep (se 1 (by rfl) ⟨6172739, by rfl⟩ : syracuseStep 8230319 = 12345479) B12345479
theorem B3085823 : Blo 1443541 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B2438687 : Blo 1443541 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B6166145 : Blo 1443541 6166145 := bstep (se 2 (by rfl) ⟨2312304, by rfl⟩ : syracuseStep 6166145 = 4624609) B4624609
theorem B22230719 : Blo 1443541 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B2741951 : Blo 1443541 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B2439335 : Blo 1443541 2439335 := bstep (se 1 (by rfl) ⟨1829501, by rfl⟩ : syracuseStep 2439335 = 3659003) B3659003
theorem B4872527 : Blo 1443541 4872527 := bstep (se 1 (by rfl) ⟨3654395, by rfl⟩ : syracuseStep 4872527 = 7308791) B7308791
theorem B3906103 : Blo 1443541 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B3250799 : Blo 1443541 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B8223713 : Blo 1443541 8223713 := bstep (se 2 (by rfl) ⟨3083892, by rfl⟩ : syracuseStep 8223713 = 6167785) B6167785
theorem B3472379 : Blo 1443541 3472379 := bstep (se 1 (by rfl) ⟨2604284, by rfl⟩ : syracuseStep 3472379 = 5208569) B5208569
theorem B4873337 : Blo 1443541 4873337 := bstep (se 2 (by rfl) ⟨1827501, by rfl⟩ : syracuseStep 4873337 = 3655003) B3655003
theorem B3251375 : Blo 1443541 3251375 := bstep (se 1 (by rfl) ⟨2438531, by rfl⟩ : syracuseStep 3251375 = 4877063) B4877063
theorem B3128507 : Blo 1443541 3128507 := bstep (se 1 (by rfl) ⟨2346380, by rfl⟩ : syracuseStep 3128507 = 4692761) B4692761
theorem B4873499 : Blo 1443541 4873499 := bstep (se 1 (by rfl) ⟨3655124, by rfl⟩ : syracuseStep 4873499 = 7310249) B7310249
theorem B3251627 : Blo 1443541 3251627 := bstep (se 1 (by rfl) ⟨2438720, by rfl⟩ : syracuseStep 3251627 = 4877441) B4877441
theorem B10976795 : Blo 1443541 10976795 := bstep (se 1 (by rfl) ⟨8232596, by rfl⟩ : syracuseStep 10976795 = 16465193) B16465193
theorem B8453695 : Blo 1443541 8453695 := bstep (se 1 (by rfl) ⟨6340271, by rfl⟩ : syracuseStep 8453695 = 12680543) B12680543
theorem B4112039 : Blo 1443541 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B8224487 : Blo 1443541 8224487 := bstep (se 1 (by rfl) ⟨6168365, by rfl⟩ : syracuseStep 8224487 = 12336731) B12336731
theorem B9256751 : Blo 1443541 9256751 := bstep (se 1 (by rfl) ⟨6942563, by rfl⟩ : syracuseStep 9256751 = 13885127) B13885127
theorem B3252095 : Blo 1443541 3252095 := bstep (se 1 (by rfl) ⟨2439071, by rfl⟩ : syracuseStep 3252095 = 4878143) B4878143
theorem B8781797 : Blo 1443541 8781797 := bstep (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) B1646587
theorem B7315433 : Blo 1443541 7315433 := bstep (se 2 (by rfl) ⟨2743287, by rfl⟩ : syracuseStep 7315433 = 5486575) B5486575
theorem B5857271 : Blo 1443541 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B16457903 : Blo 1443541 16457903 := bstep (se 1 (by rfl) ⟨12343427, by rfl⟩ : syracuseStep 16457903 = 24686855) B24686855
theorem B27762871 : Blo 1443541 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B14820479 : Blo 1443541 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B27748109 : Blo 1443541 27748109 := bstep (se 3 (by rfl) ⟨5202770, by rfl⟩ : syracuseStep 27748109 = 10405541) B10405541
theorem B1443655 : Blo 1443541 1443655 := bstep (se 1 (by rfl) ⟨1082741, by rfl⟩ : syracuseStep 1443655 = 2165483) B2165483
theorem B1443743 : Blo 1443541 1443743 := bstep (se 1 (by rfl) ⟨1082807, by rfl⟩ : syracuseStep 1443743 = 2165615) B2165615
theorem B5482475 : Blo 1443541 5482475 := bstep (se 1 (by rfl) ⟨4111856, by rfl⟩ : syracuseStep 5482475 = 8223713) B8223713
theorem B7317863 : Blo 1443541 7317863 := bstep (se 1 (by rfl) ⟨5488397, by rfl⟩ : syracuseStep 7317863 = 10976795) B10976795
theorem B1444255 : Blo 1443541 1444255 := bstep (se 1 (by rfl) ⟨1083191, by rfl⟩ : syracuseStep 1444255 = 2166383) B2166383
theorem B1444303 : Blo 1443541 1444303 := bstep (se 1 (by rfl) ⟨1083227, by rfl⟩ : syracuseStep 1444303 = 2166455) B2166455
theorem B5482991 : Blo 1443541 5482991 := bstep (se 1 (by rfl) ⟨4112243, by rfl⟩ : syracuseStep 5482991 = 8224487) B8224487
theorem B1444335 : Blo 1443541 1444335 := bstep (se 1 (by rfl) ⟨1083251, by rfl⟩ : syracuseStep 1444335 = 2166503) B2166503
theorem B4876793 : Blo 1443541 4876793 := bstep (se 2 (by rfl) ⟨1828797, by rfl⟩ : syracuseStep 4876793 = 3657595) B3657595
theorem B6171167 : Blo 1443541 6171167 := bstep (se 1 (by rfl) ⟨4628375, by rfl⟩ : syracuseStep 6171167 = 9256751) B9256751
theorem B4876955 : Blo 1443541 4876955 := bstep (se 1 (by rfl) ⟨3657716, by rfl⟩ : syracuseStep 4876955 = 7315433) B7315433
theorem B2165513 : Blo 1443541 2165513 := bstep (se 2 (by rfl) ⟨812067, by rfl⟩ : syracuseStep 2165513 = 1624135) B1624135
theorem B1444671 : Blo 1443541 1444671 := bstep (se 1 (by rfl) ⟨1083503, by rfl⟩ : syracuseStep 1444671 = 2167007) B2167007
theorem B1444711 : Blo 1443541 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B2165753 : Blo 1443541 2165753 := bstep (se 2 (by rfl) ⟨812157, by rfl⟩ : syracuseStep 2165753 = 1624315) B1624315
theorem B16460819 : Blo 1443541 16460819 := bstep (se 1 (by rfl) ⟨12345614, by rfl⟩ : syracuseStep 16460819 = 24691229) B24691229
theorem B1625179 : Blo 1443541 1625179 := bstep (se 1 (by rfl) ⟨1218884, by rfl⟩ : syracuseStep 1625179 = 2437769) B2437769
theorem B5483645 : Blo 1443541 5483645 := bstep (se 3 (by rfl) ⟨1028183, by rfl⟩ : syracuseStep 5483645 = 2056367) B2056367
theorem B1444991 : Blo 1443541 1444991 := bstep (se 1 (by rfl) ⟨1083743, by rfl⟩ : syracuseStep 1444991 = 2167487) B2167487
theorem B62434475 : Blo 1443541 62434475 := bstep (se 1 (by rfl) ⟨46825856, by rfl⟩ : syracuseStep 62434475 = 93651713) B93651713
theorem B24669359 : Blo 1443541 24669359 := bstep (se 1 (by rfl) ⟨18502019, by rfl⟩ : syracuseStep 24669359 = 37004039) B37004039
theorem B1445183 : Blo 1443541 1445183 := bstep (se 1 (by rfl) ⟨1083887, by rfl⟩ : syracuseStep 1445183 = 2167775) B2167775
theorem B1625791 : Blo 1443541 1625791 := bstep (se 1 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 1625791 = 2438687) B2438687
theorem B4878305 : Blo 1443541 4878305 := bstep (se 2 (by rfl) ⟨1829364, by rfl⟩ : syracuseStep 4878305 = 3658729) B3658729
theorem B8228861 : Blo 1443541 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B1626223 : Blo 1443541 1626223 := bstep (se 1 (by rfl) ⟨1219667, by rfl⟩ : syracuseStep 1626223 = 2439335) B2439335
theorem B7409825 : Blo 1443541 7409825 := bstep (se 2 (by rfl) ⟨2778684, by rfl⟩ : syracuseStep 7409825 = 5557369) B5557369
theorem B3248351 : Blo 1443541 3248351 := bstep (se 1 (by rfl) ⟨2436263, by rfl⟩ : syracuseStep 3248351 = 4872527) B4872527
theorem B13889819 : Blo 1443541 13889819 := bstep (se 1 (by rfl) ⟨10417364, by rfl⟩ : syracuseStep 13889819 = 20834729) B20834729
theorem B3248441 : Blo 1443541 3248441 := bstep (se 2 (by rfl) ⟨1218165, by rfl⟩ : syracuseStep 3248441 = 2436331) B2436331
theorem B2437499 : Blo 1443541 2437499 := bstep (se 1 (by rfl) ⟨1828124, by rfl⟩ : syracuseStep 2437499 = 3656249) B3656249
theorem B2167199 : Blo 1443541 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B2437607 : Blo 1443541 2437607 := bstep (se 1 (by rfl) ⟨1828205, by rfl⟩ : syracuseStep 2437607 = 3656411) B3656411
theorem B7311869 : Blo 1443541 7311869 := bstep (se 3 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 7311869 = 2741951) B2741951
theorem B9384553 : Blo 1443541 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B2314919 : Blo 1443541 2314919 := bstep (se 1 (by rfl) ⟨1736189, by rfl⟩ : syracuseStep 2314919 = 3472379) B3472379
theorem B225104629 : Blo 1443541 225104629 := bstep (se 5 (by rfl) ⟨10551779, by rfl⟩ : syracuseStep 225104629 = 21103559) B21103559
theorem B3248891 : Blo 1443541 3248891 := bstep (se 1 (by rfl) ⟨2436668, by rfl⟩ : syracuseStep 3248891 = 4873337) B4873337
theorem B2167583 : Blo 1443541 2167583 := bstep (se 1 (by rfl) ⟨1625687, by rfl⟩ : syracuseStep 2167583 = 3251375) B3251375
theorem B2085671 : Blo 1443541 2085671 := bstep (se 1 (by rfl) ⟨1564253, by rfl⟩ : syracuseStep 2085671 = 3128507) B3128507
theorem B20812585 : Blo 1443541 20812585 := bstep (se 2 (by rfl) ⟨7804719, by rfl⟩ : syracuseStep 20812585 = 15609439) B15609439
theorem B3248999 : Blo 1443541 3248999 := bstep (se 1 (by rfl) ⟨2436749, by rfl⟩ : syracuseStep 3248999 = 4873499) B4873499
theorem B2167751 : Blo 1443541 2167751 := bstep (se 1 (by rfl) ⟨1625813, by rfl⟩ : syracuseStep 2167751 = 3251627) B3251627
theorem B2741359 : Blo 1443541 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B6943931 : Blo 1443541 6943931 := bstep (se 1 (by rfl) ⟨5207948, by rfl⟩ : syracuseStep 6943931 = 10415897) B10415897
theorem B2168063 : Blo 1443541 2168063 := bstep (se 1 (by rfl) ⟨1626047, by rfl⟩ : syracuseStep 2168063 = 3252095) B3252095
theorem B5854531 : Blo 1443541 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B3904847 : Blo 1443541 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B5486075 : Blo 1443541 5486075 := bstep (se 1 (by rfl) ⟨4114556, by rfl⟩ : syracuseStep 5486075 = 8229113) B8229113
theorem B89003609 : Blo 1443541 89003609 := bstep (se 2 (by rfl) ⟨33376353, by rfl⟩ : syracuseStep 89003609 = 66752707) B66752707
theorem B12507203 : Blo 1443541 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B5208137 : Blo 1443541 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B5486879 : Blo 1443541 5486879 := bstep (se 1 (by rfl) ⟨4115159, by rfl⟩ : syracuseStep 5486879 = 8230319) B8230319
theorem B4110763 : Blo 1443541 4110763 := bstep (se 1 (by rfl) ⟨3083072, by rfl⟩ : syracuseStep 4110763 = 6166145) B6166145
theorem B8231503 : Blo 1443541 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B9255521 : Blo 1443541 9255521 := bstep (se 2 (by rfl) ⟨3470820, by rfl⟩ : syracuseStep 9255521 = 6941641) B6941641
theorem B11271593 : Blo 1443541 11271593 := bstep (se 2 (by rfl) ⟨4226847, by rfl⟩ : syracuseStep 11271593 = 8453695) B8453695
theorem B6938567 : Blo 1443541 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B3252167 : Blo 1443541 3252167 := bstep (se 1 (by rfl) ⟨2439125, by rfl⟩ : syracuseStep 3252167 = 4878251) B4878251
theorem B4939883 : Blo 1443541 4939883 := bstep (se 1 (by rfl) ⟨3704912, by rfl⟩ : syracuseStep 4939883 = 7409825) B7409825
theorem B4874579 : Blo 1443541 4874579 := bstep (se 1 (by rfl) ⟨3655934, by rfl⟩ : syracuseStep 4874579 = 7311869) B7311869
theorem B5481017 : Blo 1443541 5481017 := bstep (se 2 (by rfl) ⟨2055381, by rfl⟩ : syracuseStep 5481017 = 4110763) B4110763
theorem B9880319 : Blo 1443541 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B4629287 : Blo 1443541 4629287 := bstep (se 1 (by rfl) ⟨3471965, by rfl⟩ : syracuseStep 4629287 = 6943931) B6943931
theorem B300139505 : Blo 1443541 300139505 := bstep (se 2 (by rfl) ⟨112552314, by rfl⟩ : syracuseStep 300139505 = 225104629) B225104629
theorem B59335739 : Blo 1443541 59335739 := bstep (se 1 (by rfl) ⟨44501804, by rfl⟩ : syracuseStep 59335739 = 89003609) B89003609
theorem B30057581 : Blo 1443541 30057581 := bstep (se 3 (by rfl) ⟨5635796, by rfl⟩ : syracuseStep 30057581 = 11271593) B11271593
theorem B18498739 : Blo 1443541 18498739 := bstep (se 1 (by rfl) ⟨13874054, by rfl⟩ : syracuseStep 18498739 = 27748109) B27748109
theorem B3654983 : Blo 1443541 3654983 := bstep (se 1 (by rfl) ⟨2741237, by rfl⟩ : syracuseStep 3654983 = 5482475) B5482475
theorem B3655145 : Blo 1443541 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B3655327 : Blo 1443541 3655327 := bstep (se 1 (by rfl) ⟨2741495, by rfl⟩ : syracuseStep 3655327 = 5482991) B5482991
theorem B6170347 : Blo 1443541 6170347 := bstep (se 1 (by rfl) ⟨4627760, by rfl⟩ : syracuseStep 6170347 = 9255521) B9255521
theorem B1443675 : Blo 1443541 1443675 := bstep (se 1 (by rfl) ⟨1082756, by rfl⟩ : syracuseStep 1443675 = 2165513) B2165513
theorem B1443835 : Blo 1443541 1443835 := bstep (se 1 (by rfl) ⟨1082876, by rfl⟩ : syracuseStep 1443835 = 2165753) B2165753
theorem B3655763 : Blo 1443541 3655763 := bstep (se 1 (by rfl) ⟨2741822, by rfl⟩ : syracuseStep 3655763 = 5483645) B5483645
theorem B10971935 : Blo 1443541 10971935 := bstep (se 1 (by rfl) ⟨8228951, by rfl⟩ : syracuseStep 10971935 = 16457903) B16457903
theorem B2165567 : Blo 1443541 2165567 := bstep (se 1 (by rfl) ⟨1624175, by rfl⟩ : syracuseStep 2165567 = 3248351) B3248351
theorem B9259879 : Blo 1443541 9259879 := bstep (se 1 (by rfl) ⟨6944909, by rfl⟩ : syracuseStep 9259879 = 13889819) B13889819
theorem B2165627 : Blo 1443541 2165627 := bstep (se 1 (by rfl) ⟨1624220, by rfl⟩ : syracuseStep 2165627 = 3248441) B3248441
theorem B1624999 : Blo 1443541 1624999 := bstep (se 1 (by rfl) ⟨1218749, by rfl⟩ : syracuseStep 1624999 = 2437499) B2437499
theorem B1444799 : Blo 1443541 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B1625071 : Blo 1443541 1625071 := bstep (se 1 (by rfl) ⟨1218803, by rfl⟩ : syracuseStep 1625071 = 2437607) B2437607
theorem B2165927 : Blo 1443541 2165927 := bstep (se 1 (by rfl) ⟨1624445, by rfl⟩ : syracuseStep 2165927 = 3248891) B3248891
theorem B1445055 : Blo 1443541 1445055 := bstep (se 1 (by rfl) ⟨1083791, by rfl⟩ : syracuseStep 1445055 = 2167583) B2167583
theorem B2165999 : Blo 1443541 2165999 := bstep (se 1 (by rfl) ⟨1624499, by rfl⟩ : syracuseStep 2165999 = 3248999) B3248999
theorem B1445167 : Blo 1443541 1445167 := bstep (se 1 (by rfl) ⟨1083875, by rfl⟩ : syracuseStep 1445167 = 2167751) B2167751
theorem B12512737 : Blo 1443541 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B1445375 : Blo 1443541 1445375 := bstep (se 1 (by rfl) ⟨1084031, by rfl⟩ : syracuseStep 1445375 = 2168063) B2168063
theorem B3657383 : Blo 1443541 3657383 := bstep (se 1 (by rfl) ⟨2743037, by rfl⟩ : syracuseStep 3657383 = 5486075) B5486075
theorem B27750113 : Blo 1443541 27750113 := bstep (se 2 (by rfl) ⟨10406292, by rfl⟩ : syracuseStep 27750113 = 20812585) B20812585
theorem B2166905 : Blo 1443541 2166905 := bstep (se 2 (by rfl) ⟨812589, by rfl⟩ : syracuseStep 2166905 = 1625179) B1625179
theorem B3657919 : Blo 1443541 3657919 := bstep (se 1 (by rfl) ⟨2743439, by rfl⟩ : syracuseStep 3657919 = 5486879) B5486879
theorem B4878575 : Blo 1443541 4878575 := bstep (se 1 (by rfl) ⟨3658931, by rfl⟩ : syracuseStep 4878575 = 7317863) B7317863
theorem B6173117 : Blo 1443541 6173117 := bstep (se 3 (by rfl) ⟨1157459, by rfl⟩ : syracuseStep 6173117 = 2314919) B2314919
theorem B10973879 : Blo 1443541 10973879 := bstep (se 1 (by rfl) ⟨8230409, by rfl⟩ : syracuseStep 10973879 = 16460819) B16460819
theorem B16446239 : Blo 1443541 16446239 := bstep (se 1 (by rfl) ⟨12334679, by rfl⟩ : syracuseStep 16446239 = 24669359) B24669359
theorem B2167721 : Blo 1443541 2167721 := bstep (se 2 (by rfl) ⟨812895, by rfl⟩ : syracuseStep 2167721 = 1625791) B1625791
theorem B4625711 : Blo 1443541 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B2168111 : Blo 1443541 2168111 := bstep (se 1 (by rfl) ⟨1626083, by rfl⟩ : syracuseStep 2168111 = 3252167) B3252167
theorem B5485907 : Blo 1443541 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B2168297 : Blo 1443541 2168297 := bstep (se 2 (by rfl) ⟨813111, by rfl⟩ : syracuseStep 2168297 = 1626223) B1626223
theorem B37017161 : Blo 1443541 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B10975337 : Blo 1443541 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B2603231 : Blo 1443541 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B8338135 : Blo 1443541 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B3472091 : Blo 1443541 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B16456445 : Blo 1443541 16456445 := bstep (se 3 (by rfl) ⟨3085583, by rfl⟩ : syracuseStep 16456445 = 6171167) B6171167
theorem B3251195 : Blo 1443541 3251195 := bstep (se 1 (by rfl) ⟨2438396, by rfl⟩ : syracuseStep 3251195 = 4876793) B4876793
theorem B7806041 : Blo 1443541 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B3251303 : Blo 1443541 3251303 := bstep (se 1 (by rfl) ⟨2438477, by rfl⟩ : syracuseStep 3251303 = 4876955) B4876955
theorem B5561789 : Blo 1443541 5561789 := bstep (se 3 (by rfl) ⟨1042835, by rfl⟩ : syracuseStep 5561789 = 2085671) B2085671
theorem B41622983 : Blo 1443541 41622983 := bstep (se 1 (by rfl) ⟨31217237, by rfl⟩ : syracuseStep 41622983 = 62434475) B62434475
theorem B3252203 : Blo 1443541 3252203 := bstep (se 1 (by rfl) ⟨2439152, by rfl⟩ : syracuseStep 3252203 = 4878305) B4878305
theorem B3293255 : Blo 1443541 3293255 := bstep (se 1 (by rfl) ⟨2469941, by rfl⟩ : syracuseStep 3293255 = 4939883) B4939883
theorem B3252383 : Blo 1443541 3252383 := bstep (se 1 (by rfl) ⟨2439287, by rfl⟩ : syracuseStep 3252383 = 4878575) B4878575
theorem B3654011 : Blo 1443541 3654011 := bstep (se 1 (by rfl) ⟨2740508, by rfl⟩ : syracuseStep 3654011 = 5481017) B5481017
theorem B7315919 : Blo 1443541 7315919 := bstep (se 1 (by rfl) ⟨5486939, by rfl⟩ : syracuseStep 7315919 = 10973879) B10973879
theorem B6586879 : Blo 1443541 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B11117513 : Blo 1443541 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B12346505 : Blo 1443541 12346505 := bstep (se 2 (by rfl) ⟨4629939, by rfl⟩ : syracuseStep 12346505 = 9259879) B9259879
theorem B7316891 : Blo 1443541 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B10970963 : Blo 1443541 10970963 := bstep (se 1 (by rfl) ⟨8228222, by rfl⟩ : syracuseStep 10970963 = 16456445) B16456445
theorem B1443711 : Blo 1443541 1443711 := bstep (se 1 (by rfl) ⟨1082783, by rfl⟩ : syracuseStep 1443711 = 2165567) B2165567
theorem B1443751 : Blo 1443541 1443751 := bstep (se 1 (by rfl) ⟨1082813, by rfl⟩ : syracuseStep 1443751 = 2165627) B2165627
theorem B5204027 : Blo 1443541 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B1443951 : Blo 1443541 1443951 := bstep (se 1 (by rfl) ⟨1082963, by rfl⟩ : syracuseStep 1443951 = 2165927) B2165927
theorem B1443999 : Blo 1443541 1443999 := bstep (se 1 (by rfl) ⟨1082999, by rfl⟩ : syracuseStep 1443999 = 2165999) B2165999
theorem B27748655 : Blo 1443541 27748655 := bstep (se 1 (by rfl) ⟨20811491, by rfl⟩ : syracuseStep 27748655 = 41622983) B41622983
theorem B8227129 : Blo 1443541 8227129 := bstep (se 2 (by rfl) ⟨3085173, by rfl⟩ : syracuseStep 8227129 = 6170347) B6170347
theorem B18500075 : Blo 1443541 18500075 := bstep (se 1 (by rfl) ⟨13875056, by rfl⟩ : syracuseStep 18500075 = 27750113) B27750113
theorem B66734597 : Blo 1443541 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B1444603 : Blo 1443541 1444603 := bstep (se 1 (by rfl) ⟨1083452, by rfl⟩ : syracuseStep 1444603 = 2166905) B2166905
theorem B4877225 : Blo 1443541 4877225 := bstep (se 2 (by rfl) ⟨1828959, by rfl⟩ : syracuseStep 4877225 = 3657919) B3657919
theorem B80153549 : Blo 1443541 80153549 := bstep (se 3 (by rfl) ⟨15028790, by rfl⟩ : syracuseStep 80153549 = 30057581) B30057581
theorem B4115411 : Blo 1443541 4115411 := bstep (se 1 (by rfl) ⟨3086558, by rfl⟩ : syracuseStep 4115411 = 6173117) B6173117
theorem B10964159 : Blo 1443541 10964159 := bstep (se 1 (by rfl) ⟨8223119, by rfl⟩ : syracuseStep 10964159 = 16446239) B16446239
theorem B1445147 : Blo 1443541 1445147 := bstep (se 1 (by rfl) ⟨1083860, by rfl⟩ : syracuseStep 1445147 = 2167721) B2167721
theorem B200093003 : Blo 1443541 200093003 := bstep (se 1 (by rfl) ⟨150069752, by rfl⟩ : syracuseStep 200093003 = 300139505) B300139505
theorem B3083807 : Blo 1443541 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B1445407 : Blo 1443541 1445407 := bstep (se 1 (by rfl) ⟨1084055, by rfl⟩ : syracuseStep 1445407 = 2168111) B2168111
theorem B2436655 : Blo 1443541 2436655 := bstep (se 1 (by rfl) ⟨1827491, by rfl⟩ : syracuseStep 2436655 = 3654983) B3654983
theorem B3657271 : Blo 1443541 3657271 := bstep (se 1 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 3657271 = 5485907) B5485907
theorem B2436763 : Blo 1443541 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B1445531 : Blo 1443541 1445531 := bstep (se 1 (by rfl) ⟨1084148, by rfl⟩ : syracuseStep 1445531 = 2168297) B2168297
theorem B24678107 : Blo 1443541 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B14831437 : Blo 1443541 14831437 := bstep (se 3 (by rfl) ⟨2780894, by rfl⟩ : syracuseStep 14831437 = 5561789) B5561789
theorem B2166665 : Blo 1443541 2166665 := bstep (se 2 (by rfl) ⟨812499, by rfl⟩ : syracuseStep 2166665 = 1624999) B1624999
theorem B2166761 : Blo 1443541 2166761 := bstep (se 2 (by rfl) ⟨812535, by rfl⟩ : syracuseStep 2166761 = 1625071) B1625071
theorem B2437175 : Blo 1443541 2437175 := bstep (se 1 (by rfl) ⟨1827881, by rfl⟩ : syracuseStep 2437175 = 3655763) B3655763
theorem B2314727 : Blo 1443541 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B2167463 : Blo 1443541 2167463 := bstep (se 1 (by rfl) ⟨1625597, by rfl⟩ : syracuseStep 2167463 = 3251195) B3251195
theorem B2167535 : Blo 1443541 2167535 := bstep (se 1 (by rfl) ⟨1625651, by rfl⟩ : syracuseStep 2167535 = 3251303) B3251303
theorem B2438255 : Blo 1443541 2438255 := bstep (se 1 (by rfl) ⟨1828691, by rfl⟩ : syracuseStep 2438255 = 3657383) B3657383
theorem B2168135 : Blo 1443541 2168135 := bstep (se 1 (by rfl) ⟨1626101, by rfl⟩ : syracuseStep 2168135 = 3252203) B3252203
theorem B3249719 : Blo 1443541 3249719 := bstep (se 1 (by rfl) ⟨2437289, by rfl⟩ : syracuseStep 3249719 = 4874579) B4874579
theorem B3086191 : Blo 1443541 3086191 := bstep (se 1 (by rfl) ⟨2314643, by rfl⟩ : syracuseStep 3086191 = 4629287) B4629287
theorem B39557159 : Blo 1443541 39557159 := bstep (se 1 (by rfl) ⟨29667869, by rfl⟩ : syracuseStep 39557159 = 59335739) B59335739
theorem B1735487 : Blo 1443541 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B24664985 : Blo 1443541 24664985 := bstep (se 2 (by rfl) ⟨9249369, by rfl⟩ : syracuseStep 24664985 = 18498739) B18498739
theorem B7314623 : Blo 1443541 7314623 := bstep (se 1 (by rfl) ⟨5485967, by rfl⟩ : syracuseStep 7314623 = 10971935) B10971935
theorem B4873769 : Blo 1443541 4873769 := bstep (se 2 (by rfl) ⟨1827663, by rfl⟩ : syracuseStep 4873769 = 3655327) B3655327
theorem B13877405 : Blo 1443541 13877405 := bstep (se 3 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 13877405 = 5204027) B5204027
theorem B8782013 : Blo 1443541 8782013 := bstep (se 3 (by rfl) ⟨1646627, by rfl⟩ : syracuseStep 8782013 = 3293255) B3293255
theorem B10969505 : Blo 1443541 10969505 := bstep (se 2 (by rfl) ⟨4113564, by rfl⟩ : syracuseStep 10969505 = 8227129) B8227129
theorem B8782505 : Blo 1443541 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B26371439 : Blo 1443541 26371439 := bstep (se 1 (by rfl) ⟨19778579, by rfl⟩ : syracuseStep 26371439 = 39557159) B39557159
theorem B18499103 : Blo 1443541 18499103 := bstep (se 1 (by rfl) ⟨13874327, by rfl⟩ : syracuseStep 18499103 = 27748655) B27748655
theorem B16443323 : Blo 1443541 16443323 := bstep (se 1 (by rfl) ⟨12332492, by rfl⟩ : syracuseStep 16443323 = 24664985) B24664985
theorem B4876361 : Blo 1443541 4876361 := bstep (se 2 (by rfl) ⟨1828635, by rfl⟩ : syracuseStep 4876361 = 3657271) B3657271
theorem B7309439 : Blo 1443541 7309439 := bstep (se 1 (by rfl) ⟨5482079, by rfl⟩ : syracuseStep 7309439 = 10964159) B10964159
theorem B4876415 : Blo 1443541 4876415 := bstep (se 1 (by rfl) ⟨3657311, by rfl⟩ : syracuseStep 4876415 = 7314623) B7314623
theorem B16452071 : Blo 1443541 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B4114921 : Blo 1443541 4114921 := bstep (se 2 (by rfl) ⟨1543095, by rfl⟩ : syracuseStep 4114921 = 3086191) B3086191
theorem B1444443 : Blo 1443541 1444443 := bstep (se 1 (by rfl) ⟨1083332, by rfl⟩ : syracuseStep 1444443 = 2166665) B2166665
theorem B1444507 : Blo 1443541 1444507 := bstep (se 1 (by rfl) ⟨1083380, by rfl⟩ : syracuseStep 1444507 = 2166761) B2166761
theorem B1624783 : Blo 1443541 1624783 := bstep (se 1 (by rfl) ⟨1218587, by rfl⟩ : syracuseStep 1624783 = 2437175) B2437175
theorem B2436007 : Blo 1443541 2436007 := bstep (se 1 (by rfl) ⟨1827005, by rfl⟩ : syracuseStep 2436007 = 3654011) B3654011
theorem B4877279 : Blo 1443541 4877279 := bstep (se 1 (by rfl) ⟨3657959, by rfl⟩ : syracuseStep 4877279 = 7315919) B7315919
theorem B1543151 : Blo 1443541 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B1444975 : Blo 1443541 1444975 := bstep (se 1 (by rfl) ⟨1083731, by rfl⟩ : syracuseStep 1444975 = 2167463) B2167463
theorem B1445023 : Blo 1443541 1445023 := bstep (se 1 (by rfl) ⟨1083767, by rfl⟩ : syracuseStep 1445023 = 2167535) B2167535
theorem B1625503 : Blo 1443541 1625503 := bstep (se 1 (by rfl) ⟨1219127, by rfl⟩ : syracuseStep 1625503 = 2438255) B2438255
theorem B1445423 : Blo 1443541 1445423 := bstep (se 1 (by rfl) ⟨1084067, by rfl⟩ : syracuseStep 1445423 = 2168135) B2168135
theorem B4877927 : Blo 1443541 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B2166479 : Blo 1443541 2166479 := bstep (se 1 (by rfl) ⟨1624859, by rfl⟩ : syracuseStep 2166479 = 3249719) B3249719
theorem B12333383 : Blo 1443541 12333383 := bstep (se 1 (by rfl) ⟨9250037, by rfl⟩ : syracuseStep 12333383 = 18500075) B18500075
theorem B3248873 : Blo 1443541 3248873 := bstep (se 2 (by rfl) ⟨1218327, by rfl⟩ : syracuseStep 3248873 = 2436655) B2436655
theorem B3249017 : Blo 1443541 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B133395335 : Blo 1443541 133395335 := bstep (se 1 (by rfl) ⟨100046501, by rfl⟩ : syracuseStep 133395335 = 200093003) B200093003
theorem B3249179 : Blo 1443541 3249179 := bstep (se 1 (by rfl) ⟨2436884, by rfl⟩ : syracuseStep 3249179 = 4873769) B4873769
theorem B2168255 : Blo 1443541 2168255 := bstep (se 1 (by rfl) ⟨1626191, by rfl⟩ : syracuseStep 2168255 = 3252383) B3252383
theorem B7411675 : Blo 1443541 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B18511861 : Blo 1443541 18511861 := bstep (se 5 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 18511861 = 1735487) B1735487
theorem B8231003 : Blo 1443541 8231003 := bstep (se 1 (by rfl) ⟨6173252, by rfl⟩ : syracuseStep 8231003 = 12346505) B12346505
theorem B7313975 : Blo 1443541 7313975 := bstep (se 1 (by rfl) ⟨5485481, by rfl⟩ : syracuseStep 7313975 = 10970963) B10970963
theorem B44489731 : Blo 1443541 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B3251483 : Blo 1443541 3251483 := bstep (se 1 (by rfl) ⟨2438612, by rfl⟩ : syracuseStep 3251483 = 4877225) B4877225
theorem B53435699 : Blo 1443541 53435699 := bstep (se 1 (by rfl) ⟨40076774, by rfl⟩ : syracuseStep 53435699 = 80153549) B80153549
theorem B2743607 : Blo 1443541 2743607 := bstep (se 1 (by rfl) ⟨2057705, by rfl⟩ : syracuseStep 2743607 = 4115411) B4115411
theorem B2055871 : Blo 1443541 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B19775249 : Blo 1443541 19775249 := bstep (se 2 (by rfl) ⟨7415718, by rfl⟩ : syracuseStep 19775249 = 14831437) B14831437
theorem B17580959 : Blo 1443541 17580959 := bstep (se 1 (by rfl) ⟨13185719, by rfl⟩ : syracuseStep 17580959 = 26371439) B26371439
theorem B10962215 : Blo 1443541 10962215 := bstep (se 1 (by rfl) ⟨8221661, by rfl⟩ : syracuseStep 10962215 = 16443323) B16443323
theorem B59319641 : Blo 1443541 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B4875983 : Blo 1443541 4875983 := bstep (se 1 (by rfl) ⟨3656987, by rfl⟩ : syracuseStep 4875983 = 7313975) B7313975
theorem B1829071 : Blo 1443541 1829071 := bstep (se 1 (by rfl) ⟨1371803, by rfl⟩ : syracuseStep 1829071 = 2743607) B2743607
theorem B1444319 : Blo 1443541 1444319 := bstep (se 1 (by rfl) ⟨1083239, by rfl⟩ : syracuseStep 1444319 = 2166479) B2166479
theorem B13183499 : Blo 1443541 13183499 := bstep (se 1 (by rfl) ⟨9887624, by rfl⟩ : syracuseStep 13183499 = 19775249) B19775249
theorem B9882233 : Blo 1443541 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B4115069 : Blo 1443541 4115069 := bstep (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) B1543151
theorem B9251603 : Blo 1443541 9251603 := bstep (se 1 (by rfl) ⟨6938702, by rfl⟩ : syracuseStep 9251603 = 13877405) B13877405
theorem B2165915 : Blo 1443541 2165915 := bstep (se 1 (by rfl) ⟨1624436, by rfl⟩ : syracuseStep 2165915 = 3248873) B3248873
theorem B2166011 : Blo 1443541 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B2166119 : Blo 1443541 2166119 := bstep (se 1 (by rfl) ⟨1624589, by rfl⟩ : syracuseStep 2166119 = 3249179) B3249179
theorem B2166377 : Blo 1443541 2166377 := bstep (se 2 (by rfl) ⟨812391, by rfl⟩ : syracuseStep 2166377 = 1624783) B1624783
theorem B1445503 : Blo 1443541 1445503 := bstep (se 1 (by rfl) ⟨1084127, by rfl⟩ : syracuseStep 1445503 = 2168255) B2168255
theorem B10964645 : Blo 1443541 10964645 := bstep (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) B2055871
theorem B12332735 : Blo 1443541 12332735 := bstep (se 1 (by rfl) ⟨9249551, by rfl⟩ : syracuseStep 12332735 = 18499103) B18499103
theorem B3248009 : Blo 1443541 3248009 := bstep (se 2 (by rfl) ⟨1218003, by rfl⟩ : syracuseStep 3248009 = 2436007) B2436007
theorem B2167337 : Blo 1443541 2167337 := bstep (se 2 (by rfl) ⟨812751, by rfl⟩ : syracuseStep 2167337 = 1625503) B1625503
theorem B2167655 : Blo 1443541 2167655 := bstep (se 1 (by rfl) ⟨1625741, by rfl⟩ : syracuseStep 2167655 = 3251483) B3251483
theorem B35623799 : Blo 1443541 35623799 := bstep (se 1 (by rfl) ⟨26717849, by rfl⟩ : syracuseStep 35623799 = 53435699) B53435699
theorem B5854675 : Blo 1443541 5854675 := bstep (se 1 (by rfl) ⟨4391006, by rfl⟩ : syracuseStep 5854675 = 8782013) B8782013
theorem B8222255 : Blo 1443541 8222255 := bstep (se 1 (by rfl) ⟨6166691, by rfl⟩ : syracuseStep 8222255 = 12333383) B12333383
theorem B7313003 : Blo 1443541 7313003 := bstep (se 1 (by rfl) ⟨5484752, by rfl⟩ : syracuseStep 7313003 = 10969505) B10969505
theorem B5855003 : Blo 1443541 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B88930223 : Blo 1443541 88930223 := bstep (se 1 (by rfl) ⟨66697667, by rfl⟩ : syracuseStep 88930223 = 133395335) B133395335
theorem B5486561 : Blo 1443541 5486561 := bstep (se 2 (by rfl) ⟨2057460, by rfl⟩ : syracuseStep 5486561 = 4114921) B4114921
theorem B3250907 : Blo 1443541 3250907 := bstep (se 1 (by rfl) ⟨2438180, by rfl⟩ : syracuseStep 3250907 = 4876361) B4876361
theorem B5487335 : Blo 1443541 5487335 := bstep (se 1 (by rfl) ⟨4115501, by rfl⟩ : syracuseStep 5487335 = 8231003) B8231003
theorem B4872959 : Blo 1443541 4872959 := bstep (se 1 (by rfl) ⟨3654719, by rfl⟩ : syracuseStep 4872959 = 7309439) B7309439
theorem B3250943 : Blo 1443541 3250943 := bstep (se 1 (by rfl) ⟨2438207, by rfl⟩ : syracuseStep 3250943 = 4876415) B4876415
theorem B10968047 : Blo 1443541 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B3251519 : Blo 1443541 3251519 := bstep (se 1 (by rfl) ⟨2438639, by rfl⟩ : syracuseStep 3251519 = 4877279) B4877279
theorem B3251951 : Blo 1443541 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B24682481 : Blo 1443541 24682481 := bstep (se 2 (by rfl) ⟨9255930, by rfl⟩ : syracuseStep 24682481 = 18511861) B18511861
theorem B23749199 : Blo 1443541 23749199 := bstep (se 1 (by rfl) ⟨17811899, by rfl⟩ : syracuseStep 23749199 = 35623799) B35623799
theorem B7308143 : Blo 1443541 7308143 := bstep (se 1 (by rfl) ⟨5481107, by rfl⟩ : syracuseStep 7308143 = 10962215) B10962215
theorem B5481503 : Blo 1443541 5481503 := bstep (se 1 (by rfl) ⟨4111127, by rfl⟩ : syracuseStep 5481503 = 8222255) B8222255
theorem B4875335 : Blo 1443541 4875335 := bstep (se 1 (by rfl) ⟨3656501, by rfl⟩ : syracuseStep 4875335 = 7313003) B7313003
theorem B59286815 : Blo 1443541 59286815 := bstep (se 1 (by rfl) ⟨44465111, by rfl⟩ : syracuseStep 59286815 = 88930223) B88930223
theorem B6588155 : Blo 1443541 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B1443943 : Blo 1443541 1443943 := bstep (se 1 (by rfl) ⟨1082957, by rfl⟩ : syracuseStep 1443943 = 2165915) B2165915
theorem B1444007 : Blo 1443541 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B1444079 : Blo 1443541 1444079 := bstep (se 1 (by rfl) ⟨1083059, by rfl⟩ : syracuseStep 1444079 = 2166119) B2166119
theorem B1444251 : Blo 1443541 1444251 := bstep (se 1 (by rfl) ⟨1083188, by rfl⟩ : syracuseStep 1444251 = 2166377) B2166377
theorem B7309763 : Blo 1443541 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B2165339 : Blo 1443541 2165339 := bstep (se 1 (by rfl) ⟨1624004, by rfl⟩ : syracuseStep 2165339 = 3248009) B3248009
theorem B1444891 : Blo 1443541 1444891 := bstep (se 1 (by rfl) ⟨1083668, by rfl⟩ : syracuseStep 1444891 = 2167337) B2167337
theorem B1445103 : Blo 1443541 1445103 := bstep (se 1 (by rfl) ⟨1083827, by rfl⟩ : syracuseStep 1445103 = 2167655) B2167655
theorem B3903335 : Blo 1443541 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B3657707 : Blo 1443541 3657707 := bstep (se 1 (by rfl) ⟨2743280, by rfl⟩ : syracuseStep 3657707 = 5486561) B5486561
theorem B2167271 : Blo 1443541 2167271 := bstep (se 1 (by rfl) ⟨1625453, by rfl⟩ : syracuseStep 2167271 = 3250907) B3250907
theorem B3658223 : Blo 1443541 3658223 := bstep (se 1 (by rfl) ⟨2743667, by rfl⟩ : syracuseStep 3658223 = 5487335) B5487335
theorem B3248639 : Blo 1443541 3248639 := bstep (se 1 (by rfl) ⟨2436479, by rfl⟩ : syracuseStep 3248639 = 4872959) B4872959
theorem B2167295 : Blo 1443541 2167295 := bstep (se 1 (by rfl) ⟨1625471, by rfl⟩ : syracuseStep 2167295 = 3250943) B3250943
theorem B7312031 : Blo 1443541 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B2167679 : Blo 1443541 2167679 := bstep (se 1 (by rfl) ⟨1625759, by rfl⟩ : syracuseStep 2167679 = 3251519) B3251519
theorem B8221823 : Blo 1443541 8221823 := bstep (se 1 (by rfl) ⟨6166367, by rfl⟩ : syracuseStep 8221823 = 12332735) B12332735
theorem B2167967 : Blo 1443541 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B16454987 : Blo 1443541 16454987 := bstep (se 1 (by rfl) ⟨12341240, by rfl⟩ : syracuseStep 16454987 = 24682481) B24682481
theorem B2438761 : Blo 1443541 2438761 := bstep (se 2 (by rfl) ⟨914535, by rfl⟩ : syracuseStep 2438761 = 1829071) B1829071
theorem B11720639 : Blo 1443541 11720639 := bstep (se 1 (by rfl) ⟨8790479, by rfl⟩ : syracuseStep 11720639 = 17580959) B17580959
theorem B158185709 : Blo 1443541 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B3250655 : Blo 1443541 3250655 := bstep (se 1 (by rfl) ⟨2437991, by rfl⟩ : syracuseStep 3250655 = 4875983) B4875983
theorem B8788999 : Blo 1443541 8788999 := bstep (se 1 (by rfl) ⟨6591749, by rfl⟩ : syracuseStep 8788999 = 13183499) B13183499
theorem B2743379 : Blo 1443541 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B6167735 : Blo 1443541 6167735 := bstep (se 1 (by rfl) ⟨4625801, by rfl⟩ : syracuseStep 6167735 = 9251603) B9251603
theorem B7806233 : Blo 1443541 7806233 := bstep (se 2 (by rfl) ⟨2927337, by rfl⟩ : syracuseStep 7806233 = 5854675) B5854675
theorem B4874687 : Blo 1443541 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B3654335 : Blo 1443541 3654335 := bstep (se 1 (by rfl) ⟨2740751, by rfl⟩ : syracuseStep 3654335 = 5481503) B5481503
theorem B5481215 : Blo 1443541 5481215 := bstep (se 1 (by rfl) ⟨4110911, by rfl⟩ : syracuseStep 5481215 = 8221823) B8221823
theorem B10969991 : Blo 1443541 10969991 := bstep (se 1 (by rfl) ⟨8227493, by rfl⟩ : syracuseStep 10969991 = 16454987) B16454987
theorem B105457139 : Blo 1443541 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B1443559 : Blo 1443541 1443559 := bstep (se 1 (by rfl) ⟨1082669, by rfl⟩ : syracuseStep 1443559 = 2165339) B2165339
theorem B1828919 : Blo 1443541 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B5204155 : Blo 1443541 5204155 := bstep (se 1 (by rfl) ⟨3903116, by rfl⟩ : syracuseStep 5204155 = 7806233) B7806233
theorem B1444847 : Blo 1443541 1444847 := bstep (se 1 (by rfl) ⟨1083635, by rfl⟩ : syracuseStep 1444847 = 2167271) B2167271
theorem B2165759 : Blo 1443541 2165759 := bstep (se 1 (by rfl) ⟨1624319, by rfl⟩ : syracuseStep 2165759 = 3248639) B3248639
theorem B1444863 : Blo 1443541 1444863 := bstep (se 1 (by rfl) ⟨1083647, by rfl⟩ : syracuseStep 1444863 = 2167295) B2167295
theorem B1445119 : Blo 1443541 1445119 := bstep (se 1 (by rfl) ⟨1083839, by rfl⟩ : syracuseStep 1445119 = 2167679) B2167679
theorem B1445311 : Blo 1443541 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B11718665 : Blo 1443541 11718665 := bstep (se 2 (by rfl) ⟨4394499, by rfl⟩ : syracuseStep 11718665 = 8788999) B8788999
theorem B2167103 : Blo 1443541 2167103 := bstep (se 1 (by rfl) ⟨1625327, by rfl⟩ : syracuseStep 2167103 = 3250655) B3250655
theorem B17568413 : Blo 1443541 17568413 := bstep (se 3 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 17568413 = 6588155) B6588155
theorem B2602223 : Blo 1443541 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B2438471 : Blo 1443541 2438471 := bstep (se 1 (by rfl) ⟨1828853, by rfl⟩ : syracuseStep 2438471 = 3657707) B3657707
theorem B2438815 : Blo 1443541 2438815 := bstep (se 1 (by rfl) ⟨1829111, by rfl⟩ : syracuseStep 2438815 = 3658223) B3658223
theorem B15832799 : Blo 1443541 15832799 := bstep (se 1 (by rfl) ⟨11874599, by rfl⟩ : syracuseStep 15832799 = 23749199) B23749199
theorem B4872095 : Blo 1443541 4872095 := bstep (se 1 (by rfl) ⟨3654071, by rfl⟩ : syracuseStep 4872095 = 7308143) B7308143
theorem B3250223 : Blo 1443541 3250223 := bstep (se 1 (by rfl) ⟨2437667, by rfl⟩ : syracuseStep 3250223 = 4875335) B4875335
theorem B39524543 : Blo 1443541 39524543 := bstep (se 1 (by rfl) ⟨29643407, by rfl⟩ : syracuseStep 39524543 = 59286815) B59286815
theorem B7813759 : Blo 1443541 7813759 := bstep (se 1 (by rfl) ⟨5860319, by rfl⟩ : syracuseStep 7813759 = 11720639) B11720639
theorem B4873175 : Blo 1443541 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B4111823 : Blo 1443541 4111823 := bstep (se 1 (by rfl) ⟨3083867, by rfl⟩ : syracuseStep 4111823 = 6167735) B6167735
theorem B3251681 : Blo 1443541 3251681 := bstep (se 2 (by rfl) ⟨1219380, by rfl⟩ : syracuseStep 3251681 = 2438761) B2438761
theorem B6938873 : Blo 1443541 6938873 := bstep (se 2 (by rfl) ⟨2602077, by rfl⟩ : syracuseStep 6938873 = 5204155) B5204155
theorem B3654143 : Blo 1443541 3654143 := bstep (se 1 (by rfl) ⟨2740607, by rfl⟩ : syracuseStep 3654143 = 5481215) B5481215
theorem B70304759 : Blo 1443541 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B1443839 : Blo 1443541 1443839 := bstep (se 1 (by rfl) ⟨1082879, by rfl⟩ : syracuseStep 1443839 = 2165759) B2165759
theorem B4877117 : Blo 1443541 4877117 := bstep (se 3 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 4877117 = 1828919) B1828919
theorem B1444735 : Blo 1443541 1444735 := bstep (se 1 (by rfl) ⟨1083551, by rfl⟩ : syracuseStep 1444735 = 2167103) B2167103
theorem B2436223 : Blo 1443541 2436223 := bstep (se 1 (by rfl) ⟨1827167, by rfl⟩ : syracuseStep 2436223 = 3654335) B3654335
theorem B1625647 : Blo 1443541 1625647 := bstep (se 1 (by rfl) ⟨1219235, by rfl⟩ : syracuseStep 1625647 = 2438471) B2438471
theorem B10555199 : Blo 1443541 10555199 := bstep (se 1 (by rfl) ⟨7916399, by rfl⟩ : syracuseStep 10555199 = 15832799) B15832799
theorem B3248063 : Blo 1443541 3248063 := bstep (se 1 (by rfl) ⟨2436047, by rfl⟩ : syracuseStep 3248063 = 4872095) B4872095
theorem B2166815 : Blo 1443541 2166815 := bstep (se 1 (by rfl) ⟨1625111, by rfl⟩ : syracuseStep 2166815 = 3250223) B3250223
theorem B26349695 : Blo 1443541 26349695 := bstep (se 1 (by rfl) ⟨19762271, by rfl⟩ : syracuseStep 26349695 = 39524543) B39524543
theorem B3248783 : Blo 1443541 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B2741215 : Blo 1443541 2741215 := bstep (se 1 (by rfl) ⟨2055911, by rfl⟩ : syracuseStep 2741215 = 4111823) B4111823
theorem B2167787 : Blo 1443541 2167787 := bstep (se 1 (by rfl) ⟨1625840, by rfl⟩ : syracuseStep 2167787 = 3251681) B3251681
theorem B7812443 : Blo 1443541 7812443 := bstep (se 1 (by rfl) ⟨5859332, by rfl⟩ : syracuseStep 7812443 = 11718665) B11718665
theorem B3249791 : Blo 1443541 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B11712275 : Blo 1443541 11712275 := bstep (se 1 (by rfl) ⟨8784206, by rfl⟩ : syracuseStep 11712275 = 17568413) B17568413
theorem B7313327 : Blo 1443541 7313327 := bstep (se 1 (by rfl) ⟨5484995, by rfl⟩ : syracuseStep 7313327 = 10969991) B10969991
theorem B1734815 : Blo 1443541 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B10418345 : Blo 1443541 10418345 := bstep (se 2 (by rfl) ⟨3906879, by rfl⟩ : syracuseStep 10418345 = 7813759) B7813759
theorem B3251753 : Blo 1443541 3251753 := bstep (se 2 (by rfl) ⟨1219407, by rfl⟩ : syracuseStep 3251753 = 2438815) B2438815
theorem B7808183 : Blo 1443541 7808183 := bstep (se 1 (by rfl) ⟨5856137, by rfl⟩ : syracuseStep 7808183 = 11712275) B11712275
theorem B4875551 : Blo 1443541 4875551 := bstep (se 1 (by rfl) ⟨3656663, by rfl⟩ : syracuseStep 4875551 = 7313327) B7313327
theorem B3654953 : Blo 1443541 3654953 := bstep (se 2 (by rfl) ⟨1370607, by rfl⟩ : syracuseStep 3654953 = 2741215) B2741215
theorem B2165375 : Blo 1443541 2165375 := bstep (se 1 (by rfl) ⟨1624031, by rfl⟩ : syracuseStep 2165375 = 3248063) B3248063
theorem B1444543 : Blo 1443541 1444543 := bstep (se 1 (by rfl) ⟨1083407, by rfl⟩ : syracuseStep 1444543 = 2166815) B2166815
theorem B17566463 : Blo 1443541 17566463 := bstep (se 1 (by rfl) ⟨13174847, by rfl⟩ : syracuseStep 17566463 = 26349695) B26349695
theorem B2436095 : Blo 1443541 2436095 := bstep (se 1 (by rfl) ⟨1827071, by rfl⟩ : syracuseStep 2436095 = 3654143) B3654143
theorem B2165855 : Blo 1443541 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B1445191 : Blo 1443541 1445191 := bstep (se 1 (by rfl) ⟨1083893, by rfl⟩ : syracuseStep 1445191 = 2167787) B2167787
theorem B46869839 : Blo 1443541 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B2166527 : Blo 1443541 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B3248297 : Blo 1443541 3248297 := bstep (se 2 (by rfl) ⟨1218111, by rfl⟩ : syracuseStep 3248297 = 2436223) B2436223
theorem B2167529 : Blo 1443541 2167529 := bstep (se 2 (by rfl) ⟨812823, by rfl⟩ : syracuseStep 2167529 = 1625647) B1625647
theorem B2167835 : Blo 1443541 2167835 := bstep (se 1 (by rfl) ⟨1625876, by rfl⟩ : syracuseStep 2167835 = 3251753) B3251753
theorem B4625915 : Blo 1443541 4625915 := bstep (se 1 (by rfl) ⟨3469436, by rfl⟩ : syracuseStep 4625915 = 6938873) B6938873
theorem B4626173 : Blo 1443541 4626173 := bstep (se 3 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 4626173 = 1734815) B1734815
theorem B5208295 : Blo 1443541 5208295 := bstep (se 1 (by rfl) ⟨3906221, by rfl⟩ : syracuseStep 5208295 = 7812443) B7812443
theorem B6945563 : Blo 1443541 6945563 := bstep (se 1 (by rfl) ⟨5209172, by rfl⟩ : syracuseStep 6945563 = 10418345) B10418345
theorem B3251411 : Blo 1443541 3251411 := bstep (se 1 (by rfl) ⟨2438558, by rfl⟩ : syracuseStep 3251411 = 4877117) B4877117
theorem B7036799 : Blo 1443541 7036799 := bstep (se 1 (by rfl) ⟨5277599, by rfl⟩ : syracuseStep 7036799 = 10555199) B10555199
theorem B1443583 : Blo 1443541 1443583 := bstep (se 1 (by rfl) ⟨1082687, by rfl⟩ : syracuseStep 1443583 = 2165375) B2165375
theorem B4630375 : Blo 1443541 4630375 := bstep (se 1 (by rfl) ⟨3472781, by rfl⟩ : syracuseStep 4630375 = 6945563) B6945563
theorem B1624063 : Blo 1443541 1624063 := bstep (se 1 (by rfl) ⟨1218047, by rfl⟩ : syracuseStep 1624063 = 2436095) B2436095
theorem B1443903 : Blo 1443541 1443903 := bstep (se 1 (by rfl) ⟨1082927, by rfl⟩ : syracuseStep 1443903 = 2165855) B2165855
theorem B31246559 : Blo 1443541 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B1444351 : Blo 1443541 1444351 := bstep (se 1 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 1444351 = 2166527) B2166527
theorem B2165531 : Blo 1443541 2165531 := bstep (se 1 (by rfl) ⟨1624148, by rfl⟩ : syracuseStep 2165531 = 3248297) B3248297
theorem B1445019 : Blo 1443541 1445019 := bstep (se 1 (by rfl) ⟨1083764, by rfl⟩ : syracuseStep 1445019 = 2167529) B2167529
theorem B1445223 : Blo 1443541 1445223 := bstep (se 1 (by rfl) ⟨1083917, by rfl⟩ : syracuseStep 1445223 = 2167835) B2167835
theorem B5205455 : Blo 1443541 5205455 := bstep (se 1 (by rfl) ⟨3904091, by rfl⟩ : syracuseStep 5205455 = 7808183) B7808183
theorem B2436635 : Blo 1443541 2436635 := bstep (se 1 (by rfl) ⟨1827476, by rfl⟩ : syracuseStep 2436635 = 3654953) B3654953
theorem B3084115 : Blo 1443541 3084115 := bstep (se 1 (by rfl) ⟨2313086, by rfl⟩ : syracuseStep 3084115 = 4626173) B4626173
theorem B11710975 : Blo 1443541 11710975 := bstep (se 1 (by rfl) ⟨8783231, by rfl⟩ : syracuseStep 11710975 = 17566463) B17566463
theorem B2167607 : Blo 1443541 2167607 := bstep (se 1 (by rfl) ⟨1625705, by rfl⟩ : syracuseStep 2167607 = 3251411) B3251411
theorem B18764797 : Blo 1443541 18764797 := bstep (se 3 (by rfl) ⟨3518399, by rfl⟩ : syracuseStep 18764797 = 7036799) B7036799
theorem B6944393 : Blo 1443541 6944393 := bstep (se 2 (by rfl) ⟨2604147, by rfl⟩ : syracuseStep 6944393 = 5208295) B5208295
theorem B3250367 : Blo 1443541 3250367 := bstep (se 1 (by rfl) ⟨2437775, by rfl⟩ : syracuseStep 3250367 = 4875551) B4875551
theorem B12335773 : Blo 1443541 12335773 := bstep (se 3 (by rfl) ⟨2312957, by rfl⟩ : syracuseStep 12335773 = 4625915) B4625915
theorem B15614633 : Blo 1443541 15614633 := bstep (se 2 (by rfl) ⟨5855487, by rfl⟩ : syracuseStep 15614633 = 11710975) B11710975
theorem B4629595 : Blo 1443541 4629595 := bstep (se 1 (by rfl) ⟨3472196, by rfl⟩ : syracuseStep 4629595 = 6944393) B6944393
theorem B25019729 : Blo 1443541 25019729 := bstep (se 2 (by rfl) ⟨9382398, by rfl⟩ : syracuseStep 25019729 = 18764797) B18764797
theorem B1443687 : Blo 1443541 1443687 := bstep (se 1 (by rfl) ⟨1082765, by rfl⟩ : syracuseStep 1443687 = 2165531) B2165531
theorem B1624423 : Blo 1443541 1624423 := bstep (se 1 (by rfl) ⟨1218317, by rfl⟩ : syracuseStep 1624423 = 2436635) B2436635
theorem B2165417 : Blo 1443541 2165417 := bstep (se 2 (by rfl) ⟨812031, by rfl⟩ : syracuseStep 2165417 = 1624063) B1624063
theorem B1445071 : Blo 1443541 1445071 := bstep (se 1 (by rfl) ⟨1083803, by rfl⟩ : syracuseStep 1445071 = 2167607) B2167607
theorem B2166911 : Blo 1443541 2166911 := bstep (se 1 (by rfl) ⟨1625183, by rfl⟩ : syracuseStep 2166911 = 3250367) B3250367
theorem B3470303 : Blo 1443541 3470303 := bstep (se 1 (by rfl) ⟨2602727, by rfl⟩ : syracuseStep 3470303 = 5205455) B5205455
theorem B6173833 : Blo 1443541 6173833 := bstep (se 2 (by rfl) ⟨2315187, by rfl⟩ : syracuseStep 6173833 = 4630375) B4630375
theorem B16447697 : Blo 1443541 16447697 := bstep (se 2 (by rfl) ⟨6167886, by rfl⟩ : syracuseStep 16447697 = 12335773) B12335773
theorem B20831039 : Blo 1443541 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B4112153 : Blo 1443541 4112153 := bstep (se 2 (by rfl) ⟨1542057, by rfl⟩ : syracuseStep 4112153 = 3084115) B3084115
theorem B16679819 : Blo 1443541 16679819 := bstep (se 1 (by rfl) ⟨12509864, by rfl⟩ : syracuseStep 16679819 = 25019729) B25019729
theorem B1443611 : Blo 1443541 1443611 := bstep (se 1 (by rfl) ⟨1082708, by rfl⟩ : syracuseStep 1443611 = 2165417) B2165417
theorem B13887359 : Blo 1443541 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B1444607 : Blo 1443541 1444607 := bstep (se 1 (by rfl) ⟨1083455, by rfl⟩ : syracuseStep 1444607 = 2166911) B2166911
theorem B2165897 : Blo 1443541 2165897 := bstep (se 2 (by rfl) ⟨812211, by rfl⟩ : syracuseStep 2165897 = 1624423) B1624423
theorem B2313535 : Blo 1443541 2313535 := bstep (se 1 (by rfl) ⟨1735151, by rfl⟩ : syracuseStep 2313535 = 3470303) B3470303
theorem B6172793 : Blo 1443541 6172793 := bstep (se 2 (by rfl) ⟨2314797, by rfl⟩ : syracuseStep 6172793 = 4629595) B4629595
theorem B10965131 : Blo 1443541 10965131 := bstep (se 1 (by rfl) ⟨8223848, by rfl⟩ : syracuseStep 10965131 = 16447697) B16447697
theorem B2741435 : Blo 1443541 2741435 := bstep (se 1 (by rfl) ⟨2056076, by rfl⟩ : syracuseStep 2741435 = 4112153) B4112153
theorem B10409755 : Blo 1443541 10409755 := bstep (se 1 (by rfl) ⟨7807316, by rfl⟩ : syracuseStep 10409755 = 15614633) B15614633
theorem B8231777 : Blo 1443541 8231777 := bstep (se 2 (by rfl) ⟨3086916, by rfl⟩ : syracuseStep 8231777 = 6173833) B6173833
theorem B1827623 : Blo 1443541 1827623 := bstep (se 1 (by rfl) ⟨1370717, by rfl⟩ : syracuseStep 1827623 = 2741435) B2741435
theorem B9258239 : Blo 1443541 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B1443931 : Blo 1443541 1443931 := bstep (se 1 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 1443931 = 2165897) B2165897
theorem B13879673 : Blo 1443541 13879673 := bstep (se 2 (by rfl) ⟨5204877, by rfl⟩ : syracuseStep 13879673 = 10409755) B10409755
theorem B4115195 : Blo 1443541 4115195 := bstep (se 1 (by rfl) ⟨3086396, by rfl⟩ : syracuseStep 4115195 = 6172793) B6172793
theorem B7310087 : Blo 1443541 7310087 := bstep (se 1 (by rfl) ⟨5482565, by rfl⟩ : syracuseStep 7310087 = 10965131) B10965131
theorem B11119879 : Blo 1443541 11119879 := bstep (se 1 (by rfl) ⟨8339909, by rfl⟩ : syracuseStep 11119879 = 16679819) B16679819
theorem B3084713 : Blo 1443541 3084713 := bstep (se 2 (by rfl) ⟨1156767, by rfl⟩ : syracuseStep 3084713 = 2313535) B2313535
theorem B5487851 : Blo 1443541 5487851 := bstep (se 1 (by rfl) ⟨4115888, by rfl⟩ : syracuseStep 5487851 = 8231777) B8231777
theorem B2056475 : Blo 1443541 2056475 := bstep (se 1 (by rfl) ⟨1542356, by rfl⟩ : syracuseStep 2056475 = 3084713) B3084713
theorem B6172159 : Blo 1443541 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B9253115 : Blo 1443541 9253115 := bstep (se 1 (by rfl) ⟨6939836, by rfl⟩ : syracuseStep 9253115 = 13879673) B13879673
theorem B3658567 : Blo 1443541 3658567 := bstep (se 1 (by rfl) ⟨2743925, by rfl⟩ : syracuseStep 3658567 = 5487851) B5487851
theorem B14826505 : Blo 1443541 14826505 := bstep (se 2 (by rfl) ⟨5559939, by rfl⟩ : syracuseStep 14826505 = 11119879) B11119879
theorem B2743463 : Blo 1443541 2743463 := bstep (se 1 (by rfl) ⟨2057597, by rfl⟩ : syracuseStep 2743463 = 4115195) B4115195
theorem B4873391 : Blo 1443541 4873391 := bstep (se 1 (by rfl) ⟨3655043, by rfl⟩ : syracuseStep 4873391 = 7310087) B7310087
theorem B4873661 : Blo 1443541 4873661 := bstep (se 3 (by rfl) ⟨913811, by rfl⟩ : syracuseStep 4873661 = 1827623) B1827623
theorem B6168743 : Blo 1443541 6168743 := bstep (se 1 (by rfl) ⟨4626557, by rfl⟩ : syracuseStep 6168743 = 9253115) B9253115
theorem B19768673 : Blo 1443541 19768673 := bstep (se 2 (by rfl) ⟨7413252, by rfl⟩ : syracuseStep 19768673 = 14826505) B14826505
theorem B1828975 : Blo 1443541 1828975 := bstep (se 1 (by rfl) ⟨1371731, by rfl⟩ : syracuseStep 1828975 = 2743463) B2743463
theorem B5483933 : Blo 1443541 5483933 := bstep (se 3 (by rfl) ⟨1028237, by rfl⟩ : syracuseStep 5483933 = 2056475) B2056475
theorem B4878089 : Blo 1443541 4878089 := bstep (se 2 (by rfl) ⟨1829283, by rfl⟩ : syracuseStep 4878089 = 3658567) B3658567
theorem B8229545 : Blo 1443541 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B3248927 : Blo 1443541 3248927 := bstep (se 1 (by rfl) ⟨2436695, by rfl⟩ : syracuseStep 3248927 = 4873391) B4873391
theorem B3249107 : Blo 1443541 3249107 := bstep (se 1 (by rfl) ⟨2436830, by rfl⟩ : syracuseStep 3249107 = 4873661) B4873661
theorem B4112495 : Blo 1443541 4112495 := bstep (se 1 (by rfl) ⟨3084371, by rfl⟩ : syracuseStep 4112495 = 6168743) B6168743
theorem B3655955 : Blo 1443541 3655955 := bstep (se 1 (by rfl) ⟨2741966, by rfl⟩ : syracuseStep 3655955 = 5483933) B5483933
theorem B2165951 : Blo 1443541 2165951 := bstep (se 1 (by rfl) ⟨1624463, by rfl⟩ : syracuseStep 2165951 = 3248927) B3248927
theorem B2166071 : Blo 1443541 2166071 := bstep (se 1 (by rfl) ⟨1624553, by rfl⟩ : syracuseStep 2166071 = 3249107) B3249107
theorem B2438633 : Blo 1443541 2438633 := bstep (se 2 (by rfl) ⟨914487, by rfl⟩ : syracuseStep 2438633 = 1828975) B1828975
theorem B5486363 : Blo 1443541 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B13179115 : Blo 1443541 13179115 := bstep (se 1 (by rfl) ⟨9884336, by rfl⟩ : syracuseStep 13179115 = 19768673) B19768673
theorem B3252059 : Blo 1443541 3252059 := bstep (se 1 (by rfl) ⟨2439044, by rfl⟩ : syracuseStep 3252059 = 4878089) B4878089
theorem B17572153 : Blo 1443541 17572153 := bstep (se 2 (by rfl) ⟨6589557, by rfl⟩ : syracuseStep 17572153 = 13179115) B13179115
theorem B1443967 : Blo 1443541 1443967 := bstep (se 1 (by rfl) ⟨1082975, by rfl⟩ : syracuseStep 1443967 = 2165951) B2165951
theorem B1444047 : Blo 1443541 1444047 := bstep (se 1 (by rfl) ⟨1083035, by rfl⟩ : syracuseStep 1444047 = 2166071) B2166071
theorem B1625755 : Blo 1443541 1625755 := bstep (se 1 (by rfl) ⟨1219316, by rfl⟩ : syracuseStep 1625755 = 2438633) B2438633
theorem B3657575 : Blo 1443541 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B2437303 : Blo 1443541 2437303 := bstep (se 1 (by rfl) ⟨1827977, by rfl⟩ : syracuseStep 2437303 = 3655955) B3655955
theorem B2168039 : Blo 1443541 2168039 := bstep (se 1 (by rfl) ⟨1626029, by rfl⟩ : syracuseStep 2168039 = 3252059) B3252059
theorem B2741663 : Blo 1443541 2741663 := bstep (se 1 (by rfl) ⟨2056247, by rfl⟩ : syracuseStep 2741663 = 4112495) B4112495
theorem B23429537 : Blo 1443541 23429537 := bstep (se 2 (by rfl) ⟨8786076, by rfl⟩ : syracuseStep 23429537 = 17572153) B17572153
theorem B1827775 : Blo 1443541 1827775 := bstep (se 1 (by rfl) ⟨1370831, by rfl⟩ : syracuseStep 1827775 = 2741663) B2741663
theorem B1445359 : Blo 1443541 1445359 := bstep (se 1 (by rfl) ⟨1084019, by rfl⟩ : syracuseStep 1445359 = 2168039) B2168039
theorem B2167673 : Blo 1443541 2167673 := bstep (se 2 (by rfl) ⟨812877, by rfl⟩ : syracuseStep 2167673 = 1625755) B1625755
theorem B2438383 : Blo 1443541 2438383 := bstep (se 1 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 2438383 = 3657575) B3657575
theorem B3249737 : Blo 1443541 3249737 := bstep (se 2 (by rfl) ⟨1218651, by rfl⟩ : syracuseStep 3249737 = 2437303) B2437303
theorem B1445115 : Blo 1443541 1445115 := bstep (se 1 (by rfl) ⟨1083836, by rfl⟩ : syracuseStep 1445115 = 2167673) B2167673
theorem B2166491 : Blo 1443541 2166491 := bstep (se 1 (by rfl) ⟨1624868, by rfl⟩ : syracuseStep 2166491 = 3249737) B3249737
theorem B2437033 : Blo 1443541 2437033 := bstep (se 2 (by rfl) ⟨913887, by rfl⟩ : syracuseStep 2437033 = 1827775) B1827775
theorem B15619691 : Blo 1443541 15619691 := bstep (se 1 (by rfl) ⟨11714768, by rfl⟩ : syracuseStep 15619691 = 23429537) B23429537
theorem B3251177 : Blo 1443541 3251177 := bstep (se 2 (by rfl) ⟨1219191, by rfl⟩ : syracuseStep 3251177 = 2438383) B2438383
theorem B10413127 : Blo 1443541 10413127 := bstep (se 1 (by rfl) ⟨7809845, by rfl⟩ : syracuseStep 10413127 = 15619691) B15619691
theorem B1444327 : Blo 1443541 1444327 := bstep (se 1 (by rfl) ⟨1083245, by rfl⟩ : syracuseStep 1444327 = 2166491) B2166491
theorem B2167451 : Blo 1443541 2167451 := bstep (se 1 (by rfl) ⟨1625588, by rfl⟩ : syracuseStep 2167451 = 3251177) B3251177
theorem B3249377 : Blo 1443541 3249377 := bstep (se 2 (by rfl) ⟨1218516, by rfl⟩ : syracuseStep 3249377 = 2437033) B2437033
theorem B1444967 : Blo 1443541 1444967 := bstep (se 1 (by rfl) ⟨1083725, by rfl⟩ : syracuseStep 1444967 = 2167451) B2167451
theorem B2166251 : Blo 1443541 2166251 := bstep (se 1 (by rfl) ⟨1624688, by rfl⟩ : syracuseStep 2166251 = 3249377) B3249377
theorem B13884169 : Blo 1443541 13884169 := bstep (se 2 (by rfl) ⟨5206563, by rfl⟩ : syracuseStep 13884169 = 10413127) B10413127
theorem B1444167 : Blo 1443541 1444167 := bstep (se 1 (by rfl) ⟨1083125, by rfl⟩ : syracuseStep 1444167 = 2166251) B2166251
theorem B18512225 : Blo 1443541 18512225 := bstep (se 2 (by rfl) ⟨6942084, by rfl⟩ : syracuseStep 18512225 = 13884169) B13884169
theorem B12341483 : Blo 1443541 12341483 := bstep (se 1 (by rfl) ⟨9256112, by rfl⟩ : syracuseStep 12341483 = 18512225) B18512225
theorem B8227655 : Blo 1443541 8227655 := bstep (se 1 (by rfl) ⟨6170741, by rfl⟩ : syracuseStep 8227655 = 12341483) B12341483
theorem B5485103 : Blo 1443541 5485103 := bstep (se 1 (by rfl) ⟨4113827, by rfl⟩ : syracuseStep 5485103 = 8227655) B8227655
theorem B3656735 : Blo 1443541 3656735 := bstep (se 1 (by rfl) ⟨2742551, by rfl⟩ : syracuseStep 3656735 = 5485103) B5485103
theorem B2437823 : Blo 1443541 2437823 := bstep (se 1 (by rfl) ⟨1828367, by rfl⟩ : syracuseStep 2437823 = 3656735) B3656735
theorem B1625215 : Blo 1443541 1625215 := bstep (se 1 (by rfl) ⟨1218911, by rfl⟩ : syracuseStep 1625215 = 2437823) B2437823
theorem B2166953 : Blo 1443541 2166953 := bstep (se 2 (by rfl) ⟨812607, by rfl⟩ : syracuseStep 2166953 = 1625215) B1625215
theorem B1444635 : Blo 1443541 1444635 := bstep (se 1 (by rfl) ⟨1083476, by rfl⟩ : syracuseStep 1444635 = 2166953) B2166953

theorem C0 (j : ℕ) (h1 : 360885 ≤ j) (h2 : j ≤ 361384) : Blo 1443541 (4 * j + 3) := by
  interval_cases j
  · exact B1443543
  · exact B1443547
  · exact B1443551
  · exact B1443555
  · exact B1443559
  · exact B1443563
  · exact B1443567
  · exact B1443571
  · exact B1443575
  · exact B1443579
  · exact B1443583
  · exact B1443587
  · exact B1443591
  · exact B1443595
  · exact B1443599
  · exact B1443603
  · exact B1443607
  · exact B1443611
  · exact B1443615
  · exact B1443619
  · exact B1443623
  · exact B1443627
  · exact B1443631
  · exact B1443635
  · exact B1443639
  · exact B1443643
  · exact B1443647
  · exact B1443651
  · exact B1443655
  · exact B1443659
  · exact B1443663
  · exact B1443667
  · exact B1443671
  · exact B1443675
  · exact B1443679
  · exact B1443683
  · exact B1443687
  · exact B1443691
  · exact B1443695
  · exact B1443699
  · exact B1443703
  · exact B1443707
  · exact B1443711
  · exact B1443715
  · exact B1443719
  · exact B1443723
  · exact B1443727
  · exact B1443731
  · exact B1443735
  · exact B1443739
  · exact B1443743
  · exact B1443747
  · exact B1443751
  · exact B1443755
  · exact B1443759
  · exact B1443763
  · exact B1443767
  · exact B1443771
  · exact B1443775
  · exact B1443779
  · exact B1443783
  · exact B1443787
  · exact B1443791
  · exact B1443795
  · exact B1443799
  · exact B1443803
  · exact B1443807
  · exact B1443811
  · exact B1443815
  · exact B1443819
  · exact B1443823
  · exact B1443827
  · exact B1443831
  · exact B1443835
  · exact B1443839
  · exact B1443843
  · exact B1443847
  · exact B1443851
  · exact B1443855
  · exact B1443859
  · exact B1443863
  · exact B1443867
  · exact B1443871
  · exact B1443875
  · exact B1443879
  · exact B1443883
  · exact B1443887
  · exact B1443891
  · exact B1443895
  · exact B1443899
  · exact B1443903
  · exact B1443907
  · exact B1443911
  · exact B1443915
  · exact B1443919
  · exact B1443923
  · exact B1443927
  · exact B1443931
  · exact B1443935
  · exact B1443939
  · exact B1443943
  · exact B1443947
  · exact B1443951
  · exact B1443955
  · exact B1443959
  · exact B1443963
  · exact B1443967
  · exact B1443971
  · exact B1443975
  · exact B1443979
  · exact B1443983
  · exact B1443987
  · exact B1443991
  · exact B1443995
  · exact B1443999
  · exact B1444003
  · exact B1444007
  · exact B1444011
  · exact B1444015
  · exact B1444019
  · exact B1444023
  · exact B1444027
  · exact B1444031
  · exact B1444035
  · exact B1444039
  · exact B1444043
  · exact B1444047
  · exact B1444051
  · exact B1444055
  · exact B1444059
  · exact B1444063
  · exact B1444067
  · exact B1444071
  · exact B1444075
  · exact B1444079
  · exact B1444083
  · exact B1444087
  · exact B1444091
  · exact B1444095
  · exact B1444099
  · exact B1444103
  · exact B1444107
  · exact B1444111
  · exact B1444115
  · exact B1444119
  · exact B1444123
  · exact B1444127
  · exact B1444131
  · exact B1444135
  · exact B1444139
  · exact B1444143
  · exact B1444147
  · exact B1444151
  · exact B1444155
  · exact B1444159
  · exact B1444163
  · exact B1444167
  · exact B1444171
  · exact B1444175
  · exact B1444179
  · exact B1444183
  · exact B1444187
  · exact B1444191
  · exact B1444195
  · exact B1444199
  · exact B1444203
  · exact B1444207
  · exact B1444211
  · exact B1444215
  · exact B1444219
  · exact B1444223
  · exact B1444227
  · exact B1444231
  · exact B1444235
  · exact B1444239
  · exact B1444243
  · exact B1444247
  · exact B1444251
  · exact B1444255
  · exact B1444259
  · exact B1444263
  · exact B1444267
  · exact B1444271
  · exact B1444275
  · exact B1444279
  · exact B1444283
  · exact B1444287
  · exact B1444291
  · exact B1444295
  · exact B1444299
  · exact B1444303
  · exact B1444307
  · exact B1444311
  · exact B1444315
  · exact B1444319
  · exact B1444323
  · exact B1444327
  · exact B1444331
  · exact B1444335
  · exact B1444339
  · exact B1444343
  · exact B1444347
  · exact B1444351
  · exact B1444355
  · exact B1444359
  · exact B1444363
  · exact B1444367
  · exact B1444371
  · exact B1444375
  · exact B1444379
  · exact B1444383
  · exact B1444387
  · exact B1444391
  · exact B1444395
  · exact B1444399
  · exact B1444403
  · exact B1444407
  · exact B1444411
  · exact B1444415
  · exact B1444419
  · exact B1444423
  · exact B1444427
  · exact B1444431
  · exact B1444435
  · exact B1444439
  · exact B1444443
  · exact B1444447
  · exact B1444451
  · exact B1444455
  · exact B1444459
  · exact B1444463
  · exact B1444467
  · exact B1444471
  · exact B1444475
  · exact B1444479
  · exact B1444483
  · exact B1444487
  · exact B1444491
  · exact B1444495
  · exact B1444499
  · exact B1444503
  · exact B1444507
  · exact B1444511
  · exact B1444515
  · exact B1444519
  · exact B1444523
  · exact B1444527
  · exact B1444531
  · exact B1444535
  · exact B1444539
  · exact B1444543
  · exact B1444547
  · exact B1444551
  · exact B1444555
  · exact B1444559
  · exact B1444563
  · exact B1444567
  · exact B1444571
  · exact B1444575
  · exact B1444579
  · exact B1444583
  · exact B1444587
  · exact B1444591
  · exact B1444595
  · exact B1444599
  · exact B1444603
  · exact B1444607
  · exact B1444611
  · exact B1444615
  · exact B1444619
  · exact B1444623
  · exact B1444627
  · exact B1444631
  · exact B1444635
  · exact B1444639
  · exact B1444643
  · exact B1444647
  · exact B1444651
  · exact B1444655
  · exact B1444659
  · exact B1444663
  · exact B1444667
  · exact B1444671
  · exact B1444675
  · exact B1444679
  · exact B1444683
  · exact B1444687
  · exact B1444691
  · exact B1444695
  · exact B1444699
  · exact B1444703
  · exact B1444707
  · exact B1444711
  · exact B1444715
  · exact B1444719
  · exact B1444723
  · exact B1444727
  · exact B1444731
  · exact B1444735
  · exact B1444739
  · exact B1444743
  · exact B1444747
  · exact B1444751
  · exact B1444755
  · exact B1444759
  · exact B1444763
  · exact B1444767
  · exact B1444771
  · exact B1444775
  · exact B1444779
  · exact B1444783
  · exact B1444787
  · exact B1444791
  · exact B1444795
  · exact B1444799
  · exact B1444803
  · exact B1444807
  · exact B1444811
  · exact B1444815
  · exact B1444819
  · exact B1444823
  · exact B1444827
  · exact B1444831
  · exact B1444835
  · exact B1444839
  · exact B1444843
  · exact B1444847
  · exact B1444851
  · exact B1444855
  · exact B1444859
  · exact B1444863
  · exact B1444867
  · exact B1444871
  · exact B1444875
  · exact B1444879
  · exact B1444883
  · exact B1444887
  · exact B1444891
  · exact B1444895
  · exact B1444899
  · exact B1444903
  · exact B1444907
  · exact B1444911
  · exact B1444915
  · exact B1444919
  · exact B1444923
  · exact B1444927
  · exact B1444931
  · exact B1444935
  · exact B1444939
  · exact B1444943
  · exact B1444947
  · exact B1444951
  · exact B1444955
  · exact B1444959
  · exact B1444963
  · exact B1444967
  · exact B1444971
  · exact B1444975
  · exact B1444979
  · exact B1444983
  · exact B1444987
  · exact B1444991
  · exact B1444995
  · exact B1444999
  · exact B1445003
  · exact B1445007
  · exact B1445011
  · exact B1445015
  · exact B1445019
  · exact B1445023
  · exact B1445027
  · exact B1445031
  · exact B1445035
  · exact B1445039
  · exact B1445043
  · exact B1445047
  · exact B1445051
  · exact B1445055
  · exact B1445059
  · exact B1445063
  · exact B1445067
  · exact B1445071
  · exact B1445075
  · exact B1445079
  · exact B1445083
  · exact B1445087
  · exact B1445091
  · exact B1445095
  · exact B1445099
  · exact B1445103
  · exact B1445107
  · exact B1445111
  · exact B1445115
  · exact B1445119
  · exact B1445123
  · exact B1445127
  · exact B1445131
  · exact B1445135
  · exact B1445139
  · exact B1445143
  · exact B1445147
  · exact B1445151
  · exact B1445155
  · exact B1445159
  · exact B1445163
  · exact B1445167
  · exact B1445171
  · exact B1445175
  · exact B1445179
  · exact B1445183
  · exact B1445187
  · exact B1445191
  · exact B1445195
  · exact B1445199
  · exact B1445203
  · exact B1445207
  · exact B1445211
  · exact B1445215
  · exact B1445219
  · exact B1445223
  · exact B1445227
  · exact B1445231
  · exact B1445235
  · exact B1445239
  · exact B1445243
  · exact B1445247
  · exact B1445251
  · exact B1445255
  · exact B1445259
  · exact B1445263
  · exact B1445267
  · exact B1445271
  · exact B1445275
  · exact B1445279
  · exact B1445283
  · exact B1445287
  · exact B1445291
  · exact B1445295
  · exact B1445299
  · exact B1445303
  · exact B1445307
  · exact B1445311
  · exact B1445315
  · exact B1445319
  · exact B1445323
  · exact B1445327
  · exact B1445331
  · exact B1445335
  · exact B1445339
  · exact B1445343
  · exact B1445347
  · exact B1445351
  · exact B1445355
  · exact B1445359
  · exact B1445363
  · exact B1445367
  · exact B1445371
  · exact B1445375
  · exact B1445379
  · exact B1445383
  · exact B1445387
  · exact B1445391
  · exact B1445395
  · exact B1445399
  · exact B1445403
  · exact B1445407
  · exact B1445411
  · exact B1445415
  · exact B1445419
  · exact B1445423
  · exact B1445427
  · exact B1445431
  · exact B1445435
  · exact B1445439
  · exact B1445443
  · exact B1445447
  · exact B1445451
  · exact B1445455
  · exact B1445459
  · exact B1445463
  · exact B1445467
  · exact B1445471
  · exact B1445475
  · exact B1445479
  · exact B1445483
  · exact B1445487
  · exact B1445491
  · exact B1445495
  · exact B1445499
  · exact B1445503
  · exact B1445507
  · exact B1445511
  · exact B1445515
  · exact B1445519
  · exact B1445523
  · exact B1445527
  · exact B1445531
  · exact B1445535
  · exact B1445539

theorem solution (m : ℕ) (hlo : 1443541 ≤ m) (hhi : m ≤ 1445541) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 360885 ≤ j := by omega
    have hj2 : j ≤ 361384 := by omega
    have hb : Blo 1443541 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
