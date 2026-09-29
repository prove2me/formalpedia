-- Prove2me | solution 1 for syracuse_descends_range_1813608_1815608
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:54:20.652588+00:00
-- url     : https://prove2.me/submissions/6ea9eae0-9618-4d64-9771-7891c8ec3537

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


theorem B4595717 : Blo 1813608 4595717 := bbase (se 4 (by rfl) ⟨430848, by rfl⟩ : syracuseStep 4595717 = 861697) (by norm_num)
theorem B4137077 : Blo 1813608 4137077 := bbase (se 5 (by rfl) ⟨193925, by rfl⟩ : syracuseStep 4137077 = 387851) (by norm_num)
theorem B19620245 : Blo 1813608 19620245 := bbase (se 6 (by rfl) ⟨459849, by rfl⟩ : syracuseStep 19620245 = 919699) (by norm_num)
theorem B2097649 : Blo 1813608 2097649 := bbase (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) (by norm_num)
theorem B2040313 : Blo 1813608 2040313 := bbase (se 2 (by rfl) ⟨765117, by rfl⟩ : syracuseStep 2040313 = 1530235) (by norm_num)
theorem B2040349 : Blo 1813608 2040349 := bbase (se 3 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 2040349 = 765131) (by norm_num)
theorem B3875357 : Blo 1813608 3875357 := bbase (se 3 (by rfl) ⟨726629, by rfl⟩ : syracuseStep 3875357 = 1453259) (by norm_num)
theorem B7750181 : Blo 1813608 7750181 := bbase (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) (by norm_num)
theorem B8741429 : Blo 1813608 8741429 := bbase (se 5 (by rfl) ⟨409754, by rfl⟩ : syracuseStep 8741429 = 819509) (by norm_num)
theorem B2040385 : Blo 1813608 2040385 := bbase (se 2 (by rfl) ⟨765144, by rfl⟩ : syracuseStep 2040385 = 1530289) (by norm_num)
theorem B2040421 : Blo 1813608 2040421 := bbase (se 4 (by rfl) ⟨191289, by rfl⟩ : syracuseStep 2040421 = 382579) (by norm_num)
theorem B4653677 : Blo 1813608 4653677 := bbase (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) (by norm_num)
theorem B2040457 : Blo 1813608 2040457 := bbase (se 2 (by rfl) ⟨765171, by rfl⟩ : syracuseStep 2040457 = 1530343) (by norm_num)
theorem B2720429 : Blo 1813608 2720429 := bbase (se 3 (by rfl) ⟨510080, by rfl⟩ : syracuseStep 2720429 = 1020161) (by norm_num)
theorem B2040493 : Blo 1813608 2040493 := bbase (se 3 (by rfl) ⟨382592, by rfl⟩ : syracuseStep 2040493 = 765185) (by norm_num)
theorem B3875501 : Blo 1813608 3875501 := bbase (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) (by norm_num)
theorem B2720453 : Blo 1813608 2720453 := bbase (se 4 (by rfl) ⟨255042, by rfl⟩ : syracuseStep 2720453 = 510085) (by norm_num)
theorem B9183941 : Blo 1813608 9183941 := bbase (se 4 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 9183941 = 1721989) (by norm_num)
theorem B2040529 : Blo 1813608 2040529 := bbase (se 2 (by rfl) ⟨765198, by rfl⟩ : syracuseStep 2040529 = 1530397) (by norm_num)
theorem B2720477 : Blo 1813608 2720477 := bbase (se 3 (by rfl) ⟨510089, by rfl⟩ : syracuseStep 2720477 = 1020179) (by norm_num)
theorem B2720501 : Blo 1813608 2720501 := bbase (se 5 (by rfl) ⟨127523, by rfl⟩ : syracuseStep 2720501 = 255047) (by norm_num)
theorem B2040565 : Blo 1813608 2040565 := bbase (se 5 (by rfl) ⟨95651, by rfl⟩ : syracuseStep 2040565 = 191303) (by norm_num)
theorem B2720525 : Blo 1813608 2720525 := bbase (se 3 (by rfl) ⟨510098, by rfl⟩ : syracuseStep 2720525 = 1020197) (by norm_num)
theorem B2040601 : Blo 1813608 2040601 := bbase (se 2 (by rfl) ⟨765225, by rfl⟩ : syracuseStep 2040601 = 1530451) (by norm_num)
theorem B2720549 : Blo 1813608 2720549 := bbase (se 4 (by rfl) ⟨255051, by rfl⟩ : syracuseStep 2720549 = 510103) (by norm_num)
theorem B2720573 : Blo 1813608 2720573 := bbase (se 3 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 2720573 = 1020215) (by norm_num)
theorem B2040637 : Blo 1813608 2040637 := bbase (se 3 (by rfl) ⟨382619, by rfl⟩ : syracuseStep 2040637 = 765239) (by norm_num)
theorem B2720597 : Blo 1813608 2720597 := bbase (se 9 (by rfl) ⟨7970, by rfl⟩ : syracuseStep 2720597 = 15941) (by norm_num)
theorem B2040673 : Blo 1813608 2040673 := bbase (se 2 (by rfl) ⟨765252, by rfl⟩ : syracuseStep 2040673 = 1530505) (by norm_num)
theorem B2720621 : Blo 1813608 2720621 := bbase (se 3 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 2720621 = 1020233) (by norm_num)
theorem B2720645 : Blo 1813608 2720645 := bbase (se 4 (by rfl) ⟨255060, by rfl⟩ : syracuseStep 2720645 = 510121) (by norm_num)
theorem B2040709 : Blo 1813608 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B2720669 : Blo 1813608 2720669 := bbase (se 3 (by rfl) ⟨510125, by rfl⟩ : syracuseStep 2720669 = 1020251) (by norm_num)
theorem B2040745 : Blo 1813608 2040745 := bbase (se 2 (by rfl) ⟨765279, by rfl⟩ : syracuseStep 2040745 = 1530559) (by norm_num)
theorem B2720693 : Blo 1813608 2720693 := bbase (se 5 (by rfl) ⟨127532, by rfl⟩ : syracuseStep 2720693 = 255065) (by norm_num)
theorem B2720717 : Blo 1813608 2720717 := bbase (se 3 (by rfl) ⟨510134, by rfl⟩ : syracuseStep 2720717 = 1020269) (by norm_num)
theorem B2040781 : Blo 1813608 2040781 := bbase (se 3 (by rfl) ⟨382646, by rfl⟩ : syracuseStep 2040781 = 765293) (by norm_num)
theorem B3490781 : Blo 1813608 3490781 := bbase (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) (by norm_num)
theorem B2720741 : Blo 1813608 2720741 := bbase (se 4 (by rfl) ⟨255069, by rfl⟩ : syracuseStep 2720741 = 510139) (by norm_num)
theorem B2040817 : Blo 1813608 2040817 := bbase (se 2 (by rfl) ⟨765306, by rfl⟩ : syracuseStep 2040817 = 1530613) (by norm_num)
theorem B2720765 : Blo 1813608 2720765 := bbase (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) (by norm_num)
theorem B4080653 : Blo 1813608 4080653 := bbase (se 3 (by rfl) ⟨765122, by rfl⟩ : syracuseStep 4080653 = 1530245) (by norm_num)
theorem B2720789 : Blo 1813608 2720789 := bbase (se 6 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 2720789 = 127537) (by norm_num)
theorem B2040853 : Blo 1813608 2040853 := bbase (se 6 (by rfl) ⟨47832, by rfl⟩ : syracuseStep 2040853 = 95665) (by norm_num)
theorem B2720813 : Blo 1813608 2720813 := bbase (se 3 (by rfl) ⟨510152, by rfl⟩ : syracuseStep 2720813 = 1020305) (by norm_num)
theorem B2040889 : Blo 1813608 2040889 := bbase (se 2 (by rfl) ⟨765333, by rfl⟩ : syracuseStep 2040889 = 1530667) (by norm_num)
theorem B2720837 : Blo 1813608 2720837 := bbase (se 4 (by rfl) ⟨255078, by rfl⟩ : syracuseStep 2720837 = 510157) (by norm_num)
theorem B4080725 : Blo 1813608 4080725 := bbase (se 8 (by rfl) ⟨23910, by rfl⟩ : syracuseStep 4080725 = 47821) (by norm_num)
theorem B2720861 : Blo 1813608 2720861 := bbase (se 3 (by rfl) ⟨510161, by rfl⟩ : syracuseStep 2720861 = 1020323) (by norm_num)
theorem B2040925 : Blo 1813608 2040925 := bbase (se 3 (by rfl) ⟨382673, by rfl⟩ : syracuseStep 2040925 = 765347) (by norm_num)
theorem B2720885 : Blo 1813608 2720885 := bbase (se 5 (by rfl) ⟨127541, by rfl⟩ : syracuseStep 2720885 = 255083) (by norm_num)
theorem B2040961 : Blo 1813608 2040961 := bbase (se 2 (by rfl) ⟨765360, by rfl⟩ : syracuseStep 2040961 = 1530721) (by norm_num)
theorem B6890629 : Blo 1813608 6890629 := bbase (se 4 (by rfl) ⟨645996, by rfl⟩ : syracuseStep 6890629 = 1291993) (by norm_num)
theorem B2720909 : Blo 1813608 2720909 := bbase (se 3 (by rfl) ⟨510170, by rfl⟩ : syracuseStep 2720909 = 1020341) (by norm_num)
theorem B4080797 : Blo 1813608 4080797 := bbase (se 3 (by rfl) ⟨765149, by rfl⟩ : syracuseStep 4080797 = 1530299) (by norm_num)
theorem B2720933 : Blo 1813608 2720933 := bbase (se 4 (by rfl) ⟨255087, by rfl⟩ : syracuseStep 2720933 = 510175) (by norm_num)
theorem B2040997 : Blo 1813608 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B2720957 : Blo 1813608 2720957 := bbase (se 3 (by rfl) ⟨510179, by rfl⟩ : syracuseStep 2720957 = 1020359) (by norm_num)
theorem B2041033 : Blo 1813608 2041033 := bbase (se 2 (by rfl) ⟨765387, by rfl⟩ : syracuseStep 2041033 = 1530775) (by norm_num)
theorem B2720981 : Blo 1813608 2720981 := bbase (se 7 (by rfl) ⟨31886, by rfl⟩ : syracuseStep 2720981 = 63773) (by norm_num)
theorem B4080869 : Blo 1813608 4080869 := bbase (se 4 (by rfl) ⟨382581, by rfl⟩ : syracuseStep 4080869 = 765163) (by norm_num)
theorem B2721005 : Blo 1813608 2721005 := bbase (se 3 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 2721005 = 1020377) (by norm_num)
theorem B2041069 : Blo 1813608 2041069 := bbase (se 3 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 2041069 = 765401) (by norm_num)
theorem B2721029 : Blo 1813608 2721029 := bbase (se 4 (by rfl) ⟨255096, by rfl⟩ : syracuseStep 2721029 = 510193) (by norm_num)
theorem B2041105 : Blo 1813608 2041105 := bbase (se 2 (by rfl) ⟨765414, by rfl⟩ : syracuseStep 2041105 = 1530829) (by norm_num)
theorem B2721053 : Blo 1813608 2721053 := bbase (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) (by norm_num)
theorem B4080941 : Blo 1813608 4080941 := bbase (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) (by norm_num)
theorem B2721077 : Blo 1813608 2721077 := bbase (se 5 (by rfl) ⟨127550, by rfl⟩ : syracuseStep 2721077 = 255101) (by norm_num)
theorem B2041141 : Blo 1813608 2041141 := bbase (se 5 (by rfl) ⟨95678, by rfl⟩ : syracuseStep 2041141 = 191357) (by norm_num)
theorem B2721101 : Blo 1813608 2721101 := bbase (se 3 (by rfl) ⟨510206, by rfl⟩ : syracuseStep 2721101 = 1020413) (by norm_num)
theorem B2041177 : Blo 1813608 2041177 := bbase (se 2 (by rfl) ⟨765441, by rfl⟩ : syracuseStep 2041177 = 1530883) (by norm_num)
theorem B2721125 : Blo 1813608 2721125 := bbase (se 4 (by rfl) ⟨255105, by rfl⟩ : syracuseStep 2721125 = 510211) (by norm_num)
theorem B4081013 : Blo 1813608 4081013 := bbase (se 5 (by rfl) ⟨191297, by rfl⟩ : syracuseStep 4081013 = 382595) (by norm_num)
theorem B2721149 : Blo 1813608 2721149 := bbase (se 3 (by rfl) ⟨510215, by rfl⟩ : syracuseStep 2721149 = 1020431) (by norm_num)
theorem B2041213 : Blo 1813608 2041213 := bbase (se 3 (by rfl) ⟨382727, by rfl⟩ : syracuseStep 2041213 = 765455) (by norm_num)
theorem B2721173 : Blo 1813608 2721173 := bbase (se 6 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 2721173 = 127555) (by norm_num)
theorem B3876245 : Blo 1813608 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B2041249 : Blo 1813608 2041249 := bbase (se 2 (by rfl) ⟨765468, by rfl⟩ : syracuseStep 2041249 = 1530937) (by norm_num)
theorem B2721197 : Blo 1813608 2721197 := bbase (se 3 (by rfl) ⟨510224, by rfl⟩ : syracuseStep 2721197 = 1020449) (by norm_num)
theorem B6890933 : Blo 1813608 6890933 := bbase (se 5 (by rfl) ⟨323012, by rfl⟩ : syracuseStep 6890933 = 646025) (by norm_num)
theorem B4081085 : Blo 1813608 4081085 := bbase (se 3 (by rfl) ⟨765203, by rfl⟩ : syracuseStep 4081085 = 1530407) (by norm_num)
theorem B2721221 : Blo 1813608 2721221 := bbase (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) (by norm_num)
theorem B2041285 : Blo 1813608 2041285 := bbase (se 4 (by rfl) ⟨191370, by rfl⟩ : syracuseStep 2041285 = 382741) (by norm_num)
theorem B2721245 : Blo 1813608 2721245 := bbase (se 3 (by rfl) ⟨510233, by rfl⟩ : syracuseStep 2721245 = 1020467) (by norm_num)
theorem B2041321 : Blo 1813608 2041321 := bbase (se 2 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 2041321 = 1530991) (by norm_num)
theorem B2721269 : Blo 1813608 2721269 := bbase (se 5 (by rfl) ⟨127559, by rfl⟩ : syracuseStep 2721269 = 255119) (by norm_num)
theorem B4081157 : Blo 1813608 4081157 := bbase (se 4 (by rfl) ⟨382608, by rfl⟩ : syracuseStep 4081157 = 765217) (by norm_num)
theorem B7751173 : Blo 1813608 7751173 := bbase (se 4 (by rfl) ⟨726672, by rfl⟩ : syracuseStep 7751173 = 1453345) (by norm_num)
theorem B2721293 : Blo 1813608 2721293 := bbase (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) (by norm_num)
theorem B2041357 : Blo 1813608 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B37242389 : Blo 1813608 37242389 := bbase (se 6 (by rfl) ⟨872868, by rfl⟩ : syracuseStep 37242389 = 1745737) (by norm_num)
theorem B8717861 : Blo 1813608 8717861 := bbase (se 4 (by rfl) ⟨817299, by rfl⟩ : syracuseStep 8717861 = 1634599) (by norm_num)
theorem B2721317 : Blo 1813608 2721317 := bbase (se 4 (by rfl) ⟨255123, by rfl⟩ : syracuseStep 2721317 = 510247) (by norm_num)
theorem B2041393 : Blo 1813608 2041393 := bbase (se 2 (by rfl) ⟨765522, by rfl⟩ : syracuseStep 2041393 = 1531045) (by norm_num)
theorem B2328113 : Blo 1813608 2328113 := bbase (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) (by norm_num)
theorem B2721341 : Blo 1813608 2721341 := bbase (se 3 (by rfl) ⟨510251, by rfl⟩ : syracuseStep 2721341 = 1020503) (by norm_num)
theorem B2295373 : Blo 1813608 2295373 := bbase (se 3 (by rfl) ⟨430382, by rfl⟩ : syracuseStep 2295373 = 860765) (by norm_num)
theorem B4081229 : Blo 1813608 4081229 := bbase (se 3 (by rfl) ⟨765230, by rfl⟩ : syracuseStep 4081229 = 1530461) (by norm_num)
theorem B2721365 : Blo 1813608 2721365 := bbase (se 8 (by rfl) ⟨15945, by rfl⟩ : syracuseStep 2721365 = 31891) (by norm_num)
theorem B2041429 : Blo 1813608 2041429 := bbase (se 8 (by rfl) ⟨11961, by rfl⟩ : syracuseStep 2041429 = 23923) (by norm_num)
theorem B6121061 : Blo 1813608 6121061 := bbase (se 4 (by rfl) ⟨573849, by rfl⟩ : syracuseStep 6121061 = 1147699) (by norm_num)
theorem B2721389 : Blo 1813608 2721389 := bbase (se 3 (by rfl) ⟨510260, by rfl⟩ : syracuseStep 2721389 = 1020521) (by norm_num)
theorem B2041465 : Blo 1813608 2041465 := bbase (se 2 (by rfl) ⟨765549, by rfl⟩ : syracuseStep 2041465 = 1531099) (by norm_num)
theorem B2721413 : Blo 1813608 2721413 := bbase (se 4 (by rfl) ⟨255132, by rfl⟩ : syracuseStep 2721413 = 510265) (by norm_num)
theorem B4081301 : Blo 1813608 4081301 := bbase (se 6 (by rfl) ⟨95655, by rfl⟩ : syracuseStep 4081301 = 191311) (by norm_num)
theorem B2721437 : Blo 1813608 2721437 := bbase (se 3 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 2721437 = 1020539) (by norm_num)
theorem B2041501 : Blo 1813608 2041501 := bbase (se 3 (by rfl) ⟨382781, by rfl⟩ : syracuseStep 2041501 = 765563) (by norm_num)
theorem B2295469 : Blo 1813608 2295469 := bbase (se 3 (by rfl) ⟨430400, by rfl⟩ : syracuseStep 2295469 = 860801) (by norm_num)
theorem B4359853 : Blo 1813608 4359853 := bbase (se 3 (by rfl) ⟨817472, by rfl⟩ : syracuseStep 4359853 = 1634945) (by norm_num)
theorem B2721461 : Blo 1813608 2721461 := bbase (se 5 (by rfl) ⟨127568, by rfl⟩ : syracuseStep 2721461 = 255137) (by norm_num)
theorem B2041537 : Blo 1813608 2041537 := bbase (se 2 (by rfl) ⟨765576, by rfl⟩ : syracuseStep 2041537 = 1531153) (by norm_num)
theorem B2721485 : Blo 1813608 2721485 := bbase (se 3 (by rfl) ⟨510278, by rfl⟩ : syracuseStep 2721485 = 1020557) (by norm_num)
theorem B8840917 : Blo 1813608 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B4081373 : Blo 1813608 4081373 := bbase (se 3 (by rfl) ⟨765257, by rfl⟩ : syracuseStep 4081373 = 1530515) (by norm_num)
theorem B4359901 : Blo 1813608 4359901 := bbase (se 3 (by rfl) ⟨817481, by rfl⟩ : syracuseStep 4359901 = 1634963) (by norm_num)
theorem B2721509 : Blo 1813608 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B2041573 : Blo 1813608 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B2180849 : Blo 1813608 2180849 := bbase (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) (by norm_num)
theorem B2721533 : Blo 1813608 2721533 := bbase (se 3 (by rfl) ⟨510287, by rfl⟩ : syracuseStep 2721533 = 1020575) (by norm_num)
theorem B2041609 : Blo 1813608 2041609 := bbase (se 2 (by rfl) ⟨765603, by rfl⟩ : syracuseStep 2041609 = 1531207) (by norm_num)
theorem B2721557 : Blo 1813608 2721557 := bbase (se 6 (by rfl) ⟨63786, by rfl⟩ : syracuseStep 2721557 = 127573) (by norm_num)
theorem B4081445 : Blo 1813608 4081445 := bbase (se 4 (by rfl) ⟨382635, by rfl⟩ : syracuseStep 4081445 = 765271) (by norm_num)
theorem B2721581 : Blo 1813608 2721581 := bbase (se 3 (by rfl) ⟨510296, by rfl⟩ : syracuseStep 2721581 = 1020593) (by norm_num)
theorem B2041645 : Blo 1813608 2041645 := bbase (se 3 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 2041645 = 765617) (by norm_num)
theorem B2721605 : Blo 1813608 2721605 := bbase (se 4 (by rfl) ⟨255150, by rfl⟩ : syracuseStep 2721605 = 510301) (by norm_num)
theorem B2041681 : Blo 1813608 2041681 := bbase (se 2 (by rfl) ⟨765630, by rfl⟩ : syracuseStep 2041681 = 1531261) (by norm_num)
theorem B2295641 : Blo 1813608 2295641 := bbase (se 2 (by rfl) ⟨860865, by rfl⟩ : syracuseStep 2295641 = 1721731) (by norm_num)
theorem B2721629 : Blo 1813608 2721629 := bbase (se 3 (by rfl) ⟨510305, by rfl⟩ : syracuseStep 2721629 = 1020611) (by norm_num)
theorem B4081517 : Blo 1813608 4081517 := bbase (se 3 (by rfl) ⟨765284, by rfl⟩ : syracuseStep 4081517 = 1530569) (by norm_num)
theorem B2721653 : Blo 1813608 2721653 := bbase (se 5 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 2721653 = 255155) (by norm_num)
theorem B2041717 : Blo 1813608 2041717 := bbase (se 5 (by rfl) ⟨95705, by rfl⟩ : syracuseStep 2041717 = 191411) (by norm_num)
theorem B3729277 : Blo 1813608 3729277 := bbase (se 3 (by rfl) ⟨699239, by rfl⟩ : syracuseStep 3729277 = 1398479) (by norm_num)
theorem B2451341 : Blo 1813608 2451341 := bbase (se 3 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 2451341 = 919253) (by norm_num)
theorem B2721677 : Blo 1813608 2721677 := bbase (se 3 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 2721677 = 1020629) (by norm_num)
theorem B2295697 : Blo 1813608 2295697 := bbase (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) (by norm_num)
theorem B2041753 : Blo 1813608 2041753 := bbase (se 2 (by rfl) ⟨765657, by rfl⟩ : syracuseStep 2041753 = 1531315) (by norm_num)
theorem B2582437 : Blo 1813608 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B2721701 : Blo 1813608 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B4081589 : Blo 1813608 4081589 := bbase (se 5 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 4081589 = 382649) (by norm_num)
theorem B2721725 : Blo 1813608 2721725 := bbase (se 3 (by rfl) ⟨510323, by rfl⟩ : syracuseStep 2721725 = 1020647) (by norm_num)
theorem B2041789 : Blo 1813608 2041789 := bbase (se 3 (by rfl) ⟨382835, by rfl⟩ : syracuseStep 2041789 = 765671) (by norm_num)
theorem B9185237 : Blo 1813608 9185237 := bbase (se 7 (by rfl) ⟨107639, by rfl⟩ : syracuseStep 9185237 = 215279) (by norm_num)
theorem B2721749 : Blo 1813608 2721749 := bbase (se 7 (by rfl) ⟨31895, by rfl⟩ : syracuseStep 2721749 = 63791) (by norm_num)
theorem B2041825 : Blo 1813608 2041825 := bbase (se 2 (by rfl) ⟨765684, by rfl⟩ : syracuseStep 2041825 = 1531369) (by norm_num)
theorem B2721773 : Blo 1813608 2721773 := bbase (se 3 (by rfl) ⟨510332, by rfl⟩ : syracuseStep 2721773 = 1020665) (by norm_num)
theorem B2295793 : Blo 1813608 2295793 := bbase (se 2 (by rfl) ⟨860922, by rfl⟩ : syracuseStep 2295793 = 1721845) (by norm_num)
theorem B5515253 : Blo 1813608 5515253 := bbase (se 5 (by rfl) ⟨258527, by rfl⟩ : syracuseStep 5515253 = 517055) (by norm_num)
theorem B4081661 : Blo 1813608 4081661 := bbase (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) (by norm_num)
theorem B2721797 : Blo 1813608 2721797 := bbase (se 4 (by rfl) ⟨255168, by rfl⟩ : syracuseStep 2721797 = 510337) (by norm_num)
theorem B2041861 : Blo 1813608 2041861 := bbase (se 4 (by rfl) ⟨191424, by rfl⟩ : syracuseStep 2041861 = 382849) (by norm_num)
theorem B6121493 : Blo 1813608 6121493 := bbase (se 6 (by rfl) ⟨143472, by rfl⟩ : syracuseStep 6121493 = 286945) (by norm_num)
theorem B2721821 : Blo 1813608 2721821 := bbase (se 3 (by rfl) ⟨510341, by rfl⟩ : syracuseStep 2721821 = 1020683) (by norm_num)
theorem B2041897 : Blo 1813608 2041897 := bbase (se 2 (by rfl) ⟨765711, by rfl⟩ : syracuseStep 2041897 = 1531423) (by norm_num)
theorem B2721845 : Blo 1813608 2721845 := bbase (se 5 (by rfl) ⟨127586, by rfl⟩ : syracuseStep 2721845 = 255173) (by norm_num)
theorem B2181181 : Blo 1813608 2181181 := bbase (se 3 (by rfl) ⟨408971, by rfl⟩ : syracuseStep 2181181 = 817943) (by norm_num)
theorem B4081733 : Blo 1813608 4081733 := bbase (se 4 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 4081733 = 765325) (by norm_num)
theorem B2721869 : Blo 1813608 2721869 := bbase (se 3 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 2721869 = 1020701) (by norm_num)
theorem B2041933 : Blo 1813608 2041933 := bbase (se 3 (by rfl) ⟨382862, by rfl⟩ : syracuseStep 2041933 = 765725) (by norm_num)
theorem B2721893 : Blo 1813608 2721893 := bbase (se 4 (by rfl) ⟨255177, by rfl⟩ : syracuseStep 2721893 = 510355) (by norm_num)
theorem B2041969 : Blo 1813608 2041969 := bbase (se 2 (by rfl) ⟨765738, by rfl⟩ : syracuseStep 2041969 = 1531477) (by norm_num)
theorem B2721917 : Blo 1813608 2721917 := bbase (se 3 (by rfl) ⟨510359, by rfl⟩ : syracuseStep 2721917 = 1020719) (by norm_num)
theorem B3876997 : Blo 1813608 3876997 := bbase (se 4 (by rfl) ⟨363468, by rfl⟩ : syracuseStep 3876997 = 726937) (by norm_num)
theorem B4081805 : Blo 1813608 4081805 := bbase (se 3 (by rfl) ⟨765338, by rfl⟩ : syracuseStep 4081805 = 1530677) (by norm_num)
theorem B2721941 : Blo 1813608 2721941 := bbase (se 6 (by rfl) ⟨63795, by rfl⟩ : syracuseStep 2721941 = 127591) (by norm_num)
theorem B2042005 : Blo 1813608 2042005 := bbase (se 6 (by rfl) ⟨47859, by rfl⟩ : syracuseStep 2042005 = 95719) (by norm_num)
theorem B2295965 : Blo 1813608 2295965 := bbase (se 3 (by rfl) ⟨430493, by rfl⟩ : syracuseStep 2295965 = 860987) (by norm_num)
theorem B2721965 : Blo 1813608 2721965 := bbase (se 3 (by rfl) ⟨510368, by rfl⟩ : syracuseStep 2721965 = 1020737) (by norm_num)
theorem B2042041 : Blo 1813608 2042041 := bbase (se 2 (by rfl) ⟨765765, by rfl⟩ : syracuseStep 2042041 = 1531531) (by norm_num)
theorem B2721989 : Blo 1813608 2721989 := bbase (se 4 (by rfl) ⟨255186, by rfl⟩ : syracuseStep 2721989 = 510373) (by norm_num)
theorem B2296021 : Blo 1813608 2296021 := bbase (se 7 (by rfl) ⟨26906, by rfl⟩ : syracuseStep 2296021 = 53813) (by norm_num)
theorem B4081877 : Blo 1813608 4081877 := bbase (se 7 (by rfl) ⟨47834, by rfl⟩ : syracuseStep 4081877 = 95669) (by norm_num)
theorem B2722013 : Blo 1813608 2722013 := bbase (se 3 (by rfl) ⟨510377, by rfl⟩ : syracuseStep 2722013 = 1020755) (by norm_num)
theorem B2042077 : Blo 1813608 2042077 := bbase (se 3 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 2042077 = 765779) (by norm_num)
theorem B2722037 : Blo 1813608 2722037 := bbase (se 5 (by rfl) ⟨127595, by rfl⟩ : syracuseStep 2722037 = 255191) (by norm_num)
theorem B2042113 : Blo 1813608 2042113 := bbase (se 2 (by rfl) ⟨765792, by rfl⟩ : syracuseStep 2042113 = 1531585) (by norm_num)
theorem B2722061 : Blo 1813608 2722061 := bbase (se 3 (by rfl) ⟨510386, by rfl⟩ : syracuseStep 2722061 = 1020773) (by norm_num)
theorem B3877141 : Blo 1813608 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B2582813 : Blo 1813608 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B4081949 : Blo 1813608 4081949 := bbase (se 3 (by rfl) ⟨765365, by rfl⟩ : syracuseStep 4081949 = 1530731) (by norm_num)
theorem B2722085 : Blo 1813608 2722085 := bbase (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) (by norm_num)
theorem B2042149 : Blo 1813608 2042149 := bbase (se 4 (by rfl) ⟨191451, by rfl⟩ : syracuseStep 2042149 = 382903) (by norm_num)
theorem B2296117 : Blo 1813608 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B2722109 : Blo 1813608 2722109 := bbase (se 3 (by rfl) ⟨510395, by rfl⟩ : syracuseStep 2722109 = 1020791) (by norm_num)
theorem B4360517 : Blo 1813608 4360517 := bbase (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) (by norm_num)
theorem B3680581 : Blo 1813608 3680581 := bbase (se 4 (by rfl) ⟨345054, by rfl⟩ : syracuseStep 3680581 = 690109) (by norm_num)
theorem B2042185 : Blo 1813608 2042185 := bbase (se 2 (by rfl) ⟨765819, by rfl⟩ : syracuseStep 2042185 = 1531639) (by norm_num)
theorem B2722133 : Blo 1813608 2722133 := bbase (se 10 (by rfl) ⟨3987, by rfl⟩ : syracuseStep 2722133 = 7975) (by norm_num)
theorem B4082021 : Blo 1813608 4082021 := bbase (se 4 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 4082021 = 765379) (by norm_num)
theorem B2722157 : Blo 1813608 2722157 := bbase (se 3 (by rfl) ⟨510404, by rfl⟩ : syracuseStep 2722157 = 1020809) (by norm_num)
theorem B2042221 : Blo 1813608 2042221 := bbase (se 3 (by rfl) ⟨382916, by rfl⟩ : syracuseStep 2042221 = 765833) (by norm_num)
theorem B2722181 : Blo 1813608 2722181 := bbase (se 4 (by rfl) ⟨255204, by rfl⟩ : syracuseStep 2722181 = 510409) (by norm_num)
theorem B2042257 : Blo 1813608 2042257 := bbase (se 2 (by rfl) ⟨765846, by rfl⟩ : syracuseStep 2042257 = 1531693) (by norm_num)
theorem B2722205 : Blo 1813608 2722205 := bbase (se 3 (by rfl) ⟨510413, by rfl⟩ : syracuseStep 2722205 = 1020827) (by norm_num)
theorem B4082093 : Blo 1813608 4082093 := bbase (se 3 (by rfl) ⟨765392, by rfl⟩ : syracuseStep 4082093 = 1530785) (by norm_num)
theorem B2722229 : Blo 1813608 2722229 := bbase (se 5 (by rfl) ⟨127604, by rfl⟩ : syracuseStep 2722229 = 255209) (by norm_num)
theorem B2042293 : Blo 1813608 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B6121925 : Blo 1813608 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B2722253 : Blo 1813608 2722253 := bbase (se 3 (by rfl) ⟨510422, by rfl⟩ : syracuseStep 2722253 = 1020845) (by norm_num)
theorem B2042329 : Blo 1813608 2042329 := bbase (se 2 (by rfl) ⟨765873, by rfl⟩ : syracuseStep 2042329 = 1531747) (by norm_num)
theorem B2296289 : Blo 1813608 2296289 := bbase (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) (by norm_num)
theorem B2722277 : Blo 1813608 2722277 := bbase (se 4 (by rfl) ⟨255213, by rfl⟩ : syracuseStep 2722277 = 510427) (by norm_num)
theorem B4082165 : Blo 1813608 4082165 := bbase (se 5 (by rfl) ⟨191351, by rfl⟩ : syracuseStep 4082165 = 382703) (by norm_num)
theorem B2722301 : Blo 1813608 2722301 := bbase (se 3 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 2722301 = 1020863) (by norm_num)
theorem B2042365 : Blo 1813608 2042365 := bbase (se 3 (by rfl) ⟨382943, by rfl⟩ : syracuseStep 2042365 = 765887) (by norm_num)
theorem B2722325 : Blo 1813608 2722325 := bbase (se 6 (by rfl) ⟨63804, by rfl⟩ : syracuseStep 2722325 = 127609) (by norm_num)
theorem B2296345 : Blo 1813608 2296345 := bbase (se 2 (by rfl) ⟨861129, by rfl⟩ : syracuseStep 2296345 = 1722259) (by norm_num)
theorem B2042401 : Blo 1813608 2042401 := bbase (se 2 (by rfl) ⟨765900, by rfl⟩ : syracuseStep 2042401 = 1531801) (by norm_num)
theorem B2722349 : Blo 1813608 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B5810741 : Blo 1813608 5810741 := bbase (se 5 (by rfl) ⟨272378, by rfl⟩ : syracuseStep 5810741 = 544757) (by norm_num)
theorem B4082237 : Blo 1813608 4082237 := bbase (se 3 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 4082237 = 1530839) (by norm_num)
theorem B2722373 : Blo 1813608 2722373 := bbase (se 4 (by rfl) ⟨255222, by rfl⟩ : syracuseStep 2722373 = 510445) (by norm_num)
theorem B2042437 : Blo 1813608 2042437 := bbase (se 4 (by rfl) ⟨191478, by rfl⟩ : syracuseStep 2042437 = 382957) (by norm_num)
theorem B2722397 : Blo 1813608 2722397 := bbase (se 3 (by rfl) ⟨510449, by rfl⟩ : syracuseStep 2722397 = 1020899) (by norm_num)
theorem B2042473 : Blo 1813608 2042473 := bbase (se 2 (by rfl) ⟨765927, by rfl⟩ : syracuseStep 2042473 = 1531855) (by norm_num)
theorem B2722421 : Blo 1813608 2722421 := bbase (se 5 (by rfl) ⟨127613, by rfl⟩ : syracuseStep 2722421 = 255227) (by norm_num)
theorem B2296441 : Blo 1813608 2296441 := bbase (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) (by norm_num)
theorem B4082309 : Blo 1813608 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B2722445 : Blo 1813608 2722445 := bbase (se 3 (by rfl) ⟨510458, by rfl⟩ : syracuseStep 2722445 = 1020917) (by norm_num)
theorem B3877517 : Blo 1813608 3877517 := bbase (se 3 (by rfl) ⟨727034, by rfl⟩ : syracuseStep 3877517 = 1454069) (by norm_num)
theorem B2042509 : Blo 1813608 2042509 := bbase (se 3 (by rfl) ⟨382970, by rfl⟩ : syracuseStep 2042509 = 765941) (by norm_num)
theorem B4139669 : Blo 1813608 4139669 := bbase (se 6 (by rfl) ⟨97023, by rfl⟩ : syracuseStep 4139669 = 194047) (by norm_num)
theorem B4360861 : Blo 1813608 4360861 := bbase (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) (by norm_num)
theorem B2722469 : Blo 1813608 2722469 := bbase (se 4 (by rfl) ⟨255231, by rfl⟩ : syracuseStep 2722469 = 510463) (by norm_num)
theorem B2042545 : Blo 1813608 2042545 := bbase (se 2 (by rfl) ⟨765954, by rfl⟩ : syracuseStep 2042545 = 1531909) (by norm_num)
theorem B2722493 : Blo 1813608 2722493 := bbase (se 3 (by rfl) ⟨510467, by rfl⟩ : syracuseStep 2722493 = 1020935) (by norm_num)
theorem B4082381 : Blo 1813608 4082381 := bbase (se 3 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 4082381 = 1530893) (by norm_num)
theorem B2722517 : Blo 1813608 2722517 := bbase (se 7 (by rfl) ⟨31904, by rfl⟩ : syracuseStep 2722517 = 63809) (by norm_num)
theorem B2722541 : Blo 1813608 2722541 := bbase (se 3 (by rfl) ⟨510476, by rfl⟩ : syracuseStep 2722541 = 1020953) (by norm_num)
theorem B8719109 : Blo 1813608 8719109 := bbase (se 4 (by rfl) ⟨817416, by rfl⟩ : syracuseStep 8719109 = 1634833) (by norm_num)
theorem B2722565 : Blo 1813608 2722565 := bbase (se 4 (by rfl) ⟨255240, by rfl⟩ : syracuseStep 2722565 = 510481) (by norm_num)
theorem B4082453 : Blo 1813608 4082453 := bbase (se 6 (by rfl) ⟨95682, by rfl⟩ : syracuseStep 4082453 = 191365) (by norm_num)
theorem B3443485 : Blo 1813608 3443485 := bbase (se 3 (by rfl) ⟨645653, by rfl⟩ : syracuseStep 3443485 = 1291307) (by norm_num)
theorem B2722589 : Blo 1813608 2722589 := bbase (se 3 (by rfl) ⟨510485, by rfl⟩ : syracuseStep 2722589 = 1020971) (by norm_num)
theorem B2296613 : Blo 1813608 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B2722613 : Blo 1813608 2722613 := bbase (se 5 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 2722613 = 255245) (by norm_num)
theorem B2722637 : Blo 1813608 2722637 := bbase (se 3 (by rfl) ⟨510494, by rfl⟩ : syracuseStep 2722637 = 1020989) (by norm_num)
theorem B4082525 : Blo 1813608 4082525 := bbase (se 3 (by rfl) ⟨765473, by rfl⟩ : syracuseStep 4082525 = 1530947) (by norm_num)
theorem B2296669 : Blo 1813608 2296669 := bbase (se 3 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 2296669 = 861251) (by norm_num)
theorem B2722661 : Blo 1813608 2722661 := bbase (se 4 (by rfl) ⟨255249, by rfl⟩ : syracuseStep 2722661 = 510499) (by norm_num)
theorem B6122357 : Blo 1813608 6122357 := bbase (se 5 (by rfl) ⟨286985, by rfl⟩ : syracuseStep 6122357 = 573971) (by norm_num)
theorem B2722685 : Blo 1813608 2722685 := bbase (se 3 (by rfl) ⟨510503, by rfl⟩ : syracuseStep 2722685 = 1021007) (by norm_num)
theorem B4361093 : Blo 1813608 4361093 := bbase (se 4 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 4361093 = 817705) (by norm_num)
theorem B2722709 : Blo 1813608 2722709 := bbase (se 6 (by rfl) ⟨63813, by rfl⟩ : syracuseStep 2722709 = 127627) (by norm_num)
theorem B4082597 : Blo 1813608 4082597 := bbase (se 4 (by rfl) ⟨382743, by rfl⟩ : syracuseStep 4082597 = 765487) (by norm_num)
theorem B3443629 : Blo 1813608 3443629 := bbase (se 3 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 3443629 = 1291361) (by norm_num)
theorem B2722733 : Blo 1813608 2722733 := bbase (se 3 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 2722733 = 1021025) (by norm_num)
theorem B2296765 : Blo 1813608 2296765 := bbase (se 3 (by rfl) ⟨430643, by rfl⟩ : syracuseStep 2296765 = 861287) (by norm_num)
theorem B2722757 : Blo 1813608 2722757 := bbase (se 4 (by rfl) ⟨255258, by rfl⟩ : syracuseStep 2722757 = 510517) (by norm_num)
theorem B2722781 : Blo 1813608 2722781 := bbase (se 3 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 2722781 = 1021043) (by norm_num)
theorem B4082669 : Blo 1813608 4082669 := bbase (se 3 (by rfl) ⟨765500, by rfl⟩ : syracuseStep 4082669 = 1531001) (by norm_num)
theorem B2722805 : Blo 1813608 2722805 := bbase (se 5 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 2722805 = 255263) (by norm_num)
theorem B2722829 : Blo 1813608 2722829 := bbase (se 3 (by rfl) ⟨510530, by rfl⟩ : syracuseStep 2722829 = 1021061) (by norm_num)
theorem B2722853 : Blo 1813608 2722853 := bbase (se 4 (by rfl) ⟨255267, by rfl⟩ : syracuseStep 2722853 = 510535) (by norm_num)
theorem B4082741 : Blo 1813608 4082741 := bbase (se 5 (by rfl) ⟨191378, by rfl⟩ : syracuseStep 4082741 = 382757) (by norm_num)
theorem B2722877 : Blo 1813608 2722877 := bbase (se 3 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 2722877 = 1021079) (by norm_num)
theorem B4361285 : Blo 1813608 4361285 := bbase (se 4 (by rfl) ⟨408870, by rfl⟩ : syracuseStep 4361285 = 817741) (by norm_num)
theorem B3443789 : Blo 1813608 3443789 := bbase (se 3 (by rfl) ⟨645710, by rfl⟩ : syracuseStep 3443789 = 1291421) (by norm_num)
theorem B2722901 : Blo 1813608 2722901 := bbase (se 8 (by rfl) ⟨15954, by rfl⟩ : syracuseStep 2722901 = 31909) (by norm_num)
theorem B7359589 : Blo 1813608 7359589 := bbase (se 4 (by rfl) ⟨689961, by rfl⟩ : syracuseStep 7359589 = 1379923) (by norm_num)
theorem B2296937 : Blo 1813608 2296937 := bbase (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) (by norm_num)
theorem B2722925 : Blo 1813608 2722925 := bbase (se 3 (by rfl) ⟨510548, by rfl⟩ : syracuseStep 2722925 = 1021097) (by norm_num)
theorem B13085813 : Blo 1813608 13085813 := bbase (se 5 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 13085813 = 1226795) (by norm_num)
theorem B4082813 : Blo 1813608 4082813 := bbase (se 3 (by rfl) ⟨765527, by rfl⟩ : syracuseStep 4082813 = 1531055) (by norm_num)
theorem B2722949 : Blo 1813608 2722949 := bbase (se 4 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 2722949 = 510553) (by norm_num)
theorem B9809045 : Blo 1813608 9809045 := bbase (se 6 (by rfl) ⟨229899, by rfl⟩ : syracuseStep 9809045 = 459799) (by norm_num)
theorem B18877589 : Blo 1813608 18877589 := bbase (se 6 (by rfl) ⟨442443, by rfl⟩ : syracuseStep 18877589 = 884887) (by norm_num)
theorem B2722973 : Blo 1813608 2722973 := bbase (se 3 (by rfl) ⟨510557, by rfl⟩ : syracuseStep 2722973 = 1021115) (by norm_num)
theorem B2296993 : Blo 1813608 2296993 := bbase (se 2 (by rfl) ⟨861372, by rfl⟩ : syracuseStep 2296993 = 1722745) (by norm_num)
theorem B2722997 : Blo 1813608 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B2985157 : Blo 1813608 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B4082885 : Blo 1813608 4082885 := bbase (se 4 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 4082885 = 765541) (by norm_num)
theorem B2723021 : Blo 1813608 2723021 := bbase (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) (by norm_num)
theorem B15502549 : Blo 1813608 15502549 := bbase (se 7 (by rfl) ⟨181670, by rfl⟩ : syracuseStep 15502549 = 363341) (by norm_num)
theorem B3443933 : Blo 1813608 3443933 := bbase (se 3 (by rfl) ⟨645737, by rfl⟩ : syracuseStep 3443933 = 1291475) (by norm_num)
theorem B9186533 : Blo 1813608 9186533 := bbase (se 4 (by rfl) ⟨861237, by rfl⟩ : syracuseStep 9186533 = 1722475) (by norm_num)
theorem B2723045 : Blo 1813608 2723045 := bbase (se 4 (by rfl) ⟨255285, by rfl⟩ : syracuseStep 2723045 = 510571) (by norm_num)
theorem B2723069 : Blo 1813608 2723069 := bbase (se 3 (by rfl) ⟨510575, by rfl⟩ : syracuseStep 2723069 = 1021151) (by norm_num)
theorem B2297089 : Blo 1813608 2297089 := bbase (se 2 (by rfl) ⟨861408, by rfl⟩ : syracuseStep 2297089 = 1722817) (by norm_num)
theorem B4082957 : Blo 1813608 4082957 := bbase (se 3 (by rfl) ⟨765554, by rfl⟩ : syracuseStep 4082957 = 1531109) (by norm_num)
theorem B2723093 : Blo 1813608 2723093 := bbase (se 6 (by rfl) ⟨63822, by rfl⟩ : syracuseStep 2723093 = 127645) (by norm_num)
theorem B4590877 : Blo 1813608 4590877 := bbase (se 3 (by rfl) ⟨860789, by rfl⟩ : syracuseStep 4590877 = 1721579) (by norm_num)
theorem B6122789 : Blo 1813608 6122789 := bbase (se 4 (by rfl) ⟨574011, by rfl⟩ : syracuseStep 6122789 = 1148023) (by norm_num)
theorem B2723117 : Blo 1813608 2723117 := bbase (se 3 (by rfl) ⟨510584, by rfl⟩ : syracuseStep 2723117 = 1021169) (by norm_num)
theorem B5811509 : Blo 1813608 5811509 := bbase (se 5 (by rfl) ⟨272414, by rfl⟩ : syracuseStep 5811509 = 544829) (by norm_num)
theorem B2723141 : Blo 1813608 2723141 := bbase (se 4 (by rfl) ⟨255294, by rfl⟩ : syracuseStep 2723141 = 510589) (by norm_num)
theorem B4083029 : Blo 1813608 4083029 := bbase (se 11 (by rfl) ⟨2990, by rfl⟩ : syracuseStep 4083029 = 5981) (by norm_num)
theorem B2723165 : Blo 1813608 2723165 := bbase (se 3 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 2723165 = 1021187) (by norm_num)
theorem B4361573 : Blo 1813608 4361573 := bbase (se 4 (by rfl) ⟨408897, by rfl⟩ : syracuseStep 4361573 = 817795) (by norm_num)
theorem B2723189 : Blo 1813608 2723189 := bbase (se 5 (by rfl) ⟨127649, by rfl⟩ : syracuseStep 2723189 = 255299) (by norm_num)
theorem B4590989 : Blo 1813608 4590989 := bbase (se 3 (by rfl) ⟨860810, by rfl⟩ : syracuseStep 4590989 = 1721621) (by norm_num)
theorem B2723213 : Blo 1813608 2723213 := bbase (se 3 (by rfl) ⟨510602, by rfl⟩ : syracuseStep 2723213 = 1021205) (by norm_num)
theorem B4656533 : Blo 1813608 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B4083101 : Blo 1813608 4083101 := bbase (se 3 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 4083101 = 1531163) (by norm_num)
theorem B2723237 : Blo 1813608 2723237 := bbase (se 4 (by rfl) ⟨255303, by rfl⟩ : syracuseStep 2723237 = 510607) (by norm_num)
theorem B2297261 : Blo 1813608 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B2723261 : Blo 1813608 2723261 := bbase (se 3 (by rfl) ⟨510611, by rfl⟩ : syracuseStep 2723261 = 1021223) (by norm_num)
theorem B2723285 : Blo 1813608 2723285 := bbase (se 7 (by rfl) ⟨31913, by rfl⟩ : syracuseStep 2723285 = 63827) (by norm_num)
theorem B4083173 : Blo 1813608 4083173 := bbase (se 4 (by rfl) ⟨382797, by rfl⟩ : syracuseStep 4083173 = 765595) (by norm_num)
theorem B2297317 : Blo 1813608 2297317 := bbase (se 4 (by rfl) ⟨215373, by rfl⟩ : syracuseStep 2297317 = 430747) (by norm_num)
theorem B2723309 : Blo 1813608 2723309 := bbase (se 3 (by rfl) ⟨510620, by rfl⟩ : syracuseStep 2723309 = 1021241) (by norm_num)
theorem B6893045 : Blo 1813608 6893045 := bbase (se 5 (by rfl) ⟨323111, by rfl⟩ : syracuseStep 6893045 = 646223) (by norm_num)
theorem B3444221 : Blo 1813608 3444221 := bbase (se 3 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 3444221 = 1291583) (by norm_num)
theorem B8277509 : Blo 1813608 8277509 := bbase (se 4 (by rfl) ⟨776016, by rfl⟩ : syracuseStep 8277509 = 1552033) (by norm_num)
theorem B2797061 : Blo 1813608 2797061 := bbase (se 4 (by rfl) ⟨262224, by rfl⟩ : syracuseStep 2797061 = 524449) (by norm_num)
theorem B2723333 : Blo 1813608 2723333 := bbase (se 4 (by rfl) ⟨255312, by rfl⟩ : syracuseStep 2723333 = 510625) (by norm_num)
theorem B2723357 : Blo 1813608 2723357 := bbase (se 3 (by rfl) ⟨510629, by rfl⟩ : syracuseStep 2723357 = 1021259) (by norm_num)
theorem B4083245 : Blo 1813608 4083245 := bbase (se 3 (by rfl) ⟨765608, by rfl⟩ : syracuseStep 4083245 = 1531217) (by norm_num)
theorem B2723381 : Blo 1813608 2723381 := bbase (se 5 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 2723381 = 255317) (by norm_num)
theorem B2297413 : Blo 1813608 2297413 := bbase (se 4 (by rfl) ⟨215382, by rfl⟩ : syracuseStep 2297413 = 430765) (by norm_num)
theorem B4591181 : Blo 1813608 4591181 := bbase (se 3 (by rfl) ⟨860846, by rfl⟩ : syracuseStep 4591181 = 1721693) (by norm_num)
theorem B2723405 : Blo 1813608 2723405 := bbase (se 3 (by rfl) ⟨510638, by rfl⟩ : syracuseStep 2723405 = 1021277) (by norm_num)
theorem B4083317 : Blo 1813608 4083317 := bbase (se 5 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 4083317 = 382811) (by norm_num)
theorem B2485885 : Blo 1813608 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B1937029 : Blo 1813608 1937029 := bbase (se 4 (by rfl) ⟨181596, by rfl⟩ : syracuseStep 1937029 = 363193) (by norm_num)
theorem B3927685 : Blo 1813608 3927685 := bbase (se 4 (by rfl) ⟨368220, by rfl⟩ : syracuseStep 3927685 = 736441) (by norm_num)
theorem B3444373 : Blo 1813608 3444373 := bbase (se 6 (by rfl) ⟨80727, by rfl⟩ : syracuseStep 3444373 = 161455) (by norm_num)
theorem B2584237 : Blo 1813608 2584237 := bbase (se 3 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 2584237 = 969089) (by norm_num)
theorem B4140725 : Blo 1813608 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B4083389 : Blo 1813608 4083389 := bbase (se 3 (by rfl) ⟨765635, by rfl⟩ : syracuseStep 4083389 = 1531271) (by norm_num)
theorem B6123221 : Blo 1813608 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B2297585 : Blo 1813608 2297585 := bbase (se 2 (by rfl) ⟨861594, by rfl⟩ : syracuseStep 2297585 = 1723189) (by norm_num)
theorem B4083461 : Blo 1813608 4083461 := bbase (se 4 (by rfl) ⟨382824, by rfl⟩ : syracuseStep 4083461 = 765649) (by norm_num)
theorem B6893333 : Blo 1813608 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B2297641 : Blo 1813608 2297641 := bbase (se 2 (by rfl) ⟨861615, by rfl⟩ : syracuseStep 2297641 = 1723231) (by norm_num)
theorem B5812021 : Blo 1813608 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B4083533 : Blo 1813608 4083533 := bbase (se 3 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 4083533 = 1531325) (by norm_num)
theorem B2297737 : Blo 1813608 2297737 := bbase (se 2 (by rfl) ⟨861651, by rfl⟩ : syracuseStep 2297737 = 1723303) (by norm_num)
theorem B4083605 : Blo 1813608 4083605 := bbase (se 6 (by rfl) ⟨95709, by rfl⟩ : syracuseStep 4083605 = 191419) (by norm_num)
theorem B4591525 : Blo 1813608 4591525 := bbase (se 4 (by rfl) ⟨430455, by rfl⟩ : syracuseStep 4591525 = 860911) (by norm_num)
theorem B3444677 : Blo 1813608 3444677 := bbase (se 4 (by rfl) ⟨322938, by rfl⟩ : syracuseStep 3444677 = 645877) (by norm_num)
theorem B4083677 : Blo 1813608 4083677 := bbase (se 3 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 4083677 = 1531379) (by norm_num)
theorem B1937405 : Blo 1813608 1937405 := bbase (se 3 (by rfl) ⟨363263, by rfl⟩ : syracuseStep 1937405 = 726527) (by norm_num)
theorem B4591637 : Blo 1813608 4591637 := bbase (se 6 (by rfl) ⟨107616, by rfl⟩ : syracuseStep 4591637 = 215233) (by norm_num)
theorem B4083749 : Blo 1813608 4083749 := bbase (se 4 (by rfl) ⟨382851, by rfl⟩ : syracuseStep 4083749 = 765703) (by norm_num)
theorem B1937477 : Blo 1813608 1937477 := bbase (se 4 (by rfl) ⟨181638, by rfl⟩ : syracuseStep 1937477 = 363277) (by norm_num)
theorem B4083821 : Blo 1813608 4083821 := bbase (se 3 (by rfl) ⟨765716, by rfl⟩ : syracuseStep 4083821 = 1531433) (by norm_num)
theorem B1863805 : Blo 1813608 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B6123653 : Blo 1813608 6123653 := bbase (se 4 (by rfl) ⟨574092, by rfl⟩ : syracuseStep 6123653 = 1148185) (by norm_num)
theorem B4083893 : Blo 1813608 4083893 := bbase (se 5 (by rfl) ⟨191432, by rfl⟩ : syracuseStep 4083893 = 382865) (by norm_num)
theorem B4591829 : Blo 1813608 4591829 := bbase (se 7 (by rfl) ⟨53810, by rfl⟩ : syracuseStep 4591829 = 107621) (by norm_num)
theorem B8835301 : Blo 1813608 8835301 := bbase (se 4 (by rfl) ⟨828309, by rfl⟩ : syracuseStep 8835301 = 1656619) (by norm_num)
theorem B4083965 : Blo 1813608 4083965 := bbase (se 3 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 4083965 = 1531487) (by norm_num)
theorem B2584829 : Blo 1813608 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B1937665 : Blo 1813608 1937665 := bbase (se 2 (by rfl) ⟨726624, by rfl⟩ : syracuseStep 1937665 = 1453249) (by norm_num)
theorem B4084037 : Blo 1813608 4084037 := bbase (se 4 (by rfl) ⟨382878, by rfl⟩ : syracuseStep 4084037 = 765757) (by norm_num)
theorem B2584909 : Blo 1813608 2584909 := bbase (se 3 (by rfl) ⟨484670, by rfl⟩ : syracuseStep 2584909 = 969341) (by norm_num)
theorem B2068849 : Blo 1813608 2068849 := bbase (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) (by norm_num)
theorem B4084109 : Blo 1813608 4084109 := bbase (se 3 (by rfl) ⟨765770, by rfl⟩ : syracuseStep 4084109 = 1531541) (by norm_num)
theorem B2068885 : Blo 1813608 2068885 := bbase (se 6 (by rfl) ⟨48489, by rfl⟩ : syracuseStep 2068885 = 96979) (by norm_num)
theorem B13783445 : Blo 1813608 13783445 := bbase (se 6 (by rfl) ⟨323049, by rfl⟩ : syracuseStep 13783445 = 646099) (by norm_num)
theorem B1937849 : Blo 1813608 1937849 := bbase (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) (by norm_num)
theorem B2585029 : Blo 1813608 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B20672981 : Blo 1813608 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B4084181 : Blo 1813608 4084181 := bbase (se 7 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 4084181 = 95723) (by norm_num)
theorem B9187829 : Blo 1813608 9187829 := bbase (se 5 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 9187829 = 861359) (by norm_num)
theorem B4084253 : Blo 1813608 4084253 := bbase (se 3 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 4084253 = 1531595) (by norm_num)
theorem B4592173 : Blo 1813608 4592173 := bbase (se 3 (by rfl) ⟨861032, by rfl⟩ : syracuseStep 4592173 = 1722065) (by norm_num)
theorem B6124085 : Blo 1813608 6124085 := bbase (se 5 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 6124085 = 574133) (by norm_num)
theorem B9441893 : Blo 1813608 9441893 := bbase (se 4 (by rfl) ⟨885177, by rfl⟩ : syracuseStep 9441893 = 1770355) (by norm_num)
theorem B4084325 : Blo 1813608 4084325 := bbase (se 4 (by rfl) ⟨382905, by rfl⟩ : syracuseStep 4084325 = 765811) (by norm_num)
theorem B4592285 : Blo 1813608 4592285 := bbase (se 3 (by rfl) ⟨861053, by rfl⟩ : syracuseStep 4592285 = 1722107) (by norm_num)
theorem B4084397 : Blo 1813608 4084397 := bbase (se 3 (by rfl) ⟨765824, by rfl⟩ : syracuseStep 4084397 = 1531649) (by norm_num)
theorem B13251253 : Blo 1813608 13251253 := bbase (se 5 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 13251253 = 1242305) (by norm_num)
theorem B3445429 : Blo 1813608 3445429 := bbase (se 5 (by rfl) ⟨161504, by rfl⟩ : syracuseStep 3445429 = 323009) (by norm_num)
theorem B4084469 : Blo 1813608 4084469 := bbase (se 5 (by rfl) ⟨191459, by rfl⟩ : syracuseStep 4084469 = 382919) (by norm_num)
theorem B3060517 : Blo 1813608 3060517 := bbase (se 4 (by rfl) ⟨286923, by rfl⟩ : syracuseStep 3060517 = 573847) (by norm_num)
theorem B13775669 : Blo 1813608 13775669 := bbase (se 5 (by rfl) ⟨645734, by rfl⟩ : syracuseStep 13775669 = 1291469) (by norm_num)
theorem B4084541 : Blo 1813608 4084541 := bbase (se 3 (by rfl) ⟨765851, by rfl⟩ : syracuseStep 4084541 = 1531703) (by norm_num)
theorem B3445573 : Blo 1813608 3445573 := bbase (se 4 (by rfl) ⟨323022, by rfl⟩ : syracuseStep 3445573 = 646045) (by norm_num)
theorem B4592477 : Blo 1813608 4592477 := bbase (se 3 (by rfl) ⟨861089, by rfl⟩ : syracuseStep 4592477 = 1722179) (by norm_num)
theorem B3060605 : Blo 1813608 3060605 := bbase (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) (by norm_num)
theorem B5165957 : Blo 1813608 5165957 := bbase (se 4 (by rfl) ⟨484308, by rfl⟩ : syracuseStep 5165957 = 968617) (by norm_num)
theorem B4084613 : Blo 1813608 4084613 := bbase (se 4 (by rfl) ⟨382932, by rfl⟩ : syracuseStep 4084613 = 765865) (by norm_num)
theorem B3314621 : Blo 1813608 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B4084685 : Blo 1813608 4084685 := bbase (se 3 (by rfl) ⟨765878, by rfl⟩ : syracuseStep 4084685 = 1531757) (by norm_num)
theorem B6124517 : Blo 1813608 6124517 := bbase (se 4 (by rfl) ⟨574173, by rfl⟩ : syracuseStep 6124517 = 1148347) (by norm_num)
theorem B3445733 : Blo 1813608 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B2757613 : Blo 1813608 2757613 := bbase (se 3 (by rfl) ⟨517052, by rfl⟩ : syracuseStep 2757613 = 1034105) (by norm_num)
theorem B3060733 : Blo 1813608 3060733 := bbase (se 3 (by rfl) ⟨573887, by rfl⟩ : syracuseStep 3060733 = 1147775) (by norm_num)
theorem B4084757 : Blo 1813608 4084757 := bbase (se 6 (by rfl) ⟨95736, by rfl⟩ : syracuseStep 4084757 = 191473) (by norm_num)
theorem B3060821 : Blo 1813608 3060821 := bbase (se 8 (by rfl) ⟨17934, by rfl⟩ : syracuseStep 3060821 = 35869) (by norm_num)
theorem B4084829 : Blo 1813608 4084829 := bbase (se 3 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 4084829 = 1531811) (by norm_num)
theorem B3445877 : Blo 1813608 3445877 := bbase (se 5 (by rfl) ⟨161525, by rfl⟩ : syracuseStep 3445877 = 323051) (by norm_num)
theorem B15504533 : Blo 1813608 15504533 := bbase (se 6 (by rfl) ⟨363387, by rfl⟩ : syracuseStep 15504533 = 726775) (by norm_num)
theorem B4084901 : Blo 1813608 4084901 := bbase (se 4 (by rfl) ⟨382959, by rfl⟩ : syracuseStep 4084901 = 765919) (by norm_num)
theorem B1889449 : Blo 1813608 1889449 := bbase (se 2 (by rfl) ⟨708543, by rfl⟩ : syracuseStep 1889449 = 1417087) (by norm_num)
theorem B1938601 : Blo 1813608 1938601 := bbase (se 2 (by rfl) ⟨726975, by rfl⟩ : syracuseStep 1938601 = 1453951) (by norm_num)
theorem B4592821 : Blo 1813608 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B3060949 : Blo 1813608 3060949 := bbase (se 7 (by rfl) ⟨35870, by rfl⟩ : syracuseStep 3060949 = 71741) (by norm_num)
theorem B4084973 : Blo 1813608 4084973 := bbase (se 3 (by rfl) ⟨765932, by rfl⟩ : syracuseStep 4084973 = 1531865) (by norm_num)
theorem B1938673 : Blo 1813608 1938673 := bbase (se 2 (by rfl) ⟨727002, by rfl⟩ : syracuseStep 1938673 = 1454005) (by norm_num)
theorem B2069761 : Blo 1813608 2069761 := bbase (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) (by norm_num)
theorem B4592933 : Blo 1813608 4592933 := bbase (se 4 (by rfl) ⟨430587, by rfl⟩ : syracuseStep 4592933 = 861175) (by norm_num)
theorem B3061037 : Blo 1813608 3061037 := bbase (se 3 (by rfl) ⟨573944, by rfl⟩ : syracuseStep 3061037 = 1147889) (by norm_num)
theorem B4085045 : Blo 1813608 4085045 := bbase (se 5 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 4085045 = 382973) (by norm_num)
theorem B6886741 : Blo 1813608 6886741 := bbase (se 14 (by rfl) ⟨630, by rfl⟩ : syracuseStep 6886741 = 1261) (by norm_num)
theorem B7853429 : Blo 1813608 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B4085117 : Blo 1813608 4085117 := bbase (se 3 (by rfl) ⟨765959, by rfl⟩ : syracuseStep 4085117 = 1531919) (by norm_num)
theorem B6124949 : Blo 1813608 6124949 := bbase (se 6 (by rfl) ⟨143553, by rfl⟩ : syracuseStep 6124949 = 287107) (by norm_num)
theorem B3446165 : Blo 1813608 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B3061165 : Blo 1813608 3061165 := bbase (se 3 (by rfl) ⟨573968, by rfl⟩ : syracuseStep 3061165 = 1147937) (by norm_num)
theorem B10474933 : Blo 1813608 10474933 := bbase (se 5 (by rfl) ⟨491012, by rfl⟩ : syracuseStep 10474933 = 982025) (by norm_num)
theorem B8721877 : Blo 1813608 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B4593125 : Blo 1813608 4593125 := bbase (se 4 (by rfl) ⟨430605, by rfl⟩ : syracuseStep 4593125 = 861211) (by norm_num)
theorem B3061253 : Blo 1813608 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B5813765 : Blo 1813608 5813765 := bbase (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) (by norm_num)
theorem B5166629 : Blo 1813608 5166629 := bbase (se 4 (by rfl) ⟨484371, by rfl⟩ : syracuseStep 5166629 = 968743) (by norm_num)
theorem B3446317 : Blo 1813608 3446317 := bbase (se 3 (by rfl) ⟨646184, by rfl⟩ : syracuseStep 3446317 = 1292369) (by norm_num)
theorem B6207029 : Blo 1813608 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B16553557 : Blo 1813608 16553557 := bbase (se 8 (by rfl) ⟨96993, by rfl⟩ : syracuseStep 16553557 = 193987) (by norm_num)
theorem B6887045 : Blo 1813608 6887045 := bbase (se 4 (by rfl) ⟨645660, by rfl⟩ : syracuseStep 6887045 = 1291321) (by norm_num)
theorem B3061381 : Blo 1813608 3061381 := bbase (se 4 (by rfl) ⟨287004, by rfl⟩ : syracuseStep 3061381 = 574009) (by norm_num)
theorem B5813957 : Blo 1813608 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B3061469 : Blo 1813608 3061469 := bbase (se 3 (by rfl) ⟨574025, by rfl⟩ : syracuseStep 3061469 = 1148051) (by norm_num)
theorem B9189125 : Blo 1813608 9189125 := bbase (se 4 (by rfl) ⟨861480, by rfl⟩ : syracuseStep 9189125 = 1722961) (by norm_num)
theorem B11622197 : Blo 1813608 11622197 := bbase (se 5 (by rfl) ⟨544790, by rfl⟩ : syracuseStep 11622197 = 1089581) (by norm_num)
theorem B4593469 : Blo 1813608 4593469 := bbase (se 3 (by rfl) ⟨861275, by rfl⟩ : syracuseStep 4593469 = 1722551) (by norm_num)
theorem B6125381 : Blo 1813608 6125381 := bbase (se 4 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 6125381 = 1148509) (by norm_num)
theorem B3061597 : Blo 1813608 3061597 := bbase (se 3 (by rfl) ⟨574049, by rfl⟩ : syracuseStep 3061597 = 1148099) (by norm_num)
theorem B3446621 : Blo 1813608 3446621 := bbase (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) (by norm_num)
theorem B1963873 : Blo 1813608 1963873 := bbase (se 2 (by rfl) ⟨736452, by rfl⟩ : syracuseStep 1963873 = 1472905) (by norm_num)
theorem B2905973 : Blo 1813608 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B4593581 : Blo 1813608 4593581 := bbase (se 3 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 4593581 = 1722593) (by norm_num)
theorem B3061685 : Blo 1813608 3061685 := bbase (se 5 (by rfl) ⟨143516, by rfl⟩ : syracuseStep 3061685 = 287033) (by norm_num)
theorem B5167061 : Blo 1813608 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B2906165 : Blo 1813608 2906165 := bbase (se 5 (by rfl) ⟨136226, by rfl⟩ : syracuseStep 2906165 = 272453) (by norm_num)
theorem B3061813 : Blo 1813608 3061813 := bbase (se 5 (by rfl) ⟨143522, by rfl⟩ : syracuseStep 3061813 = 287045) (by norm_num)
theorem B4593773 : Blo 1813608 4593773 := bbase (se 3 (by rfl) ⟨861332, by rfl⟩ : syracuseStep 4593773 = 1722665) (by norm_num)
theorem B3061901 : Blo 1813608 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B2906293 : Blo 1813608 2906293 := bbase (se 5 (by rfl) ⟨136232, by rfl⟩ : syracuseStep 2906293 = 272465) (by norm_num)
theorem B6125813 : Blo 1813608 6125813 := bbase (se 5 (by rfl) ⟨287147, by rfl⟩ : syracuseStep 6125813 = 574295) (by norm_num)
theorem B3062029 : Blo 1813608 3062029 := bbase (se 3 (by rfl) ⟨574130, by rfl⟩ : syracuseStep 3062029 = 1148261) (by norm_num)
theorem B3316045 : Blo 1813608 3316045 := bbase (se 3 (by rfl) ⟨621758, by rfl⟩ : syracuseStep 3316045 = 1243517) (by norm_num)
theorem B3062117 : Blo 1813608 3062117 := bbase (se 4 (by rfl) ⟨287073, by rfl⟩ : syracuseStep 3062117 = 574147) (by norm_num)
theorem B4594117 : Blo 1813608 4594117 := bbase (se 4 (by rfl) ⟨430698, by rfl⟩ : syracuseStep 4594117 = 861397) (by norm_num)
theorem B18627029 : Blo 1813608 18627029 := bbase (se 7 (by rfl) ⟨218285, by rfl⟩ : syracuseStep 18627029 = 436571) (by norm_num)
theorem B3062245 : Blo 1813608 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B4594229 : Blo 1813608 4594229 := bbase (se 5 (by rfl) ⟨215354, by rfl⟩ : syracuseStep 4594229 = 430709) (by norm_num)
theorem B3062333 : Blo 1813608 3062333 := bbase (se 3 (by rfl) ⟨574187, by rfl⟩ : syracuseStep 3062333 = 1148375) (by norm_num)
theorem B2210413 : Blo 1813608 2210413 := bbase (se 3 (by rfl) ⟨414452, by rfl⟩ : syracuseStep 2210413 = 828905) (by norm_num)
theorem B6126245 : Blo 1813608 6126245 := bbase (se 4 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 6126245 = 1148671) (by norm_num)
theorem B3062461 : Blo 1813608 3062461 := bbase (se 3 (by rfl) ⟨574211, by rfl⟩ : syracuseStep 3062461 = 1148423) (by norm_num)
theorem B5167813 : Blo 1813608 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B15923957 : Blo 1813608 15923957 := bbase (se 5 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 15923957 = 1492871) (by norm_num)
theorem B4594421 : Blo 1813608 4594421 := bbase (se 5 (by rfl) ⟨215363, by rfl⟩ : syracuseStep 4594421 = 430727) (by norm_num)
theorem B5593877 : Blo 1813608 5593877 := bbase (se 6 (by rfl) ⟨131106, by rfl⟩ : syracuseStep 5593877 = 262213) (by norm_num)
theorem B3062549 : Blo 1813608 3062549 := bbase (se 6 (by rfl) ⟨71778, by rfl⟩ : syracuseStep 3062549 = 143557) (by norm_num)
theorem B7748405 : Blo 1813608 7748405 := bbase (se 5 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 7748405 = 726413) (by norm_num)
theorem B2906933 : Blo 1813608 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B3677005 : Blo 1813608 3677005 := bbase (se 3 (by rfl) ⟨689438, by rfl⟩ : syracuseStep 3677005 = 1378877) (by norm_num)
theorem B3062677 : Blo 1813608 3062677 := bbase (se 6 (by rfl) ⟨71781, by rfl⟩ : syracuseStep 3062677 = 143563) (by norm_num)
theorem B3062765 : Blo 1813608 3062765 := bbase (se 3 (by rfl) ⟨574268, by rfl⟩ : syracuseStep 3062765 = 1148537) (by norm_num)
theorem B9190421 : Blo 1813608 9190421 := bbase (se 6 (by rfl) ⟨215400, by rfl⟩ : syracuseStep 9190421 = 430801) (by norm_num)
theorem B4594765 : Blo 1813608 4594765 := bbase (se 3 (by rfl) ⟨861518, by rfl⟩ : syracuseStep 4594765 = 1723037) (by norm_num)
theorem B6126677 : Blo 1813608 6126677 := bbase (se 8 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 6126677 = 71797) (by norm_num)
theorem B2210917 : Blo 1813608 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B3062893 : Blo 1813608 3062893 := bbase (se 3 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 3062893 = 1148585) (by norm_num)
theorem B33119381 : Blo 1813608 33119381 := bbase (se 6 (by rfl) ⟨776235, by rfl⟩ : syracuseStep 33119381 = 1552471) (by norm_num)
theorem B4594877 : Blo 1813608 4594877 := bbase (se 3 (by rfl) ⟨861539, by rfl⟩ : syracuseStep 4594877 = 1723079) (by norm_num)
theorem B3062981 : Blo 1813608 3062981 := bbase (se 4 (by rfl) ⟨287154, by rfl⟩ : syracuseStep 3062981 = 574309) (by norm_num)
theorem B3873997 : Blo 1813608 3873997 := bbase (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) (by norm_num)
theorem B2907389 : Blo 1813608 2907389 := bbase (se 3 (by rfl) ⟨545135, by rfl⟩ : syracuseStep 2907389 = 1090271) (by norm_num)
theorem B3063109 : Blo 1813608 3063109 := bbase (se 4 (by rfl) ⟨287166, by rfl⟩ : syracuseStep 3063109 = 574333) (by norm_num)
theorem B1989965 : Blo 1813608 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B11181397 : Blo 1813608 11181397 := bbase (se 11 (by rfl) ⟨8189, by rfl⟩ : syracuseStep 11181397 = 16379) (by norm_num)
theorem B4595069 : Blo 1813608 4595069 := bbase (se 3 (by rfl) ⟨861575, by rfl⟩ : syracuseStep 4595069 = 1723151) (by norm_num)
theorem B3980677 : Blo 1813608 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B5520773 : Blo 1813608 5520773 := bbase (se 4 (by rfl) ⟨517572, by rfl⟩ : syracuseStep 5520773 = 1035145) (by norm_num)
theorem B10624405 : Blo 1813608 10624405 := bbase (se 6 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 10624405 = 498019) (by norm_num)
theorem B3063197 : Blo 1813608 3063197 := bbase (se 3 (by rfl) ⟨574349, by rfl⟩ : syracuseStep 3063197 = 1148699) (by norm_num)
theorem B9182645 : Blo 1813608 9182645 := bbase (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) (by norm_num)
theorem B3677629 : Blo 1813608 3677629 := bbase (se 3 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 3677629 = 1379111) (by norm_num)
theorem B2907613 : Blo 1813608 2907613 := bbase (se 3 (by rfl) ⟨545177, by rfl⟩ : syracuseStep 2907613 = 1090355) (by norm_num)
theorem B3980773 : Blo 1813608 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B14720501 : Blo 1813608 14720501 := bbase (se 5 (by rfl) ⟨690023, by rfl⟩ : syracuseStep 14720501 = 1380047) (by norm_num)
theorem B6127109 : Blo 1813608 6127109 := bbase (se 4 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 6127109 = 1148833) (by norm_num)
theorem B2760205 : Blo 1813608 2760205 := bbase (se 3 (by rfl) ⟨517538, by rfl⟩ : syracuseStep 2760205 = 1035077) (by norm_num)
theorem B10337813 : Blo 1813608 10337813 := bbase (se 6 (by rfl) ⟨242292, by rfl⟩ : syracuseStep 10337813 = 484585) (by norm_num)
theorem B2907677 : Blo 1813608 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B3063325 : Blo 1813608 3063325 := bbase (se 3 (by rfl) ⟨574373, by rfl⟩ : syracuseStep 3063325 = 1148747) (by norm_num)
theorem B7356005 : Blo 1813608 7356005 := bbase (se 4 (by rfl) ⟨689625, by rfl⟩ : syracuseStep 7356005 = 1379251) (by norm_num)
theorem B3063413 : Blo 1813608 3063413 := bbase (se 5 (by rfl) ⟨143597, by rfl⟩ : syracuseStep 3063413 = 287195) (by norm_num)
theorem B2907805 : Blo 1813608 2907805 := bbase (se 3 (by rfl) ⟨545213, by rfl⟩ : syracuseStep 2907805 = 1090427) (by norm_num)
theorem B4906661 : Blo 1813608 4906661 := bbase (se 4 (by rfl) ⟨459999, by rfl⟩ : syracuseStep 4906661 = 919999) (by norm_num)
theorem B3874493 : Blo 1813608 3874493 := bbase (se 3 (by rfl) ⟨726467, by rfl⟩ : syracuseStep 3874493 = 1452935) (by norm_num)
theorem B6889157 : Blo 1813608 6889157 := bbase (se 4 (by rfl) ⟨645858, by rfl⟩ : syracuseStep 6889157 = 1291717) (by norm_num)
theorem B4595413 : Blo 1813608 4595413 := bbase (se 7 (by rfl) ⟨53852, by rfl⟩ : syracuseStep 4595413 = 107705) (by norm_num)
theorem B2178797 : Blo 1813608 2178797 := bbase (se 3 (by rfl) ⟨408524, by rfl⟩ : syracuseStep 2178797 = 817049) (by norm_num)
theorem B3063541 : Blo 1813608 3063541 := bbase (se 5 (by rfl) ⟨143603, by rfl⟩ : syracuseStep 3063541 = 287207) (by norm_num)
theorem B2096965 : Blo 1813608 2096965 := bbase (se 4 (by rfl) ⟨196590, by rfl⟩ : syracuseStep 2096965 = 393181) (by norm_num)
theorem B4595525 : Blo 1813608 4595525 := bbase (se 4 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 4595525 = 861661) (by norm_num)
theorem B2178893 : Blo 1813608 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B3063629 : Blo 1813608 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B2178913 : Blo 1813608 2178913 := bbase (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) (by norm_num)
theorem B3104669 : Blo 1813608 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B6127541 : Blo 1813608 6127541 := bbase (se 5 (by rfl) ⟨287228, by rfl⟩ : syracuseStep 6127541 = 574457) (by norm_num)
theorem B3063757 : Blo 1813608 3063757 := bbase (se 3 (by rfl) ⟨574454, by rfl⟩ : syracuseStep 3063757 = 1148909) (by norm_num)
theorem B6889445 : Blo 1813608 6889445 := bbase (se 4 (by rfl) ⟨645885, by rfl⟩ : syracuseStep 6889445 = 1291771) (by norm_num)
theorem B2179057 : Blo 1813608 2179057 := bbase (se 2 (by rfl) ⟨817146, by rfl⟩ : syracuseStep 2179057 = 1634293) (by norm_num)
theorem B17440757 : Blo 1813608 17440757 := bbase (se 5 (by rfl) ⟨817535, by rfl⟩ : syracuseStep 17440757 = 1635071) (by norm_num)
theorem B3063811 : Blo 1813608 3063811 := bstep (se 1 (by rfl) ⟨2297858, by rfl⟩ : syracuseStep 3063811 = 4595717) B4595717
theorem B29835317 : Blo 1813608 29835317 := bstep (se 5 (by rfl) ⟨1398530, by rfl⟩ : syracuseStep 29835317 = 2797061) B2797061
theorem B2908241 : Blo 1813608 2908241 := bstep (se 2 (by rfl) ⟨1090590, by rfl⟩ : syracuseStep 2908241 = 2181181) B2181181
theorem B5169329 : Blo 1813608 5169329 := bstep (se 2 (by rfl) ⟨1938498, by rfl⟩ : syracuseStep 5169329 = 3876997) B3876997
theorem B3875057 : Blo 1813608 3875057 := bstep (se 2 (by rfl) ⟨1453146, by rfl⟩ : syracuseStep 3875057 = 2906293) B2906293
theorem B11780401 : Blo 1813608 11780401 := bstep (se 2 (by rfl) ⟨4417650, by rfl⟩ : syracuseStep 11780401 = 8835301) B8835301
theorem B5169521 : Blo 1813608 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B4907441 : Blo 1813608 4907441 := bstep (se 2 (by rfl) ⟨1840290, by rfl⟩ : syracuseStep 4907441 = 3680581) B3680581
theorem B9183779 : Blo 1813608 9183779 := bstep (se 1 (by rfl) ⟨6887834, by rfl⟩ : syracuseStep 9183779 = 13775669) B13775669
theorem B31007285 : Blo 1813608 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B2040403 : Blo 1813608 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B2720417 : Blo 1813608 2720417 := bstep (se 2 (by rfl) ⟨1020156, by rfl⟩ : syracuseStep 2720417 = 2040313) B2040313
theorem B2720435 : Blo 1813608 2720435 := bstep (se 1 (by rfl) ⟨2040326, by rfl⟩ : syracuseStep 2720435 = 4080653) B4080653
theorem B2720465 : Blo 1813608 2720465 := bstep (se 2 (by rfl) ⟨1020174, by rfl⟩ : syracuseStep 2720465 = 2040349) B2040349
theorem B2720483 : Blo 1813608 2720483 := bstep (se 1 (by rfl) ⟨2040362, by rfl⟩ : syracuseStep 2720483 = 4080725) B4080725
theorem B2040547 : Blo 1813608 2040547 := bstep (se 1 (by rfl) ⟨1530410, by rfl⟩ : syracuseStep 2040547 = 3060821) B3060821
theorem B2720513 : Blo 1813608 2720513 := bstep (se 2 (by rfl) ⟨1020192, by rfl⟩ : syracuseStep 2720513 = 2040385) B2040385
theorem B2720531 : Blo 1813608 2720531 := bstep (se 1 (by rfl) ⟨2040398, by rfl⟩ : syracuseStep 2720531 = 4080797) B4080797
theorem B2720561 : Blo 1813608 2720561 := bstep (se 2 (by rfl) ⟨1020210, by rfl⟩ : syracuseStep 2720561 = 2040421) B2040421
theorem B2720579 : Blo 1813608 2720579 := bstep (se 1 (by rfl) ⟨2040434, by rfl⟩ : syracuseStep 2720579 = 4080869) B4080869
theorem B23257925 : Blo 1813608 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B2720609 : Blo 1813608 2720609 := bstep (se 2 (by rfl) ⟨1020228, by rfl⟩ : syracuseStep 2720609 = 2040457) B2040457
theorem B2720627 : Blo 1813608 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B2040691 : Blo 1813608 2040691 := bstep (se 1 (by rfl) ⟨1530518, by rfl⟩ : syracuseStep 2040691 = 3061037) B3061037
theorem B10077061 : Blo 1813608 10077061 := bstep (se 4 (by rfl) ⟨944724, by rfl⟩ : syracuseStep 10077061 = 1889449) B1889449
theorem B2720657 : Blo 1813608 2720657 := bstep (se 2 (by rfl) ⟨1020246, by rfl⟩ : syracuseStep 2720657 = 2040493) B2040493
theorem B2720675 : Blo 1813608 2720675 := bstep (se 1 (by rfl) ⟨2040506, by rfl⟩ : syracuseStep 2720675 = 4081013) B4081013
theorem B5235619 : Blo 1813608 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B6890417 : Blo 1813608 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B2720705 : Blo 1813608 2720705 := bstep (se 2 (by rfl) ⟨1020264, by rfl⟩ : syracuseStep 2720705 = 2040529) B2040529
theorem B2720723 : Blo 1813608 2720723 := bstep (se 1 (by rfl) ⟨2040542, by rfl⟩ : syracuseStep 2720723 = 4081085) B4081085
theorem B2720753 : Blo 1813608 2720753 := bstep (se 2 (by rfl) ⟨1020282, by rfl⟩ : syracuseStep 2720753 = 2040565) B2040565
theorem B2720771 : Blo 1813608 2720771 := bstep (se 1 (by rfl) ⟨2040578, by rfl⟩ : syracuseStep 2720771 = 4081157) B4081157
theorem B2040835 : Blo 1813608 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B3875843 : Blo 1813608 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B2720801 : Blo 1813608 2720801 := bstep (se 2 (by rfl) ⟨1020300, by rfl⟩ : syracuseStep 2720801 = 2040601) B2040601
theorem B4138019 : Blo 1813608 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B4080689 : Blo 1813608 4080689 := bstep (se 2 (by rfl) ⟨1530258, by rfl⟩ : syracuseStep 4080689 = 3060517) B3060517
theorem B2720819 : Blo 1813608 2720819 := bstep (se 1 (by rfl) ⟨2040614, by rfl⟩ : syracuseStep 2720819 = 4081229) B4081229
theorem B4080707 : Blo 1813608 4080707 := bstep (se 1 (by rfl) ⟨3060530, by rfl⟩ : syracuseStep 4080707 = 6121061) B6121061
theorem B20661317 : Blo 1813608 20661317 := bstep (se 4 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 20661317 = 3873997) B3873997
theorem B2720849 : Blo 1813608 2720849 := bstep (se 2 (by rfl) ⟨1020318, by rfl⟩ : syracuseStep 2720849 = 2040637) B2040637
theorem B2720867 : Blo 1813608 2720867 := bstep (se 1 (by rfl) ⟨2040650, by rfl⟩ : syracuseStep 2720867 = 4081301) B4081301
theorem B2720897 : Blo 1813608 2720897 := bstep (se 2 (by rfl) ⟨1020336, by rfl⟩ : syracuseStep 2720897 = 2040673) B2040673
theorem B2720915 : Blo 1813608 2720915 := bstep (se 1 (by rfl) ⟨2040686, by rfl⟩ : syracuseStep 2720915 = 4081373) B4081373
theorem B2040979 : Blo 1813608 2040979 := bstep (se 1 (by rfl) ⟨1530734, by rfl⟩ : syracuseStep 2040979 = 3061469) B3061469
theorem B2720945 : Blo 1813608 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B2720963 : Blo 1813608 2720963 := bstep (se 1 (by rfl) ⟨2040722, by rfl⟩ : syracuseStep 2720963 = 4081445) B4081445
theorem B2720993 : Blo 1813608 2720993 := bstep (se 2 (by rfl) ⟨1020372, by rfl⟩ : syracuseStep 2720993 = 2040745) B2040745
theorem B2721011 : Blo 1813608 2721011 := bstep (se 1 (by rfl) ⟨2040758, by rfl⟩ : syracuseStep 2721011 = 4081517) B4081517
theorem B10339589 : Blo 1813608 10339589 := bstep (se 4 (by rfl) ⟨969336, by rfl⟩ : syracuseStep 10339589 = 1938673) B1938673
theorem B2721041 : Blo 1813608 2721041 := bstep (se 2 (by rfl) ⟨1020390, by rfl⟩ : syracuseStep 2721041 = 2040781) B2040781
theorem B2721059 : Blo 1813608 2721059 := bstep (se 1 (by rfl) ⟨2040794, by rfl⟩ : syracuseStep 2721059 = 4081589) B4081589
theorem B2041123 : Blo 1813608 2041123 := bstep (se 1 (by rfl) ⟨1530842, by rfl⟩ : syracuseStep 2041123 = 3061685) B3061685
theorem B2721089 : Blo 1813608 2721089 := bstep (se 2 (by rfl) ⟨1020408, by rfl⟩ : syracuseStep 2721089 = 2040817) B2040817
theorem B9184589 : Blo 1813608 9184589 := bstep (se 3 (by rfl) ⟨1722110, by rfl⟩ : syracuseStep 9184589 = 3444221) B3444221
theorem B4080977 : Blo 1813608 4080977 := bstep (se 2 (by rfl) ⟨1530366, by rfl⟩ : syracuseStep 4080977 = 3060733) B3060733
theorem B2721107 : Blo 1813608 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B4080995 : Blo 1813608 4080995 := bstep (se 1 (by rfl) ⟨3060746, by rfl⟩ : syracuseStep 4080995 = 6121493) B6121493
theorem B2721137 : Blo 1813608 2721137 := bstep (se 2 (by rfl) ⟨1020426, by rfl⟩ : syracuseStep 2721137 = 2040853) B2040853
theorem B2721155 : Blo 1813608 2721155 := bstep (se 1 (by rfl) ⟨2040866, by rfl⟩ : syracuseStep 2721155 = 4081733) B4081733
theorem B99313037 : Blo 1813608 99313037 := bstep (se 3 (by rfl) ⟨18621194, by rfl⟩ : syracuseStep 99313037 = 37242389) B37242389
theorem B2721185 : Blo 1813608 2721185 := bstep (se 2 (by rfl) ⟨1020444, by rfl⟩ : syracuseStep 2721185 = 2040889) B2040889
theorem B2721203 : Blo 1813608 2721203 := bstep (se 1 (by rfl) ⟨2040902, by rfl⟩ : syracuseStep 2721203 = 4081805) B4081805
theorem B2041267 : Blo 1813608 2041267 := bstep (se 1 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 2041267 = 3061901) B3061901
theorem B2721233 : Blo 1813608 2721233 := bstep (se 2 (by rfl) ⟨1020462, by rfl⟩ : syracuseStep 2721233 = 2040925) B2040925
theorem B2721251 : Blo 1813608 2721251 := bstep (se 1 (by rfl) ⟨2040938, by rfl⟩ : syracuseStep 2721251 = 4081877) B4081877
theorem B2721281 : Blo 1813608 2721281 := bstep (se 2 (by rfl) ⟨1020480, by rfl⟩ : syracuseStep 2721281 = 2040961) B2040961
theorem B2721299 : Blo 1813608 2721299 := bstep (se 1 (by rfl) ⟨2040974, by rfl⟩ : syracuseStep 2721299 = 4081949) B4081949
theorem B2721329 : Blo 1813608 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B2721347 : Blo 1813608 2721347 := bstep (se 1 (by rfl) ⟨2041010, by rfl⟩ : syracuseStep 2721347 = 4082021) B4082021
theorem B2041411 : Blo 1813608 2041411 := bstep (se 1 (by rfl) ⟨1531058, by rfl⟩ : syracuseStep 2041411 = 3062117) B3062117
theorem B2721377 : Blo 1813608 2721377 := bstep (se 2 (by rfl) ⟨1020516, by rfl⟩ : syracuseStep 2721377 = 2041033) B2041033
theorem B4081265 : Blo 1813608 4081265 := bstep (se 2 (by rfl) ⟨1530474, by rfl⟩ : syracuseStep 4081265 = 3060949) B3060949
theorem B20670065 : Blo 1813608 20670065 := bstep (se 2 (by rfl) ⟨7751274, by rfl⟩ : syracuseStep 20670065 = 15502549) B15502549
theorem B2721395 : Blo 1813608 2721395 := bstep (se 1 (by rfl) ⟨2041046, by rfl⟩ : syracuseStep 2721395 = 4082093) B4082093
theorem B4081283 : Blo 1813608 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B2721425 : Blo 1813608 2721425 := bstep (se 2 (by rfl) ⟨1020534, by rfl⟩ : syracuseStep 2721425 = 2041069) B2041069
theorem B2721443 : Blo 1813608 2721443 := bstep (se 1 (by rfl) ⟨2041082, by rfl⟩ : syracuseStep 2721443 = 4082165) B4082165
theorem B2721473 : Blo 1813608 2721473 := bstep (se 2 (by rfl) ⟨1020552, by rfl⟩ : syracuseStep 2721473 = 2041105) B2041105
theorem B10340045 : Blo 1813608 10340045 := bstep (se 3 (by rfl) ⟨1938758, by rfl⟩ : syracuseStep 10340045 = 3877517) B3877517
theorem B6121169 : Blo 1813608 6121169 := bstep (se 2 (by rfl) ⟨2295438, by rfl⟩ : syracuseStep 6121169 = 4590877) B4590877
theorem B2721491 : Blo 1813608 2721491 := bstep (se 1 (by rfl) ⟨2041118, by rfl⟩ : syracuseStep 2721491 = 4082237) B4082237
theorem B2041555 : Blo 1813608 2041555 := bstep (se 1 (by rfl) ⟨1531166, by rfl⟩ : syracuseStep 2041555 = 3062333) B3062333
theorem B2721521 : Blo 1813608 2721521 := bstep (se 2 (by rfl) ⟨1020570, by rfl⟩ : syracuseStep 2721521 = 2041141) B2041141
theorem B2721539 : Blo 1813608 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B13084429 : Blo 1813608 13084429 := bstep (se 3 (by rfl) ⟨2453330, by rfl⟩ : syracuseStep 13084429 = 4906661) B4906661
theorem B2721569 : Blo 1813608 2721569 := bstep (se 2 (by rfl) ⟨1020588, by rfl⟩ : syracuseStep 2721569 = 2041177) B2041177
theorem B2721587 : Blo 1813608 2721587 := bstep (se 1 (by rfl) ⟨2041190, by rfl⟩ : syracuseStep 2721587 = 4082381) B4082381
theorem B10331981 : Blo 1813608 10331981 := bstep (se 3 (by rfl) ⟨1937246, by rfl⟩ : syracuseStep 10331981 = 3874493) B3874493
theorem B2721617 : Blo 1813608 2721617 := bstep (se 2 (by rfl) ⟨1020606, by rfl⟩ : syracuseStep 2721617 = 2041213) B2041213
theorem B2721635 : Blo 1813608 2721635 := bstep (se 1 (by rfl) ⟨2041226, by rfl⟩ : syracuseStep 2721635 = 4082453) B4082453
theorem B3729251 : Blo 1813608 3729251 := bstep (se 1 (by rfl) ⟨2796938, by rfl⟩ : syracuseStep 3729251 = 5593877) B5593877
theorem B2041699 : Blo 1813608 2041699 := bstep (se 1 (by rfl) ⟨1531274, by rfl⟩ : syracuseStep 2041699 = 3062549) B3062549
theorem B14165873 : Blo 1813608 14165873 := bstep (se 2 (by rfl) ⟨5312202, by rfl⟩ : syracuseStep 14165873 = 10624405) B10624405
theorem B2721665 : Blo 1813608 2721665 := bstep (se 2 (by rfl) ⟨1020624, by rfl⟩ : syracuseStep 2721665 = 2041249) B2041249
theorem B4081553 : Blo 1813608 4081553 := bstep (se 2 (by rfl) ⟨1530582, by rfl⟩ : syracuseStep 4081553 = 3061165) B3061165
theorem B2721683 : Blo 1813608 2721683 := bstep (se 1 (by rfl) ⟨2041262, by rfl⟩ : syracuseStep 2721683 = 4082525) B4082525
theorem B4081571 : Blo 1813608 4081571 := bstep (se 1 (by rfl) ⟨3061178, by rfl⟩ : syracuseStep 4081571 = 6122357) B6122357
theorem B2721713 : Blo 1813608 2721713 := bstep (se 2 (by rfl) ⟨1020642, by rfl⟩ : syracuseStep 2721713 = 2041285) B2041285
theorem B2721731 : Blo 1813608 2721731 := bstep (se 1 (by rfl) ⟨2041298, by rfl⟩ : syracuseStep 2721731 = 4082597) B4082597
theorem B5810125 : Blo 1813608 5810125 := bstep (se 3 (by rfl) ⟨1089398, by rfl⟩ : syracuseStep 5810125 = 2178797) B2178797
theorem B3876817 : Blo 1813608 3876817 := bstep (se 2 (by rfl) ⟨1453806, by rfl⟩ : syracuseStep 3876817 = 2907613) B2907613
theorem B2721761 : Blo 1813608 2721761 := bstep (se 2 (by rfl) ⟨1020660, by rfl⟩ : syracuseStep 2721761 = 2041321) B2041321
theorem B2721779 : Blo 1813608 2721779 := bstep (se 1 (by rfl) ⟨2041334, by rfl⟩ : syracuseStep 2721779 = 4082669) B4082669
theorem B2041843 : Blo 1813608 2041843 := bstep (se 1 (by rfl) ⟨1531382, by rfl⟩ : syracuseStep 2041843 = 3062765) B3062765
theorem B2721809 : Blo 1813608 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B3680273 : Blo 1813608 3680273 := bstep (se 2 (by rfl) ⟨1380102, by rfl⟩ : syracuseStep 3680273 = 2760205) B2760205
theorem B2721827 : Blo 1813608 2721827 := bstep (se 1 (by rfl) ⟨2041370, by rfl⟩ : syracuseStep 2721827 = 4082741) B4082741
theorem B2295859 : Blo 1813608 2295859 := bstep (se 1 (by rfl) ⟨1721894, by rfl⟩ : syracuseStep 2295859 = 3443789) B3443789
theorem B2721857 : Blo 1813608 2721857 := bstep (se 2 (by rfl) ⟨1020696, by rfl⟩ : syracuseStep 2721857 = 2041393) B2041393
theorem B2721875 : Blo 1813608 2721875 := bstep (se 1 (by rfl) ⟨2041406, by rfl⟩ : syracuseStep 2721875 = 4082813) B4082813
theorem B6539363 : Blo 1813608 6539363 := bstep (se 1 (by rfl) ⟨4904522, by rfl⟩ : syracuseStep 6539363 = 9809045) B9809045
theorem B12585059 : Blo 1813608 12585059 := bstep (se 1 (by rfl) ⟨9438794, by rfl⟩ : syracuseStep 12585059 = 18877589) B18877589
theorem B22079587 : Blo 1813608 22079587 := bstep (se 1 (by rfl) ⟨16559690, by rfl⟩ : syracuseStep 22079587 = 33119381) B33119381
theorem B22071409 : Blo 1813608 22071409 := bstep (se 2 (by rfl) ⟨8276778, by rfl⟩ : syracuseStep 22071409 = 16553557) B16553557
theorem B2721905 : Blo 1813608 2721905 := bstep (se 2 (by rfl) ⟨1020714, by rfl⟩ : syracuseStep 2721905 = 2041429) B2041429
theorem B2721923 : Blo 1813608 2721923 := bstep (se 1 (by rfl) ⟨2041442, by rfl⟩ : syracuseStep 2721923 = 4082885) B4082885
theorem B2041987 : Blo 1813608 2041987 := bstep (se 1 (by rfl) ⟨1531490, by rfl⟩ : syracuseStep 2041987 = 3062981) B3062981
theorem B2295955 : Blo 1813608 2295955 := bstep (se 1 (by rfl) ⟨1721966, by rfl⟩ : syracuseStep 2295955 = 3443933) B3443933
theorem B2721953 : Blo 1813608 2721953 := bstep (se 2 (by rfl) ⟨1020732, by rfl⟩ : syracuseStep 2721953 = 2041465) B2041465
theorem B2582705 : Blo 1813608 2582705 := bstep (se 2 (by rfl) ⟨968514, by rfl⟩ : syracuseStep 2582705 = 1937029) B1937029
theorem B4081841 : Blo 1813608 4081841 := bstep (se 2 (by rfl) ⟨1530690, by rfl⟩ : syracuseStep 4081841 = 3061381) B3061381
theorem B5236913 : Blo 1813608 5236913 := bstep (se 2 (by rfl) ⟨1963842, by rfl⟩ : syracuseStep 5236913 = 3927685) B3927685
theorem B2721971 : Blo 1813608 2721971 := bstep (se 1 (by rfl) ⟨2041478, by rfl⟩ : syracuseStep 2721971 = 4082957) B4082957
theorem B4081859 : Blo 1813608 4081859 := bstep (se 1 (by rfl) ⟨3061394, by rfl⟩ : syracuseStep 4081859 = 6122789) B6122789
theorem B5810381 : Blo 1813608 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B2722001 : Blo 1813608 2722001 := bstep (se 2 (by rfl) ⟨1020750, by rfl⟩ : syracuseStep 2722001 = 2041501) B2041501
theorem B3877073 : Blo 1813608 3877073 := bstep (se 2 (by rfl) ⟨1453902, by rfl⟩ : syracuseStep 3877073 = 2907805) B2907805
theorem B2722019 : Blo 1813608 2722019 := bstep (se 1 (by rfl) ⟨2041514, by rfl⟩ : syracuseStep 2722019 = 4083029) B4083029
theorem B6121709 : Blo 1813608 6121709 := bstep (se 3 (by rfl) ⟨1147820, by rfl⟩ : syracuseStep 6121709 = 2295641) B2295641
theorem B2722049 : Blo 1813608 2722049 := bstep (se 2 (by rfl) ⟨1020768, by rfl⟩ : syracuseStep 2722049 = 2041537) B2041537
theorem B3680515 : Blo 1813608 3680515 := bstep (se 1 (by rfl) ⟨2760386, by rfl⟩ : syracuseStep 3680515 = 5520773) B5520773
theorem B2722067 : Blo 1813608 2722067 := bstep (se 1 (by rfl) ⟨2041550, by rfl⟩ : syracuseStep 2722067 = 4083101) B4083101
theorem B2042131 : Blo 1813608 2042131 := bstep (se 1 (by rfl) ⟨1531598, by rfl⟩ : syracuseStep 2042131 = 3063197) B3063197
theorem B6121763 : Blo 1813608 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B2722097 : Blo 1813608 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B37234997 : Blo 1813608 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B2722115 : Blo 1813608 2722115 := bstep (se 1 (by rfl) ⟨2041586, by rfl⟩ : syracuseStep 2722115 = 4083173) B4083173
theorem B2722145 : Blo 1813608 2722145 := bstep (se 2 (by rfl) ⟨1020804, by rfl⟩ : syracuseStep 2722145 = 2041609) B2041609
theorem B6891875 : Blo 1813608 6891875 := bstep (se 1 (by rfl) ⟨5168906, by rfl⟩ : syracuseStep 6891875 = 10337813) B10337813
theorem B2722163 : Blo 1813608 2722163 := bstep (se 1 (by rfl) ⟨2041622, by rfl⟩ : syracuseStep 2722163 = 4083245) B4083245
theorem B2722193 : Blo 1813608 2722193 := bstep (se 2 (by rfl) ⟨1020822, by rfl⟩ : syracuseStep 2722193 = 2041645) B2041645
theorem B2722211 : Blo 1813608 2722211 := bstep (se 1 (by rfl) ⟨2041658, by rfl⟩ : syracuseStep 2722211 = 4083317) B4083317
theorem B2042275 : Blo 1813608 2042275 := bstep (se 1 (by rfl) ⟨1531706, by rfl⟩ : syracuseStep 2042275 = 3063413) B3063413
theorem B2795953 : Blo 1813608 2795953 := bstep (se 2 (by rfl) ⟨1048482, by rfl⟩ : syracuseStep 2795953 = 2096965) B2096965
theorem B2722241 : Blo 1813608 2722241 := bstep (se 2 (by rfl) ⟨1020840, by rfl⟩ : syracuseStep 2722241 = 2041681) B2041681
theorem B4082129 : Blo 1813608 4082129 := bstep (se 2 (by rfl) ⟨1530798, by rfl⟩ : syracuseStep 4082129 = 3061597) B3061597
theorem B2722259 : Blo 1813608 2722259 := bstep (se 1 (by rfl) ⟨2041694, by rfl⟩ : syracuseStep 2722259 = 4083389) B4083389
theorem B4082147 : Blo 1813608 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B2722289 : Blo 1813608 2722289 := bstep (se 2 (by rfl) ⟨1020858, by rfl⟩ : syracuseStep 2722289 = 2041717) B2041717
theorem B2722307 : Blo 1813608 2722307 := bstep (se 1 (by rfl) ⟨2041730, by rfl⟩ : syracuseStep 2722307 = 4083461) B4083461
theorem B2722337 : Blo 1813608 2722337 := bstep (se 2 (by rfl) ⟨1020876, by rfl⟩ : syracuseStep 2722337 = 2041753) B2041753
theorem B3443249 : Blo 1813608 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B6122033 : Blo 1813608 6122033 := bstep (se 2 (by rfl) ⟨2295762, by rfl⟩ : syracuseStep 6122033 = 4591525) B4591525
theorem B2722355 : Blo 1813608 2722355 := bstep (se 1 (by rfl) ⟨2041766, by rfl⟩ : syracuseStep 2722355 = 4083533) B4083533
theorem B2042419 : Blo 1813608 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B2722385 : Blo 1813608 2722385 := bstep (se 2 (by rfl) ⟨1020894, by rfl⟩ : syracuseStep 2722385 = 2041789) B2041789
theorem B2722403 : Blo 1813608 2722403 := bstep (se 1 (by rfl) ⟨2041802, by rfl⟩ : syracuseStep 2722403 = 4083605) B4083605
theorem B2722433 : Blo 1813608 2722433 := bstep (se 2 (by rfl) ⟨1020912, by rfl⟩ : syracuseStep 2722433 = 2041825) B2041825
theorem B2296451 : Blo 1813608 2296451 := bstep (se 1 (by rfl) ⟨1722338, by rfl⟩ : syracuseStep 2296451 = 3444677) B3444677
theorem B2722451 : Blo 1813608 2722451 := bstep (se 1 (by rfl) ⟨2041838, by rfl⟩ : syracuseStep 2722451 = 4083677) B4083677
theorem B11627171 : Blo 1813608 11627171 := bstep (se 1 (by rfl) ⟨8720378, by rfl⟩ : syracuseStep 11627171 = 17440757) B17440757
theorem B2722481 : Blo 1813608 2722481 := bstep (se 2 (by rfl) ⟨1020930, by rfl⟩ : syracuseStep 2722481 = 2041861) B2041861
theorem B2722499 : Blo 1813608 2722499 := bstep (se 1 (by rfl) ⟨2041874, by rfl⟩ : syracuseStep 2722499 = 4083749) B4083749
theorem B2722529 : Blo 1813608 2722529 := bstep (se 2 (by rfl) ⟨1020948, by rfl⟩ : syracuseStep 2722529 = 2041897) B2041897
theorem B4082417 : Blo 1813608 4082417 := bstep (se 2 (by rfl) ⟨1530906, by rfl⟩ : syracuseStep 4082417 = 3061813) B3061813
theorem B2722547 : Blo 1813608 2722547 := bstep (se 1 (by rfl) ⟨2041910, by rfl⟩ : syracuseStep 2722547 = 4083821) B4083821
theorem B4082435 : Blo 1813608 4082435 := bstep (se 1 (by rfl) ⟨3061826, by rfl⟩ : syracuseStep 4082435 = 6123653) B6123653
theorem B2722577 : Blo 1813608 2722577 := bstep (se 2 (by rfl) ⟨1020966, by rfl⟩ : syracuseStep 2722577 = 2041933) B2041933
theorem B2722595 : Blo 1813608 2722595 := bstep (se 1 (by rfl) ⟨2041946, by rfl⟩ : syracuseStep 2722595 = 4083893) B4083893
theorem B2722625 : Blo 1813608 2722625 := bstep (se 2 (by rfl) ⟨1020984, by rfl⟩ : syracuseStep 2722625 = 2041969) B2041969
theorem B2485073 : Blo 1813608 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B2722643 : Blo 1813608 2722643 := bstep (se 1 (by rfl) ⟨2041982, by rfl⟩ : syracuseStep 2722643 = 4083965) B4083965
theorem B2722673 : Blo 1813608 2722673 := bstep (se 2 (by rfl) ⟨1021002, by rfl⟩ : syracuseStep 2722673 = 2042005) B2042005
theorem B2722691 : Blo 1813608 2722691 := bstep (se 1 (by rfl) ⟨2042018, by rfl⟩ : syracuseStep 2722691 = 4084037) B4084037
theorem B2722721 : Blo 1813608 2722721 := bstep (se 2 (by rfl) ⟨1021020, by rfl⟩ : syracuseStep 2722721 = 2042041) B2042041
theorem B2722739 : Blo 1813608 2722739 := bstep (se 1 (by rfl) ⟨2042054, by rfl⟩ : syracuseStep 2722739 = 4084109) B4084109
theorem B2722769 : Blo 1813608 2722769 := bstep (se 2 (by rfl) ⟨1021038, by rfl⟩ : syracuseStep 2722769 = 2042077) B2042077
theorem B13781987 : Blo 1813608 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B2722787 : Blo 1813608 2722787 := bstep (se 1 (by rfl) ⟨2042090, by rfl⟩ : syracuseStep 2722787 = 4084181) B4084181
theorem B2722817 : Blo 1813608 2722817 := bstep (se 2 (by rfl) ⟨1021056, by rfl⟩ : syracuseStep 2722817 = 2042113) B2042113
theorem B4082705 : Blo 1813608 4082705 := bstep (se 2 (by rfl) ⟨1531014, by rfl⟩ : syracuseStep 4082705 = 3062029) B3062029
theorem B2583571 : Blo 1813608 2583571 := bstep (se 1 (by rfl) ⟨1937678, by rfl⟩ : syracuseStep 2583571 = 3875357) B3875357
theorem B2722835 : Blo 1813608 2722835 := bstep (se 1 (by rfl) ⟨2042126, by rfl⟩ : syracuseStep 2722835 = 4084253) B4084253
theorem B4082723 : Blo 1813608 4082723 := bstep (se 1 (by rfl) ⟨3062042, by rfl⟩ : syracuseStep 4082723 = 6124085) B6124085
theorem B5827619 : Blo 1813608 5827619 := bstep (se 1 (by rfl) ⟨4370714, by rfl⟩ : syracuseStep 5827619 = 8741429) B8741429
theorem B2722865 : Blo 1813608 2722865 := bstep (se 2 (by rfl) ⟨1021074, by rfl⟩ : syracuseStep 2722865 = 2042149) B2042149
theorem B2722883 : Blo 1813608 2722883 := bstep (se 1 (by rfl) ⟨2042162, by rfl⟩ : syracuseStep 2722883 = 4084325) B4084325
theorem B6122573 : Blo 1813608 6122573 := bstep (se 3 (by rfl) ⟨1147982, by rfl⟩ : syracuseStep 6122573 = 2295965) B2295965
theorem B2722913 : Blo 1813608 2722913 := bstep (se 2 (by rfl) ⟨1021092, by rfl⟩ : syracuseStep 2722913 = 2042185) B2042185
theorem B1813619 : Blo 1813608 1813619 := bstep (se 1 (by rfl) ⟨1360214, by rfl⟩ : syracuseStep 1813619 = 2720429) B2720429
theorem B2583667 : Blo 1813608 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B2722931 : Blo 1813608 2722931 := bstep (se 1 (by rfl) ⟨2042198, by rfl⟩ : syracuseStep 2722931 = 4084397) B4084397
theorem B1813635 : Blo 1813608 1813635 := bstep (se 1 (by rfl) ⟨1360226, by rfl⟩ : syracuseStep 1813635 = 2720453) B2720453
theorem B6122627 : Blo 1813608 6122627 := bstep (se 1 (by rfl) ⟨4591970, by rfl⟩ : syracuseStep 6122627 = 9183941) B9183941
theorem B2722961 : Blo 1813608 2722961 := bstep (se 2 (by rfl) ⟨1021110, by rfl⟩ : syracuseStep 2722961 = 2042221) B2042221
theorem B1813651 : Blo 1813608 1813651 := bstep (se 1 (by rfl) ⟨1360238, by rfl⟩ : syracuseStep 1813651 = 2720477) B2720477
theorem B1813667 : Blo 1813608 1813667 := bstep (se 1 (by rfl) ⟨1360250, by rfl⟩ : syracuseStep 1813667 = 2720501) B2720501
theorem B2722979 : Blo 1813608 2722979 := bstep (se 1 (by rfl) ⟨2042234, by rfl⟩ : syracuseStep 2722979 = 4084469) B4084469
theorem B1813683 : Blo 1813608 1813683 := bstep (se 1 (by rfl) ⟨1360262, by rfl⟩ : syracuseStep 1813683 = 2720525) B2720525
theorem B2723009 : Blo 1813608 2723009 := bstep (se 2 (by rfl) ⟨1021128, by rfl⟩ : syracuseStep 2723009 = 2042257) B2042257
theorem B1813699 : Blo 1813608 1813699 := bstep (se 1 (by rfl) ⟨1360274, by rfl⟩ : syracuseStep 1813699 = 2720549) B2720549
theorem B1813715 : Blo 1813608 1813715 := bstep (se 1 (by rfl) ⟨1360286, by rfl⟩ : syracuseStep 1813715 = 2720573) B2720573
theorem B2723027 : Blo 1813608 2723027 := bstep (se 1 (by rfl) ⟨2042270, by rfl⟩ : syracuseStep 2723027 = 4084541) B4084541
theorem B1813731 : Blo 1813608 1813731 := bstep (se 1 (by rfl) ⟨1360298, by rfl⟩ : syracuseStep 1813731 = 2720597) B2720597
theorem B2723057 : Blo 1813608 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B1813747 : Blo 1813608 1813747 := bstep (se 1 (by rfl) ⟨1360310, by rfl⟩ : syracuseStep 1813747 = 2720621) B2720621
theorem B1813763 : Blo 1813608 1813763 := bstep (se 1 (by rfl) ⟨1360322, by rfl⟩ : syracuseStep 1813763 = 2720645) B2720645
theorem B3443971 : Blo 1813608 3443971 := bstep (se 1 (by rfl) ⟨2582978, by rfl⟩ : syracuseStep 3443971 = 5165957) B5165957
theorem B2723075 : Blo 1813608 2723075 := bstep (se 1 (by rfl) ⟨2042306, by rfl⟩ : syracuseStep 2723075 = 4084613) B4084613
theorem B1813779 : Blo 1813608 1813779 := bstep (se 1 (by rfl) ⟨1360334, by rfl⟩ : syracuseStep 1813779 = 2720669) B2720669
theorem B2723105 : Blo 1813608 2723105 := bstep (se 2 (by rfl) ⟨1021164, by rfl⟩ : syracuseStep 2723105 = 2042329) B2042329
theorem B1813795 : Blo 1813608 1813795 := bstep (se 1 (by rfl) ⟨1360346, by rfl⟩ : syracuseStep 1813795 = 2720693) B2720693
theorem B4082993 : Blo 1813608 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B1813811 : Blo 1813608 1813811 := bstep (se 1 (by rfl) ⟨1360358, by rfl⟩ : syracuseStep 1813811 = 2720717) B2720717
theorem B2723123 : Blo 1813608 2723123 := bstep (se 1 (by rfl) ⟨2042342, by rfl⟩ : syracuseStep 2723123 = 4084685) B4084685
theorem B2796865 : Blo 1813608 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B1813827 : Blo 1813608 1813827 := bstep (se 1 (by rfl) ⟨1360370, by rfl⟩ : syracuseStep 1813827 = 2720741) B2720741
theorem B4083011 : Blo 1813608 4083011 := bstep (se 1 (by rfl) ⟨3062258, by rfl⟩ : syracuseStep 4083011 = 6124517) B6124517
theorem B2297155 : Blo 1813608 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B6892877 : Blo 1813608 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B2723153 : Blo 1813608 2723153 := bstep (se 2 (by rfl) ⟨1021182, by rfl⟩ : syracuseStep 2723153 = 2042365) B2042365
theorem B1813843 : Blo 1813608 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B1813859 : Blo 1813608 1813859 := bstep (se 1 (by rfl) ⟨1360394, by rfl⟩ : syracuseStep 1813859 = 2720789) B2720789
theorem B2723171 : Blo 1813608 2723171 := bstep (se 1 (by rfl) ⟨2042378, by rfl⟩ : syracuseStep 2723171 = 4084757) B4084757
theorem B1813875 : Blo 1813608 1813875 := bstep (se 1 (by rfl) ⟨1360406, by rfl⟩ : syracuseStep 1813875 = 2720813) B2720813
theorem B2723201 : Blo 1813608 2723201 := bstep (se 2 (by rfl) ⟨1021200, by rfl⟩ : syracuseStep 2723201 = 2042401) B2042401
theorem B1813891 : Blo 1813608 1813891 := bstep (se 1 (by rfl) ⟨1360418, by rfl⟩ : syracuseStep 1813891 = 2720837) B2720837
theorem B6122897 : Blo 1813608 6122897 := bstep (se 2 (by rfl) ⟨2296086, by rfl⟩ : syracuseStep 6122897 = 4592173) B4592173
theorem B1813907 : Blo 1813608 1813907 := bstep (se 1 (by rfl) ⟨1360430, by rfl⟩ : syracuseStep 1813907 = 2720861) B2720861
theorem B2723219 : Blo 1813608 2723219 := bstep (se 1 (by rfl) ⟨2042414, by rfl⟩ : syracuseStep 2723219 = 4084829) B4084829
theorem B1813923 : Blo 1813608 1813923 := bstep (se 1 (by rfl) ⟨1360442, by rfl⟩ : syracuseStep 1813923 = 2720885) B2720885
theorem B2297251 : Blo 1813608 2297251 := bstep (se 1 (by rfl) ⟨1722938, by rfl⟩ : syracuseStep 2297251 = 3445877) B3445877
theorem B1813939 : Blo 1813608 1813939 := bstep (se 1 (by rfl) ⟨1360454, by rfl⟩ : syracuseStep 1813939 = 2720909) B2720909
theorem B2723249 : Blo 1813608 2723249 := bstep (se 2 (by rfl) ⟨1021218, by rfl⟩ : syracuseStep 2723249 = 2042437) B2042437
theorem B1813955 : Blo 1813608 1813955 := bstep (se 1 (by rfl) ⟨1360466, by rfl⟩ : syracuseStep 1813955 = 2720933) B2720933
theorem B2723267 : Blo 1813608 2723267 := bstep (se 1 (by rfl) ⟨2042450, by rfl⟩ : syracuseStep 2723267 = 4084901) B4084901
theorem B1813971 : Blo 1813608 1813971 := bstep (se 1 (by rfl) ⟨1360478, by rfl⟩ : syracuseStep 1813971 = 2720957) B2720957
theorem B2723297 : Blo 1813608 2723297 := bstep (se 2 (by rfl) ⟨1021236, by rfl⟩ : syracuseStep 2723297 = 2042473) B2042473
theorem B1813987 : Blo 1813608 1813987 := bstep (se 1 (by rfl) ⟨1360490, by rfl⟩ : syracuseStep 1813987 = 2720981) B2720981
theorem B1814003 : Blo 1813608 1814003 := bstep (se 1 (by rfl) ⟨1360502, by rfl⟩ : syracuseStep 1814003 = 2721005) B2721005
theorem B2723315 : Blo 1813608 2723315 := bstep (se 1 (by rfl) ⟨2042486, by rfl⟩ : syracuseStep 2723315 = 4084973) B4084973
theorem B1814019 : Blo 1813608 1814019 := bstep (se 1 (by rfl) ⟨1360514, by rfl⟩ : syracuseStep 1814019 = 2721029) B2721029
theorem B2723345 : Blo 1813608 2723345 := bstep (se 2 (by rfl) ⟨1021254, by rfl⟩ : syracuseStep 2723345 = 2042509) B2042509
theorem B1814035 : Blo 1813608 1814035 := bstep (se 1 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 1814035 = 2721053) B2721053
theorem B1814051 : Blo 1813608 1814051 := bstep (se 1 (by rfl) ⟨1360538, by rfl⟩ : syracuseStep 1814051 = 2721077) B2721077
theorem B2723363 : Blo 1813608 2723363 := bstep (se 1 (by rfl) ⟨2042522, by rfl⟩ : syracuseStep 2723363 = 4085045) B4085045
theorem B1814067 : Blo 1813608 1814067 := bstep (se 1 (by rfl) ⟨1360550, by rfl⟩ : syracuseStep 1814067 = 2721101) B2721101
theorem B2723393 : Blo 1813608 2723393 := bstep (se 2 (by rfl) ⟨1021272, by rfl⟩ : syracuseStep 2723393 = 2042545) B2042545
theorem B1814083 : Blo 1813608 1814083 := bstep (se 1 (by rfl) ⟨1360562, by rfl⟩ : syracuseStep 1814083 = 2721125) B2721125
theorem B4083281 : Blo 1813608 4083281 := bstep (se 2 (by rfl) ⟨1531230, by rfl⟩ : syracuseStep 4083281 = 3062461) B3062461
theorem B1814099 : Blo 1813608 1814099 := bstep (se 1 (by rfl) ⟨1360574, by rfl⟩ : syracuseStep 1814099 = 2721149) B2721149
theorem B2723411 : Blo 1813608 2723411 := bstep (se 1 (by rfl) ⟨2042558, by rfl⟩ : syracuseStep 2723411 = 4085117) B4085117
theorem B1814115 : Blo 1813608 1814115 := bstep (se 1 (by rfl) ⟨1360586, by rfl⟩ : syracuseStep 1814115 = 2721173) B2721173
theorem B4083299 : Blo 1813608 4083299 := bstep (se 1 (by rfl) ⟨3062474, by rfl⟩ : syracuseStep 4083299 = 6124949) B6124949
theorem B2584163 : Blo 1813608 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B1814131 : Blo 1813608 1814131 := bstep (se 1 (by rfl) ⟨1360598, by rfl⟩ : syracuseStep 1814131 = 2721197) B2721197
theorem B1814147 : Blo 1813608 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B1814163 : Blo 1813608 1814163 := bstep (se 1 (by rfl) ⟨1360622, by rfl⟩ : syracuseStep 1814163 = 2721245) B2721245
theorem B1814179 : Blo 1813608 1814179 := bstep (se 1 (by rfl) ⟨1360634, by rfl⟩ : syracuseStep 1814179 = 2721269) B2721269
theorem B1814195 : Blo 1813608 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B5811907 : Blo 1813608 5811907 := bstep (se 1 (by rfl) ⟨4358930, by rfl⟩ : syracuseStep 5811907 = 8717861) B8717861
theorem B1814211 : Blo 1813608 1814211 := bstep (se 1 (by rfl) ⟨1360658, by rfl⟩ : syracuseStep 1814211 = 2721317) B2721317
theorem B3444419 : Blo 1813608 3444419 := bstep (se 1 (by rfl) ⟨2583314, by rfl⟩ : syracuseStep 3444419 = 5166629) B5166629
theorem B4591313 : Blo 1813608 4591313 := bstep (se 2 (by rfl) ⟨1721742, by rfl⟩ : syracuseStep 4591313 = 3443485) B3443485
theorem B1814227 : Blo 1813608 1814227 := bstep (se 1 (by rfl) ⟨1360670, by rfl⟩ : syracuseStep 1814227 = 2721341) B2721341
theorem B1814243 : Blo 1813608 1814243 := bstep (se 1 (by rfl) ⟨1360682, by rfl⟩ : syracuseStep 1814243 = 2721365) B2721365
theorem B1814259 : Blo 1813608 1814259 := bstep (se 1 (by rfl) ⟨1360694, by rfl⟩ : syracuseStep 1814259 = 2721389) B2721389
theorem B4591363 : Blo 1813608 4591363 := bstep (se 1 (by rfl) ⟨3443522, by rfl⟩ : syracuseStep 4591363 = 6887045) B6887045
theorem B1814275 : Blo 1813608 1814275 := bstep (se 1 (by rfl) ⟨1360706, by rfl⟩ : syracuseStep 1814275 = 2721413) B2721413
theorem B1814291 : Blo 1813608 1814291 := bstep (se 1 (by rfl) ⟨1360718, by rfl⟩ : syracuseStep 1814291 = 2721437) B2721437
theorem B282693397 : Blo 1813608 282693397 := bstep (se 6 (by rfl) ⟨6625626, by rfl⟩ : syracuseStep 282693397 = 13251253) B13251253
theorem B1814307 : Blo 1813608 1814307 := bstep (se 1 (by rfl) ⟨1360730, by rfl⟩ : syracuseStep 1814307 = 2721461) B2721461
theorem B1814323 : Blo 1813608 1814323 := bstep (se 1 (by rfl) ⟨1360742, by rfl⟩ : syracuseStep 1814323 = 2721485) B2721485
theorem B1814339 : Blo 1813608 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B1814355 : Blo 1813608 1814355 := bstep (se 1 (by rfl) ⟨1360766, by rfl⟩ : syracuseStep 1814355 = 2721533) B2721533
theorem B1814371 : Blo 1813608 1814371 := bstep (se 1 (by rfl) ⟨1360778, by rfl⟩ : syracuseStep 1814371 = 2721557) B2721557
theorem B4083569 : Blo 1813608 4083569 := bstep (se 2 (by rfl) ⟨1531338, by rfl⟩ : syracuseStep 4083569 = 3062677) B3062677
theorem B1814387 : Blo 1813608 1814387 := bstep (se 1 (by rfl) ⟨1360790, by rfl⟩ : syracuseStep 1814387 = 2721581) B2721581
theorem B1814403 : Blo 1813608 1814403 := bstep (se 1 (by rfl) ⟨1360802, by rfl⟩ : syracuseStep 1814403 = 2721605) B2721605
theorem B4083587 : Blo 1813608 4083587 := bstep (se 1 (by rfl) ⟨3062690, by rfl⟩ : syracuseStep 4083587 = 6125381) B6125381
theorem B4591505 : Blo 1813608 4591505 := bstep (se 2 (by rfl) ⟨1721814, by rfl⟩ : syracuseStep 4591505 = 3443629) B3443629
theorem B1814419 : Blo 1813608 1814419 := bstep (se 1 (by rfl) ⟨1360814, by rfl⟩ : syracuseStep 1814419 = 2721629) B2721629
theorem B2297747 : Blo 1813608 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B1937315 : Blo 1813608 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B1814435 : Blo 1813608 1814435 := bstep (se 1 (by rfl) ⟨1360826, by rfl⟩ : syracuseStep 1814435 = 2721653) B2721653
theorem B6123437 : Blo 1813608 6123437 := bstep (se 3 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 6123437 = 2296289) B2296289
theorem B1814451 : Blo 1813608 1814451 := bstep (se 1 (by rfl) ⟨1360838, by rfl⟩ : syracuseStep 1814451 = 2721677) B2721677
theorem B1814467 : Blo 1813608 1814467 := bstep (se 1 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 1814467 = 2721701) B2721701
theorem B1814483 : Blo 1813608 1814483 := bstep (se 1 (by rfl) ⟨1360862, by rfl⟩ : syracuseStep 1814483 = 2721725) B2721725
theorem B6123491 : Blo 1813608 6123491 := bstep (se 1 (by rfl) ⟨4592618, by rfl⟩ : syracuseStep 6123491 = 9185237) B9185237
theorem B3444707 : Blo 1813608 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B1814499 : Blo 1813608 1814499 := bstep (se 1 (by rfl) ⟨1360874, by rfl⟩ : syracuseStep 1814499 = 2721749) B2721749
theorem B1814515 : Blo 1813608 1814515 := bstep (se 1 (by rfl) ⟨1360886, by rfl⟩ : syracuseStep 1814515 = 2721773) B2721773
theorem B10334213 : Blo 1813608 10334213 := bstep (se 4 (by rfl) ⟨968832, by rfl⟩ : syracuseStep 10334213 = 1937665) B1937665
theorem B1814531 : Blo 1813608 1814531 := bstep (se 1 (by rfl) ⟨1360898, by rfl⟩ : syracuseStep 1814531 = 2721797) B2721797
theorem B22073357 : Blo 1813608 22073357 := bstep (se 3 (by rfl) ⟨4138754, by rfl⟩ : syracuseStep 22073357 = 8277509) B8277509
theorem B1814547 : Blo 1813608 1814547 := bstep (se 1 (by rfl) ⟨1360910, by rfl⟩ : syracuseStep 1814547 = 2721821) B2721821
theorem B1937443 : Blo 1813608 1937443 := bstep (se 1 (by rfl) ⟨1453082, by rfl⟩ : syracuseStep 1937443 = 2906165) B2906165
theorem B1814563 : Blo 1813608 1814563 := bstep (se 1 (by rfl) ⟨1360922, by rfl⟩ : syracuseStep 1814563 = 2721845) B2721845
theorem B1814579 : Blo 1813608 1814579 := bstep (se 1 (by rfl) ⟨1360934, by rfl⟩ : syracuseStep 1814579 = 2721869) B2721869
theorem B1814595 : Blo 1813608 1814595 := bstep (se 1 (by rfl) ⟨1360946, by rfl⟩ : syracuseStep 1814595 = 2721893) B2721893
theorem B7753805 : Blo 1813608 7753805 := bstep (se 3 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 7753805 = 2907677) B2907677
theorem B1814611 : Blo 1813608 1814611 := bstep (se 1 (by rfl) ⟨1360958, by rfl⟩ : syracuseStep 1814611 = 2721917) B2721917
theorem B1814627 : Blo 1813608 1814627 := bstep (se 1 (by rfl) ⟨1360970, by rfl⟩ : syracuseStep 1814627 = 2721941) B2721941
theorem B1814643 : Blo 1813608 1814643 := bstep (se 1 (by rfl) ⟨1360982, by rfl⟩ : syracuseStep 1814643 = 2721965) B2721965
theorem B1814659 : Blo 1813608 1814659 := bstep (se 1 (by rfl) ⟨1360994, by rfl⟩ : syracuseStep 1814659 = 2721989) B2721989
theorem B4083857 : Blo 1813608 4083857 := bstep (se 2 (by rfl) ⟨1531446, by rfl⟩ : syracuseStep 4083857 = 3062893) B3062893
theorem B1814675 : Blo 1813608 1814675 := bstep (se 1 (by rfl) ⟨1361006, by rfl⟩ : syracuseStep 1814675 = 2722013) B2722013
theorem B1814691 : Blo 1813608 1814691 := bstep (se 1 (by rfl) ⟨1361018, by rfl⟩ : syracuseStep 1814691 = 2722037) B2722037
theorem B4083875 : Blo 1813608 4083875 := bstep (se 1 (by rfl) ⟨3062906, by rfl⟩ : syracuseStep 4083875 = 6125813) B6125813
theorem B9187505 : Blo 1813608 9187505 := bstep (se 2 (by rfl) ⟨3445314, by rfl⟩ : syracuseStep 9187505 = 6890629) B6890629
theorem B1814707 : Blo 1813608 1814707 := bstep (se 1 (by rfl) ⟨1361030, by rfl⟩ : syracuseStep 1814707 = 2722061) B2722061
theorem B1814723 : Blo 1813608 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B1814739 : Blo 1813608 1814739 := bstep (se 1 (by rfl) ⟨1361054, by rfl⟩ : syracuseStep 1814739 = 2722109) B2722109
theorem B2584801 : Blo 1813608 2584801 := bstep (se 2 (by rfl) ⟨969300, by rfl⟩ : syracuseStep 2584801 = 1938601) B1938601
theorem B1814755 : Blo 1813608 1814755 := bstep (se 1 (by rfl) ⟨1361066, by rfl⟩ : syracuseStep 1814755 = 2722133) B2722133
theorem B6123761 : Blo 1813608 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B1814771 : Blo 1813608 1814771 := bstep (se 1 (by rfl) ⟨1361078, by rfl⟩ : syracuseStep 1814771 = 2722157) B2722157
theorem B1814787 : Blo 1813608 1814787 := bstep (se 1 (by rfl) ⟨1361090, by rfl⟩ : syracuseStep 1814787 = 2722181) B2722181
theorem B25178381 : Blo 1813608 25178381 := bstep (se 3 (by rfl) ⟨4720946, by rfl⟩ : syracuseStep 25178381 = 9441893) B9441893
theorem B1814803 : Blo 1813608 1814803 := bstep (se 1 (by rfl) ⟨1361102, by rfl⟩ : syracuseStep 1814803 = 2722205) B2722205
theorem B1814819 : Blo 1813608 1814819 := bstep (se 1 (by rfl) ⟨1361114, by rfl⟩ : syracuseStep 1814819 = 2722229) B2722229
theorem B1814835 : Blo 1813608 1814835 := bstep (se 1 (by rfl) ⟨1361126, by rfl⟩ : syracuseStep 1814835 = 2722253) B2722253
theorem B1814851 : Blo 1813608 1814851 := bstep (se 1 (by rfl) ⟨1361138, by rfl⟩ : syracuseStep 1814851 = 2722277) B2722277
theorem B1814867 : Blo 1813608 1814867 := bstep (se 1 (by rfl) ⟨1361150, by rfl⟩ : syracuseStep 1814867 = 2722301) B2722301
theorem B1814883 : Blo 1813608 1814883 := bstep (se 1 (by rfl) ⟨1361162, by rfl⟩ : syracuseStep 1814883 = 2722325) B2722325
theorem B1814899 : Blo 1813608 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B1814915 : Blo 1813608 1814915 := bstep (se 1 (by rfl) ⟨1361186, by rfl⟩ : syracuseStep 1814915 = 2722373) B2722373
theorem B1814931 : Blo 1813608 1814931 := bstep (se 1 (by rfl) ⟨1361198, by rfl⟩ : syracuseStep 1814931 = 2722397) B2722397
theorem B1814947 : Blo 1813608 1814947 := bstep (se 1 (by rfl) ⟨1361210, by rfl⟩ : syracuseStep 1814947 = 2722421) B2722421
theorem B4084145 : Blo 1813608 4084145 := bstep (se 2 (by rfl) ⟨1531554, by rfl⟩ : syracuseStep 4084145 = 3063109) B3063109
theorem B1814963 : Blo 1813608 1814963 := bstep (se 1 (by rfl) ⟨1361222, by rfl⟩ : syracuseStep 1814963 = 2722445) B2722445
theorem B1814979 : Blo 1813608 1814979 := bstep (se 1 (by rfl) ⟨1361234, by rfl⟩ : syracuseStep 1814979 = 2722469) B2722469
theorem B4084163 : Blo 1813608 4084163 := bstep (se 1 (by rfl) ⟨3063122, by rfl⟩ : syracuseStep 4084163 = 6126245) B6126245
theorem B1814995 : Blo 1813608 1814995 := bstep (se 1 (by rfl) ⟨1361246, by rfl⟩ : syracuseStep 1814995 = 2722493) B2722493
theorem B1815011 : Blo 1813608 1815011 := bstep (se 1 (by rfl) ⟨1361258, by rfl⟩ : syracuseStep 1815011 = 2722517) B2722517
theorem B1815027 : Blo 1813608 1815027 := bstep (se 1 (by rfl) ⟨1361270, by rfl⟩ : syracuseStep 1815027 = 2722541) B2722541
theorem B5812739 : Blo 1813608 5812739 := bstep (se 1 (by rfl) ⟨4359554, by rfl⟩ : syracuseStep 5812739 = 8719109) B8719109
theorem B1815043 : Blo 1813608 1815043 := bstep (se 1 (by rfl) ⟨1361282, by rfl⟩ : syracuseStep 1815043 = 2722565) B2722565
theorem B15503885 : Blo 1813608 15503885 := bstep (se 3 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 15503885 = 5813957) B5813957
theorem B1815059 : Blo 1813608 1815059 := bstep (se 1 (by rfl) ⟨1361294, by rfl⟩ : syracuseStep 1815059 = 2722589) B2722589
theorem B5165603 : Blo 1813608 5165603 := bstep (se 1 (by rfl) ⟨3874202, by rfl⟩ : syracuseStep 5165603 = 7748405) B7748405
theorem B1815075 : Blo 1813608 1815075 := bstep (se 1 (by rfl) ⟨1361306, by rfl⟩ : syracuseStep 1815075 = 2722613) B2722613
theorem B1815091 : Blo 1813608 1815091 := bstep (se 1 (by rfl) ⟨1361318, by rfl⟩ : syracuseStep 1815091 = 2722637) B2722637
theorem B1815107 : Blo 1813608 1815107 := bstep (se 1 (by rfl) ⟨1361330, by rfl⟩ : syracuseStep 1815107 = 2722661) B2722661
theorem B4903505 : Blo 1813608 4903505 := bstep (se 2 (by rfl) ⟨1838814, by rfl⟩ : syracuseStep 4903505 = 3677629) B3677629
theorem B1815123 : Blo 1813608 1815123 := bstep (se 1 (by rfl) ⟨1361342, by rfl⟩ : syracuseStep 1815123 = 2722685) B2722685
theorem B1815139 : Blo 1813608 1815139 := bstep (se 1 (by rfl) ⟨1361354, by rfl⟩ : syracuseStep 1815139 = 2722709) B2722709
theorem B11629169 : Blo 1813608 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B1815155 : Blo 1813608 1815155 := bstep (se 1 (by rfl) ⟨1361366, by rfl⟩ : syracuseStep 1815155 = 2722733) B2722733
theorem B1815171 : Blo 1813608 1815171 := bstep (se 1 (by rfl) ⟨1361378, by rfl⟩ : syracuseStep 1815171 = 2722757) B2722757
theorem B42463885 : Blo 1813608 42463885 := bstep (se 3 (by rfl) ⟨7961978, by rfl⟩ : syracuseStep 42463885 = 15923957) B15923957
theorem B1815187 : Blo 1813608 1815187 := bstep (se 1 (by rfl) ⟨1361390, by rfl⟩ : syracuseStep 1815187 = 2722781) B2722781
theorem B1815203 : Blo 1813608 1815203 := bstep (se 1 (by rfl) ⟨1361402, by rfl⟩ : syracuseStep 1815203 = 2722805) B2722805
theorem B10334897 : Blo 1813608 10334897 := bstep (se 2 (by rfl) ⟨3875586, by rfl⟩ : syracuseStep 10334897 = 7751173) B7751173
theorem B1815219 : Blo 1813608 1815219 := bstep (se 1 (by rfl) ⟨1361414, by rfl⟩ : syracuseStep 1815219 = 2722829) B2722829
theorem B1815235 : Blo 1813608 1815235 := bstep (se 1 (by rfl) ⟨1361426, by rfl⟩ : syracuseStep 1815235 = 2722853) B2722853
theorem B4084433 : Blo 1813608 4084433 := bstep (se 2 (by rfl) ⟨1531662, by rfl⟩ : syracuseStep 4084433 = 3063325) B3063325
theorem B1815251 : Blo 1813608 1815251 := bstep (se 1 (by rfl) ⟨1361438, by rfl⟩ : syracuseStep 1815251 = 2722877) B2722877
theorem B1815267 : Blo 1813608 1815267 := bstep (se 1 (by rfl) ⟨1361450, by rfl⟩ : syracuseStep 1815267 = 2722901) B2722901
theorem B4084451 : Blo 1813608 4084451 := bstep (se 1 (by rfl) ⟨3063338, by rfl⟩ : syracuseStep 4084451 = 6126677) B6126677
theorem B1815283 : Blo 1813608 1815283 := bstep (se 1 (by rfl) ⟨1361462, by rfl⟩ : syracuseStep 1815283 = 2722925) B2722925
theorem B1815299 : Blo 1813608 1815299 := bstep (se 1 (by rfl) ⟨1361474, by rfl⟩ : syracuseStep 1815299 = 2722949) B2722949
theorem B6124301 : Blo 1813608 6124301 := bstep (se 3 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 6124301 = 2296613) B2296613
theorem B3060497 : Blo 1813608 3060497 := bstep (se 2 (by rfl) ⟨1147686, by rfl⟩ : syracuseStep 3060497 = 2295373) B2295373
theorem B1815315 : Blo 1813608 1815315 := bstep (se 1 (by rfl) ⟨1361486, by rfl⟩ : syracuseStep 1815315 = 2722973) B2722973
theorem B1815331 : Blo 1813608 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B1815347 : Blo 1813608 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B6124355 : Blo 1813608 6124355 := bstep (se 1 (by rfl) ⟨4593266, by rfl⟩ : syracuseStep 6124355 = 9186533) B9186533
theorem B1815363 : Blo 1813608 1815363 := bstep (se 1 (by rfl) ⟨1361522, by rfl⟩ : syracuseStep 1815363 = 2723045) B2723045
theorem B3314513 : Blo 1813608 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B1938259 : Blo 1813608 1938259 := bstep (se 1 (by rfl) ⟨1453694, by rfl⟩ : syracuseStep 1938259 = 2907389) B2907389
theorem B1815379 : Blo 1813608 1815379 := bstep (se 1 (by rfl) ⟨1361534, by rfl⟩ : syracuseStep 1815379 = 2723069) B2723069
theorem B1815395 : Blo 1813608 1815395 := bstep (se 1 (by rfl) ⟨1361546, by rfl⟩ : syracuseStep 1815395 = 2723093) B2723093
theorem B4592497 : Blo 1813608 4592497 := bstep (se 2 (by rfl) ⟨1722186, by rfl⟩ : syracuseStep 4592497 = 3444373) B3444373
theorem B1815411 : Blo 1813608 1815411 := bstep (se 1 (by rfl) ⟨1361558, by rfl⟩ : syracuseStep 1815411 = 2723117) B2723117
theorem B1815427 : Blo 1813608 1815427 := bstep (se 1 (by rfl) ⟨1361570, by rfl⟩ : syracuseStep 1815427 = 2723141) B2723141
theorem B3060625 : Blo 1813608 3060625 := bstep (se 2 (by rfl) ⟨1147734, by rfl⟩ : syracuseStep 3060625 = 2295469) B2295469
theorem B5813137 : Blo 1813608 5813137 := bstep (se 2 (by rfl) ⟨2179926, by rfl⟩ : syracuseStep 5813137 = 4359853) B4359853
theorem B3445649 : Blo 1813608 3445649 := bstep (se 2 (by rfl) ⟨1292118, by rfl⟩ : syracuseStep 3445649 = 2584237) B2584237
theorem B1815443 : Blo 1813608 1815443 := bstep (se 1 (by rfl) ⟨1361582, by rfl⟩ : syracuseStep 1815443 = 2723165) B2723165
theorem B1815459 : Blo 1813608 1815459 := bstep (se 1 (by rfl) ⟨1361594, by rfl⟩ : syracuseStep 1815459 = 2723189) B2723189
theorem B3060659 : Blo 1813608 3060659 := bstep (se 1 (by rfl) ⟨2295494, by rfl⟩ : syracuseStep 3060659 = 4590989) B4590989
theorem B1815475 : Blo 1813608 1815475 := bstep (se 1 (by rfl) ⟨1361606, by rfl⟩ : syracuseStep 1815475 = 2723213) B2723213
theorem B1815491 : Blo 1813608 1815491 := bstep (se 1 (by rfl) ⟨1361618, by rfl⟩ : syracuseStep 1815491 = 2723237) B2723237
theorem B5813201 : Blo 1813608 5813201 := bstep (se 2 (by rfl) ⟨2179950, by rfl⟩ : syracuseStep 5813201 = 4359901) B4359901
theorem B1815507 : Blo 1813608 1815507 := bstep (se 1 (by rfl) ⟨1361630, by rfl⟩ : syracuseStep 1815507 = 2723261) B2723261
theorem B1815523 : Blo 1813608 1815523 := bstep (se 1 (by rfl) ⟨1361642, by rfl⟩ : syracuseStep 1815523 = 2723285) B2723285
theorem B4084721 : Blo 1813608 4084721 := bstep (se 2 (by rfl) ⟨1531770, by rfl⟩ : syracuseStep 4084721 = 3063541) B3063541
theorem B1815539 : Blo 1813608 1815539 := bstep (se 1 (by rfl) ⟨1361654, by rfl⟩ : syracuseStep 1815539 = 2723309) B2723309
theorem B4084739 : Blo 1813608 4084739 := bstep (se 1 (by rfl) ⟨3063554, by rfl⟩ : syracuseStep 4084739 = 6127109) B6127109
theorem B1815555 : Blo 1813608 1815555 := bstep (se 1 (by rfl) ⟨1361666, by rfl⟩ : syracuseStep 1815555 = 2723333) B2723333
theorem B1815571 : Blo 1813608 1815571 := bstep (se 1 (by rfl) ⟨1361678, by rfl⟩ : syracuseStep 1815571 = 2723357) B2723357
theorem B1815587 : Blo 1813608 1815587 := bstep (se 1 (by rfl) ⟨1361690, by rfl⟩ : syracuseStep 1815587 = 2723381) B2723381
theorem B3060787 : Blo 1813608 3060787 := bstep (se 1 (by rfl) ⟨2295590, by rfl⟩ : syracuseStep 3060787 = 4591181) B4591181
theorem B1815603 : Blo 1813608 1815603 := bstep (se 1 (by rfl) ⟨1361702, by rfl⟩ : syracuseStep 1815603 = 2723405) B2723405
theorem B4904003 : Blo 1813608 4904003 := bstep (se 1 (by rfl) ⟨3678002, by rfl⟩ : syracuseStep 4904003 = 7356005) B7356005
theorem B8279117 : Blo 1813608 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B6124625 : Blo 1813608 6124625 := bstep (se 2 (by rfl) ⟨2296734, by rfl⟩ : syracuseStep 6124625 = 4593469) B4593469
theorem B2905217 : Blo 1813608 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B2618497 : Blo 1813608 2618497 := bstep (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) B1963873
theorem B4592771 : Blo 1813608 4592771 := bstep (se 1 (by rfl) ⟨3444578, by rfl⟩ : syracuseStep 4592771 = 6889157) B6889157
theorem B23262389 : Blo 1813608 23262389 := bstep (se 5 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 23262389 = 2180849) B2180849
theorem B3060929 : Blo 1813608 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B4085009 : Blo 1813608 4085009 := bstep (se 2 (by rfl) ⟨1531878, by rfl⟩ : syracuseStep 4085009 = 3063757) B3063757
theorem B4085027 : Blo 1813608 4085027 := bstep (se 1 (by rfl) ⟨3063770, by rfl⟩ : syracuseStep 4085027 = 6127541) B6127541
theorem B2905409 : Blo 1813608 2905409 := bstep (se 2 (by rfl) ⟨1089528, by rfl⟩ : syracuseStep 2905409 = 2179057) B2179057
theorem B3061057 : Blo 1813608 3061057 := bstep (se 2 (by rfl) ⟨1147896, by rfl⟩ : syracuseStep 3061057 = 2295793) B2295793
theorem B4592963 : Blo 1813608 4592963 := bstep (se 1 (by rfl) ⟨3444722, by rfl⟩ : syracuseStep 4592963 = 6889445) B6889445
theorem B5166413 : Blo 1813608 5166413 := bstep (se 3 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 5166413 = 1937405) B1937405
theorem B3061091 : Blo 1813608 3061091 := bstep (se 1 (by rfl) ⟨2295818, by rfl⟩ : syracuseStep 3061091 = 4591637) B4591637
theorem B2758051 : Blo 1813608 2758051 := bstep (se 1 (by rfl) ⟨2068538, by rfl⟩ : syracuseStep 2758051 = 4137077) B4137077
theorem B3061219 : Blo 1813608 3061219 := bstep (se 1 (by rfl) ⟨2295914, by rfl⟩ : syracuseStep 3061219 = 4591829) B4591829
theorem B5166605 : Blo 1813608 5166605 := bstep (se 3 (by rfl) ⟨968738, by rfl⟩ : syracuseStep 5166605 = 1937477) B1937477
theorem B13080163 : Blo 1813608 13080163 := bstep (se 1 (by rfl) ⟨9810122, by rfl⟩ : syracuseStep 13080163 = 19620245) B19620245
theorem B9188963 : Blo 1813608 9188963 := bstep (se 1 (by rfl) ⟨6891722, by rfl⟩ : syracuseStep 9188963 = 13783445) B13783445
theorem B6125165 : Blo 1813608 6125165 := bstep (se 3 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 6125165 = 2296937) B2296937
theorem B3061361 : Blo 1813608 3061361 := bstep (se 2 (by rfl) ⟨1148010, by rfl⟩ : syracuseStep 3061361 = 2296021) B2296021
theorem B6125219 : Blo 1813608 6125219 := bstep (se 1 (by rfl) ⟨4593914, by rfl⟩ : syracuseStep 6125219 = 9187829) B9187829
theorem B3061489 : Blo 1813608 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B4421393 : Blo 1813608 4421393 := bstep (se 2 (by rfl) ⟨1658022, by rfl⟩ : syracuseStep 4421393 = 3316045) B3316045
theorem B3446545 : Blo 1813608 3446545 := bstep (se 2 (by rfl) ⟨1292454, by rfl⟩ : syracuseStep 3446545 = 2584909) B2584909
theorem B3061523 : Blo 1813608 3061523 := bstep (se 1 (by rfl) ⟨2296142, by rfl⟩ : syracuseStep 3061523 = 4592285) B4592285
theorem B2758465 : Blo 1813608 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B3061651 : Blo 1813608 3061651 := bstep (se 1 (by rfl) ⟨2296238, by rfl⟩ : syracuseStep 3061651 = 4592477) B4592477
theorem B6125489 : Blo 1813608 6125489 := bstep (se 2 (by rfl) ⟨2297058, by rfl⟩ : syracuseStep 6125489 = 4594117) B4594117
theorem B3446705 : Blo 1813608 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B3061793 : Blo 1813608 3061793 := bstep (se 2 (by rfl) ⟨1148172, by rfl⟩ : syracuseStep 3061793 = 2296345) B2296345
theorem B6887501 : Blo 1813608 6887501 := bstep (se 3 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 6887501 = 2582813) B2582813
theorem B10336355 : Blo 1813608 10336355 := bstep (se 1 (by rfl) ⟨7752266, by rfl⟩ : syracuseStep 10336355 = 15504533) B15504533
theorem B2947217 : Blo 1813608 2947217 := bstep (se 2 (by rfl) ⟨1105206, by rfl⟩ : syracuseStep 2947217 = 2210413) B2210413
theorem B3061921 : Blo 1813608 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B3061955 : Blo 1813608 3061955 := bstep (se 1 (by rfl) ⟨2296466, by rfl⟩ : syracuseStep 3061955 = 4592933) B4592933
theorem B5306573 : Blo 1813608 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B4593905 : Blo 1813608 4593905 := bstep (se 2 (by rfl) ⟨1722714, by rfl⟩ : syracuseStep 4593905 = 3445429) B3445429
theorem B11630861 : Blo 1813608 11630861 := bstep (se 3 (by rfl) ⟨2180786, by rfl⟩ : syracuseStep 11630861 = 4361573) B4361573
theorem B4593955 : Blo 1813608 4593955 := bstep (se 1 (by rfl) ⟨3445466, by rfl⟩ : syracuseStep 4593955 = 6890933) B6890933
theorem B3062083 : Blo 1813608 3062083 := bstep (se 1 (by rfl) ⟨2296562, by rfl⟩ : syracuseStep 3062083 = 4593125) B4593125
theorem B12417421 : Blo 1813608 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B9189773 : Blo 1813608 9189773 := bstep (se 3 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 9189773 = 3446165) B3446165
theorem B4594097 : Blo 1813608 4594097 := bstep (se 2 (by rfl) ⟨1722786, by rfl⟩ : syracuseStep 4594097 = 3445573) B3445573
theorem B6126029 : Blo 1813608 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B3062225 : Blo 1813608 3062225 := bstep (se 2 (by rfl) ⟨1148334, by rfl⟩ : syracuseStep 3062225 = 2296669) B2296669
theorem B5167597 : Blo 1813608 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B6126083 : Blo 1813608 6126083 := bstep (se 1 (by rfl) ⟨4594562, by rfl⟩ : syracuseStep 6126083 = 9189125) B9189125
theorem B7748131 : Blo 1813608 7748131 := bstep (se 1 (by rfl) ⟨5811098, by rfl⟩ : syracuseStep 7748131 = 11622197) B11622197
theorem B3062353 : Blo 1813608 3062353 := bstep (se 2 (by rfl) ⟨1148382, by rfl⟩ : syracuseStep 3062353 = 2296765) B2296765
theorem B3062387 : Blo 1813608 3062387 := bstep (se 1 (by rfl) ⟨2296790, by rfl⟩ : syracuseStep 3062387 = 4593581) B4593581
theorem B39254669 : Blo 1813608 39254669 := bstep (se 3 (by rfl) ⟨7360250, by rfl⟩ : syracuseStep 39254669 = 14720501) B14720501
theorem B3676817 : Blo 1813608 3676817 := bstep (se 2 (by rfl) ⟨1378806, by rfl⟩ : syracuseStep 3676817 = 2757613) B2757613
theorem B3676835 : Blo 1813608 3676835 := bstep (se 1 (by rfl) ⟨2757626, by rfl⟩ : syracuseStep 3676835 = 5515253) B5515253
theorem B3062515 : Blo 1813608 3062515 := bstep (se 1 (by rfl) ⟨2296886, by rfl⟩ : syracuseStep 3062515 = 4593773) B4593773
theorem B20667149 : Blo 1813608 20667149 := bstep (se 3 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 20667149 = 7750181) B7750181
theorem B6126353 : Blo 1813608 6126353 := bstep (se 2 (by rfl) ⟨2297382, by rfl⟩ : syracuseStep 6126353 = 4594765) B4594765
theorem B6208301 : Blo 1813608 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B9812785 : Blo 1813608 9812785 := bstep (se 2 (by rfl) ⟨3679794, by rfl⟩ : syracuseStep 9812785 = 7359589) B7359589
theorem B2947889 : Blo 1813608 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B3062657 : Blo 1813608 3062657 := bstep (se 2 (by rfl) ⟨1148496, by rfl⟩ : syracuseStep 3062657 = 2296993) B2296993
theorem B2907011 : Blo 1813608 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B3980209 : Blo 1813608 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B12409805 : Blo 1813608 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B12418019 : Blo 1813608 12418019 := bstep (se 1 (by rfl) ⟨9313514, by rfl⟩ : syracuseStep 12418019 = 18627029) B18627029
theorem B3062785 : Blo 1813608 3062785 := bstep (se 2 (by rfl) ⟨1148544, by rfl⟩ : syracuseStep 3062785 = 2297089) B2297089
theorem B2759681 : Blo 1813608 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B3873827 : Blo 1813608 3873827 := bstep (se 1 (by rfl) ⟨2905370, by rfl⟩ : syracuseStep 3873827 = 5810741) B5810741
theorem B3062819 : Blo 1813608 3062819 := bstep (se 1 (by rfl) ⟨2297114, by rfl⟩ : syracuseStep 3062819 = 4594229) B4594229
theorem B19610693 : Blo 1813608 19610693 := bstep (se 4 (by rfl) ⟨1838502, by rfl⟩ : syracuseStep 19610693 = 3677005) B3677005
theorem B2759779 : Blo 1813608 2759779 := bstep (se 1 (by rfl) ⟨2069834, by rfl⟩ : syracuseStep 2759779 = 4139669) B4139669
theorem B14908529 : Blo 1813608 14908529 := bstep (se 2 (by rfl) ⟨5590698, by rfl⟩ : syracuseStep 14908529 = 11181397) B11181397
theorem B9182321 : Blo 1813608 9182321 := bstep (se 2 (by rfl) ⟨3443370, by rfl⟩ : syracuseStep 9182321 = 6886741) B6886741
theorem B11041933 : Blo 1813608 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B3062947 : Blo 1813608 3062947 := bstep (se 1 (by rfl) ⟨2297210, by rfl⟩ : syracuseStep 3062947 = 4594421) B4594421
theorem B5307569 : Blo 1813608 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B13966577 : Blo 1813608 13966577 := bstep (se 2 (by rfl) ⟨5237466, by rfl⟩ : syracuseStep 13966577 = 10474933) B10474933
theorem B2907395 : Blo 1813608 2907395 := bstep (se 1 (by rfl) ⟨2180546, by rfl⟩ : syracuseStep 2907395 = 4361093) B4361093
theorem B6126893 : Blo 1813608 6126893 := bstep (se 3 (by rfl) ⟨1148792, by rfl⟩ : syracuseStep 6126893 = 2297585) B2297585
theorem B5307697 : Blo 1813608 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B3063089 : Blo 1813608 3063089 := bstep (se 2 (by rfl) ⟨1148658, by rfl⟩ : syracuseStep 3063089 = 2297317) B2297317
theorem B6126947 : Blo 1813608 6126947 := bstep (se 1 (by rfl) ⟨4595210, by rfl⟩ : syracuseStep 6126947 = 9190421) B9190421
theorem B2907523 : Blo 1813608 2907523 := bstep (se 1 (by rfl) ⟨2180642, by rfl⟩ : syracuseStep 2907523 = 4361285) B4361285
theorem B4595089 : Blo 1813608 4595089 := bstep (se 2 (by rfl) ⟨1723158, by rfl⟩ : syracuseStep 4595089 = 3446317) B3446317
theorem B8723875 : Blo 1813608 8723875 := bstep (se 1 (by rfl) ⟨6542906, by rfl⟩ : syracuseStep 8723875 = 13085813) B13085813
theorem B3063217 : Blo 1813608 3063217 := bstep (se 2 (by rfl) ⟨1148706, by rfl⟩ : syracuseStep 3063217 = 2297413) B2297413
theorem B11034053 : Blo 1813608 11034053 := bstep (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) B2068885
theorem B3063251 : Blo 1813608 3063251 := bstep (se 1 (by rfl) ⟨2297438, by rfl⟩ : syracuseStep 3063251 = 4594877) B4594877
theorem B3874339 : Blo 1813608 3874339 := bstep (se 1 (by rfl) ⟨2905754, by rfl⟩ : syracuseStep 3874339 = 5811509) B5811509
theorem B3063379 : Blo 1813608 3063379 := bstep (se 1 (by rfl) ⟨2297534, by rfl⟩ : syracuseStep 3063379 = 4595069) B4595069
theorem B11787889 : Blo 1813608 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B6127217 : Blo 1813608 6127217 := bstep (se 2 (by rfl) ⟨2297706, by rfl⟩ : syracuseStep 6127217 = 4595413) B4595413
theorem B4595363 : Blo 1813608 4595363 := bstep (se 1 (by rfl) ⟨3446522, by rfl⟩ : syracuseStep 4595363 = 6893045) B6893045
theorem B6536909 : Blo 1813608 6536909 := bstep (se 3 (by rfl) ⟨1225670, by rfl⟩ : syracuseStep 6536909 = 2451341) B2451341
theorem B3063521 : Blo 1813608 3063521 := bstep (se 2 (by rfl) ⟨1148820, by rfl⟩ : syracuseStep 3063521 = 2297641) B2297641
theorem B7749361 : Blo 1813608 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B8838989 : Blo 1813608 8838989 := bstep (se 3 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 8838989 = 3314621) B3314621
theorem B4972369 : Blo 1813608 4972369 := bstep (se 2 (by rfl) ⟨1864638, by rfl⟩ : syracuseStep 4972369 = 3729277) B3729277
theorem B3063649 : Blo 1813608 3063649 := bstep (se 2 (by rfl) ⟨1148868, by rfl⟩ : syracuseStep 3063649 = 2297737) B2297737
theorem B4595555 : Blo 1813608 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B3063683 : Blo 1813608 3063683 := bstep (se 1 (by rfl) ⟨2297762, by rfl⟩ : syracuseStep 3063683 = 4595525) B4595525
theorem B6889475 : Blo 1813608 6889475 := bstep (se 1 (by rfl) ⟨5167106, by rfl⟩ : syracuseStep 6889475 = 10334213) B10334213
theorem B19890211 : Blo 1813608 19890211 := bstep (se 1 (by rfl) ⟨14917658, by rfl⟩ : syracuseStep 19890211 = 29835317) B29835317
theorem B9814061 : Blo 1813608 9814061 := bstep (se 3 (by rfl) ⟨1840136, by rfl⟩ : syracuseStep 9814061 = 3680273) B3680273
theorem B5169203 : Blo 1813608 5169203 := bstep (se 1 (by rfl) ⟨3876902, by rfl⟩ : syracuseStep 5169203 = 7753805) B7753805
theorem B16785587 : Blo 1813608 16785587 := bstep (se 1 (by rfl) ⟨12589190, by rfl⟩ : syracuseStep 16785587 = 25178381) B25178381
theorem B3875159 : Blo 1813608 3875159 := bstep (se 1 (by rfl) ⟨2906369, by rfl⟩ : syracuseStep 3875159 = 5812739) B5812739
theorem B4907353 : Blo 1813608 4907353 := bstep (se 2 (by rfl) ⟨1840257, by rfl⟩ : syracuseStep 4907353 = 3680515) B3680515
theorem B3269003 : Blo 1813608 3269003 := bstep (se 1 (by rfl) ⟨2451752, by rfl⟩ : syracuseStep 3269003 = 4903505) B4903505
theorem B6889931 : Blo 1813608 6889931 := bstep (se 1 (by rfl) ⟨5167448, by rfl⟩ : syracuseStep 6889931 = 10334897) B10334897
theorem B2040331 : Blo 1813608 2040331 := bstep (se 1 (by rfl) ⟨1530248, by rfl⟩ : syracuseStep 2040331 = 3060497) B3060497
theorem B16556561 : Blo 1813608 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B3727937 : Blo 1813608 3727937 := bstep (se 2 (by rfl) ⟨1397976, by rfl⟩ : syracuseStep 3727937 = 2795953) B2795953
theorem B13779557 : Blo 1813608 13779557 := bstep (se 4 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 13779557 = 2583667) B2583667
theorem B2040439 : Blo 1813608 2040439 := bstep (se 1 (by rfl) ⟨1530329, by rfl⟩ : syracuseStep 2040439 = 3060659) B3060659
theorem B3875467 : Blo 1813608 3875467 := bstep (se 1 (by rfl) ⟨2906600, by rfl⟩ : syracuseStep 3875467 = 5813201) B5813201
theorem B6890129 : Blo 1813608 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B2720459 : Blo 1813608 2720459 := bstep (se 1 (by rfl) ⟨2040344, by rfl⟩ : syracuseStep 2720459 = 4080689) B4080689
theorem B2720471 : Blo 1813608 2720471 := bstep (se 1 (by rfl) ⟨2040353, by rfl⟩ : syracuseStep 2720471 = 4080707) B4080707
theorem B3269335 : Blo 1813608 3269335 := bstep (se 1 (by rfl) ⟨2452001, by rfl⟩ : syracuseStep 3269335 = 4904003) B4904003
theorem B10330841 : Blo 1813608 10330841 := bstep (se 2 (by rfl) ⟨3874065, by rfl⟩ : syracuseStep 10330841 = 7748131) B7748131
theorem B2720537 : Blo 1813608 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B15508259 : Blo 1813608 15508259 := bstep (se 1 (by rfl) ⟨11631194, by rfl⟩ : syracuseStep 15508259 = 23262389) B23262389
theorem B2040619 : Blo 1813608 2040619 := bstep (se 1 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 2040619 = 3060929) B3060929
theorem B2720651 : Blo 1813608 2720651 := bstep (se 1 (by rfl) ⟨2040488, by rfl⟩ : syracuseStep 2720651 = 4080977) B4080977
theorem B2720663 : Blo 1813608 2720663 := bstep (se 1 (by rfl) ⟨2040497, by rfl⟩ : syracuseStep 2720663 = 4080995) B4080995
theorem B2040727 : Blo 1813608 2040727 := bstep (se 1 (by rfl) ⟨1530545, by rfl⟩ : syracuseStep 2040727 = 3061091) B3061091
theorem B66208691 : Blo 1813608 66208691 := bstep (se 1 (by rfl) ⟨49656518, by rfl⟩ : syracuseStep 66208691 = 99313037) B99313037
theorem B2720729 : Blo 1813608 2720729 := bstep (se 2 (by rfl) ⟨1020273, by rfl⟩ : syracuseStep 2720729 = 2040547) B2040547
theorem B13083713 : Blo 1813608 13083713 := bstep (se 2 (by rfl) ⟨4906392, by rfl⟩ : syracuseStep 13083713 = 9812785) B9812785
theorem B2720843 : Blo 1813608 2720843 := bstep (se 1 (by rfl) ⟨2040632, by rfl⟩ : syracuseStep 2720843 = 4081265) B4081265
theorem B2040907 : Blo 1813608 2040907 := bstep (se 1 (by rfl) ⟨1530680, by rfl⟩ : syracuseStep 2040907 = 3061361) B3061361
theorem B13780043 : Blo 1813608 13780043 := bstep (se 1 (by rfl) ⟨10335032, by rfl⟩ : syracuseStep 13780043 = 20670065) B20670065
theorem B2720855 : Blo 1813608 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B4080779 : Blo 1813608 4080779 := bstep (se 1 (by rfl) ⟨3060584, by rfl⟩ : syracuseStep 4080779 = 6121169) B6121169
theorem B2720921 : Blo 1813608 2720921 := bstep (se 2 (by rfl) ⟨1020345, by rfl⟩ : syracuseStep 2720921 = 2040691) B2040691
theorem B13436081 : Blo 1813608 13436081 := bstep (se 2 (by rfl) ⟨5038530, by rfl⟩ : syracuseStep 13436081 = 10077061) B10077061
theorem B2041015 : Blo 1813608 2041015 := bstep (se 1 (by rfl) ⟨1530761, by rfl⟩ : syracuseStep 2041015 = 3061523) B3061523
theorem B4080833 : Blo 1813608 4080833 := bstep (se 2 (by rfl) ⟨1530312, by rfl⟩ : syracuseStep 4080833 = 3060625) B3060625
theorem B7750849 : Blo 1813608 7750849 := bstep (se 2 (by rfl) ⟨2906568, by rfl⟩ : syracuseStep 7750849 = 5813137) B5813137
theorem B6980825 : Blo 1813608 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2721035 : Blo 1813608 2721035 := bstep (se 1 (by rfl) ⟨2040776, by rfl⟩ : syracuseStep 2721035 = 4081553) B4081553
theorem B2721047 : Blo 1813608 2721047 := bstep (se 1 (by rfl) ⟨2040785, by rfl⟩ : syracuseStep 2721047 = 4081571) B4081571
theorem B2721113 : Blo 1813608 2721113 := bstep (se 2 (by rfl) ⟨1020417, by rfl⟩ : syracuseStep 2721113 = 2040835) B2040835
theorem B2041195 : Blo 1813608 2041195 := bstep (se 1 (by rfl) ⟨1530896, by rfl⟩ : syracuseStep 2041195 = 3061793) B3061793
theorem B4359575 : Blo 1813608 4359575 := bstep (se 1 (by rfl) ⟨3269681, by rfl⟩ : syracuseStep 4359575 = 6539363) B6539363
theorem B8390039 : Blo 1813608 8390039 := bstep (se 1 (by rfl) ⟨6292529, by rfl⟩ : syracuseStep 8390039 = 12585059) B12585059
theorem B4081049 : Blo 1813608 4081049 := bstep (se 2 (by rfl) ⟨1530393, by rfl⟩ : syracuseStep 4081049 = 3060787) B3060787
theorem B6890903 : Blo 1813608 6890903 := bstep (se 1 (by rfl) ⟨5168177, by rfl⟩ : syracuseStep 6890903 = 10336355) B10336355
theorem B2721227 : Blo 1813608 2721227 := bstep (se 1 (by rfl) ⟨2040920, by rfl⟩ : syracuseStep 2721227 = 4081841) B4081841
theorem B3491275 : Blo 1813608 3491275 := bstep (se 1 (by rfl) ⟨2618456, by rfl⟩ : syracuseStep 3491275 = 5236913) B5236913
theorem B2721239 : Blo 1813608 2721239 := bstep (se 1 (by rfl) ⟨2040929, by rfl⟩ : syracuseStep 2721239 = 4081859) B4081859
theorem B2041303 : Blo 1813608 2041303 := bstep (se 1 (by rfl) ⟨1530977, by rfl⟩ : syracuseStep 2041303 = 3061955) B3061955
theorem B3679705 : Blo 1813608 3679705 := bstep (se 2 (by rfl) ⟨1379889, by rfl⟩ : syracuseStep 3679705 = 2759779) B2759779
theorem B4081139 : Blo 1813608 4081139 := bstep (se 1 (by rfl) ⟨3060854, by rfl⟩ : syracuseStep 4081139 = 6121709) B6121709
theorem B14722577 : Blo 1813608 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B4081175 : Blo 1813608 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B2721305 : Blo 1813608 2721305 := bstep (se 2 (by rfl) ⟨1020489, by rfl⟩ : syracuseStep 2721305 = 2040979) B2040979
theorem B24823331 : Blo 1813608 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B6891101 : Blo 1813608 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B2721419 : Blo 1813608 2721419 := bstep (se 1 (by rfl) ⟨2041064, by rfl⟩ : syracuseStep 2721419 = 4082129) B4082129
theorem B2041483 : Blo 1813608 2041483 := bstep (se 1 (by rfl) ⟨1531112, by rfl⟩ : syracuseStep 2041483 = 3062225) B3062225
theorem B2721431 : Blo 1813608 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B4081355 : Blo 1813608 4081355 := bstep (se 1 (by rfl) ⟨3061016, by rfl⟩ : syracuseStep 4081355 = 6122033) B6122033
theorem B2721497 : Blo 1813608 2721497 := bstep (se 2 (by rfl) ⟨1020561, by rfl⟩ : syracuseStep 2721497 = 2041123) B2041123
theorem B2041591 : Blo 1813608 2041591 := bstep (se 1 (by rfl) ⟨1531193, by rfl⟩ : syracuseStep 2041591 = 3062387) B3062387
theorem B4081409 : Blo 1813608 4081409 := bstep (se 2 (by rfl) ⟨1530528, by rfl⟩ : syracuseStep 4081409 = 3061057) B3061057
theorem B2451223 : Blo 1813608 2451223 := bstep (se 1 (by rfl) ⟨1838417, by rfl⟩ : syracuseStep 2451223 = 3676835) B3676835
theorem B7751447 : Blo 1813608 7751447 := bstep (se 1 (by rfl) ⟨5813585, by rfl⟩ : syracuseStep 7751447 = 11627171) B11627171
theorem B2721611 : Blo 1813608 2721611 := bstep (se 1 (by rfl) ⟨2041208, by rfl⟩ : syracuseStep 2721611 = 4082417) B4082417
theorem B2721623 : Blo 1813608 2721623 := bstep (se 1 (by rfl) ⟨2041217, by rfl⟩ : syracuseStep 2721623 = 4082435) B4082435
theorem B3876697 : Blo 1813608 3876697 := bstep (se 2 (by rfl) ⟨1453761, by rfl⟩ : syracuseStep 3876697 = 2907523) B2907523
theorem B4138867 : Blo 1813608 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B2721689 : Blo 1813608 2721689 := bstep (se 2 (by rfl) ⟨1020633, by rfl⟩ : syracuseStep 2721689 = 2041267) B2041267
theorem B2041771 : Blo 1813608 2041771 := bstep (se 1 (by rfl) ⟨1531328, by rfl⟩ : syracuseStep 2041771 = 3062657) B3062657
theorem B4081625 : Blo 1813608 4081625 := bstep (se 2 (by rfl) ⟨1530609, by rfl⟩ : syracuseStep 4081625 = 3061219) B3061219
theorem B2721803 : Blo 1813608 2721803 := bstep (se 1 (by rfl) ⟨2041352, by rfl⟩ : syracuseStep 2721803 = 4082705) B4082705
theorem B2582551 : Blo 1813608 2582551 := bstep (se 1 (by rfl) ⟨1936913, by rfl⟩ : syracuseStep 2582551 = 3873827) B3873827
theorem B2721815 : Blo 1813608 2721815 := bstep (se 1 (by rfl) ⟨2041361, by rfl⟩ : syracuseStep 2721815 = 4082723) B4082723
theorem B2041879 : Blo 1813608 2041879 := bstep (se 1 (by rfl) ⟨1531409, by rfl⟩ : syracuseStep 2041879 = 3062819) B3062819
theorem B3885079 : Blo 1813608 3885079 := bstep (se 1 (by rfl) ⟨2913809, by rfl⟩ : syracuseStep 3885079 = 5827619) B5827619
theorem B4081715 : Blo 1813608 4081715 := bstep (se 1 (by rfl) ⟨3061286, by rfl⟩ : syracuseStep 4081715 = 6122573) B6122573
theorem B9939019 : Blo 1813608 9939019 := bstep (se 1 (by rfl) ⟨7454264, by rfl⟩ : syracuseStep 9939019 = 14908529) B14908529
theorem B6121547 : Blo 1813608 6121547 := bstep (se 1 (by rfl) ⟨4591160, by rfl⟩ : syracuseStep 6121547 = 9182321) B9182321
theorem B4081751 : Blo 1813608 4081751 := bstep (se 1 (by rfl) ⟨3061313, by rfl⟩ : syracuseStep 4081751 = 6122627) B6122627
theorem B2721881 : Blo 1813608 2721881 := bstep (se 2 (by rfl) ⟨1020705, by rfl⟩ : syracuseStep 2721881 = 2041411) B2041411
theorem B2721995 : Blo 1813608 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B2042059 : Blo 1813608 2042059 := bstep (se 1 (by rfl) ⟨1531544, by rfl⟩ : syracuseStep 2042059 = 3063089) B3063089
theorem B2722007 : Blo 1813608 2722007 := bstep (se 1 (by rfl) ⟨2041505, by rfl⟩ : syracuseStep 2722007 = 4083011) B4083011
theorem B4081931 : Blo 1813608 4081931 := bstep (se 1 (by rfl) ⟨3061448, by rfl⟩ : syracuseStep 4081931 = 6122897) B6122897
theorem B2722073 : Blo 1813608 2722073 := bstep (se 2 (by rfl) ⟨1020777, by rfl⟩ : syracuseStep 2722073 = 2041555) B2041555
theorem B2042167 : Blo 1813608 2042167 := bstep (se 1 (by rfl) ⟨1531625, by rfl⟩ : syracuseStep 2042167 = 3063251) B3063251
theorem B10332481 : Blo 1813608 10332481 := bstep (se 2 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 10332481 = 7749361) B7749361
theorem B4081985 : Blo 1813608 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B6121817 : Blo 1813608 6121817 := bstep (se 2 (by rfl) ⟨2295681, by rfl⟩ : syracuseStep 6121817 = 4591363) B4591363
theorem B376924529 : Blo 1813608 376924529 := bstep (se 2 (by rfl) ⟨141346698, by rfl⟩ : syracuseStep 376924529 = 282693397) B282693397
theorem B2722187 : Blo 1813608 2722187 := bstep (se 1 (by rfl) ⟨2041640, by rfl⟩ : syracuseStep 2722187 = 4083281) B4083281
theorem B2722199 : Blo 1813608 2722199 := bstep (se 1 (by rfl) ⟨2041649, by rfl⟩ : syracuseStep 2722199 = 4083299) B4083299
theorem B6629825 : Blo 1813608 6629825 := bstep (se 2 (by rfl) ⟨2486184, by rfl⟩ : syracuseStep 6629825 = 4972369) B4972369
theorem B2296279 : Blo 1813608 2296279 := bstep (se 1 (by rfl) ⟨1722209, by rfl⟩ : syracuseStep 2296279 = 3444419) B3444419
theorem B2722265 : Blo 1813608 2722265 := bstep (se 2 (by rfl) ⟨1020849, by rfl⟩ : syracuseStep 2722265 = 2041699) B2041699
theorem B2042347 : Blo 1813608 2042347 := bstep (se 1 (by rfl) ⟨1531760, by rfl⟩ : syracuseStep 2042347 = 3063521) B3063521
theorem B4082201 : Blo 1813608 4082201 := bstep (se 2 (by rfl) ⟨1530825, by rfl⟩ : syracuseStep 4082201 = 3061651) B3061651
theorem B5892659 : Blo 1813608 5892659 := bstep (se 1 (by rfl) ⟨4419494, by rfl⟩ : syracuseStep 5892659 = 8838989) B8838989
theorem B2722379 : Blo 1813608 2722379 := bstep (se 1 (by rfl) ⟨2041784, by rfl⟩ : syracuseStep 2722379 = 4083569) B4083569
theorem B2722391 : Blo 1813608 2722391 := bstep (se 1 (by rfl) ⟨2041793, by rfl⟩ : syracuseStep 2722391 = 4083587) B4083587
theorem B2042455 : Blo 1813608 2042455 := bstep (se 1 (by rfl) ⟨1531841, by rfl⟩ : syracuseStep 2042455 = 3063683) B3063683
theorem B9185885 : Blo 1813608 9185885 := bstep (se 3 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 9185885 = 3444707) B3444707
theorem B4082291 : Blo 1813608 4082291 := bstep (se 1 (by rfl) ⟨3061718, by rfl⟩ : syracuseStep 4082291 = 6123437) B6123437
theorem B4082327 : Blo 1813608 4082327 := bstep (se 1 (by rfl) ⟨3061745, by rfl⟩ : syracuseStep 4082327 = 6123491) B6123491
theorem B2722457 : Blo 1813608 2722457 := bstep (se 2 (by rfl) ⟨1020921, by rfl⟩ : syracuseStep 2722457 = 2041843) B2041843
theorem B7359149 : Blo 1813608 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B58862285 : Blo 1813608 58862285 := bstep (se 3 (by rfl) ⟨11036678, by rfl⟩ : syracuseStep 58862285 = 22073357) B22073357
theorem B2583257 : Blo 1813608 2583257 := bstep (se 2 (by rfl) ⟨968721, by rfl⟩ : syracuseStep 2583257 = 1937443) B1937443
theorem B2722571 : Blo 1813608 2722571 := bstep (se 1 (by rfl) ⟨2041928, by rfl⟩ : syracuseStep 2722571 = 4083857) B4083857
theorem B2722583 : Blo 1813608 2722583 := bstep (se 1 (by rfl) ⟨2041937, by rfl⟩ : syracuseStep 2722583 = 4083875) B4083875
theorem B2583371 : Blo 1813608 2583371 := bstep (se 1 (by rfl) ⟨1937528, by rfl⟩ : syracuseStep 2583371 = 3875057) B3875057
theorem B4082507 : Blo 1813608 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B2722649 : Blo 1813608 2722649 := bstep (se 2 (by rfl) ⟨1020993, by rfl⟩ : syracuseStep 2722649 = 2041987) B2041987
theorem B4082561 : Blo 1813608 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B2722763 : Blo 1813608 2722763 := bstep (se 1 (by rfl) ⟨2042072, by rfl⟩ : syracuseStep 2722763 = 4084145) B4084145
theorem B3271627 : Blo 1813608 3271627 := bstep (se 1 (by rfl) ⟨2453720, by rfl⟩ : syracuseStep 3271627 = 4907441) B4907441
theorem B2722775 : Blo 1813608 2722775 := bstep (se 1 (by rfl) ⟨2042081, by rfl⟩ : syracuseStep 2722775 = 4084163) B4084163
theorem B3443735 : Blo 1813608 3443735 := bstep (se 1 (by rfl) ⟨2582801, by rfl⟩ : syracuseStep 3443735 = 5165603) B5165603
theorem B6122519 : Blo 1813608 6122519 := bstep (se 1 (by rfl) ⟨4591889, by rfl⟩ : syracuseStep 6122519 = 9183779) B9183779
theorem B2722841 : Blo 1813608 2722841 := bstep (se 2 (by rfl) ⟨1021065, by rfl⟩ : syracuseStep 2722841 = 2042131) B2042131
theorem B20671523 : Blo 1813608 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B15707201 : Blo 1813608 15707201 := bstep (se 2 (by rfl) ⟨5890200, by rfl⟩ : syracuseStep 15707201 = 11780401) B11780401
theorem B7752779 : Blo 1813608 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B4082777 : Blo 1813608 4082777 := bstep (se 2 (by rfl) ⟨1531041, by rfl⟩ : syracuseStep 4082777 = 3062083) B3062083
theorem B1813611 : Blo 1813608 1813611 := bstep (se 1 (by rfl) ⟨1360208, by rfl⟩ : syracuseStep 1813611 = 2720417) B2720417
theorem B1813623 : Blo 1813608 1813623 := bstep (se 1 (by rfl) ⟨1360217, by rfl⟩ : syracuseStep 1813623 = 2720435) B2720435
theorem B1813643 : Blo 1813608 1813643 := bstep (se 1 (by rfl) ⟨1360232, by rfl⟩ : syracuseStep 1813643 = 2720465) B2720465
theorem B2722955 : Blo 1813608 2722955 := bstep (se 1 (by rfl) ⟨2042216, by rfl⟩ : syracuseStep 2722955 = 4084433) B4084433
theorem B1813655 : Blo 1813608 1813655 := bstep (se 1 (by rfl) ⟨1360241, by rfl⟩ : syracuseStep 1813655 = 2720483) B2720483
theorem B2722967 : Blo 1813608 2722967 := bstep (se 1 (by rfl) ⟨2042225, by rfl⟩ : syracuseStep 2722967 = 4084451) B4084451
theorem B1813675 : Blo 1813608 1813675 := bstep (se 1 (by rfl) ⟨1360256, by rfl⟩ : syracuseStep 1813675 = 2720513) B2720513
theorem B4082867 : Blo 1813608 4082867 := bstep (se 1 (by rfl) ⟨3062150, by rfl⟩ : syracuseStep 4082867 = 6124301) B6124301
theorem B1813687 : Blo 1813608 1813687 := bstep (se 1 (by rfl) ⟨1360265, by rfl⟩ : syracuseStep 1813687 = 2720531) B2720531
theorem B1813707 : Blo 1813608 1813707 := bstep (se 1 (by rfl) ⟨1360280, by rfl⟩ : syracuseStep 1813707 = 2720561) B2720561
theorem B14150861 : Blo 1813608 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1813719 : Blo 1813608 1813719 := bstep (se 1 (by rfl) ⟨1360289, by rfl⟩ : syracuseStep 1813719 = 2720579) B2720579
theorem B4082903 : Blo 1813608 4082903 := bstep (se 1 (by rfl) ⟨3062177, by rfl⟩ : syracuseStep 4082903 = 6124355) B6124355
theorem B2723033 : Blo 1813608 2723033 := bstep (se 2 (by rfl) ⟨1021137, by rfl⟩ : syracuseStep 2723033 = 2042275) B2042275
theorem B1813739 : Blo 1813608 1813739 := bstep (se 1 (by rfl) ⟨1360304, by rfl⟩ : syracuseStep 1813739 = 2720609) B2720609
theorem B1813751 : Blo 1813608 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B117714181 : Blo 1813608 117714181 := bstep (se 4 (by rfl) ⟨11035704, by rfl⟩ : syracuseStep 117714181 = 22071409) B22071409
theorem B1813771 : Blo 1813608 1813771 := bstep (se 1 (by rfl) ⟨1360328, by rfl⟩ : syracuseStep 1813771 = 2720657) B2720657
theorem B2297099 : Blo 1813608 2297099 := bstep (se 1 (by rfl) ⟨1722824, by rfl⟩ : syracuseStep 2297099 = 3445649) B3445649
theorem B1813783 : Blo 1813608 1813783 := bstep (se 1 (by rfl) ⟨1360337, by rfl⟩ : syracuseStep 1813783 = 2720675) B2720675
theorem B1813803 : Blo 1813608 1813803 := bstep (se 1 (by rfl) ⟨1360352, by rfl⟩ : syracuseStep 1813803 = 2720705) B2720705
theorem B1813815 : Blo 1813608 1813815 := bstep (se 1 (by rfl) ⟨1360361, by rfl⟩ : syracuseStep 1813815 = 2720723) B2720723
theorem B1813835 : Blo 1813608 1813835 := bstep (se 1 (by rfl) ⟨1360376, by rfl⟩ : syracuseStep 1813835 = 2720753) B2720753
theorem B2723147 : Blo 1813608 2723147 := bstep (se 1 (by rfl) ⟨2042360, by rfl⟩ : syracuseStep 2723147 = 4084721) B4084721
theorem B1813847 : Blo 1813608 1813847 := bstep (se 1 (by rfl) ⟨1360385, by rfl⟩ : syracuseStep 1813847 = 2720771) B2720771
theorem B2583895 : Blo 1813608 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B2723159 : Blo 1813608 2723159 := bstep (se 1 (by rfl) ⟨2042369, by rfl⟩ : syracuseStep 2723159 = 4084739) B4084739
theorem B1813867 : Blo 1813608 1813867 := bstep (se 1 (by rfl) ⟨1360400, by rfl⟩ : syracuseStep 1813867 = 2720801) B2720801
theorem B1813879 : Blo 1813608 1813879 := bstep (se 1 (by rfl) ⟨1360409, by rfl⟩ : syracuseStep 1813879 = 2720819) B2720819
theorem B13774211 : Blo 1813608 13774211 := bstep (se 1 (by rfl) ⟨10330658, by rfl⟩ : syracuseStep 13774211 = 20661317) B20661317
theorem B1813899 : Blo 1813608 1813899 := bstep (se 1 (by rfl) ⟨1360424, by rfl⟩ : syracuseStep 1813899 = 2720849) B2720849
theorem B4083083 : Blo 1813608 4083083 := bstep (se 1 (by rfl) ⟨3062312, by rfl⟩ : syracuseStep 4083083 = 6124625) B6124625
theorem B1813911 : Blo 1813608 1813911 := bstep (se 1 (by rfl) ⟨1360433, by rfl⟩ : syracuseStep 1813911 = 2720867) B2720867
theorem B2723225 : Blo 1813608 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B1936811 : Blo 1813608 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B1813931 : Blo 1813608 1813931 := bstep (se 1 (by rfl) ⟨1360448, by rfl⟩ : syracuseStep 1813931 = 2720897) B2720897
theorem B1813943 : Blo 1813608 1813943 := bstep (se 1 (by rfl) ⟨1360457, by rfl⟩ : syracuseStep 1813943 = 2720915) B2720915
theorem B4083137 : Blo 1813608 4083137 := bstep (se 2 (by rfl) ⟨1531176, by rfl⟩ : syracuseStep 4083137 = 3062353) B3062353
theorem B1813963 : Blo 1813608 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B1813975 : Blo 1813608 1813975 := bstep (se 1 (by rfl) ⟨1360481, by rfl⟩ : syracuseStep 1813975 = 2720963) B2720963
theorem B1813995 : Blo 1813608 1813995 := bstep (se 1 (by rfl) ⟨1360496, by rfl⟩ : syracuseStep 1813995 = 2720993) B2720993
theorem B1814007 : Blo 1813608 1814007 := bstep (se 1 (by rfl) ⟨1360505, by rfl⟩ : syracuseStep 1814007 = 2721011) B2721011
theorem B6893059 : Blo 1813608 6893059 := bstep (se 1 (by rfl) ⟨5169794, by rfl⟩ : syracuseStep 6893059 = 10339589) B10339589
theorem B1814027 : Blo 1813608 1814027 := bstep (se 1 (by rfl) ⟨1360520, by rfl⟩ : syracuseStep 1814027 = 2721041) B2721041
theorem B2723339 : Blo 1813608 2723339 := bstep (se 1 (by rfl) ⟨2042504, by rfl⟩ : syracuseStep 2723339 = 4085009) B4085009
theorem B56618513 : Blo 1813608 56618513 := bstep (se 2 (by rfl) ⟨21231942, by rfl⟩ : syracuseStep 56618513 = 42463885) B42463885
theorem B1814039 : Blo 1813608 1814039 := bstep (se 1 (by rfl) ⟨1360529, by rfl⟩ : syracuseStep 1814039 = 2721059) B2721059
theorem B2723351 : Blo 1813608 2723351 := bstep (se 1 (by rfl) ⟨2042513, by rfl⟩ : syracuseStep 2723351 = 4085027) B4085027
theorem B1814059 : Blo 1813608 1814059 := bstep (se 1 (by rfl) ⟨1360544, by rfl⟩ : syracuseStep 1814059 = 2721089) B2721089
theorem B6123059 : Blo 1813608 6123059 := bstep (se 1 (by rfl) ⟨4592294, by rfl⟩ : syracuseStep 6123059 = 9184589) B9184589
theorem B3444275 : Blo 1813608 3444275 := bstep (se 1 (by rfl) ⟨2583206, by rfl⟩ : syracuseStep 3444275 = 5166413) B5166413
theorem B1814071 : Blo 1813608 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B1814091 : Blo 1813608 1814091 := bstep (se 1 (by rfl) ⟨1360568, by rfl⟩ : syracuseStep 1814091 = 2721137) B2721137
theorem B1814103 : Blo 1813608 1814103 := bstep (se 1 (by rfl) ⟨1360577, by rfl⟩ : syracuseStep 1814103 = 2721155) B2721155
theorem B1814123 : Blo 1813608 1814123 := bstep (se 1 (by rfl) ⟨1360592, by rfl⟩ : syracuseStep 1814123 = 2721185) B2721185
theorem B1814135 : Blo 1813608 1814135 := bstep (se 1 (by rfl) ⟨1360601, by rfl⟩ : syracuseStep 1814135 = 2721203) B2721203
theorem B1814155 : Blo 1813608 1814155 := bstep (se 1 (by rfl) ⟨1360616, by rfl⟩ : syracuseStep 1814155 = 2721233) B2721233
theorem B1814167 : Blo 1813608 1814167 := bstep (se 1 (by rfl) ⟨1360625, by rfl⟩ : syracuseStep 1814167 = 2721251) B2721251
theorem B4083353 : Blo 1813608 4083353 := bstep (se 2 (by rfl) ⟨1531257, by rfl⟩ : syracuseStep 4083353 = 3062515) B3062515
theorem B1814187 : Blo 1813608 1814187 := bstep (se 1 (by rfl) ⟨1360640, by rfl⟩ : syracuseStep 1814187 = 2721281) B2721281
theorem B1814199 : Blo 1813608 1814199 := bstep (se 1 (by rfl) ⟨1360649, by rfl⟩ : syracuseStep 1814199 = 2721299) B2721299
theorem B1814219 : Blo 1813608 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B1814231 : Blo 1813608 1814231 := bstep (se 1 (by rfl) ⟨1360673, by rfl⟩ : syracuseStep 1814231 = 2721347) B2721347
theorem B1814251 : Blo 1813608 1814251 := bstep (se 1 (by rfl) ⟨1360688, by rfl⟩ : syracuseStep 1814251 = 2721377) B2721377
theorem B4083443 : Blo 1813608 4083443 := bstep (se 1 (by rfl) ⟨3062582, by rfl⟩ : syracuseStep 4083443 = 6125165) B6125165
theorem B1814263 : Blo 1813608 1814263 := bstep (se 1 (by rfl) ⟨1360697, by rfl⟩ : syracuseStep 1814263 = 2721395) B2721395
theorem B1814283 : Blo 1813608 1814283 := bstep (se 1 (by rfl) ⟨1360712, by rfl⟩ : syracuseStep 1814283 = 2721425) B2721425
theorem B1814295 : Blo 1813608 1814295 := bstep (se 1 (by rfl) ⟨1360721, by rfl⟩ : syracuseStep 1814295 = 2721443) B2721443
theorem B4083479 : Blo 1813608 4083479 := bstep (se 1 (by rfl) ⟨3062609, by rfl⟩ : syracuseStep 4083479 = 6125219) B6125219
theorem B1814315 : Blo 1813608 1814315 := bstep (se 1 (by rfl) ⟨1360736, by rfl⟩ : syracuseStep 1814315 = 2721473) B2721473
theorem B6893363 : Blo 1813608 6893363 := bstep (se 1 (by rfl) ⟨5170022, by rfl⟩ : syracuseStep 6893363 = 10340045) B10340045
theorem B1814327 : Blo 1813608 1814327 := bstep (se 1 (by rfl) ⟨1360745, by rfl⟩ : syracuseStep 1814327 = 2721491) B2721491
theorem B6123329 : Blo 1813608 6123329 := bstep (se 2 (by rfl) ⟨2296248, by rfl⟩ : syracuseStep 6123329 = 4592497) B4592497
theorem B1814347 : Blo 1813608 1814347 := bstep (se 1 (by rfl) ⟨1360760, by rfl⟩ : syracuseStep 1814347 = 2721521) B2721521
theorem B1814359 : Blo 1813608 1814359 := bstep (se 1 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 1814359 = 2721539) B2721539
theorem B1814379 : Blo 1813608 1814379 := bstep (se 1 (by rfl) ⟨1360784, by rfl⟩ : syracuseStep 1814379 = 2721569) B2721569
theorem B1814391 : Blo 1813608 1814391 := bstep (se 1 (by rfl) ⟨1360793, by rfl⟩ : syracuseStep 1814391 = 2721587) B2721587
theorem B1814411 : Blo 1813608 1814411 := bstep (se 1 (by rfl) ⟨1360808, by rfl⟩ : syracuseStep 1814411 = 2721617) B2721617
theorem B1814423 : Blo 1813608 1814423 := bstep (se 1 (by rfl) ⟨1360817, by rfl⟩ : syracuseStep 1814423 = 2721635) B2721635
theorem B2486167 : Blo 1813608 2486167 := bstep (se 1 (by rfl) ⟨1864625, by rfl⟩ : syracuseStep 2486167 = 3729251) B3729251
theorem B1814443 : Blo 1813608 1814443 := bstep (se 1 (by rfl) ⟨1360832, by rfl⟩ : syracuseStep 1814443 = 2721665) B2721665
theorem B1814455 : Blo 1813608 1814455 := bstep (se 1 (by rfl) ⟨1360841, by rfl⟩ : syracuseStep 1814455 = 2721683) B2721683
theorem B1814475 : Blo 1813608 1814475 := bstep (se 1 (by rfl) ⟨1360856, by rfl⟩ : syracuseStep 1814475 = 2721713) B2721713
theorem B4083659 : Blo 1813608 4083659 := bstep (se 1 (by rfl) ⟨3062744, by rfl⟩ : syracuseStep 4083659 = 6125489) B6125489
theorem B2297803 : Blo 1813608 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B1814487 : Blo 1813608 1814487 := bstep (se 1 (by rfl) ⟨1360865, by rfl⟩ : syracuseStep 1814487 = 2721731) B2721731
theorem B1814507 : Blo 1813608 1814507 := bstep (se 1 (by rfl) ⟨1360880, by rfl⟩ : syracuseStep 1814507 = 2721761) B2721761
theorem B1814519 : Blo 1813608 1814519 := bstep (se 1 (by rfl) ⟨1360889, by rfl⟩ : syracuseStep 1814519 = 2721779) B2721779
theorem B4083713 : Blo 1813608 4083713 := bstep (se 2 (by rfl) ⟨1531392, by rfl⟩ : syracuseStep 4083713 = 3062785) B3062785
theorem B1814539 : Blo 1813608 1814539 := bstep (se 1 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 1814539 = 2721809) B2721809
theorem B59666453 : Blo 1813608 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B1814551 : Blo 1813608 1814551 := bstep (se 1 (by rfl) ⟨1360913, by rfl⟩ : syracuseStep 1814551 = 2721827) B2721827
theorem B3444761 : Blo 1813608 3444761 := bstep (se 2 (by rfl) ⟨1291785, by rfl⟩ : syracuseStep 3444761 = 2583571) B2583571
theorem B1814571 : Blo 1813608 1814571 := bstep (se 1 (by rfl) ⟨1360928, by rfl⟩ : syracuseStep 1814571 = 2721857) B2721857
theorem B4591667 : Blo 1813608 4591667 := bstep (se 1 (by rfl) ⟨3443750, by rfl⟩ : syracuseStep 4591667 = 6887501) B6887501
theorem B1814583 : Blo 1813608 1814583 := bstep (se 1 (by rfl) ⟨1360937, by rfl⟩ : syracuseStep 1814583 = 2721875) B2721875
theorem B1814603 : Blo 1813608 1814603 := bstep (se 1 (by rfl) ⟨1360952, by rfl⟩ : syracuseStep 1814603 = 2721905) B2721905
theorem B1814615 : Blo 1813608 1814615 := bstep (se 1 (by rfl) ⟨1360961, by rfl⟩ : syracuseStep 1814615 = 2721923) B2721923
theorem B1814635 : Blo 1813608 1814635 := bstep (se 1 (by rfl) ⟨1360976, by rfl⟩ : syracuseStep 1814635 = 2721953) B2721953
theorem B1814647 : Blo 1813608 1814647 := bstep (se 1 (by rfl) ⟨1360985, by rfl⟩ : syracuseStep 1814647 = 2721971) B2721971
theorem B1814667 : Blo 1813608 1814667 := bstep (se 1 (by rfl) ⟨1361000, by rfl⟩ : syracuseStep 1814667 = 2722001) B2722001
theorem B2584715 : Blo 1813608 2584715 := bstep (se 1 (by rfl) ⟨1938536, by rfl⟩ : syracuseStep 2584715 = 3877073) B3877073
theorem B1814679 : Blo 1813608 1814679 := bstep (se 1 (by rfl) ⟨1361009, by rfl⟩ : syracuseStep 1814679 = 2722019) B2722019
theorem B1814699 : Blo 1813608 1814699 := bstep (se 1 (by rfl) ⟨1361024, by rfl⟩ : syracuseStep 1814699 = 2722049) B2722049
theorem B7753907 : Blo 1813608 7753907 := bstep (se 1 (by rfl) ⟨5815430, by rfl⟩ : syracuseStep 7753907 = 11630861) B11630861
theorem B31436981 : Blo 1813608 31436981 := bstep (se 5 (by rfl) ⟨1473608, by rfl⟩ : syracuseStep 31436981 = 2947217) B2947217
theorem B1814711 : Blo 1813608 1814711 := bstep (se 1 (by rfl) ⟨1361033, by rfl⟩ : syracuseStep 1814711 = 2722067) B2722067
theorem B1814731 : Blo 1813608 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B1814743 : Blo 1813608 1814743 := bstep (se 1 (by rfl) ⟨1361057, by rfl⟩ : syracuseStep 1814743 = 2722115) B2722115
theorem B4083929 : Blo 1813608 4083929 := bstep (se 2 (by rfl) ⟨1531473, by rfl⟩ : syracuseStep 4083929 = 3062947) B3062947
theorem B1814763 : Blo 1813608 1814763 := bstep (se 1 (by rfl) ⟨1361072, by rfl⟩ : syracuseStep 1814763 = 2722145) B2722145
theorem B1814775 : Blo 1813608 1814775 := bstep (se 1 (by rfl) ⟨1361081, by rfl⟩ : syracuseStep 1814775 = 2722163) B2722163
theorem B1814795 : Blo 1813608 1814795 := bstep (se 1 (by rfl) ⟨1361096, by rfl⟩ : syracuseStep 1814795 = 2722193) B2722193
theorem B1814807 : Blo 1813608 1814807 := bstep (se 1 (by rfl) ⟨1361105, by rfl⟩ : syracuseStep 1814807 = 2722211) B2722211
theorem B1814827 : Blo 1813608 1814827 := bstep (se 1 (by rfl) ⟨1361120, by rfl⟩ : syracuseStep 1814827 = 2722241) B2722241
theorem B4084019 : Blo 1813608 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B1814839 : Blo 1813608 1814839 := bstep (se 1 (by rfl) ⟨1361129, by rfl⟩ : syracuseStep 1814839 = 2722259) B2722259
theorem B1814859 : Blo 1813608 1814859 := bstep (se 1 (by rfl) ⟨1361144, by rfl⟩ : syracuseStep 1814859 = 2722289) B2722289
theorem B1814871 : Blo 1813608 1814871 := bstep (se 1 (by rfl) ⟨1361153, by rfl⟩ : syracuseStep 1814871 = 2722307) B2722307
theorem B4084055 : Blo 1813608 4084055 := bstep (se 1 (by rfl) ⟨3063041, by rfl⟩ : syracuseStep 4084055 = 6126083) B6126083
theorem B4591961 : Blo 1813608 4591961 := bstep (se 2 (by rfl) ⟨1721985, by rfl⟩ : syracuseStep 4591961 = 3443971) B3443971
theorem B6123869 : Blo 1813608 6123869 := bstep (se 3 (by rfl) ⟨1148225, by rfl⟩ : syracuseStep 6123869 = 2296451) B2296451
theorem B1814891 : Blo 1813608 1814891 := bstep (se 1 (by rfl) ⟨1361168, by rfl⟩ : syracuseStep 1814891 = 2722337) B2722337
theorem B1814903 : Blo 1813608 1814903 := bstep (se 1 (by rfl) ⟨1361177, by rfl⟩ : syracuseStep 1814903 = 2722355) B2722355
theorem B1814923 : Blo 1813608 1814923 := bstep (se 1 (by rfl) ⟨1361192, by rfl⟩ : syracuseStep 1814923 = 2722385) B2722385
theorem B1814935 : Blo 1813608 1814935 := bstep (se 1 (by rfl) ⟨1361201, by rfl⟩ : syracuseStep 1814935 = 2722403) B2722403
theorem B1814955 : Blo 1813608 1814955 := bstep (se 1 (by rfl) ⟨1361216, by rfl⟩ : syracuseStep 1814955 = 2722433) B2722433
theorem B26169779 : Blo 1813608 26169779 := bstep (se 1 (by rfl) ⟨19627334, by rfl⟩ : syracuseStep 26169779 = 39254669) B39254669
theorem B1814967 : Blo 1813608 1814967 := bstep (se 1 (by rfl) ⟨1361225, by rfl⟩ : syracuseStep 1814967 = 2722451) B2722451
theorem B1814987 : Blo 1813608 1814987 := bstep (se 1 (by rfl) ⟨1361240, by rfl⟩ : syracuseStep 1814987 = 2722481) B2722481
theorem B1814999 : Blo 1813608 1814999 := bstep (se 1 (by rfl) ⟨1361249, by rfl⟩ : syracuseStep 1814999 = 2722499) B2722499
theorem B1815019 : Blo 1813608 1815019 := bstep (se 1 (by rfl) ⟨1361264, by rfl⟩ : syracuseStep 1815019 = 2722529) B2722529
theorem B1815031 : Blo 1813608 1815031 := bstep (se 1 (by rfl) ⟨1361273, by rfl⟩ : syracuseStep 1815031 = 2722547) B2722547
theorem B1815051 : Blo 1813608 1815051 := bstep (se 1 (by rfl) ⟨1361288, by rfl⟩ : syracuseStep 1815051 = 2722577) B2722577
theorem B4084235 : Blo 1813608 4084235 := bstep (se 1 (by rfl) ⟨3063176, by rfl⟩ : syracuseStep 4084235 = 6126353) B6126353
theorem B1815063 : Blo 1813608 1815063 := bstep (se 1 (by rfl) ⟨1361297, by rfl⟩ : syracuseStep 1815063 = 2722595) B2722595
theorem B1815083 : Blo 1813608 1815083 := bstep (se 1 (by rfl) ⟨1361312, by rfl⟩ : syracuseStep 1815083 = 2722625) B2722625
theorem B1815095 : Blo 1813608 1815095 := bstep (se 1 (by rfl) ⟨1361321, by rfl⟩ : syracuseStep 1815095 = 2722643) B2722643
theorem B4084289 : Blo 1813608 4084289 := bstep (se 2 (by rfl) ⟨1531608, by rfl⟩ : syracuseStep 4084289 = 3063217) B3063217
theorem B1815115 : Blo 1813608 1815115 := bstep (se 1 (by rfl) ⟨1361336, by rfl⟩ : syracuseStep 1815115 = 2722673) B2722673
theorem B1938007 : Blo 1813608 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B1815127 : Blo 1813608 1815127 := bstep (se 1 (by rfl) ⟨1361345, by rfl⟩ : syracuseStep 1815127 = 2722691) B2722691
theorem B1815147 : Blo 1813608 1815147 := bstep (se 1 (by rfl) ⟨1361360, by rfl⟩ : syracuseStep 1815147 = 2722721) B2722721
theorem B1815159 : Blo 1813608 1815159 := bstep (se 1 (by rfl) ⟨1361369, by rfl⟩ : syracuseStep 1815159 = 2722739) B2722739
theorem B1815179 : Blo 1813608 1815179 := bstep (se 1 (by rfl) ⟨1361384, by rfl⟩ : syracuseStep 1815179 = 2722769) B2722769
theorem B9187991 : Blo 1813608 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B8278679 : Blo 1813608 8278679 := bstep (se 1 (by rfl) ⟨6209009, by rfl⟩ : syracuseStep 8278679 = 12418019) B12418019
theorem B1815191 : Blo 1813608 1815191 := bstep (se 1 (by rfl) ⟨1361393, by rfl⟩ : syracuseStep 1815191 = 2722787) B2722787
theorem B1815211 : Blo 1813608 1815211 := bstep (se 1 (by rfl) ⟨1361408, by rfl⟩ : syracuseStep 1815211 = 2722817) B2722817
theorem B1815223 : Blo 1813608 1815223 := bstep (se 1 (by rfl) ⟨1361417, by rfl⟩ : syracuseStep 1815223 = 2722835) B2722835
theorem B1815243 : Blo 1813608 1815243 := bstep (se 1 (by rfl) ⟨1361432, by rfl⟩ : syracuseStep 1815243 = 2722865) B2722865
theorem B5165785 : Blo 1813608 5165785 := bstep (se 2 (by rfl) ⟨1937169, by rfl⟩ : syracuseStep 5165785 = 3874339) B3874339
theorem B1815255 : Blo 1813608 1815255 := bstep (se 1 (by rfl) ⟨1361441, by rfl⟩ : syracuseStep 1815255 = 2722883) B2722883
theorem B1815275 : Blo 1813608 1815275 := bstep (se 1 (by rfl) ⟨1361456, by rfl⟩ : syracuseStep 1815275 = 2722913) B2722913
theorem B1815287 : Blo 1813608 1815287 := bstep (se 1 (by rfl) ⟨1361465, by rfl⟩ : syracuseStep 1815287 = 2722931) B2722931
theorem B1815307 : Blo 1813608 1815307 := bstep (se 1 (by rfl) ⟨1361480, by rfl⟩ : syracuseStep 1815307 = 2722961) B2722961
theorem B1815319 : Blo 1813608 1815319 := bstep (se 1 (by rfl) ⟨1361489, by rfl⟩ : syracuseStep 1815319 = 2722979) B2722979
theorem B4084505 : Blo 1813608 4084505 := bstep (se 2 (by rfl) ⟨1531689, by rfl⟩ : syracuseStep 4084505 = 3063379) B3063379
theorem B1815339 : Blo 1813608 1815339 := bstep (se 1 (by rfl) ⟨1361504, by rfl⟩ : syracuseStep 1815339 = 2723009) B2723009
theorem B1815351 : Blo 1813608 1815351 := bstep (se 1 (by rfl) ⟨1361513, by rfl⟩ : syracuseStep 1815351 = 2723027) B2723027
theorem B15717185 : Blo 1813608 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B9311051 : Blo 1813608 9311051 := bstep (se 1 (by rfl) ⟨6983288, by rfl⟩ : syracuseStep 9311051 = 13966577) B13966577
theorem B1815371 : Blo 1813608 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B1938263 : Blo 1813608 1938263 := bstep (se 1 (by rfl) ⟨1453697, by rfl⟩ : syracuseStep 1938263 = 2907395) B2907395
theorem B1815383 : Blo 1813608 1815383 := bstep (se 1 (by rfl) ⟨1361537, by rfl⟩ : syracuseStep 1815383 = 2723075) B2723075
theorem B1815403 : Blo 1813608 1815403 := bstep (se 1 (by rfl) ⟨1361552, by rfl⟩ : syracuseStep 1815403 = 2723105) B2723105
theorem B4084595 : Blo 1813608 4084595 := bstep (se 1 (by rfl) ⟨3063446, by rfl⟩ : syracuseStep 4084595 = 6126893) B6126893
theorem B1815415 : Blo 1813608 1815415 := bstep (se 1 (by rfl) ⟨1361561, by rfl⟩ : syracuseStep 1815415 = 2723123) B2723123
theorem B1815435 : Blo 1813608 1815435 := bstep (se 1 (by rfl) ⟨1361576, by rfl⟩ : syracuseStep 1815435 = 2723153) B2723153
theorem B4084631 : Blo 1813608 4084631 := bstep (se 1 (by rfl) ⟨3063473, by rfl⟩ : syracuseStep 4084631 = 6126947) B6126947
theorem B1815447 : Blo 1813608 1815447 := bstep (se 1 (by rfl) ⟨1361585, by rfl⟩ : syracuseStep 1815447 = 2723171) B2723171
theorem B1815467 : Blo 1813608 1815467 := bstep (se 1 (by rfl) ⟨1361600, by rfl⟩ : syracuseStep 1815467 = 2723201) B2723201
theorem B1815479 : Blo 1813608 1815479 := bstep (se 1 (by rfl) ⟨1361609, by rfl⟩ : syracuseStep 1815479 = 2723219) B2723219
theorem B1815499 : Blo 1813608 1815499 := bstep (se 1 (by rfl) ⟨1361624, by rfl⟩ : syracuseStep 1815499 = 2723249) B2723249
theorem B1815511 : Blo 1813608 1815511 := bstep (se 1 (by rfl) ⟨1361633, by rfl⟩ : syracuseStep 1815511 = 2723267) B2723267
theorem B1815531 : Blo 1813608 1815531 := bstep (se 1 (by rfl) ⟨1361648, by rfl⟩ : syracuseStep 1815531 = 2723297) B2723297
theorem B1815543 : Blo 1813608 1815543 := bstep (se 1 (by rfl) ⟨1361657, by rfl⟩ : syracuseStep 1815543 = 2723315) B2723315
theorem B1815563 : Blo 1813608 1815563 := bstep (se 1 (by rfl) ⟨1361672, by rfl⟩ : syracuseStep 1815563 = 2723345) B2723345
theorem B17445905 : Blo 1813608 17445905 := bstep (se 2 (by rfl) ⟨6542214, by rfl⟩ : syracuseStep 17445905 = 13084429) B13084429
theorem B1815575 : Blo 1813608 1815575 := bstep (se 1 (by rfl) ⟨1361681, by rfl⟩ : syracuseStep 1815575 = 2723363) B2723363
theorem B1815595 : Blo 1813608 1815595 := bstep (se 1 (by rfl) ⟨1361696, by rfl⟩ : syracuseStep 1815595 = 2723393) B2723393
theorem B1815607 : Blo 1813608 1815607 := bstep (se 1 (by rfl) ⟨1361705, by rfl⟩ : syracuseStep 1815607 = 2723411) B2723411
theorem B4084811 : Blo 1813608 4084811 := bstep (se 1 (by rfl) ⟨3063608, by rfl⟩ : syracuseStep 4084811 = 6127217) B6127217
theorem B5166173 : Blo 1813608 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B4084865 : Blo 1813608 4084865 := bstep (se 2 (by rfl) ⟨1531824, by rfl⟩ : syracuseStep 4084865 = 3063649) B3063649
theorem B3060875 : Blo 1813608 3060875 := bstep (se 1 (by rfl) ⟨2295656, by rfl⟩ : syracuseStep 3060875 = 4591313) B4591313
theorem B33092813 : Blo 1813608 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B3061003 : Blo 1813608 3061003 := bstep (se 1 (by rfl) ⟨2295752, by rfl⟩ : syracuseStep 3061003 = 4591505) B4591505
theorem B7746833 : Blo 1813608 7746833 := bstep (se 2 (by rfl) ⟨2905062, by rfl⟩ : syracuseStep 7746833 = 5810125) B5810125
theorem B4085081 : Blo 1813608 4085081 := bstep (se 2 (by rfl) ⟨1531905, by rfl⟩ : syracuseStep 4085081 = 3063811) B3063811
theorem B1938827 : Blo 1813608 1938827 := bstep (se 1 (by rfl) ⟨1454120, by rfl⟩ : syracuseStep 1938827 = 2908241) B2908241
theorem B3061145 : Blo 1813608 3061145 := bstep (se 2 (by rfl) ⟨1147929, by rfl⟩ : syracuseStep 3061145 = 2295859) B2295859
theorem B6125003 : Blo 1813608 6125003 := bstep (se 1 (by rfl) ⟨4593752, by rfl⟩ : syracuseStep 6125003 = 9187505) B9187505
theorem B3446219 : Blo 1813608 3446219 := bstep (se 1 (by rfl) ⟨2584664, by rfl⟩ : syracuseStep 3446219 = 5169329) B5169329
theorem B29439449 : Blo 1813608 29439449 := bstep (se 2 (by rfl) ⟨11039793, by rfl⟩ : syracuseStep 29439449 = 22079587) B22079587
theorem B3061273 : Blo 1813608 3061273 := bstep (se 2 (by rfl) ⟨1147977, by rfl⟩ : syracuseStep 3061273 = 2295955) B2295955
theorem B3446401 : Blo 1813608 3446401 := bstep (se 2 (by rfl) ⟨1292400, by rfl⟩ : syracuseStep 3446401 = 2584801) B2584801
theorem B10335923 : Blo 1813608 10335923 := bstep (se 1 (by rfl) ⟨7751942, by rfl⟩ : syracuseStep 10335923 = 15503885) B15503885
theorem B6125273 : Blo 1813608 6125273 := bstep (se 2 (by rfl) ⟨2296977, by rfl⟩ : syracuseStep 6125273 = 4593955) B4593955
theorem B6887213 : Blo 1813608 6887213 := bstep (se 3 (by rfl) ⟨1291352, by rfl⟩ : syracuseStep 6887213 = 2582705) B2582705
theorem B15505283 : Blo 1813608 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B2209675 : Blo 1813608 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B4593611 : Blo 1813608 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B13965317 : Blo 1813608 13965317 := bstep (se 4 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 13965317 = 2618497) B2618497
theorem B2758679 : Blo 1813608 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B5519411 : Blo 1813608 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3061847 : Blo 1813608 3061847 := bstep (se 1 (by rfl) ⟨2296385, by rfl⟩ : syracuseStep 3061847 = 4592771) B4592771
theorem B7747757 : Blo 1813608 7747757 := bstep (se 3 (by rfl) ⟨1452704, by rfl⟩ : syracuseStep 7747757 = 2905409) B2905409
theorem B3061975 : Blo 1813608 3061975 := bstep (se 1 (by rfl) ⟨2296481, by rfl⟩ : syracuseStep 3061975 = 4592963) B4592963
theorem B13785389 : Blo 1813608 13785389 := bstep (se 3 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 13785389 = 5169521) B5169521
theorem B6125975 : Blo 1813608 6125975 := bstep (se 1 (by rfl) ⟨4594481, by rfl⟩ : syracuseStep 6125975 = 9188963) B9188963
theorem B2947595 : Blo 1813608 2947595 := bstep (se 1 (by rfl) ⟨2210696, by rfl⟩ : syracuseStep 2947595 = 4421393) B4421393
theorem B6887987 : Blo 1813608 6887987 := bstep (se 1 (by rfl) ⟨5165990, by rfl⟩ : syracuseStep 6887987 = 10331981) B10331981
theorem B5306945 : Blo 1813608 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B9443915 : Blo 1813608 9443915 := bstep (se 1 (by rfl) ⟨7082936, by rfl⟩ : syracuseStep 9443915 = 14165873) B14165873
theorem B13777613 : Blo 1813608 13777613 := bstep (se 3 (by rfl) ⟨2583302, by rfl⟩ : syracuseStep 13777613 = 5166605) B5166605
theorem B9181997 : Blo 1813608 9181997 := bstep (se 3 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 9181997 = 3443249) B3443249
theorem B3873587 : Blo 1813608 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B3062603 : Blo 1813608 3062603 := bstep (se 1 (by rfl) ⟨2296952, by rfl⟩ : syracuseStep 3062603 = 4593905) B4593905
theorem B4594583 : Blo 1813608 4594583 := bstep (se 1 (by rfl) ⟨3445937, by rfl⟩ : syracuseStep 4594583 = 6891875) B6891875
theorem B6126515 : Blo 1813608 6126515 := bstep (se 1 (by rfl) ⟨4594886, by rfl⟩ : syracuseStep 6126515 = 9189773) B9189773
theorem B3062731 : Blo 1813608 3062731 := bstep (se 1 (by rfl) ⟨2297048, by rfl⟩ : syracuseStep 3062731 = 4594097) B4594097
theorem B14711813 : Blo 1813608 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B9804845 : Blo 1813608 9804845 := bstep (se 3 (by rfl) ⟨1838408, by rfl⟩ : syracuseStep 9804845 = 3676817) B3676817
theorem B7076929 : Blo 1813608 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B3062873 : Blo 1813608 3062873 := bstep (se 2 (by rfl) ⟨1148577, by rfl⟩ : syracuseStep 3062873 = 2297155) B2297155
theorem B10337381 : Blo 1813608 10337381 := bstep (se 4 (by rfl) ⟨969129, by rfl⟩ : syracuseStep 10337381 = 1938259) B1938259
theorem B13778099 : Blo 1813608 13778099 := bstep (se 1 (by rfl) ⟨10333574, by rfl⟩ : syracuseStep 13778099 = 20667149) B20667149
theorem B6126785 : Blo 1813608 6126785 := bstep (se 2 (by rfl) ⟨2297544, by rfl⟩ : syracuseStep 6126785 = 4595089) B4595089
theorem B1965259 : Blo 1813608 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B17431757 : Blo 1813608 17431757 := bstep (se 3 (by rfl) ⟨3268454, by rfl⟩ : syracuseStep 17431757 = 6536909) B6536909
theorem B3677401 : Blo 1813608 3677401 := bstep (se 2 (by rfl) ⟨1379025, by rfl⟩ : syracuseStep 3677401 = 2758051) B2758051
theorem B3063001 : Blo 1813608 3063001 := bstep (se 2 (by rfl) ⟨1148625, by rfl⟩ : syracuseStep 3063001 = 2297251) B2297251
theorem B11631833 : Blo 1813608 11631833 := bstep (se 2 (by rfl) ⟨4361937, by rfl⟩ : syracuseStep 11631833 = 8723875) B8723875
theorem B13073795 : Blo 1813608 13073795 := bstep (se 1 (by rfl) ⟨9805346, by rfl⟩ : syracuseStep 13073795 = 19610693) B19610693
theorem B3538379 : Blo 1813608 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B17440217 : Blo 1813608 17440217 := bstep (se 2 (by rfl) ⟨6540081, by rfl⟩ : syracuseStep 17440217 = 13080163) B13080163
theorem B6626861 : Blo 1813608 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B4595251 : Blo 1813608 4595251 := bstep (se 1 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 4595251 = 6892877) B6892877
theorem B7749209 : Blo 1813608 7749209 := bstep (se 2 (by rfl) ⟨2905953, by rfl⟩ : syracuseStep 7749209 = 5811907) B5811907
theorem B7356035 : Blo 1813608 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B4595393 : Blo 1813608 4595393 := bstep (se 2 (by rfl) ⟨1723272, by rfl⟩ : syracuseStep 4595393 = 3446545) B3446545
theorem B6127325 : Blo 1813608 6127325 := bstep (se 3 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 6127325 = 2297747) B2297747
theorem B3063575 : Blo 1813608 3063575 := bstep (se 1 (by rfl) ⟨2297681, by rfl⟩ : syracuseStep 3063575 = 4595363) B4595363
theorem B3063703 : Blo 1813608 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B5169089 : Blo 1813608 5169089 := bstep (se 2 (by rfl) ⟨1938408, by rfl⟩ : syracuseStep 5169089 = 3876817) B3876817
theorem B9183293 : Blo 1813608 9183293 := bstep (se 3 (by rfl) ⟨1721867, by rfl⟩ : syracuseStep 9183293 = 3443735) B3443735
theorem B5169271 : Blo 1813608 5169271 := bstep (se 1 (by rfl) ⟨3876953, by rfl⟩ : syracuseStep 5169271 = 7753907) B7753907
theorem B41885869 : Blo 1813608 41885869 := bstep (se 3 (by rfl) ⟨7853600, by rfl⟩ : syracuseStep 41885869 = 15707201) B15707201
theorem B44761565 : Blo 1813608 44761565 := bstep (se 3 (by rfl) ⟨8392793, by rfl⟩ : syracuseStep 44761565 = 16785587) B16785587
theorem B10338839 : Blo 1813608 10338839 := bstep (se 1 (by rfl) ⟨7754129, by rfl⟩ : syracuseStep 10338839 = 15508259) B15508259
theorem B10478123 : Blo 1813608 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B2720441 : Blo 1813608 2720441 := bstep (se 2 (by rfl) ⟨1020165, by rfl⟩ : syracuseStep 2720441 = 2040331) B2040331
theorem B2720519 : Blo 1813608 2720519 := bstep (se 1 (by rfl) ⟨2040389, by rfl⟩ : syracuseStep 2720519 = 4080779) B4080779
theorem B2040583 : Blo 1813608 2040583 := bstep (se 1 (by rfl) ⟨1530437, by rfl⟩ : syracuseStep 2040583 = 3060875) B3060875
theorem B2720555 : Blo 1813608 2720555 := bstep (se 1 (by rfl) ⟨2040416, by rfl⟩ : syracuseStep 2720555 = 4080833) B4080833
theorem B4653883 : Blo 1813608 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2720585 : Blo 1813608 2720585 := bstep (se 2 (by rfl) ⟨1020219, by rfl⟩ : syracuseStep 2720585 = 2040439) B2040439
theorem B2720699 : Blo 1813608 2720699 := bstep (se 1 (by rfl) ⟨2040524, by rfl⟩ : syracuseStep 2720699 = 4081049) B4081049
theorem B2040763 : Blo 1813608 2040763 := bstep (se 1 (by rfl) ⟨1530572, by rfl⟩ : syracuseStep 2040763 = 3061145) B3061145
theorem B4359113 : Blo 1813608 4359113 := bstep (se 2 (by rfl) ⟨1634667, by rfl⟩ : syracuseStep 4359113 = 3269335) B3269335
theorem B2720759 : Blo 1813608 2720759 := bstep (se 1 (by rfl) ⟨2040569, by rfl⟩ : syracuseStep 2720759 = 4081139) B4081139
theorem B9815051 : Blo 1813608 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B2720783 : Blo 1813608 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B16548887 : Blo 1813608 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B8717341 : Blo 1813608 8717341 := bstep (se 3 (by rfl) ⟨1634501, by rfl⟩ : syracuseStep 8717341 = 3269003) B3269003
theorem B5170205 : Blo 1813608 5170205 := bstep (se 3 (by rfl) ⟨969413, by rfl⟩ : syracuseStep 5170205 = 1938827) B1938827
theorem B2720825 : Blo 1813608 2720825 := bstep (se 2 (by rfl) ⟨1020309, by rfl⟩ : syracuseStep 2720825 = 2040619) B2040619
theorem B6890615 : Blo 1813608 6890615 := bstep (se 1 (by rfl) ⟨5167961, by rfl⟩ : syracuseStep 6890615 = 10335923) B10335923
theorem B2720903 : Blo 1813608 2720903 := bstep (se 1 (by rfl) ⟨2040677, by rfl⟩ : syracuseStep 2720903 = 4081355) B4081355
theorem B2720939 : Blo 1813608 2720939 := bstep (se 1 (by rfl) ⟨2040704, by rfl⟩ : syracuseStep 2720939 = 4081409) B4081409
theorem B2720969 : Blo 1813608 2720969 := bstep (se 2 (by rfl) ⟨1020363, by rfl⟩ : syracuseStep 2720969 = 2040727) B2040727
theorem B2721083 : Blo 1813608 2721083 := bstep (se 1 (by rfl) ⟨2040812, by rfl⟩ : syracuseStep 2721083 = 4081625) B4081625
theorem B2721143 : Blo 1813608 2721143 := bstep (se 1 (by rfl) ⟨2040857, by rfl⟩ : syracuseStep 2721143 = 4081715) B4081715
theorem B3679607 : Blo 1813608 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B4081031 : Blo 1813608 4081031 := bstep (se 1 (by rfl) ⟨3060773, by rfl⟩ : syracuseStep 4081031 = 6121547) B6121547
theorem B2721167 : Blo 1813608 2721167 := bstep (se 1 (by rfl) ⟨2040875, by rfl⟩ : syracuseStep 2721167 = 4081751) B4081751
theorem B2041231 : Blo 1813608 2041231 := bstep (se 1 (by rfl) ⟨1530923, by rfl⟩ : syracuseStep 2041231 = 3061847) B3061847
theorem B2721209 : Blo 1813608 2721209 := bstep (se 2 (by rfl) ⟨1020453, by rfl⟩ : syracuseStep 2721209 = 2040907) B2040907
theorem B2721287 : Blo 1813608 2721287 := bstep (se 1 (by rfl) ⟨2040965, by rfl⟩ : syracuseStep 2721287 = 4081931) B4081931
theorem B2721323 : Blo 1813608 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B4081211 : Blo 1813608 4081211 := bstep (se 1 (by rfl) ⟨3060908, by rfl⟩ : syracuseStep 4081211 = 6121817) B6121817
theorem B2721353 : Blo 1813608 2721353 := bstep (se 2 (by rfl) ⟨1020507, by rfl⟩ : syracuseStep 2721353 = 2041015) B2041015
theorem B156952241 : Blo 1813608 156952241 := bstep (se 2 (by rfl) ⟨58857090, by rfl⟩ : syracuseStep 156952241 = 117714181) B117714181
theorem B4081337 : Blo 1813608 4081337 := bstep (se 2 (by rfl) ⟨1530501, by rfl⟩ : syracuseStep 4081337 = 3061003) B3061003
theorem B2721467 : Blo 1813608 2721467 := bstep (se 1 (by rfl) ⟨2041100, by rfl⟩ : syracuseStep 2721467 = 4082201) B4082201
theorem B2721527 : Blo 1813608 2721527 := bstep (se 1 (by rfl) ⟨2041145, by rfl⟩ : syracuseStep 2721527 = 4082291) B4082291
theorem B2721551 : Blo 1813608 2721551 := bstep (se 1 (by rfl) ⟨2041163, by rfl⟩ : syracuseStep 2721551 = 4082327) B4082327
theorem B9185075 : Blo 1813608 9185075 := bstep (se 1 (by rfl) ⟨6888806, by rfl⟩ : syracuseStep 9185075 = 13777613) B13777613
theorem B39241523 : Blo 1813608 39241523 := bstep (se 1 (by rfl) ⟨29431142, by rfl⟩ : syracuseStep 39241523 = 58862285) B58862285
theorem B2721593 : Blo 1813608 2721593 := bstep (se 2 (by rfl) ⟨1020597, by rfl⟩ : syracuseStep 2721593 = 2041195) B2041195
theorem B6121331 : Blo 1813608 6121331 := bstep (se 1 (by rfl) ⟨4590998, by rfl⟩ : syracuseStep 6121331 = 9181997) B9181997
theorem B2721671 : Blo 1813608 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B2041735 : Blo 1813608 2041735 := bstep (se 1 (by rfl) ⟨1531301, by rfl⟩ : syracuseStep 2041735 = 3062603) B3062603
theorem B2721707 : Blo 1813608 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B4655033 : Blo 1813608 4655033 := bstep (se 2 (by rfl) ⟨1745637, by rfl⟩ : syracuseStep 4655033 = 3491275) B3491275
theorem B2721737 : Blo 1813608 2721737 := bstep (se 2 (by rfl) ⟨1020651, by rfl⟩ : syracuseStep 2721737 = 2041303) B2041303
theorem B9807875 : Blo 1813608 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B4081679 : Blo 1813608 4081679 := bstep (se 1 (by rfl) ⟨3061259, by rfl⟩ : syracuseStep 4081679 = 6122519) B6122519
theorem B13781015 : Blo 1813608 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B4081697 : Blo 1813608 4081697 := bstep (se 2 (by rfl) ⟨1530636, by rfl⟩ : syracuseStep 4081697 = 3061273) B3061273
theorem B2721851 : Blo 1813608 2721851 := bstep (se 1 (by rfl) ⟨2041388, by rfl⟩ : syracuseStep 2721851 = 4082777) B4082777
theorem B2041915 : Blo 1813608 2041915 := bstep (se 1 (by rfl) ⟨1531436, by rfl⟩ : syracuseStep 2041915 = 3062873) B3062873
theorem B6891587 : Blo 1813608 6891587 := bstep (se 1 (by rfl) ⟨5168690, by rfl⟩ : syracuseStep 6891587 = 10337381) B10337381
theorem B9185399 : Blo 1813608 9185399 := bstep (se 1 (by rfl) ⟨6889049, by rfl⟩ : syracuseStep 9185399 = 13778099) B13778099
theorem B2721911 : Blo 1813608 2721911 := bstep (se 1 (by rfl) ⟨2041433, by rfl⟩ : syracuseStep 2721911 = 4082867) B4082867
theorem B2721935 : Blo 1813608 2721935 := bstep (se 1 (by rfl) ⟨2041451, by rfl⟩ : syracuseStep 2721935 = 4082903) B4082903
theorem B2721977 : Blo 1813608 2721977 := bstep (se 2 (by rfl) ⟨1020741, by rfl⟩ : syracuseStep 2721977 = 2041483) B2041483
theorem B2722055 : Blo 1813608 2722055 := bstep (se 1 (by rfl) ⟨2041541, by rfl⟩ : syracuseStep 2722055 = 4083083) B4083083
theorem B2722091 : Blo 1813608 2722091 := bstep (se 1 (by rfl) ⟨2041568, by rfl⟩ : syracuseStep 2722091 = 4083137) B4083137
theorem B11626811 : Blo 1813608 11626811 := bstep (se 1 (by rfl) ⟨8720108, by rfl⟩ : syracuseStep 11626811 = 17440217) B17440217
theorem B2722121 : Blo 1813608 2722121 := bstep (se 2 (by rfl) ⟨1020795, by rfl⟩ : syracuseStep 2722121 = 2041591) B2041591
theorem B4417907 : Blo 1813608 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B4082039 : Blo 1813608 4082039 := bstep (se 1 (by rfl) ⟨3061529, by rfl⟩ : syracuseStep 4082039 = 6123059) B6123059
theorem B2296183 : Blo 1813608 2296183 := bstep (se 1 (by rfl) ⟨1722137, by rfl⟩ : syracuseStep 2296183 = 3444275) B3444275
theorem B2722235 : Blo 1813608 2722235 := bstep (se 1 (by rfl) ⟨2041676, by rfl⟩ : syracuseStep 2722235 = 4083353) B4083353
theorem B176556509 : Blo 1813608 176556509 := bstep (se 3 (by rfl) ⟨33104345, by rfl⟩ : syracuseStep 176556509 = 66208691) B66208691
theorem B2722295 : Blo 1813608 2722295 := bstep (se 1 (by rfl) ⟨2041721, by rfl⟩ : syracuseStep 2722295 = 4083443) B4083443
theorem B2722319 : Blo 1813608 2722319 := bstep (se 1 (by rfl) ⟨2041739, by rfl⟩ : syracuseStep 2722319 = 4083479) B4083479
theorem B2042383 : Blo 1813608 2042383 := bstep (se 1 (by rfl) ⟨1531787, by rfl⟩ : syracuseStep 2042383 = 3063575) B3063575
theorem B4082219 : Blo 1813608 4082219 := bstep (se 1 (by rfl) ⟨3061664, by rfl⟩ : syracuseStep 4082219 = 6123329) B6123329
theorem B2722361 : Blo 1813608 2722361 := bstep (se 2 (by rfl) ⟨1020885, by rfl⟩ : syracuseStep 2722361 = 2041771) B2041771
theorem B2722439 : Blo 1813608 2722439 := bstep (se 1 (by rfl) ⟨2041829, by rfl⟩ : syracuseStep 2722439 = 4083659) B4083659
theorem B2722475 : Blo 1813608 2722475 := bstep (se 1 (by rfl) ⟨2041856, by rfl⟩ : syracuseStep 2722475 = 4083713) B4083713
theorem B2296507 : Blo 1813608 2296507 := bstep (se 1 (by rfl) ⟨1722380, by rfl⟩ : syracuseStep 2296507 = 3444761) B3444761
theorem B3443401 : Blo 1813608 3443401 := bstep (se 2 (by rfl) ⟨1291275, by rfl⟩ : syracuseStep 3443401 = 2582551) B2582551
theorem B2722505 : Blo 1813608 2722505 := bstep (se 2 (by rfl) ⟨1020939, by rfl⟩ : syracuseStep 2722505 = 2041879) B2041879
theorem B5180105 : Blo 1813608 5180105 := bstep (se 2 (by rfl) ⟨1942539, by rfl⟩ : syracuseStep 5180105 = 3885079) B3885079
theorem B26520281 : Blo 1813608 26520281 := bstep (se 2 (by rfl) ⟨9945105, by rfl⟩ : syracuseStep 26520281 = 19890211) B19890211
theorem B20957987 : Blo 1813608 20957987 := bstep (se 1 (by rfl) ⟨15718490, by rfl⟩ : syracuseStep 20957987 = 31436981) B31436981
theorem B2722619 : Blo 1813608 2722619 := bstep (se 1 (by rfl) ⟨2041964, by rfl⟩ : syracuseStep 2722619 = 4083929) B4083929
theorem B2722679 : Blo 1813608 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B2722703 : Blo 1813608 2722703 := bstep (se 1 (by rfl) ⟨2042027, by rfl⟩ : syracuseStep 2722703 = 4084055) B4084055
theorem B4082579 : Blo 1813608 4082579 := bstep (se 1 (by rfl) ⟨3061934, by rfl⟩ : syracuseStep 4082579 = 6123869) B6123869
theorem B2722745 : Blo 1813608 2722745 := bstep (se 2 (by rfl) ⟨1021029, by rfl⟩ : syracuseStep 2722745 = 2042059) B2042059
theorem B4082633 : Blo 1813608 4082633 := bstep (se 2 (by rfl) ⟨1530987, by rfl⟩ : syracuseStep 4082633 = 3061975) B3061975
theorem B2722823 : Blo 1813608 2722823 := bstep (se 1 (by rfl) ⟨2042117, by rfl⟩ : syracuseStep 2722823 = 4084235) B4084235
theorem B11037707 : Blo 1813608 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B6892573 : Blo 1813608 6892573 := bstep (se 3 (by rfl) ⟨1292357, by rfl⟩ : syracuseStep 6892573 = 2584715) B2584715
theorem B2722859 : Blo 1813608 2722859 := bstep (se 1 (by rfl) ⟨2042144, by rfl⟩ : syracuseStep 2722859 = 4084289) B4084289
theorem B9186371 : Blo 1813608 9186371 := bstep (se 1 (by rfl) ⟨6889778, by rfl⟩ : syracuseStep 9186371 = 13779557) B13779557
theorem B2722889 : Blo 1813608 2722889 := bstep (se 2 (by rfl) ⟨1021083, by rfl⟩ : syracuseStep 2722889 = 2042167) B2042167
theorem B1813639 : Blo 1813608 1813639 := bstep (se 1 (by rfl) ⟨1360229, by rfl⟩ : syracuseStep 1813639 = 2720459) B2720459
theorem B1813647 : Blo 1813608 1813647 := bstep (se 1 (by rfl) ⟨1360235, by rfl⟩ : syracuseStep 1813647 = 2720471) B2720471
theorem B1813691 : Blo 1813608 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B2723003 : Blo 1813608 2723003 := bstep (se 1 (by rfl) ⟨2042252, by rfl⟩ : syracuseStep 2723003 = 4084505) B4084505
theorem B88247501 : Blo 1813608 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2723063 : Blo 1813608 2723063 := bstep (se 1 (by rfl) ⟨2042297, by rfl⟩ : syracuseStep 2723063 = 4084595) B4084595
theorem B1813767 : Blo 1813608 1813767 := bstep (se 1 (by rfl) ⟨1360325, by rfl⟩ : syracuseStep 1813767 = 2720651) B2720651
theorem B1813775 : Blo 1813608 1813775 := bstep (se 1 (by rfl) ⟨1360331, by rfl⟩ : syracuseStep 1813775 = 2720663) B2720663
theorem B2723087 : Blo 1813608 2723087 := bstep (se 1 (by rfl) ⟨2042315, by rfl⟩ : syracuseStep 2723087 = 4084631) B4084631
theorem B2723129 : Blo 1813608 2723129 := bstep (se 2 (by rfl) ⟨1021173, by rfl⟩ : syracuseStep 2723129 = 2042347) B2042347
theorem B1813819 : Blo 1813608 1813819 := bstep (se 1 (by rfl) ⟨1360364, by rfl⟩ : syracuseStep 1813819 = 2720729) B2720729
theorem B1813895 : Blo 1813608 1813895 := bstep (se 1 (by rfl) ⟨1360421, by rfl⟩ : syracuseStep 1813895 = 2720843) B2720843
theorem B9186695 : Blo 1813608 9186695 := bstep (se 1 (by rfl) ⟨6890021, by rfl⟩ : syracuseStep 9186695 = 13780043) B13780043
theorem B2723207 : Blo 1813608 2723207 := bstep (se 1 (by rfl) ⟨2042405, by rfl⟩ : syracuseStep 2723207 = 4084811) B4084811
theorem B1813903 : Blo 1813608 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B3444115 : Blo 1813608 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B2723243 : Blo 1813608 2723243 := bstep (se 1 (by rfl) ⟨2042432, by rfl⟩ : syracuseStep 2723243 = 4084865) B4084865
theorem B1813947 : Blo 1813608 1813947 := bstep (se 1 (by rfl) ⟨1360460, by rfl⟩ : syracuseStep 1813947 = 2720921) B2720921
theorem B2584009 : Blo 1813608 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B8957387 : Blo 1813608 8957387 := bstep (se 1 (by rfl) ⟨6718040, by rfl⟩ : syracuseStep 8957387 = 13436081) B13436081
theorem B2723273 : Blo 1813608 2723273 := bstep (se 2 (by rfl) ⟨1021227, by rfl⟩ : syracuseStep 2723273 = 2042455) B2042455
theorem B1814023 : Blo 1813608 1814023 := bstep (se 1 (by rfl) ⟨1360517, by rfl⟩ : syracuseStep 1814023 = 2721035) B2721035
theorem B5164555 : Blo 1813608 5164555 := bstep (se 1 (by rfl) ⟨3873416, by rfl⟩ : syracuseStep 5164555 = 7746833) B7746833
theorem B1814031 : Blo 1813608 1814031 := bstep (se 1 (by rfl) ⟨1360523, by rfl⟩ : syracuseStep 1814031 = 2721047) B2721047
theorem B1814075 : Blo 1813608 1814075 := bstep (se 1 (by rfl) ⟨1360556, by rfl⟩ : syracuseStep 1814075 = 2721113) B2721113
theorem B2723387 : Blo 1813608 2723387 := bstep (se 1 (by rfl) ⟨2042540, by rfl⟩ : syracuseStep 2723387 = 4085081) B4085081
theorem B10333757 : Blo 1813608 10333757 := bstep (se 3 (by rfl) ⟨1937579, by rfl⟩ : syracuseStep 10333757 = 3875159) B3875159
theorem B1814151 : Blo 1813608 1814151 := bstep (se 1 (by rfl) ⟨1360613, by rfl⟩ : syracuseStep 1814151 = 2721227) B2721227
theorem B4083335 : Blo 1813608 4083335 := bstep (se 1 (by rfl) ⟨3062501, by rfl⟩ : syracuseStep 4083335 = 6125003) B6125003
theorem B2297479 : Blo 1813608 2297479 := bstep (se 1 (by rfl) ⟨1723109, by rfl⟩ : syracuseStep 2297479 = 3446219) B3446219
theorem B1814159 : Blo 1813608 1814159 := bstep (se 1 (by rfl) ⟨1360619, by rfl⟩ : syracuseStep 1814159 = 2721239) B2721239
theorem B1814203 : Blo 1813608 1814203 := bstep (se 1 (by rfl) ⟨1360652, by rfl⟩ : syracuseStep 1814203 = 2721305) B2721305
theorem B1814279 : Blo 1813608 1814279 := bstep (se 1 (by rfl) ⟨1360709, by rfl⟩ : syracuseStep 1814279 = 2721419) B2721419
theorem B1814287 : Blo 1813608 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B5164829 : Blo 1813608 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B1814331 : Blo 1813608 1814331 := bstep (se 1 (by rfl) ⟨1360748, by rfl⟩ : syracuseStep 1814331 = 2721497) B2721497
theorem B4083515 : Blo 1813608 4083515 := bstep (se 1 (by rfl) ⟨3062636, by rfl⟩ : syracuseStep 4083515 = 6125273) B6125273
theorem B4591475 : Blo 1813608 4591475 := bstep (se 1 (by rfl) ⟨3443606, by rfl⟩ : syracuseStep 4591475 = 6887213) B6887213
theorem B1814407 : Blo 1813608 1814407 := bstep (se 1 (by rfl) ⟨1360805, by rfl⟩ : syracuseStep 1814407 = 2721611) B2721611
theorem B1814415 : Blo 1813608 1814415 := bstep (se 1 (by rfl) ⟨1360811, by rfl⟩ : syracuseStep 1814415 = 2721623) B2721623
theorem B4083641 : Blo 1813608 4083641 := bstep (se 2 (by rfl) ⟨1531365, by rfl⟩ : syracuseStep 4083641 = 3062731) B3062731
theorem B4362169 : Blo 1813608 4362169 := bstep (se 2 (by rfl) ⟨1635813, by rfl⟩ : syracuseStep 4362169 = 3271627) B3271627
theorem B1814459 : Blo 1813608 1814459 := bstep (se 1 (by rfl) ⟨1360844, by rfl⟩ : syracuseStep 1814459 = 2721689) B2721689
theorem B9310211 : Blo 1813608 9310211 := bstep (se 1 (by rfl) ⟨6982658, by rfl⟩ : syracuseStep 9310211 = 13965317) B13965317
theorem B1814535 : Blo 1813608 1814535 := bstep (se 1 (by rfl) ⟨1360901, by rfl⟩ : syracuseStep 1814535 = 2721803) B2721803
theorem B1839119 : Blo 1813608 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B1814543 : Blo 1813608 1814543 := bstep (se 1 (by rfl) ⟨1360907, by rfl⟩ : syracuseStep 1814543 = 2721815) B2721815
theorem B7860253 : Blo 1813608 7860253 := bstep (se 3 (by rfl) ⟨1473797, by rfl⟩ : syracuseStep 7860253 = 2947595) B2947595
theorem B1814587 : Blo 1813608 1814587 := bstep (se 1 (by rfl) ⟨1360940, by rfl⟩ : syracuseStep 1814587 = 2721881) B2721881
theorem B5165171 : Blo 1813608 5165171 := bstep (se 1 (by rfl) ⟨3873878, by rfl⟩ : syracuseStep 5165171 = 7747757) B7747757
theorem B1814663 : Blo 1813608 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B1814671 : Blo 1813608 1814671 := bstep (se 1 (by rfl) ⟨1361003, by rfl⟩ : syracuseStep 1814671 = 2722007) B2722007
theorem B14151853 : Blo 1813608 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B9941165 : Blo 1813608 9941165 := bstep (se 3 (by rfl) ⟨1863968, by rfl⟩ : syracuseStep 9941165 = 3727937) B3727937
theorem B1814715 : Blo 1813608 1814715 := bstep (se 1 (by rfl) ⟨1361036, by rfl⟩ : syracuseStep 1814715 = 2722073) B2722073
theorem B89493749 : Blo 1813608 89493749 := bstep (se 5 (by rfl) ⟨4195019, by rfl⟩ : syracuseStep 89493749 = 8390039) B8390039
theorem B10334465 : Blo 1813608 10334465 := bstep (se 2 (by rfl) ⟨3875424, by rfl⟩ : syracuseStep 10334465 = 7750849) B7750849
theorem B1814791 : Blo 1813608 1814791 := bstep (se 1 (by rfl) ⟨1361093, by rfl⟩ : syracuseStep 1814791 = 2722187) B2722187
theorem B1814799 : Blo 1813608 1814799 := bstep (se 1 (by rfl) ⟨1361099, by rfl⟩ : syracuseStep 1814799 = 2722199) B2722199
theorem B4083983 : Blo 1813608 4083983 := bstep (se 1 (by rfl) ⟨3062987, by rfl⟩ : syracuseStep 4083983 = 6125975) B6125975
theorem B4903201 : Blo 1813608 4903201 := bstep (se 2 (by rfl) ⟨1838700, by rfl⟩ : syracuseStep 4903201 = 3677401) B3677401
theorem B4084001 : Blo 1813608 4084001 := bstep (se 2 (by rfl) ⟨1531500, by rfl⟩ : syracuseStep 4084001 = 3063001) B3063001
theorem B4419883 : Blo 1813608 4419883 := bstep (se 1 (by rfl) ⟨3314912, by rfl⟩ : syracuseStep 4419883 = 6629825) B6629825
theorem B1814843 : Blo 1813608 1814843 := bstep (se 1 (by rfl) ⟨1361132, by rfl⟩ : syracuseStep 1814843 = 2722265) B2722265
theorem B19616093 : Blo 1813608 19616093 := bstep (se 3 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 19616093 = 7356035) B7356035
theorem B4591991 : Blo 1813608 4591991 := bstep (se 1 (by rfl) ⟨3443993, by rfl⟩ : syracuseStep 4591991 = 6887987) B6887987
theorem B3928439 : Blo 1813608 3928439 := bstep (se 1 (by rfl) ⟨2946329, by rfl⟩ : syracuseStep 3928439 = 5892659) B5892659
theorem B1814919 : Blo 1813608 1814919 := bstep (se 1 (by rfl) ⟨1361189, by rfl⟩ : syracuseStep 1814919 = 2722379) B2722379
theorem B6295943 : Blo 1813608 6295943 := bstep (se 1 (by rfl) ⟨4721957, by rfl⟩ : syracuseStep 6295943 = 9443915) B9443915
theorem B1814927 : Blo 1813608 1814927 := bstep (se 1 (by rfl) ⟨1361195, by rfl⟩ : syracuseStep 1814927 = 2722391) B2722391
theorem B6123923 : Blo 1813608 6123923 := bstep (se 1 (by rfl) ⟨4592942, by rfl⟩ : syracuseStep 6123923 = 9185885) B9185885
theorem B1814971 : Blo 1813608 1814971 := bstep (se 1 (by rfl) ⟨1361228, by rfl⟩ : syracuseStep 1814971 = 2722457) B2722457
theorem B3445193 : Blo 1813608 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B1815047 : Blo 1813608 1815047 := bstep (se 1 (by rfl) ⟨1361285, by rfl⟩ : syracuseStep 1815047 = 2722571) B2722571
theorem B1815055 : Blo 1813608 1815055 := bstep (se 1 (by rfl) ⟨1361291, by rfl⟩ : syracuseStep 1815055 = 2722583) B2722583
theorem B1815099 : Blo 1813608 1815099 := bstep (se 1 (by rfl) ⟨1361324, by rfl⟩ : syracuseStep 1815099 = 2722649) B2722649
theorem B4084343 : Blo 1813608 4084343 := bstep (se 1 (by rfl) ⟨3063257, by rfl⟩ : syracuseStep 4084343 = 6126515) B6126515
theorem B1815175 : Blo 1813608 1815175 := bstep (se 1 (by rfl) ⟨1361381, by rfl⟩ : syracuseStep 1815175 = 2722763) B2722763
theorem B1815183 : Blo 1813608 1815183 := bstep (se 1 (by rfl) ⟨1361387, by rfl⟩ : syracuseStep 1815183 = 2722775) B2722775
theorem B1815227 : Blo 1813608 1815227 := bstep (se 1 (by rfl) ⟨1361420, by rfl⟩ : syracuseStep 1815227 = 2722841) B2722841
theorem B7754555 : Blo 1813608 7754555 := bstep (se 1 (by rfl) ⟨5815916, by rfl⟩ : syracuseStep 7754555 = 11631833) B11631833
theorem B1815303 : Blo 1813608 1815303 := bstep (se 1 (by rfl) ⟨1361477, by rfl⟩ : syracuseStep 1815303 = 2722955) B2722955
theorem B1815311 : Blo 1813608 1815311 := bstep (se 1 (by rfl) ⟨1361483, by rfl⟩ : syracuseStep 1815311 = 2722967) B2722967
theorem B13259557 : Blo 1813608 13259557 := bstep (se 4 (by rfl) ⟨1243083, by rfl⟩ : syracuseStep 13259557 = 2486167) B2486167
theorem B4084523 : Blo 1813608 4084523 := bstep (se 1 (by rfl) ⟨3063392, by rfl⟩ : syracuseStep 4084523 = 6126785) B6126785
theorem B9433907 : Blo 1813608 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B11621171 : Blo 1813608 11621171 := bstep (se 1 (by rfl) ⟨8715878, by rfl⟩ : syracuseStep 11621171 = 17431757) B17431757
theorem B1815355 : Blo 1813608 1815355 := bstep (se 1 (by rfl) ⟨1361516, by rfl⟩ : syracuseStep 1815355 = 2723033) B2723033
theorem B1815431 : Blo 1813608 1815431 := bstep (se 1 (by rfl) ⟨1361573, by rfl⟩ : syracuseStep 1815431 = 2723147) B2723147
theorem B1815439 : Blo 1813608 1815439 := bstep (se 1 (by rfl) ⟨1361579, by rfl⟩ : syracuseStep 1815439 = 2723159) B2723159
theorem B1815483 : Blo 1813608 1815483 := bstep (se 1 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 1815483 = 2723225) B2723225
theorem B1815559 : Blo 1813608 1815559 := bstep (se 1 (by rfl) ⟨1361669, by rfl⟩ : syracuseStep 1815559 = 2723339) B2723339
theorem B37745675 : Blo 1813608 37745675 := bstep (se 1 (by rfl) ⟨28309256, by rfl⟩ : syracuseStep 37745675 = 56618513) B56618513
theorem B1815567 : Blo 1813608 1815567 := bstep (se 1 (by rfl) ⟨1361675, by rfl⟩ : syracuseStep 1815567 = 2723351) B2723351
theorem B5166139 : Blo 1813608 5166139 := bstep (se 1 (by rfl) ⟨3874604, by rfl⟩ : syracuseStep 5166139 = 7749209) B7749209
theorem B4084883 : Blo 1813608 4084883 := bstep (se 1 (by rfl) ⟨3063662, by rfl⟩ : syracuseStep 4084883 = 6127325) B6127325
theorem B5518489 : Blo 1813608 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B2946233 : Blo 1813608 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B4084937 : Blo 1813608 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B3446059 : Blo 1813608 3446059 := bstep (se 1 (by rfl) ⟨2584544, by rfl⟩ : syracuseStep 3446059 = 5169089) B5169089
theorem B4592983 : Blo 1813608 4592983 := bstep (se 1 (by rfl) ⟨3444737, by rfl⟩ : syracuseStep 4592983 = 6889475) B6889475
theorem B39777635 : Blo 1813608 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B6542707 : Blo 1813608 6542707 := bstep (se 1 (by rfl) ⟨4907030, by rfl⟩ : syracuseStep 6542707 = 9814061) B9814061
theorem B3061111 : Blo 1813608 3061111 := bstep (se 1 (by rfl) ⟨2295833, by rfl⟩ : syracuseStep 3061111 = 4591667) B4591667
theorem B3446135 : Blo 1813608 3446135 := bstep (se 1 (by rfl) ⟨2584601, by rfl⟩ : syracuseStep 3446135 = 5169203) B5169203
theorem B13252025 : Blo 1813608 13252025 := bstep (se 2 (by rfl) ⟨4969509, by rfl⟩ : syracuseStep 13252025 = 9939019) B9939019
theorem B26146253 : Blo 1813608 26146253 := bstep (se 3 (by rfl) ⟨4902422, by rfl⟩ : syracuseStep 26146253 = 9804845) B9804845
theorem B3061307 : Blo 1813608 3061307 := bstep (se 1 (by rfl) ⟨2295980, by rfl⟩ : syracuseStep 3061307 = 4591961) B4591961
theorem B17446519 : Blo 1813608 17446519 := bstep (se 1 (by rfl) ⟨13084889, by rfl⟩ : syracuseStep 17446519 = 26169779) B26169779
theorem B4593287 : Blo 1813608 4593287 := bstep (se 1 (by rfl) ⟨3444965, by rfl⟩ : syracuseStep 4593287 = 6889931) B6889931
theorem B13776641 : Blo 1813608 13776641 := bstep (se 2 (by rfl) ⟨5166240, by rfl⟩ : syracuseStep 13776641 = 10332481) B10332481
theorem B4593419 : Blo 1813608 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B6125327 : Blo 1813608 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B5519119 : Blo 1813608 5519119 := bstep (se 1 (by rfl) ⟨4139339, by rfl⟩ : syracuseStep 5519119 = 8278679) B8278679
theorem B6543137 : Blo 1813608 6543137 := bstep (se 2 (by rfl) ⟨2453676, by rfl⟩ : syracuseStep 6543137 = 4907353) B4907353
theorem B6887227 : Blo 1813608 6887227 := bstep (se 1 (by rfl) ⟨5165420, by rfl⟩ : syracuseStep 6887227 = 10330841) B10330841
theorem B6207367 : Blo 1813608 6207367 := bstep (se 1 (by rfl) ⟨4655525, by rfl⟩ : syracuseStep 6207367 = 9311051) B9311051
theorem B3061705 : Blo 1813608 3061705 := bstep (se 2 (by rfl) ⟨1148139, by rfl⟩ : syracuseStep 3061705 = 2296279) B2296279
theorem B11630603 : Blo 1813608 11630603 := bstep (se 1 (by rfl) ⟨8722952, by rfl⟩ : syracuseStep 11630603 = 17445905) B17445905
theorem B6125597 : Blo 1813608 6125597 := bstep (se 3 (by rfl) ⟨1148549, by rfl⟩ : syracuseStep 6125597 = 2297099) B2297099
theorem B8722475 : Blo 1813608 8722475 := bstep (se 1 (by rfl) ⟨6541856, by rfl⟩ : syracuseStep 8722475 = 13083713) B13083713
theorem B5167289 : Blo 1813608 5167289 := bstep (se 2 (by rfl) ⟨1937733, by rfl⟩ : syracuseStep 5167289 = 3875467) B3875467
theorem B2906383 : Blo 1813608 2906383 := bstep (se 1 (by rfl) ⟨2179787, by rfl⟩ : syracuseStep 2906383 = 4359575) B4359575
theorem B4593935 : Blo 1813608 4593935 := bstep (se 1 (by rfl) ⟨3445451, by rfl⟩ : syracuseStep 4593935 = 6890903) B6890903
theorem B6887713 : Blo 1813608 6887713 := bstep (se 2 (by rfl) ⟨2582892, by rfl⟩ : syracuseStep 6887713 = 5165785) B5165785
theorem B1005132077 : Blo 1813608 1005132077 := bstep (se 3 (by rfl) ⟨188462264, by rfl⟩ : syracuseStep 1005132077 = 376924529) B376924529
theorem B19626299 : Blo 1813608 19626299 := bstep (se 1 (by rfl) ⟨14719724, by rfl⟩ : syracuseStep 19626299 = 29439449) B29439449
theorem B4594067 : Blo 1813608 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B5167631 : Blo 1813608 5167631 := bstep (se 1 (by rfl) ⟨3875723, by rfl⟩ : syracuseStep 5167631 = 7751447) B7751447
theorem B10336855 : Blo 1813608 10336855 := bstep (se 1 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 10336855 = 15505283) B15505283
theorem B3062407 : Blo 1813608 3062407 := bstep (se 1 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 3062407 = 4593611) B4593611
theorem B9435905 : Blo 1813608 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B9190259 : Blo 1813608 9190259 := bstep (se 1 (by rfl) ⟨6892694, by rfl⟩ : syracuseStep 9190259 = 13785389) B13785389
theorem B2620345 : Blo 1813608 2620345 := bstep (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) B1965259
theorem B4906099 : Blo 1813608 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B6888685 : Blo 1813608 6888685 := bstep (se 3 (by rfl) ⟨1291628, by rfl⟩ : syracuseStep 6888685 = 2583257) B2583257
theorem B3063055 : Blo 1813608 3063055 := bstep (se 1 (by rfl) ⟨2297291, by rfl⟩ : syracuseStep 3063055 = 4594583) B4594583
theorem B4906273 : Blo 1813608 4906273 := bstep (se 2 (by rfl) ⟨1839852, by rfl⟩ : syracuseStep 4906273 = 3679705) B3679705
theorem B9190745 : Blo 1813608 9190745 := bstep (se 2 (by rfl) ⟨3446529, by rfl⟩ : syracuseStep 9190745 = 6893059) B6893059
theorem B5168519 : Blo 1813608 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B6127001 : Blo 1813608 6127001 := bstep (se 2 (by rfl) ⟨2297625, by rfl⟩ : syracuseStep 6127001 = 4595251) B4595251
theorem B10329565 : Blo 1813608 10329565 := bstep (se 3 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 10329565 = 3873587) B3873587
theorem B4595201 : Blo 1813608 4595201 := bstep (se 2 (by rfl) ⟨1723200, by rfl⟩ : syracuseStep 4595201 = 3446401) B3446401
theorem B6888989 : Blo 1813608 6888989 := bstep (se 3 (by rfl) ⟨1291685, by rfl⟩ : syracuseStep 6888989 = 2583371) B2583371
theorem B5168701 : Blo 1813608 5168701 := bstep (se 3 (by rfl) ⟨969131, by rfl⟩ : syracuseStep 5168701 = 1938263) B1938263
theorem B8715863 : Blo 1813608 8715863 := bstep (se 1 (by rfl) ⟨6536897, by rfl⟩ : syracuseStep 8715863 = 13073795) B13073795
theorem B9182807 : Blo 1813608 9182807 := bstep (se 1 (by rfl) ⟨6887105, by rfl⟩ : syracuseStep 9182807 = 13774211) B13774211
theorem B2358919 : Blo 1813608 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3268297 : Blo 1813608 3268297 := bstep (se 2 (by rfl) ⟨1225611, by rfl⟩ : syracuseStep 3268297 = 2451223) B2451223
theorem B5168929 : Blo 1813608 5168929 := bstep (se 2 (by rfl) ⟨1938348, by rfl⟩ : syracuseStep 5168929 = 3876697) B3876697
theorem B3063595 : Blo 1813608 3063595 := bstep (se 1 (by rfl) ⟨2297696, by rfl⟩ : syracuseStep 3063595 = 4595393) B4595393
theorem B4595575 : Blo 1813608 4595575 := bstep (se 1 (by rfl) ⟨3446681, by rfl⟩ : syracuseStep 4595575 = 6893363) B6893363
theorem B3063737 : Blo 1813608 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B26173469 : Blo 1813608 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B44130365 : Blo 1813608 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B6627443 : Blo 1813608 6627443 := bstep (se 1 (by rfl) ⟨4970582, by rfl⟩ : syracuseStep 6627443 = 9941165) B9941165
theorem B59662499 : Blo 1813608 59662499 := bstep (se 1 (by rfl) ⟨44746874, by rfl⟩ : syracuseStep 59662499 = 89493749) B89493749
theorem B6889643 : Blo 1813608 6889643 := bstep (se 1 (by rfl) ⟨5167232, by rfl⟩ : syracuseStep 6889643 = 10334465) B10334465
theorem B3875177 : Blo 1813608 3875177 := bstep (se 2 (by rfl) ⟨1453191, by rfl⟩ : syracuseStep 3875177 = 2906383) B2906383
theorem B6537601 : Blo 1813608 6537601 := bstep (se 2 (by rfl) ⟨2451600, by rfl⟩ : syracuseStep 6537601 = 4903201) B4903201
theorem B9183617 : Blo 1813608 9183617 := bstep (se 2 (by rfl) ⟨3443856, by rfl⟩ : syracuseStep 9183617 = 6887713) B6887713
theorem B7856621 : Blo 1813608 7856621 := bstep (se 3 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 7856621 = 2946233) B2946233
theorem B26165861 : Blo 1813608 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B26518423 : Blo 1813608 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B2720687 : Blo 1813608 2720687 := bstep (se 1 (by rfl) ⟨2040515, by rfl⟩ : syracuseStep 2720687 = 4081031) B4081031
theorem B11781085 : Blo 1813608 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B2720777 : Blo 1813608 2720777 := bstep (se 2 (by rfl) ⟨1020291, by rfl⟩ : syracuseStep 2720777 = 2040583) B2040583
theorem B2720807 : Blo 1813608 2720807 := bstep (se 1 (by rfl) ⟨2040605, by rfl⟩ : syracuseStep 2720807 = 4081211) B4081211
theorem B2040871 : Blo 1813608 2040871 := bstep (se 1 (by rfl) ⟨1530653, by rfl⟩ : syracuseStep 2040871 = 3061307) B3061307
theorem B2720891 : Blo 1813608 2720891 := bstep (se 1 (by rfl) ⟨2040668, by rfl⟩ : syracuseStep 2720891 = 4081337) B4081337
theorem B9184427 : Blo 1813608 9184427 := bstep (se 1 (by rfl) ⟨6888320, by rfl⟩ : syracuseStep 9184427 = 13776641) B13776641
theorem B4080887 : Blo 1813608 4080887 := bstep (se 1 (by rfl) ⟨3060665, by rfl⟩ : syracuseStep 4080887 = 6121331) B6121331
theorem B2721017 : Blo 1813608 2721017 := bstep (se 2 (by rfl) ⟨1020381, by rfl⟩ : syracuseStep 2721017 = 2040763) B2040763
theorem B6538583 : Blo 1813608 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B2721119 : Blo 1813608 2721119 := bstep (se 1 (by rfl) ⟨2040839, by rfl⟩ : syracuseStep 2721119 = 4081679) B4081679
theorem B2721131 : Blo 1813608 2721131 := bstep (se 1 (by rfl) ⟨2040848, by rfl⟩ : syracuseStep 2721131 = 4081697) B4081697
theorem B7357985 : Blo 1813608 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B7751207 : Blo 1813608 7751207 := bstep (se 1 (by rfl) ⟨5813405, by rfl⟩ : syracuseStep 7751207 = 11626811) B11626811
theorem B13084199 : Blo 1813608 13084199 := bstep (se 1 (by rfl) ⟨9813149, by rfl⟩ : syracuseStep 13084199 = 19626299) B19626299
theorem B2721359 : Blo 1813608 2721359 := bstep (se 1 (by rfl) ⟨2041019, by rfl⟩ : syracuseStep 2721359 = 4082039) B4082039
theorem B9184913 : Blo 1813608 9184913 := bstep (se 2 (by rfl) ⟨3444342, by rfl⟩ : syracuseStep 9184913 = 6888685) B6888685
theorem B117704339 : Blo 1813608 117704339 := bstep (se 1 (by rfl) ⟨88278254, by rfl⟩ : syracuseStep 117704339 = 176556509) B176556509
theorem B2721479 : Blo 1813608 2721479 := bstep (se 1 (by rfl) ⟨2041109, by rfl⟩ : syracuseStep 2721479 = 4082219) B4082219
theorem B17680187 : Blo 1813608 17680187 := bstep (se 1 (by rfl) ⟨13260140, by rfl⟩ : syracuseStep 17680187 = 26520281) B26520281
theorem B4081481 : Blo 1813608 4081481 := bstep (se 2 (by rfl) ⟨1530555, by rfl⟩ : syracuseStep 4081481 = 3061111) B3061111
theorem B2721641 : Blo 1813608 2721641 := bstep (se 2 (by rfl) ⟨1020615, by rfl⟩ : syracuseStep 2721641 = 2041231) B2041231
theorem B2721719 : Blo 1813608 2721719 := bstep (se 1 (by rfl) ⟨2041289, by rfl⟩ : syracuseStep 2721719 = 4082579) B4082579
theorem B13772753 : Blo 1813608 13772753 := bstep (se 2 (by rfl) ⟨5164782, by rfl⟩ : syracuseStep 13772753 = 10329565) B10329565
theorem B2721755 : Blo 1813608 2721755 := bstep (se 1 (by rfl) ⟨2041316, by rfl⟩ : syracuseStep 2721755 = 4082633) B4082633
theorem B7358471 : Blo 1813608 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B6891601 : Blo 1813608 6891601 := bstep (se 2 (by rfl) ⟨2584350, by rfl⟩ : syracuseStep 6891601 = 5168701) B5168701
theorem B55887965 : Blo 1813608 55887965 := bstep (se 3 (by rfl) ⟨10478993, by rfl⟩ : syracuseStep 55887965 = 20957987) B20957987
theorem B20678813 : Blo 1813608 20678813 := bstep (se 3 (by rfl) ⟨3877277, by rfl⟩ : syracuseStep 20678813 = 7754555) B7754555
theorem B7358825 : Blo 1813608 7358825 := bstep (se 2 (by rfl) ⟨2759559, by rfl⟩ : syracuseStep 7358825 = 5519119) B5519119
theorem B6891905 : Blo 1813608 6891905 := bstep (se 2 (by rfl) ⟨2584464, by rfl⟩ : syracuseStep 6891905 = 5168929) B5168929
theorem B5810575 : Blo 1813608 5810575 := bstep (se 1 (by rfl) ⟨4357931, by rfl⟩ : syracuseStep 5810575 = 8715863) B8715863
theorem B6121871 : Blo 1813608 6121871 := bstep (se 1 (by rfl) ⟨4591403, by rfl⟩ : syracuseStep 6121871 = 9182807) B9182807
theorem B2722223 : Blo 1813608 2722223 := bstep (se 1 (by rfl) ⟨2041667, by rfl⟩ : syracuseStep 2722223 = 4083335) B4083335
theorem B8276489 : Blo 1813608 8276489 := bstep (se 2 (by rfl) ⟨3103683, by rfl⟩ : syracuseStep 8276489 = 6207367) B6207367
theorem B2722313 : Blo 1813608 2722313 := bstep (se 2 (by rfl) ⟨1020867, by rfl⟩ : syracuseStep 2722313 = 2041735) B2041735
theorem B3443219 : Blo 1813608 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B2722343 : Blo 1813608 2722343 := bstep (se 1 (by rfl) ⟨2041757, by rfl⟩ : syracuseStep 2722343 = 4083515) B4083515
theorem B4082273 : Blo 1813608 4082273 := bstep (se 2 (by rfl) ⟨1530852, by rfl⟩ : syracuseStep 4082273 = 3061705) B3061705
theorem B2722427 : Blo 1813608 2722427 := bstep (se 1 (by rfl) ⟨2041820, by rfl⟩ : syracuseStep 2722427 = 4083641) B4083641
theorem B2042491 : Blo 1813608 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B10480337 : Blo 1813608 10480337 := bstep (se 2 (by rfl) ⟨3930126, by rfl⟩ : syracuseStep 10480337 = 7860253) B7860253
theorem B6122195 : Blo 1813608 6122195 := bstep (se 1 (by rfl) ⟨4591646, by rfl⟩ : syracuseStep 6122195 = 9183293) B9183293
theorem B3443447 : Blo 1813608 3443447 := bstep (se 1 (by rfl) ⟨2582585, by rfl⟩ : syracuseStep 3443447 = 5165171) B5165171
theorem B2722553 : Blo 1813608 2722553 := bstep (se 2 (by rfl) ⟨1020957, by rfl⟩ : syracuseStep 2722553 = 2041915) B2041915
theorem B6892361 : Blo 1813608 6892361 := bstep (se 2 (by rfl) ⟨2584635, by rfl⟩ : syracuseStep 6892361 = 5169271) B5169271
theorem B2722655 : Blo 1813608 2722655 := bstep (se 1 (by rfl) ⟨2041991, by rfl⟩ : syracuseStep 2722655 = 4083983) B4083983
theorem B2722667 : Blo 1813608 2722667 := bstep (se 1 (by rfl) ⟨2042000, by rfl⟩ : syracuseStep 2722667 = 4084001) B4084001
theorem B55847825 : Blo 1813608 55847825 := bstep (se 2 (by rfl) ⟨20942934, by rfl⟩ : syracuseStep 55847825 = 41885869) B41885869
theorem B13077395 : Blo 1813608 13077395 := bstep (se 1 (by rfl) ⟨9808046, by rfl⟩ : syracuseStep 13077395 = 19616093) B19616093
theorem B4197295 : Blo 1813608 4197295 := bstep (se 1 (by rfl) ⟨3147971, by rfl⟩ : syracuseStep 4197295 = 6295943) B6295943
theorem B4082615 : Blo 1813608 4082615 := bstep (se 1 (by rfl) ⟨3061961, by rfl⟩ : syracuseStep 4082615 = 6123923) B6123923
theorem B6892559 : Blo 1813608 6892559 := bstep (se 1 (by rfl) ⟨5169419, by rfl⟩ : syracuseStep 6892559 = 10338839) B10338839
theorem B5893177 : Blo 1813608 5893177 := bstep (se 2 (by rfl) ⟨2209941, by rfl⟩ : syracuseStep 5893177 = 4419883) B4419883
theorem B2722895 : Blo 1813608 2722895 := bstep (se 1 (by rfl) ⟨2042171, by rfl⟩ : syracuseStep 2722895 = 4084343) B4084343
theorem B1813627 : Blo 1813608 1813627 := bstep (se 1 (by rfl) ⟨1360220, by rfl⟩ : syracuseStep 1813627 = 2720441) B2720441
theorem B1813679 : Blo 1813608 1813679 := bstep (se 1 (by rfl) ⟨1360259, by rfl⟩ : syracuseStep 1813679 = 2720519) B2720519
theorem B1813703 : Blo 1813608 1813703 := bstep (se 1 (by rfl) ⟨1360277, by rfl⟩ : syracuseStep 1813703 = 2720555) B2720555
theorem B2723015 : Blo 1813608 2723015 := bstep (se 1 (by rfl) ⟨2042261, by rfl⟩ : syracuseStep 2723015 = 4084523) B4084523
theorem B1813723 : Blo 1813608 1813723 := bstep (se 1 (by rfl) ⟨1360292, by rfl⟩ : syracuseStep 1813723 = 2720585) B2720585
theorem B1813799 : Blo 1813608 1813799 := bstep (se 1 (by rfl) ⟨1360349, by rfl⟩ : syracuseStep 1813799 = 2720699) B2720699
theorem B1813839 : Blo 1813608 1813839 := bstep (se 1 (by rfl) ⟨1360379, by rfl⟩ : syracuseStep 1813839 = 2720759) B2720759
theorem B1813855 : Blo 1813608 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B2723177 : Blo 1813608 2723177 := bstep (se 2 (by rfl) ⟨1021191, by rfl⟩ : syracuseStep 2723177 = 2042383) B2042383
theorem B1813883 : Blo 1813608 1813883 := bstep (se 1 (by rfl) ⟨1360412, by rfl⟩ : syracuseStep 1813883 = 2720825) B2720825
theorem B1813935 : Blo 1813608 1813935 := bstep (se 1 (by rfl) ⟨1360451, by rfl⟩ : syracuseStep 1813935 = 2720903) B2720903
theorem B2723255 : Blo 1813608 2723255 := bstep (se 1 (by rfl) ⟨2042441, by rfl⟩ : syracuseStep 2723255 = 4084883) B4084883
theorem B1813959 : Blo 1813608 1813959 := bstep (se 1 (by rfl) ⟨1360469, by rfl⟩ : syracuseStep 1813959 = 2720939) B2720939
theorem B13782473 : Blo 1813608 13782473 := bstep (se 2 (by rfl) ⟨5168427, by rfl⟩ : syracuseStep 13782473 = 10336855) B10336855
theorem B1813979 : Blo 1813608 1813979 := bstep (se 1 (by rfl) ⟨1360484, by rfl⟩ : syracuseStep 1813979 = 2720969) B2720969
theorem B2723291 : Blo 1813608 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B4083209 : Blo 1813608 4083209 := bstep (se 2 (by rfl) ⟨1531203, by rfl⟩ : syracuseStep 4083209 = 3062407) B3062407
theorem B1814055 : Blo 1813608 1814055 := bstep (se 1 (by rfl) ⟨1360541, by rfl⟩ : syracuseStep 1814055 = 2721083) B2721083
theorem B75476549 : Blo 1813608 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B1814095 : Blo 1813608 1814095 := bstep (se 1 (by rfl) ⟨1360571, by rfl⟩ : syracuseStep 1814095 = 2721143) B2721143
theorem B2453071 : Blo 1813608 2453071 := bstep (se 1 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 2453071 = 3679607) B3679607
theorem B2297423 : Blo 1813608 2297423 := bstep (se 1 (by rfl) ⟨1723067, by rfl⟩ : syracuseStep 2297423 = 3446135) B3446135
theorem B1814111 : Blo 1813608 1814111 := bstep (se 1 (by rfl) ⟨1360583, by rfl⟩ : syracuseStep 1814111 = 2721167) B2721167
theorem B4591201 : Blo 1813608 4591201 := bstep (se 2 (by rfl) ⟨1721700, by rfl⟩ : syracuseStep 4591201 = 3443401) B3443401
theorem B8834683 : Blo 1813608 8834683 := bstep (se 1 (by rfl) ⟨6626012, by rfl⟩ : syracuseStep 8834683 = 13252025) B13252025
theorem B1814139 : Blo 1813608 1814139 := bstep (se 1 (by rfl) ⟨1360604, by rfl⟩ : syracuseStep 1814139 = 2721209) B2721209
theorem B1814191 : Blo 1813608 1814191 := bstep (se 1 (by rfl) ⟨1360643, by rfl⟩ : syracuseStep 1814191 = 2721287) B2721287
theorem B1814215 : Blo 1813608 1814215 := bstep (se 1 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 1814215 = 2721323) B2721323
theorem B1814235 : Blo 1813608 1814235 := bstep (se 1 (by rfl) ⟨1360676, by rfl⟩ : syracuseStep 1814235 = 2721353) B2721353
theorem B6205177 : Blo 1813608 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B1814311 : Blo 1813608 1814311 := bstep (se 1 (by rfl) ⟨1360733, by rfl⟩ : syracuseStep 1814311 = 2721467) B2721467
theorem B1814351 : Blo 1813608 1814351 := bstep (se 1 (by rfl) ⟨1360763, by rfl⟩ : syracuseStep 1814351 = 2721527) B2721527
theorem B1814367 : Blo 1813608 1814367 := bstep (se 1 (by rfl) ⟨1360775, by rfl⟩ : syracuseStep 1814367 = 2721551) B2721551
theorem B4083551 : Blo 1813608 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B9187181 : Blo 1813608 9187181 := bstep (se 3 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 9187181 = 3445193) B3445193
theorem B6123383 : Blo 1813608 6123383 := bstep (se 1 (by rfl) ⟨4592537, by rfl⟩ : syracuseStep 6123383 = 9185075) B9185075
theorem B26161015 : Blo 1813608 26161015 := bstep (se 1 (by rfl) ⟨19620761, by rfl⟩ : syracuseStep 26161015 = 39241523) B39241523
theorem B1814395 : Blo 1813608 1814395 := bstep (se 1 (by rfl) ⟨1360796, by rfl⟩ : syracuseStep 1814395 = 2721593) B2721593
theorem B3493793 : Blo 1813608 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B1814447 : Blo 1813608 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B1814471 : Blo 1813608 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B1814491 : Blo 1813608 1814491 := bstep (se 1 (by rfl) ⟨1360868, by rfl⟩ : syracuseStep 1814491 = 2721737) B2721737
theorem B7753735 : Blo 1813608 7753735 := bstep (se 1 (by rfl) ⟨5815301, by rfl⟩ : syracuseStep 7753735 = 11630603) B11630603
theorem B9187343 : Blo 1813608 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B4083731 : Blo 1813608 4083731 := bstep (se 1 (by rfl) ⟨3062798, by rfl⟩ : syracuseStep 4083731 = 6125597) B6125597
theorem B1814567 : Blo 1813608 1814567 := bstep (se 1 (by rfl) ⟨1360925, by rfl⟩ : syracuseStep 1814567 = 2721851) B2721851
theorem B6123599 : Blo 1813608 6123599 := bstep (se 1 (by rfl) ⟨4592699, by rfl⟩ : syracuseStep 6123599 = 9185399) B9185399
theorem B1814607 : Blo 1813608 1814607 := bstep (se 1 (by rfl) ⟨1360955, by rfl⟩ : syracuseStep 1814607 = 2721911) B2721911
theorem B1814623 : Blo 1813608 1814623 := bstep (se 1 (by rfl) ⟨1360967, by rfl⟩ : syracuseStep 1814623 = 2721935) B2721935
theorem B3444859 : Blo 1813608 3444859 := bstep (se 1 (by rfl) ⟨2583644, by rfl⟩ : syracuseStep 3444859 = 5167289) B5167289
theorem B1814651 : Blo 1813608 1814651 := bstep (se 1 (by rfl) ⟨1360988, by rfl⟩ : syracuseStep 1814651 = 2721977) B2721977
theorem B1814703 : Blo 1813608 1814703 := bstep (se 1 (by rfl) ⟨1361027, by rfl⟩ : syracuseStep 1814703 = 2722055) B2722055
theorem B70717637 : Blo 1813608 70717637 := bstep (se 4 (by rfl) ⟨6629778, by rfl⟩ : syracuseStep 70717637 = 13259557) B13259557
theorem B1814727 : Blo 1813608 1814727 := bstep (se 1 (by rfl) ⟨1361045, by rfl⟩ : syracuseStep 1814727 = 2722091) B2722091
theorem B1814747 : Blo 1813608 1814747 := bstep (se 1 (by rfl) ⟨1361060, by rfl⟩ : syracuseStep 1814747 = 2722121) B2722121
theorem B1814823 : Blo 1813608 1814823 := bstep (se 1 (by rfl) ⟨1361117, by rfl⟩ : syracuseStep 1814823 = 2722235) B2722235
theorem B1814863 : Blo 1813608 1814863 := bstep (se 1 (by rfl) ⟨1361147, by rfl⟩ : syracuseStep 1814863 = 2722295) B2722295
theorem B3445087 : Blo 1813608 3445087 := bstep (se 1 (by rfl) ⟨2583815, by rfl⟩ : syracuseStep 3445087 = 5167631) B5167631
theorem B1814879 : Blo 1813608 1814879 := bstep (se 1 (by rfl) ⟨1361159, by rfl⟩ : syracuseStep 1814879 = 2722319) B2722319
theorem B4084073 : Blo 1813608 4084073 := bstep (se 2 (by rfl) ⟨1531527, by rfl⟩ : syracuseStep 4084073 = 3063055) B3063055
theorem B1814907 : Blo 1813608 1814907 := bstep (se 1 (by rfl) ⟨1361180, by rfl⟩ : syracuseStep 1814907 = 2722361) B2722361
theorem B6541697 : Blo 1813608 6541697 := bstep (se 2 (by rfl) ⟨2453136, by rfl⟩ : syracuseStep 6541697 = 4906273) B4906273
theorem B1814959 : Blo 1813608 1814959 := bstep (se 1 (by rfl) ⟨1361219, by rfl⟩ : syracuseStep 1814959 = 2722439) B2722439
theorem B1814983 : Blo 1813608 1814983 := bstep (se 1 (by rfl) ⟨1361237, by rfl⟩ : syracuseStep 1814983 = 2722475) B2722475
theorem B6123977 : Blo 1813608 6123977 := bstep (se 2 (by rfl) ⟨2296491, by rfl⟩ : syracuseStep 6123977 = 4592983) B4592983
theorem B1815003 : Blo 1813608 1815003 := bstep (se 1 (by rfl) ⟨1361252, by rfl⟩ : syracuseStep 1815003 = 2722505) B2722505
theorem B3453403 : Blo 1813608 3453403 := bstep (se 1 (by rfl) ⟨2590052, by rfl⟩ : syracuseStep 3453403 = 5180105) B5180105
theorem B4592153 : Blo 1813608 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B1815079 : Blo 1813608 1815079 := bstep (se 1 (by rfl) ⟨1361309, by rfl⟩ : syracuseStep 1815079 = 2722619) B2722619
theorem B1815119 : Blo 1813608 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B1815135 : Blo 1813608 1815135 := bstep (se 1 (by rfl) ⟨1361351, by rfl⟩ : syracuseStep 1815135 = 2722703) B2722703
theorem B3445345 : Blo 1813608 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B1815163 : Blo 1813608 1815163 := bstep (se 1 (by rfl) ⟨1361372, by rfl⟩ : syracuseStep 1815163 = 2722745) B2722745
theorem B1815215 : Blo 1813608 1815215 := bstep (se 1 (by rfl) ⟨1361411, by rfl⟩ : syracuseStep 1815215 = 2722823) B2722823
theorem B6886073 : Blo 1813608 6886073 := bstep (se 2 (by rfl) ⟨2582277, by rfl⟩ : syracuseStep 6886073 = 5164555) B5164555
theorem B1815239 : Blo 1813608 1815239 := bstep (se 1 (by rfl) ⟨1361429, by rfl⟩ : syracuseStep 1815239 = 2722859) B2722859
theorem B6124247 : Blo 1813608 6124247 := bstep (se 1 (by rfl) ⟨4593185, by rfl⟩ : syracuseStep 6124247 = 9186371) B9186371
theorem B1815259 : Blo 1813608 1815259 := bstep (se 1 (by rfl) ⟨1361444, by rfl⟩ : syracuseStep 1815259 = 2722889) B2722889
theorem B1815335 : Blo 1813608 1815335 := bstep (se 1 (by rfl) ⟨1361501, by rfl⟩ : syracuseStep 1815335 = 2723003) B2723003
theorem B58831667 : Blo 1813608 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B23262025 : Blo 1813608 23262025 := bstep (se 2 (by rfl) ⟨8723259, by rfl⟩ : syracuseStep 23262025 = 17446519) B17446519
theorem B1815375 : Blo 1813608 1815375 := bstep (se 1 (by rfl) ⟨1361531, by rfl⟩ : syracuseStep 1815375 = 2723063) B2723063
theorem B1815391 : Blo 1813608 1815391 := bstep (se 1 (by rfl) ⟨1361543, by rfl⟩ : syracuseStep 1815391 = 2723087) B2723087
theorem B1815419 : Blo 1813608 1815419 := bstep (se 1 (by rfl) ⟨1361564, by rfl⟩ : syracuseStep 1815419 = 2723129) B2723129
theorem B6124463 : Blo 1813608 6124463 := bstep (se 1 (by rfl) ⟨4593347, by rfl⟩ : syracuseStep 6124463 = 9186695) B9186695
theorem B3445679 : Blo 1813608 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B1815471 : Blo 1813608 1815471 := bstep (se 1 (by rfl) ⟨1361603, by rfl⟩ : syracuseStep 1815471 = 2723207) B2723207
theorem B4084667 : Blo 1813608 4084667 := bstep (se 1 (by rfl) ⟨3063500, by rfl⟩ : syracuseStep 4084667 = 6127001) B6127001
theorem B1815495 : Blo 1813608 1815495 := bstep (se 1 (by rfl) ⟨1361621, by rfl⟩ : syracuseStep 1815495 = 2723243) B2723243
theorem B1815515 : Blo 1813608 1815515 := bstep (se 1 (by rfl) ⟨1361636, by rfl⟩ : syracuseStep 1815515 = 2723273) B2723273
theorem B4592659 : Blo 1813608 4592659 := bstep (se 1 (by rfl) ⟨3444494, by rfl⟩ : syracuseStep 4592659 = 6888989) B6888989
theorem B1815591 : Blo 1813608 1815591 := bstep (se 1 (by rfl) ⟨1361693, by rfl⟩ : syracuseStep 1815591 = 2723387) B2723387
theorem B4084793 : Blo 1813608 4084793 := bstep (se 2 (by rfl) ⟨1531797, by rfl⟩ : syracuseStep 4084793 = 3063595) B3063595
theorem B3060983 : Blo 1813608 3060983 := bstep (se 1 (by rfl) ⟨2295737, by rfl⟩ : syracuseStep 3060983 = 4591475) B4591475
theorem B6206807 : Blo 1813608 6206807 := bstep (se 1 (by rfl) ⟨4655105, by rfl⟩ : syracuseStep 6206807 = 9310211) B9310211
theorem B4904317 : Blo 1813608 4904317 := bstep (se 3 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 4904317 = 1839119) B1839119
theorem B3061327 : Blo 1813608 3061327 := bstep (se 1 (by rfl) ⟨2295995, by rfl⟩ : syracuseStep 3061327 = 4591991) B4591991
theorem B29841043 : Blo 1813608 29841043 := bstep (se 1 (by rfl) ⟨22380782, by rfl⟩ : syracuseStep 29841043 = 44761565) B44761565
theorem B6985415 : Blo 1813608 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B3061577 : Blo 1813608 3061577 := bstep (se 2 (by rfl) ⟨1148091, by rfl⟩ : syracuseStep 3061577 = 2296183) B2296183
theorem B6289271 : Blo 1813608 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B2906075 : Blo 1813608 2906075 := bstep (se 1 (by rfl) ⟨2179556, by rfl⟩ : syracuseStep 2906075 = 4359113) B4359113
theorem B25163783 : Blo 1813608 25163783 := bstep (se 1 (by rfl) ⟨18872837, by rfl⟩ : syracuseStep 25163783 = 37745675) B37745675
theorem B3446803 : Blo 1813608 3446803 := bstep (se 1 (by rfl) ⟨2585102, by rfl⟩ : syracuseStep 3446803 = 5170205) B5170205
theorem B4593743 : Blo 1813608 4593743 := bstep (se 1 (by rfl) ⟨3445307, by rfl⟩ : syracuseStep 4593743 = 6890615) B6890615
theorem B3062009 : Blo 1813608 3062009 := bstep (se 2 (by rfl) ⟨1148253, by rfl⟩ : syracuseStep 3062009 = 2296507) B2296507
theorem B17430835 : Blo 1813608 17430835 := bstep (se 1 (by rfl) ⟨13073126, by rfl⟩ : syracuseStep 17430835 = 26146253) B26146253
theorem B10475837 : Blo 1813608 10475837 := bstep (se 3 (by rfl) ⟨1964219, by rfl⟩ : syracuseStep 10475837 = 3928439) B3928439
theorem B3062191 : Blo 1813608 3062191 := bstep (se 1 (by rfl) ⟨2296643, by rfl⟩ : syracuseStep 3062191 = 4593287) B4593287
theorem B104634827 : Blo 1813608 104634827 := bstep (se 1 (by rfl) ⟨78476120, by rfl⟩ : syracuseStep 104634827 = 156952241) B156952241
theorem B3062279 : Blo 1813608 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B3103355 : Blo 1813608 3103355 := bstep (se 1 (by rfl) ⟨2327516, by rfl⟩ : syracuseStep 3103355 = 4655033) B4655033
theorem B5814983 : Blo 1813608 5814983 := bstep (se 1 (by rfl) ⟨4361237, by rfl⟩ : syracuseStep 5814983 = 8722475) B8722475
theorem B11623121 : Blo 1813608 11623121 := bstep (se 2 (by rfl) ⟨4358670, by rfl⟩ : syracuseStep 11623121 = 8717341) B8717341
theorem B9190097 : Blo 1813608 9190097 := bstep (se 2 (by rfl) ⟨3446286, by rfl⟩ : syracuseStep 9190097 = 6892573) B6892573
theorem B4594391 : Blo 1813608 4594391 := bstep (se 1 (by rfl) ⟨3445793, by rfl⟩ : syracuseStep 4594391 = 6891587) B6891587
theorem B6888185 : Blo 1813608 6888185 := bstep (se 2 (by rfl) ⟨2583069, by rfl⟩ : syracuseStep 6888185 = 5166139) B5166139
theorem B3062623 : Blo 1813608 3062623 := bstep (se 1 (by rfl) ⟨2296967, by rfl⟩ : syracuseStep 3062623 = 4593935) B4593935
theorem B670088051 : Blo 1813608 670088051 := bstep (se 1 (by rfl) ⟨502566038, by rfl⟩ : syracuseStep 670088051 = 1005132077) B1005132077
theorem B3062711 : Blo 1813608 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B4594745 : Blo 1813608 4594745 := bstep (se 2 (by rfl) ⟨1723029, by rfl⟩ : syracuseStep 4594745 = 3446059) B3446059
theorem B8723609 : Blo 1813608 8723609 := bstep (se 2 (by rfl) ⟨3271353, by rfl⟩ : syracuseStep 8723609 = 6542707) B6542707
theorem B6290603 : Blo 1813608 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B6126839 : Blo 1813608 6126839 := bstep (se 1 (by rfl) ⟨4595129, by rfl⟩ : syracuseStep 6126839 = 9190259) B9190259
theorem B17448365 : Blo 1813608 17448365 := bstep (se 3 (by rfl) ⟨3271568, by rfl⟩ : syracuseStep 17448365 = 6543137) B6543137
theorem B30989789 : Blo 1813608 30989789 := bstep (se 3 (by rfl) ⟨5810585, by rfl⟩ : syracuseStep 30989789 = 11621171) B11621171
theorem B3145225 : Blo 1813608 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B3063305 : Blo 1813608 3063305 := bstep (se 2 (by rfl) ⟨1148739, by rfl⟩ : syracuseStep 3063305 = 2297479) B2297479
theorem B6127163 : Blo 1813608 6127163 := bstep (se 1 (by rfl) ⟨4595372, by rfl⟩ : syracuseStep 6127163 = 9190745) B9190745
theorem B4357729 : Blo 1813608 4357729 := bstep (se 2 (by rfl) ⟨1634148, by rfl⟩ : syracuseStep 4357729 = 3268297) B3268297
theorem B5971591 : Blo 1813608 5971591 := bstep (se 1 (by rfl) ⟨4478693, by rfl⟩ : syracuseStep 5971591 = 8957387) B8957387
theorem B3063467 : Blo 1813608 3063467 := bstep (se 1 (by rfl) ⟨2297600, by rfl⟩ : syracuseStep 3063467 = 4595201) B4595201
theorem B6889171 : Blo 1813608 6889171 := bstep (se 1 (by rfl) ⟨5166878, by rfl⟩ : syracuseStep 6889171 = 10333757) B10333757
theorem B9182969 : Blo 1813608 9182969 := bstep (se 2 (by rfl) ⟨3443613, by rfl⟩ : syracuseStep 9182969 = 6887227) B6887227
theorem B6127433 : Blo 1813608 6127433 := bstep (se 2 (by rfl) ⟨2297787, by rfl⟩ : syracuseStep 6127433 = 4595575) B4595575
theorem B5816225 : Blo 1813608 5816225 := bstep (se 2 (by rfl) ⟨2181084, by rfl⟩ : syracuseStep 5816225 = 4362169) B4362169
theorem B10338313 : Blo 1813608 10338313 := bstep (se 2 (by rfl) ⟨3876867, by rfl⟩ : syracuseStep 10338313 = 7753735) B7753735
theorem B4595737 : Blo 1813608 4595737 := bstep (se 2 (by rfl) ⟨1723401, by rfl⟩ : syracuseStep 4595737 = 3446803) B3446803
theorem B69795917 : Blo 1813608 69795917 := bstep (se 3 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 69795917 = 26173469) B26173469
theorem B47145091 : Blo 1813608 47145091 := bstep (se 1 (by rfl) ⟨35358818, by rfl⟩ : syracuseStep 47145091 = 70717637) B70717637
theorem B23241113 : Blo 1813608 23241113 := bstep (se 2 (by rfl) ⟨8715417, by rfl⟩ : syracuseStep 23241113 = 17430835) B17430835
theorem B4604537 : Blo 1813608 4604537 := bstep (se 2 (by rfl) ⟨1726701, by rfl⟩ : syracuseStep 4604537 = 3453403) B3453403
theorem B2720591 : Blo 1813608 2720591 := bstep (se 1 (by rfl) ⟨2040443, by rfl⟩ : syracuseStep 2720591 = 4080887) B4080887
theorem B2040655 : Blo 1813608 2040655 := bstep (se 1 (by rfl) ⟨1530491, by rfl⟩ : syracuseStep 2040655 = 3060983) B3060983
theorem B4137871 : Blo 1813608 4137871 := bstep (se 1 (by rfl) ⟨3103403, by rfl⟩ : syracuseStep 4137871 = 6206807) B6206807
theorem B31016033 : Blo 1813608 31016033 := bstep (se 2 (by rfl) ⟨11631012, by rfl⟩ : syracuseStep 31016033 = 23262025) B23262025
theorem B35357897 : Blo 1813608 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B2720987 : Blo 1813608 2720987 := bstep (se 1 (by rfl) ⟨2040740, by rfl⟩ : syracuseStep 2720987 = 4081481) B4081481
theorem B2041051 : Blo 1813608 2041051 := bstep (se 1 (by rfl) ⟨1530788, by rfl⟩ : syracuseStep 2041051 = 3061577) B3061577
theorem B5596393 : Blo 1813608 5596393 := bstep (se 2 (by rfl) ⟨2098647, by rfl⟩ : syracuseStep 5596393 = 4197295) B4197295
theorem B2721161 : Blo 1813608 2721161 := bstep (se 2 (by rfl) ⟨1020435, by rfl⟩ : syracuseStep 2721161 = 2040871) B2040871
theorem B37258643 : Blo 1813608 37258643 := bstep (se 1 (by rfl) ⟨27943982, by rfl⟩ : syracuseStep 37258643 = 55887965) B55887965
theorem B7857569 : Blo 1813608 7857569 := bstep (se 2 (by rfl) ⟨2946588, by rfl⟩ : syracuseStep 7857569 = 5893177) B5893177
theorem B2041339 : Blo 1813608 2041339 := bstep (se 1 (by rfl) ⟨1531004, by rfl⟩ : syracuseStep 2041339 = 3062009) B3062009
theorem B4081247 : Blo 1813608 4081247 := bstep (se 1 (by rfl) ⟨3060935, by rfl⟩ : syracuseStep 4081247 = 6121871) B6121871
theorem B69756551 : Blo 1813608 69756551 := bstep (se 1 (by rfl) ⟨52317413, by rfl⟩ : syracuseStep 69756551 = 104634827) B104634827
theorem B2041519 : Blo 1813608 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B2295479 : Blo 1813608 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2721515 : Blo 1813608 2721515 := bstep (se 1 (by rfl) ⟨2041136, by rfl⟩ : syracuseStep 2721515 = 4082273) B4082273
theorem B3876655 : Blo 1813608 3876655 := bstep (se 1 (by rfl) ⟨2907491, by rfl⟩ : syracuseStep 3876655 = 5814983) B5814983
theorem B4081463 : Blo 1813608 4081463 := bstep (se 1 (by rfl) ⟨3061097, by rfl⟩ : syracuseStep 4081463 = 6122195) B6122195
theorem B2295631 : Blo 1813608 2295631 := bstep (se 1 (by rfl) ⟨1721723, by rfl⟩ : syracuseStep 2295631 = 3443447) B3443447
theorem B6539089 : Blo 1813608 6539089 := bstep (se 2 (by rfl) ⟨2452158, by rfl⟩ : syracuseStep 6539089 = 4904317) B4904317
theorem B8718263 : Blo 1813608 8718263 := bstep (se 1 (by rfl) ⟨6538697, by rfl⟩ : syracuseStep 8718263 = 13077395) B13077395
theorem B2721743 : Blo 1813608 2721743 := bstep (se 1 (by rfl) ⟨2041307, by rfl⟩ : syracuseStep 2721743 = 4082615) B4082615
theorem B2041807 : Blo 1813608 2041807 := bstep (se 1 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 2041807 = 3062711) B3062711
theorem B34867205 : Blo 1813608 34867205 := bstep (se 4 (by rfl) ⟨3268800, by rfl⟩ : syracuseStep 34867205 = 6537601) B6537601
theorem B4081769 : Blo 1813608 4081769 := bstep (se 2 (by rfl) ⟨1530663, by rfl⟩ : syracuseStep 4081769 = 3061327) B3061327
theorem B3270761 : Blo 1813608 3270761 := bstep (se 2 (by rfl) ⟨1226535, by rfl⟩ : syracuseStep 3270761 = 2453071) B2453071
theorem B5810305 : Blo 1813608 5810305 := bstep (se 2 (by rfl) ⟨2178864, by rfl⟩ : syracuseStep 5810305 = 4357729) B4357729
theorem B6121601 : Blo 1813608 6121601 := bstep (se 2 (by rfl) ⟨2295600, by rfl⟩ : syracuseStep 6121601 = 4591201) B4591201
theorem B9185561 : Blo 1813608 9185561 := bstep (se 2 (by rfl) ⟨3444585, by rfl⟩ : syracuseStep 9185561 = 6889171) B6889171
theorem B2722139 : Blo 1813608 2722139 := bstep (se 1 (by rfl) ⟨2041604, by rfl⟩ : syracuseStep 2722139 = 4083209) B4083209
theorem B2042203 : Blo 1813608 2042203 := bstep (se 1 (by rfl) ⟨1531652, by rfl⟩ : syracuseStep 2042203 = 3063305) B3063305
theorem B50317699 : Blo 1813608 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B9316781 : Blo 1813608 9316781 := bstep (se 3 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 9316781 = 3493793) B3493793
theorem B2042311 : Blo 1813608 2042311 := bstep (se 1 (by rfl) ⟨1531733, by rfl⟩ : syracuseStep 2042311 = 3063467) B3063467
theorem B6121979 : Blo 1813608 6121979 := bstep (se 1 (by rfl) ⟨4591484, by rfl⟩ : syracuseStep 6121979 = 9182969) B9182969
theorem B2722367 : Blo 1813608 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B4082255 : Blo 1813608 4082255 := bstep (se 1 (by rfl) ⟨3061691, by rfl⟩ : syracuseStep 4082255 = 6123383) B6123383
theorem B3877483 : Blo 1813608 3877483 := bstep (se 1 (by rfl) ⟨2908112, by rfl⟩ : syracuseStep 3877483 = 5816225) B5816225
theorem B2722487 : Blo 1813608 2722487 := bstep (se 1 (by rfl) ⟨2041865, by rfl⟩ : syracuseStep 2722487 = 4083731) B4083731
theorem B29420243 : Blo 1813608 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B4082399 : Blo 1813608 4082399 := bstep (se 1 (by rfl) ⟨3061799, by rfl⟩ : syracuseStep 4082399 = 6123599) B6123599
theorem B2583451 : Blo 1813608 2583451 := bstep (se 1 (by rfl) ⟨1937588, by rfl⟩ : syracuseStep 2583451 = 3875177) B3875177
theorem B2722715 : Blo 1813608 2722715 := bstep (se 1 (by rfl) ⟨2042036, by rfl⟩ : syracuseStep 2722715 = 4084073) B4084073
theorem B6122411 : Blo 1813608 6122411 := bstep (se 1 (by rfl) ⟨4591808, by rfl⟩ : syracuseStep 6122411 = 9183617) B9183617
theorem B4361131 : Blo 1813608 4361131 := bstep (se 1 (by rfl) ⟨3270848, by rfl⟩ : syracuseStep 4361131 = 6541697) B6541697
theorem B4082651 : Blo 1813608 4082651 := bstep (se 1 (by rfl) ⟨3061988, by rfl⟩ : syracuseStep 4082651 = 6123977) B6123977
theorem B5237747 : Blo 1813608 5237747 := bstep (se 1 (by rfl) ⟨3928310, by rfl⟩ : syracuseStep 5237747 = 7856621) B7856621
theorem B17443907 : Blo 1813608 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B159099997 : Blo 1813608 159099997 := bstep (se 3 (by rfl) ⟨29831249, by rfl⟩ : syracuseStep 159099997 = 59662499) B59662499
theorem B4590715 : Blo 1813608 4590715 := bstep (se 1 (by rfl) ⟨3443036, by rfl⟩ : syracuseStep 4590715 = 6886073) B6886073
theorem B4082831 : Blo 1813608 4082831 := bstep (se 1 (by rfl) ⟨3062123, by rfl⟩ : syracuseStep 4082831 = 6124247) B6124247
theorem B4082921 : Blo 1813608 4082921 := bstep (se 2 (by rfl) ⟨1531095, by rfl⟩ : syracuseStep 4082921 = 3062191) B3062191
theorem B1813791 : Blo 1813608 1813791 := bstep (se 1 (by rfl) ⟨1360343, by rfl⟩ : syracuseStep 1813791 = 2720687) B2720687
theorem B4082975 : Blo 1813608 4082975 := bstep (se 1 (by rfl) ⟨3062231, by rfl⟩ : syracuseStep 4082975 = 6124463) B6124463
theorem B2723111 : Blo 1813608 2723111 := bstep (se 1 (by rfl) ⟨2042333, by rfl⟩ : syracuseStep 2723111 = 4084667) B4084667
theorem B1813851 : Blo 1813608 1813851 := bstep (se 1 (by rfl) ⟨1360388, by rfl⟩ : syracuseStep 1813851 = 2720777) B2720777
theorem B1813871 : Blo 1813608 1813871 := bstep (se 1 (by rfl) ⟨1360403, by rfl⟩ : syracuseStep 1813871 = 2720807) B2720807
theorem B2723195 : Blo 1813608 2723195 := bstep (se 1 (by rfl) ⟨2042396, by rfl⟩ : syracuseStep 2723195 = 4084793) B4084793
theorem B1813927 : Blo 1813608 1813927 := bstep (se 1 (by rfl) ⟨1360445, by rfl⟩ : syracuseStep 1813927 = 2720891) B2720891
theorem B6122951 : Blo 1813608 6122951 := bstep (se 1 (by rfl) ⟨4592213, by rfl⟩ : syracuseStep 6122951 = 9184427) B9184427
theorem B2723321 : Blo 1813608 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B1814011 : Blo 1813608 1814011 := bstep (se 1 (by rfl) ⟨1360508, by rfl⟩ : syracuseStep 1814011 = 2721017) B2721017
theorem B17436221 : Blo 1813608 17436221 := bstep (se 3 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 17436221 = 6538583) B6538583
theorem B1814079 : Blo 1813608 1814079 := bstep (se 1 (by rfl) ⟨1360559, by rfl⟩ : syracuseStep 1814079 = 2721119) B2721119
theorem B1814087 : Blo 1813608 1814087 := bstep (se 1 (by rfl) ⟨1360565, by rfl⟩ : syracuseStep 1814087 = 2721131) B2721131
theorem B1814239 : Blo 1813608 1814239 := bstep (se 1 (by rfl) ⟨1360679, by rfl⟩ : syracuseStep 1814239 = 2721359) B2721359
theorem B6123275 : Blo 1813608 6123275 := bstep (se 1 (by rfl) ⟨4592456, by rfl⟩ : syracuseStep 6123275 = 9184913) B9184913
theorem B4083497 : Blo 1813608 4083497 := bstep (se 2 (by rfl) ⟨1531311, by rfl⟩ : syracuseStep 4083497 = 3062623) B3062623
theorem B1814319 : Blo 1813608 1814319 := bstep (se 1 (by rfl) ⟨1360739, by rfl⟩ : syracuseStep 1814319 = 2721479) B2721479
theorem B4656943 : Blo 1813608 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B70692725 : Blo 1813608 70692725 := bstep (se 5 (by rfl) ⟨3313721, by rfl⟩ : syracuseStep 70692725 = 6627443) B6627443
theorem B1814427 : Blo 1813608 1814427 := bstep (se 1 (by rfl) ⟨1360820, by rfl⟩ : syracuseStep 1814427 = 2721641) B2721641
theorem B1814479 : Blo 1813608 1814479 := bstep (se 1 (by rfl) ⟨1360859, by rfl⟩ : syracuseStep 1814479 = 2721719) B2721719
theorem B15708113 : Blo 1813608 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B1814503 : Blo 1813608 1814503 := bstep (se 1 (by rfl) ⟨1360877, by rfl⟩ : syracuseStep 1814503 = 2721755) B2721755
theorem B6123545 : Blo 1813608 6123545 := bstep (se 2 (by rfl) ⟨2296329, by rfl⟩ : syracuseStep 6123545 = 4592659) B4592659
theorem B6983891 : Blo 1813608 6983891 := bstep (se 1 (by rfl) ⟨5237918, by rfl⟩ : syracuseStep 6983891 = 10475837) B10475837
theorem B1814815 : Blo 1813608 1814815 := bstep (se 1 (by rfl) ⟨1361111, by rfl⟩ : syracuseStep 1814815 = 2722223) B2722223
theorem B5517659 : Blo 1813608 5517659 := bstep (se 1 (by rfl) ⟨4138244, by rfl⟩ : syracuseStep 5517659 = 8276489) B8276489
theorem B1814875 : Blo 1813608 1814875 := bstep (se 1 (by rfl) ⟨1361156, by rfl⟩ : syracuseStep 1814875 = 2722313) B2722313
theorem B1814895 : Blo 1813608 1814895 := bstep (se 1 (by rfl) ⟨1361171, by rfl⟩ : syracuseStep 1814895 = 2722343) B2722343
theorem B2068903 : Blo 1813608 2068903 := bstep (se 1 (by rfl) ⟨1551677, by rfl⟩ : syracuseStep 2068903 = 3103355) B3103355
theorem B1814951 : Blo 1813608 1814951 := bstep (se 1 (by rfl) ⟨1361213, by rfl⟩ : syracuseStep 1814951 = 2722427) B2722427
theorem B4592123 : Blo 1813608 4592123 := bstep (se 1 (by rfl) ⟨3444092, by rfl⟩ : syracuseStep 4592123 = 6888185) B6888185
theorem B1815035 : Blo 1813608 1815035 := bstep (se 1 (by rfl) ⟨1361276, by rfl⟩ : syracuseStep 1815035 = 2722553) B2722553
theorem B1815103 : Blo 1813608 1815103 := bstep (se 1 (by rfl) ⟨1361327, by rfl⟩ : syracuseStep 1815103 = 2722655) B2722655
theorem B1815111 : Blo 1813608 1815111 := bstep (se 1 (by rfl) ⟨1361333, by rfl⟩ : syracuseStep 1815111 = 2722667) B2722667
theorem B1815263 : Blo 1813608 1815263 := bstep (se 1 (by rfl) ⟨1361447, by rfl⟩ : syracuseStep 1815263 = 2722895) B2722895
theorem B1815343 : Blo 1813608 1815343 := bstep (se 1 (by rfl) ⟨1361507, by rfl⟩ : syracuseStep 1815343 = 2723015) B2723015
theorem B4084559 : Blo 1813608 4084559 := bstep (se 1 (by rfl) ⟨3063419, by rfl⟩ : syracuseStep 4084559 = 6126839) B6126839
theorem B1815451 : Blo 1813608 1815451 := bstep (se 1 (by rfl) ⟨1361588, by rfl⟩ : syracuseStep 1815451 = 2723177) B2723177
theorem B1815503 : Blo 1813608 1815503 := bstep (se 1 (by rfl) ⟨1361627, by rfl⟩ : syracuseStep 1815503 = 2723255) B2723255
theorem B9188315 : Blo 1813608 9188315 := bstep (se 1 (by rfl) ⟨6891236, by rfl⟩ : syracuseStep 9188315 = 13782473) B13782473
theorem B1815527 : Blo 1813608 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B4084775 : Blo 1813608 4084775 := bstep (se 1 (by rfl) ⟨3063581, by rfl⟩ : syracuseStep 4084775 = 6127163) B6127163
theorem B9188477 : Blo 1813608 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B4084955 : Blo 1813608 4084955 := bstep (se 1 (by rfl) ⟨3063716, by rfl⟩ : syracuseStep 4084955 = 6127433) B6127433
theorem B6124787 : Blo 1813608 6124787 := bstep (se 1 (by rfl) ⟨4593590, by rfl⟩ : syracuseStep 6124787 = 9187181) B9187181
theorem B6124895 : Blo 1813608 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B9188801 : Blo 1813608 9188801 := bstep (se 2 (by rfl) ⟨3445800, by rfl⟩ : syracuseStep 9188801 = 6891601) B6891601
theorem B4593095 : Blo 1813608 4593095 := bstep (se 1 (by rfl) ⟨3444821, by rfl⟩ : syracuseStep 4593095 = 6889643) B6889643
theorem B4593145 : Blo 1813608 4593145 := bstep (se 2 (by rfl) ⟨1722429, by rfl⟩ : syracuseStep 4593145 = 3444859) B3444859
theorem B3061435 : Blo 1813608 3061435 := bstep (se 1 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 3061435 = 4592153) B4592153
theorem B4593449 : Blo 1813608 4593449 := bstep (se 2 (by rfl) ⟨1722543, by rfl⟩ : syracuseStep 4593449 = 3445087) B3445087
theorem B7747433 : Blo 1813608 7747433 := bstep (se 2 (by rfl) ⟨2905287, by rfl⟩ : syracuseStep 7747433 = 5810575) B5810575
theorem B39221111 : Blo 1813608 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B4593793 : Blo 1813608 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B4905323 : Blo 1813608 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B5167471 : Blo 1813608 5167471 := bstep (se 1 (by rfl) ⟨3875603, by rfl⟩ : syracuseStep 5167471 = 7751207) B7751207
theorem B8722799 : Blo 1813608 8722799 := bstep (se 1 (by rfl) ⟨6542099, by rfl⟩ : syracuseStep 8722799 = 13084199) B13084199
theorem B78469559 : Blo 1813608 78469559 := bstep (se 1 (by rfl) ⟨58852169, by rfl⟩ : syracuseStep 78469559 = 117704339) B117704339
theorem B11786791 : Blo 1813608 11786791 := bstep (se 1 (by rfl) ⟨8840093, by rfl⟩ : syracuseStep 11786791 = 17680187) B17680187
theorem B4192847 : Blo 1813608 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B33094277 : Blo 1813608 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B9181835 : Blo 1813608 9181835 := bstep (se 1 (by rfl) ⟨6886376, by rfl⟩ : syracuseStep 9181835 = 13772753) B13772753
theorem B16775855 : Blo 1813608 16775855 := bstep (se 1 (by rfl) ⟨12581891, by rfl⟩ : syracuseStep 16775855 = 25163783) B25163783
theorem B4905647 : Blo 1813608 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B3062495 : Blo 1813608 3062495 := bstep (se 1 (by rfl) ⟨2296871, by rfl⟩ : syracuseStep 3062495 = 4593743) B4593743
theorem B13785875 : Blo 1813608 13785875 := bstep (se 1 (by rfl) ⟨10339406, by rfl⟩ : syracuseStep 13785875 = 20678813) B20678813
theorem B6126461 : Blo 1813608 6126461 := bstep (se 3 (by rfl) ⟨1148711, by rfl⟩ : syracuseStep 6126461 = 2297423) B2297423
theorem B4905883 : Blo 1813608 4905883 := bstep (se 1 (by rfl) ⟨3679412, by rfl⟩ : syracuseStep 4905883 = 7358825) B7358825
theorem B4594603 : Blo 1813608 4594603 := bstep (se 1 (by rfl) ⟨3445952, by rfl⟩ : syracuseStep 4594603 = 6891905) B6891905
theorem B7748747 : Blo 1813608 7748747 := bstep (se 1 (by rfl) ⟨5811560, by rfl⟩ : syracuseStep 7748747 = 11623121) B11623121
theorem B6126731 : Blo 1813608 6126731 := bstep (se 1 (by rfl) ⟨4595048, by rfl⟩ : syracuseStep 6126731 = 9190097) B9190097
theorem B6986891 : Blo 1813608 6986891 := bstep (se 1 (by rfl) ⟨5240168, by rfl⟩ : syracuseStep 6986891 = 10480337) B10480337
theorem B3062927 : Blo 1813608 3062927 := bstep (se 1 (by rfl) ⟨2297195, by rfl⟩ : syracuseStep 3062927 = 4594391) B4594391
theorem B4594907 : Blo 1813608 4594907 := bstep (se 1 (by rfl) ⟨3446180, by rfl⟩ : syracuseStep 4594907 = 6892361) B6892361
theorem B446725367 : Blo 1813608 446725367 := bstep (se 1 (by rfl) ⟨335044025, by rfl⟩ : syracuseStep 446725367 = 670088051) B670088051
theorem B37231883 : Blo 1813608 37231883 := bstep (se 1 (by rfl) ⟨27923912, by rfl⟩ : syracuseStep 37231883 = 55847825) B55847825
theorem B4595039 : Blo 1813608 4595039 := bstep (se 1 (by rfl) ⟨3446279, by rfl⟩ : syracuseStep 4595039 = 6892559) B6892559
theorem B4193633 : Blo 1813608 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B3063163 : Blo 1813608 3063163 := bstep (se 1 (by rfl) ⟨2297372, by rfl⟩ : syracuseStep 3063163 = 4594745) B4594745
theorem B5815739 : Blo 1813608 5815739 := bstep (se 1 (by rfl) ⟨4361804, by rfl⟩ : syracuseStep 5815739 = 8723609) B8723609
theorem B4193735 : Blo 1813608 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B11779577 : Blo 1813608 11779577 := bstep (se 2 (by rfl) ⟨4417341, by rfl⟩ : syracuseStep 11779577 = 8834683) B8834683
theorem B7962121 : Blo 1813608 7962121 := bstep (se 2 (by rfl) ⟨2985795, by rfl⟩ : syracuseStep 7962121 = 5971591) B5971591
theorem B39788057 : Blo 1813608 39788057 := bstep (se 2 (by rfl) ⟨14920521, by rfl⟩ : syracuseStep 39788057 = 29841043) B29841043
theorem B11632243 : Blo 1813608 11632243 := bstep (se 1 (by rfl) ⟨8724182, by rfl⟩ : syracuseStep 11632243 = 17448365) B17448365
theorem B20659859 : Blo 1813608 20659859 := bstep (se 1 (by rfl) ⟨15494894, by rfl⟩ : syracuseStep 20659859 = 30989789) B30989789
theorem B34881353 : Blo 1813608 34881353 := bstep (se 2 (by rfl) ⟨13080507, by rfl⟩ : syracuseStep 34881353 = 26161015) B26161015
theorem B7749533 : Blo 1813608 7749533 := bstep (se 3 (by rfl) ⟨1453037, by rfl⟩ : syracuseStep 7749533 = 2906075) B2906075
theorem B6127649 : Blo 1813608 6127649 := bstep (se 2 (by rfl) ⟨2297868, by rfl⟩ : syracuseStep 6127649 = 4595737) B4595737
theorem B46530611 : Blo 1813608 46530611 := bstep (se 1 (by rfl) ⟨34897958, by rfl⟩ : syracuseStep 46530611 = 69795917) B69795917
theorem B6889961 : Blo 1813608 6889961 := bstep (se 2 (by rfl) ⟨2583735, by rfl⟩ : syracuseStep 6889961 = 5167471) B5167471
theorem B20677355 : Blo 1813608 20677355 := bstep (se 1 (by rfl) ⟨15508016, by rfl⟩ : syracuseStep 20677355 = 31016033) B31016033
theorem B5169977 : Blo 1813608 5169977 := bstep (se 2 (by rfl) ⟨1938741, by rfl⟩ : syracuseStep 5169977 = 3877483) B3877483
theorem B14713757 : Blo 1813608 14713757 := bstep (se 3 (by rfl) ⟨2758829, by rfl⟩ : syracuseStep 14713757 = 5517659) B5517659
theorem B2720831 : Blo 1813608 2720831 := bstep (se 1 (by rfl) ⟨2040623, by rfl⟩ : syracuseStep 2720831 = 4081247) B4081247
theorem B2720873 : Blo 1813608 2720873 := bstep (se 2 (by rfl) ⟨1020327, by rfl⟩ : syracuseStep 2720873 = 2040655) B2040655
theorem B11183293 : Blo 1813608 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B2720975 : Blo 1813608 2720975 := bstep (se 1 (by rfl) ⟨2040731, by rfl⟩ : syracuseStep 2720975 = 4081463) B4081463
theorem B2721179 : Blo 1813608 2721179 := bstep (se 1 (by rfl) ⟨2040884, by rfl⟩ : syracuseStep 2721179 = 4081769) B4081769
theorem B4081067 : Blo 1813608 4081067 := bstep (se 1 (by rfl) ⟨3060800, by rfl⟩ : syracuseStep 4081067 = 6121601) B6121601
theorem B212133329 : Blo 1813608 212133329 := bstep (se 2 (by rfl) ⟨79549998, by rfl⟩ : syracuseStep 212133329 = 159099997) B159099997
theorem B6120953 : Blo 1813608 6120953 := bstep (se 2 (by rfl) ⟨2295357, by rfl⟩ : syracuseStep 6120953 = 4590715) B4590715
theorem B3270215 : Blo 1813608 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B6211187 : Blo 1813608 6211187 := bstep (se 1 (by rfl) ⟨4658390, by rfl⟩ : syracuseStep 6211187 = 9316781) B9316781
theorem B2721401 : Blo 1813608 2721401 := bstep (se 2 (by rfl) ⟨1020525, by rfl⟩ : syracuseStep 2721401 = 2041051) B2041051
theorem B4081319 : Blo 1813608 4081319 := bstep (se 1 (by rfl) ⟨3060989, by rfl⟩ : syracuseStep 4081319 = 6121979) B6121979
theorem B2795231 : Blo 1813608 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B2721503 : Blo 1813608 2721503 := bstep (se 1 (by rfl) ⟨2041127, by rfl⟩ : syracuseStep 2721503 = 4082255) B4082255
theorem B22062851 : Blo 1813608 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B6121223 : Blo 1813608 6121223 := bstep (se 1 (by rfl) ⟨4590917, by rfl⟩ : syracuseStep 6121223 = 9181835) B9181835
theorem B11183903 : Blo 1813608 11183903 := bstep (se 1 (by rfl) ⟨8387927, by rfl⟩ : syracuseStep 11183903 = 16775855) B16775855
theorem B3270431 : Blo 1813608 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B19613495 : Blo 1813608 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B6121277 : Blo 1813608 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B2721599 : Blo 1813608 2721599 := bstep (se 1 (by rfl) ⟨2041199, by rfl⟩ : syracuseStep 2721599 = 4082399) B4082399
theorem B2041663 : Blo 1813608 2041663 := bstep (se 1 (by rfl) ⟨1531247, by rfl⟩ : syracuseStep 2041663 = 3062495) B3062495
theorem B4081607 : Blo 1813608 4081607 := bstep (se 1 (by rfl) ⟨3061205, by rfl⟩ : syracuseStep 4081607 = 6122411) B6122411
theorem B2721767 : Blo 1813608 2721767 := bstep (se 1 (by rfl) ⟨2041325, by rfl⟩ : syracuseStep 2721767 = 4082651) B4082651
theorem B3491831 : Blo 1813608 3491831 := bstep (se 1 (by rfl) ⟨2618873, by rfl⟩ : syracuseStep 3491831 = 5237747) B5237747
theorem B2721785 : Blo 1813608 2721785 := bstep (se 2 (by rfl) ⟨1020669, by rfl⟩ : syracuseStep 2721785 = 2041339) B2041339
theorem B2721887 : Blo 1813608 2721887 := bstep (se 1 (by rfl) ⟨2041415, by rfl⟩ : syracuseStep 2721887 = 4082831) B4082831
theorem B2041951 : Blo 1813608 2041951 := bstep (se 1 (by rfl) ⟨1531463, by rfl⟩ : syracuseStep 2041951 = 3062927) B3062927
theorem B15509657 : Blo 1813608 15509657 := bstep (se 2 (by rfl) ⟨5816121, by rfl⟩ : syracuseStep 15509657 = 11632243) B11632243
theorem B2721947 : Blo 1813608 2721947 := bstep (se 1 (by rfl) ⟨2041460, by rfl⟩ : syracuseStep 2721947 = 4082921) B4082921
theorem B2721983 : Blo 1813608 2721983 := bstep (se 1 (by rfl) ⟨2041487, by rfl⟩ : syracuseStep 2721983 = 4082975) B4082975
theorem B2722025 : Blo 1813608 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B2795755 : Blo 1813608 2795755 := bstep (se 1 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 2795755 = 4193633) B4193633
theorem B4081913 : Blo 1813608 4081913 := bstep (se 2 (by rfl) ⟨1530717, by rfl⟩ : syracuseStep 4081913 = 3061435) B3061435
theorem B3877159 : Blo 1813608 3877159 := bstep (se 1 (by rfl) ⟨2907869, by rfl⟩ : syracuseStep 3877159 = 5815739) B5815739
theorem B4081967 : Blo 1813608 4081967 := bstep (se 1 (by rfl) ⟨3061475, by rfl⟩ : syracuseStep 4081967 = 6122951) B6122951
theorem B13773239 : Blo 1813608 13773239 := bstep (se 1 (by rfl) ⟨10329929, by rfl⟩ : syracuseStep 13773239 = 20659859) B20659859
theorem B8718785 : Blo 1813608 8718785 := bstep (se 2 (by rfl) ⟨3269544, by rfl⟩ : syracuseStep 8718785 = 6539089) B6539089
theorem B4082183 : Blo 1813608 4082183 := bstep (se 1 (by rfl) ⟨3061637, by rfl⟩ : syracuseStep 4082183 = 6123275) B6123275
theorem B2722331 : Blo 1813608 2722331 := bstep (se 1 (by rfl) ⟨2041748, by rfl⟩ : syracuseStep 2722331 = 4083497) B4083497
theorem B2722409 : Blo 1813608 2722409 := bstep (se 2 (by rfl) ⟨1020903, by rfl⟩ : syracuseStep 2722409 = 2041807) B2041807
theorem B10472075 : Blo 1813608 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B4082363 : Blo 1813608 4082363 := bstep (se 1 (by rfl) ⟨3061772, by rfl⟩ : syracuseStep 4082363 = 6123545) B6123545
theorem B4655927 : Blo 1813608 4655927 := bstep (se 1 (by rfl) ⟨3491945, by rfl⟩ : syracuseStep 4655927 = 6983891) B6983891
theorem B62860121 : Blo 1813608 62860121 := bstep (se 2 (by rfl) ⟨23572545, by rfl⟩ : syracuseStep 62860121 = 47145091) B47145091
theorem B15494075 : Blo 1813608 15494075 := bstep (se 1 (by rfl) ⟨11620556, by rfl⟩ : syracuseStep 15494075 = 23241113) B23241113
theorem B2722937 : Blo 1813608 2722937 := bstep (se 2 (by rfl) ⟨1021101, by rfl⟩ : syracuseStep 2722937 = 2042203) B2042203
theorem B1813727 : Blo 1813608 1813727 := bstep (se 1 (by rfl) ⟨1360295, by rfl⟩ : syracuseStep 1813727 = 2720591) B2720591
theorem B2723039 : Blo 1813608 2723039 := bstep (se 1 (by rfl) ⟨2042279, by rfl⟩ : syracuseStep 2723039 = 4084559) B4084559
theorem B2723081 : Blo 1813608 2723081 := bstep (se 2 (by rfl) ⟨1021155, by rfl⟩ : syracuseStep 2723081 = 2042311) B2042311
theorem B2723183 : Blo 1813608 2723183 := bstep (se 1 (by rfl) ⟨2042387, by rfl⟩ : syracuseStep 2723183 = 4084775) B4084775
theorem B15715721 : Blo 1813608 15715721 := bstep (se 2 (by rfl) ⟨5893395, by rfl⟩ : syracuseStep 15715721 = 11786791) B11786791
theorem B23571931 : Blo 1813608 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B1813991 : Blo 1813608 1813991 := bstep (se 1 (by rfl) ⟨1360493, by rfl⟩ : syracuseStep 1813991 = 2720987) B2720987
theorem B2723303 : Blo 1813608 2723303 := bstep (se 1 (by rfl) ⟨2042477, by rfl⟩ : syracuseStep 2723303 = 4084955) B4084955
theorem B4083191 : Blo 1813608 4083191 := bstep (se 1 (by rfl) ⟨3062393, by rfl⟩ : syracuseStep 4083191 = 6124787) B6124787
theorem B4083263 : Blo 1813608 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B1814107 : Blo 1813608 1814107 := bstep (se 1 (by rfl) ⟨1360580, by rfl⟩ : syracuseStep 1814107 = 2721161) B2721161
theorem B5238379 : Blo 1813608 5238379 := bstep (se 1 (by rfl) ⟨3928784, by rfl⟩ : syracuseStep 5238379 = 7857569) B7857569
theorem B99356381 : Blo 1813608 99356381 := bstep (se 3 (by rfl) ⟨18629321, by rfl⟩ : syracuseStep 99356381 = 37258643) B37258643
theorem B1814343 : Blo 1813608 1814343 := bstep (se 1 (by rfl) ⟨1360757, by rfl⟩ : syracuseStep 1814343 = 2721515) B2721515
theorem B5517161 : Blo 1813608 5517161 := bstep (se 2 (by rfl) ⟨2068935, by rfl⟩ : syracuseStep 5517161 = 4137871) B4137871
theorem B3444601 : Blo 1813608 3444601 := bstep (se 2 (by rfl) ⟨1291725, by rfl⟩ : syracuseStep 3444601 = 2583451) B2583451
theorem B6541177 : Blo 1813608 6541177 := bstep (se 2 (by rfl) ⟨2452941, by rfl⟩ : syracuseStep 6541177 = 4905883) B4905883
theorem B5164955 : Blo 1813608 5164955 := bstep (se 1 (by rfl) ⟨3873716, by rfl⟩ : syracuseStep 5164955 = 7747433) B7747433
theorem B5812175 : Blo 1813608 5812175 := bstep (se 1 (by rfl) ⟨4359131, by rfl⟩ : syracuseStep 5812175 = 8718263) B8718263
theorem B1814495 : Blo 1813608 1814495 := bstep (se 1 (by rfl) ⟨1360871, by rfl⟩ : syracuseStep 1814495 = 2721743) B2721743
theorem B23244803 : Blo 1813608 23244803 := bstep (se 1 (by rfl) ⟨17433602, by rfl⟩ : syracuseStep 23244803 = 34867205) B34867205
theorem B6123707 : Blo 1813608 6123707 := bstep (se 1 (by rfl) ⟨4592780, by rfl⟩ : syracuseStep 6123707 = 9185561) B9185561
theorem B1814759 : Blo 1813608 1814759 := bstep (se 1 (by rfl) ⟨1361069, by rfl⟩ : syracuseStep 1814759 = 2722139) B2722139
theorem B1814911 : Blo 1813608 1814911 := bstep (se 1 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 1814911 = 2722367) B2722367
theorem B1814991 : Blo 1813608 1814991 := bstep (se 1 (by rfl) ⟨1361243, by rfl⟩ : syracuseStep 1814991 = 2722487) B2722487
theorem B4084217 : Blo 1813608 4084217 := bstep (se 2 (by rfl) ⟨1531581, by rfl⟩ : syracuseStep 4084217 = 3063163) B3063163
theorem B4084307 : Blo 1813608 4084307 := bstep (se 1 (by rfl) ⟨3063230, by rfl⟩ : syracuseStep 4084307 = 6126461) B6126461
theorem B1815143 : Blo 1813608 1815143 := bstep (se 1 (by rfl) ⟨1361357, by rfl⟩ : syracuseStep 1815143 = 2722715) B2722715
theorem B6124193 : Blo 1813608 6124193 := bstep (se 2 (by rfl) ⟨2296572, by rfl⟩ : syracuseStep 6124193 = 4593145) B4593145
theorem B11629271 : Blo 1813608 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B5165831 : Blo 1813608 5165831 := bstep (se 1 (by rfl) ⟨3874373, by rfl⟩ : syracuseStep 5165831 = 7748747) B7748747
theorem B4084487 : Blo 1813608 4084487 := bstep (se 1 (by rfl) ⟨3063365, by rfl⟩ : syracuseStep 4084487 = 6126731) B6126731
theorem B4657927 : Blo 1813608 4657927 := bstep (se 1 (by rfl) ⟨3493445, by rfl⟩ : syracuseStep 4657927 = 6986891) B6986891
theorem B297816911 : Blo 1813608 297816911 := bstep (se 1 (by rfl) ⟨223362683, by rfl⟩ : syracuseStep 297816911 = 446725367) B446725367
theorem B1815407 : Blo 1813608 1815407 := bstep (se 1 (by rfl) ⟨1361555, by rfl⟩ : syracuseStep 1815407 = 2723111) B2723111
theorem B1815463 : Blo 1813608 1815463 := bstep (se 1 (by rfl) ⟨1361597, by rfl⟩ : syracuseStep 1815463 = 2723195) B2723195
theorem B7853051 : Blo 1813608 7853051 := bstep (se 1 (by rfl) ⟨5889788, by rfl⟩ : syracuseStep 7853051 = 11779577) B11779577
theorem B1815547 : Blo 1813608 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B3060841 : Blo 1813608 3060841 := bstep (se 2 (by rfl) ⟨1147815, by rfl⟩ : syracuseStep 3060841 = 2295631) B2295631
theorem B23254235 : Blo 1813608 23254235 := bstep (se 1 (by rfl) ⟨17440676, by rfl⟩ : syracuseStep 23254235 = 34881353) B34881353
theorem B5166355 : Blo 1813608 5166355 := bstep (se 1 (by rfl) ⟨3874766, by rfl⟩ : syracuseStep 5166355 = 7749533) B7749533
theorem B13784417 : Blo 1813608 13784417 := bstep (se 2 (by rfl) ⟨5169156, by rfl⟩ : syracuseStep 13784417 = 10338313) B10338313
theorem B42464645 : Blo 1813608 42464645 := bstep (se 4 (by rfl) ⟨3981060, by rfl⟩ : syracuseStep 42464645 = 7962121) B7962121
theorem B7747073 : Blo 1813608 7747073 := bstep (se 2 (by rfl) ⟨2905152, by rfl⟩ : syracuseStep 7747073 = 5810305) B5810305
theorem B6125057 : Blo 1813608 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B3061415 : Blo 1813608 3061415 := bstep (se 1 (by rfl) ⟨2296061, by rfl⟩ : syracuseStep 3061415 = 4592123) B4592123
theorem B67090265 : Blo 1813608 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B2758537 : Blo 1813608 2758537 := bstep (se 2 (by rfl) ⟨1034451, by rfl⟩ : syracuseStep 2758537 = 2068903) B2068903
theorem B6125543 : Blo 1813608 6125543 := bstep (se 1 (by rfl) ⟨4594157, by rfl⟩ : syracuseStep 6125543 = 9188315) B9188315
theorem B6125651 : Blo 1813608 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B6125867 : Blo 1813608 6125867 := bstep (se 1 (by rfl) ⟨4594400, by rfl⟩ : syracuseStep 6125867 = 9188801) B9188801
theorem B3062063 : Blo 1813608 3062063 := bstep (se 1 (by rfl) ⟨2296547, by rfl⟩ : syracuseStep 3062063 = 4593095) B4593095
theorem B46504367 : Blo 1813608 46504367 := bstep (se 1 (by rfl) ⟨34878275, by rfl⟩ : syracuseStep 46504367 = 69756551) B69756551
theorem B34888117 : Blo 1813608 34888117 := bstep (se 5 (by rfl) ⟨1635380, by rfl⟩ : syracuseStep 34888117 = 3270761) B3270761
theorem B3062299 : Blo 1813608 3062299 := bstep (se 1 (by rfl) ⟨2296724, by rfl⟩ : syracuseStep 3062299 = 4593449) B4593449
theorem B5814841 : Blo 1813608 5814841 := bstep (se 2 (by rfl) ⟨2180565, by rfl⟩ : syracuseStep 5814841 = 4361131) B4361131
theorem B6126137 : Blo 1813608 6126137 := bstep (se 2 (by rfl) ⟨2297301, by rfl⟩ : syracuseStep 6126137 = 4594603) B4594603
theorem B26147407 : Blo 1813608 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B106101485 : Blo 1813608 106101485 := bstep (se 3 (by rfl) ⟨19894028, by rfl⟩ : syracuseStep 106101485 = 39788057) B39788057
theorem B5815199 : Blo 1813608 5815199 := bstep (se 1 (by rfl) ⟨4361399, by rfl⟩ : syracuseStep 5815199 = 8722799) B8722799
theorem B24837029 : Blo 1813608 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B52313039 : Blo 1813608 52313039 := bstep (se 1 (by rfl) ⟨39234779, by rfl⟩ : syracuseStep 52313039 = 78469559) B78469559
theorem B7461857 : Blo 1813608 7461857 := bstep (se 2 (by rfl) ⟨2798196, by rfl⟩ : syracuseStep 7461857 = 5596393) B5596393
theorem B12278765 : Blo 1813608 12278765 := bstep (se 3 (by rfl) ⟨2302268, by rfl⟩ : syracuseStep 12278765 = 4604537) B4604537
theorem B9190583 : Blo 1813608 9190583 := bstep (se 1 (by rfl) ⟨6892937, by rfl⟩ : syracuseStep 9190583 = 13785875) B13785875
theorem B3063271 : Blo 1813608 3063271 := bstep (se 1 (by rfl) ⟨2297453, by rfl⟩ : syracuseStep 3063271 = 4594907) B4594907
theorem B24821255 : Blo 1813608 24821255 := bstep (se 1 (by rfl) ⟨18615941, by rfl⟩ : syracuseStep 24821255 = 37231883) B37231883
theorem B3063359 : Blo 1813608 3063359 := bstep (se 1 (by rfl) ⟨2297519, by rfl⟩ : syracuseStep 3063359 = 4595039) B4595039
theorem B11624147 : Blo 1813608 11624147 := bstep (se 1 (by rfl) ⟨8718110, by rfl⟩ : syracuseStep 11624147 = 17436221) B17436221
theorem B5168873 : Blo 1813608 5168873 := bstep (se 2 (by rfl) ⟨1938327, by rfl⟩ : syracuseStep 5168873 = 3876655) B3876655
theorem B47128483 : Blo 1813608 47128483 := bstep (se 1 (by rfl) ⟨35346362, by rfl⟩ : syracuseStep 47128483 = 70692725) B70692725
theorem B3727673 : Blo 1813608 3727673 := bstep (se 2 (by rfl) ⟨1397877, by rfl⟩ : syracuseStep 3727673 = 2795755) B2795755
theorem B5169545 : Blo 1813608 5169545 := bstep (se 2 (by rfl) ⟨1938579, by rfl⟩ : syracuseStep 5169545 = 3877159) B3877159
theorem B5235367 : Blo 1813608 5235367 := bstep (se 1 (by rfl) ⟨3926525, by rfl⟩ : syracuseStep 5235367 = 7853051) B7853051
theorem B2720711 : Blo 1813608 2720711 := bstep (se 1 (by rfl) ⟨2040533, by rfl⟩ : syracuseStep 2720711 = 4081067) B4081067
theorem B4080635 : Blo 1813608 4080635 := bstep (se 1 (by rfl) ⟨3060476, by rfl⟩ : syracuseStep 4080635 = 6120953) B6120953
theorem B6210569 : Blo 1813608 6210569 := bstep (se 2 (by rfl) ⟨2328963, by rfl⟩ : syracuseStep 6210569 = 4657927) B4657927
theorem B2180143 : Blo 1813608 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B2720879 : Blo 1813608 2720879 := bstep (se 1 (by rfl) ⟨2040659, by rfl⟩ : syracuseStep 2720879 = 4081319) B4081319
theorem B2040943 : Blo 1813608 2040943 := bstep (se 1 (by rfl) ⟨1530707, by rfl⟩ : syracuseStep 2040943 = 3061415) B3061415
theorem B4080815 : Blo 1813608 4080815 := bstep (se 1 (by rfl) ⟨3060611, by rfl⟩ : syracuseStep 4080815 = 6121223) B6121223
theorem B7455935 : Blo 1813608 7455935 := bstep (se 1 (by rfl) ⟨5591951, by rfl⟩ : syracuseStep 7455935 = 11183903) B11183903
theorem B2180287 : Blo 1813608 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B13075663 : Blo 1813608 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B4080851 : Blo 1813608 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B2721071 : Blo 1813608 2721071 := bstep (se 1 (by rfl) ⟨2040803, by rfl⟩ : syracuseStep 2721071 = 4081607) B4081607
theorem B2327887 : Blo 1813608 2327887 := bstep (se 1 (by rfl) ⟨1745915, by rfl⟩ : syracuseStep 2327887 = 3491831) B3491831
theorem B10339771 : Blo 1813608 10339771 := bstep (se 1 (by rfl) ⟨7754828, by rfl⟩ : syracuseStep 10339771 = 15509657) B15509657
theorem B4081121 : Blo 1813608 4081121 := bstep (se 2 (by rfl) ⟨1530420, by rfl⟩ : syracuseStep 4081121 = 3060841) B3060841
theorem B2721275 : Blo 1813608 2721275 := bstep (se 1 (by rfl) ⟨2040956, by rfl⟩ : syracuseStep 2721275 = 4081913) B4081913
theorem B2721311 : Blo 1813608 2721311 := bstep (se 1 (by rfl) ⟨2040983, by rfl⟩ : syracuseStep 2721311 = 4081967) B4081967
theorem B2041375 : Blo 1813608 2041375 := bstep (se 1 (by rfl) ⟨1531031, by rfl⟩ : syracuseStep 2041375 = 3062063) B3062063
theorem B14911057 : Blo 1813608 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B2721455 : Blo 1813608 2721455 := bstep (se 1 (by rfl) ⟨2041091, by rfl⟩ : syracuseStep 2721455 = 4082183) B4082183
theorem B6981383 : Blo 1813608 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B2721575 : Blo 1813608 2721575 := bstep (se 1 (by rfl) ⟨2041181, by rfl⟩ : syracuseStep 2721575 = 4082363) B4082363
theorem B16558019 : Blo 1813608 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B34875359 : Blo 1813608 34875359 := bstep (se 1 (by rfl) ⟨26156519, by rfl⟩ : syracuseStep 34875359 = 52313039) B52313039
theorem B4974571 : Blo 1813608 4974571 := bstep (se 1 (by rfl) ⟨3730928, by rfl⟩ : syracuseStep 4974571 = 7461857) B7461857
theorem B8185843 : Blo 1813608 8185843 := bstep (se 1 (by rfl) ⟨6139382, by rfl⟩ : syracuseStep 8185843 = 12278765) B12278765
theorem B2722127 : Blo 1813608 2722127 := bstep (se 1 (by rfl) ⟨2041595, by rfl⟩ : syracuseStep 2722127 = 4083191) B4083191
theorem B2722175 : Blo 1813608 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B2042239 : Blo 1813608 2042239 := bstep (se 1 (by rfl) ⟨1531679, by rfl⟩ : syracuseStep 2042239 = 3063359) B3063359
theorem B2722217 : Blo 1813608 2722217 := bstep (se 2 (by rfl) ⟨1020831, by rfl⟩ : syracuseStep 2722217 = 2041663) B2041663
theorem B3443303 : Blo 1813608 3443303 := bstep (se 1 (by rfl) ⟨2582477, by rfl⟩ : syracuseStep 3443303 = 5164955) B5164955
theorem B4082471 : Blo 1813608 4082471 := bstep (se 1 (by rfl) ⟨3061853, by rfl⟩ : syracuseStep 4082471 = 6123707) B6123707
theorem B2722601 : Blo 1813608 2722601 := bstep (se 2 (by rfl) ⟨1020975, by rfl⟩ : syracuseStep 2722601 = 2041951) B2041951
theorem B2722811 : Blo 1813608 2722811 := bstep (se 1 (by rfl) ⟨2042108, by rfl⟩ : syracuseStep 2722811 = 4084217) B4084217
theorem B2722871 : Blo 1813608 2722871 := bstep (se 1 (by rfl) ⟨2042153, by rfl⟩ : syracuseStep 2722871 = 4084307) B4084307
theorem B4082795 : Blo 1813608 4082795 := bstep (se 1 (by rfl) ⟨3062096, by rfl⟩ : syracuseStep 4082795 = 6124193) B6124193
theorem B7752847 : Blo 1813608 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B3443887 : Blo 1813608 3443887 := bstep (se 1 (by rfl) ⟨2582915, by rfl⟩ : syracuseStep 3443887 = 5165831) B5165831
theorem B2722991 : Blo 1813608 2722991 := bstep (se 1 (by rfl) ⟨2042243, by rfl⟩ : syracuseStep 2722991 = 4084487) B4084487
theorem B198544607 : Blo 1813608 198544607 := bstep (se 1 (by rfl) ⟨148908455, by rfl⟩ : syracuseStep 198544607 = 297816911) B297816911
theorem B46517489 : Blo 1813608 46517489 := bstep (se 2 (by rfl) ⟨17444058, by rfl⟩ : syracuseStep 46517489 = 34888117) B34888117
theorem B9809171 : Blo 1813608 9809171 := bstep (se 1 (by rfl) ⟨7356878, by rfl⟩ : syracuseStep 9809171 = 14713757) B14713757
theorem B4083065 : Blo 1813608 4083065 := bstep (se 2 (by rfl) ⟨1531149, by rfl⟩ : syracuseStep 4083065 = 3062299) B3062299
theorem B1813887 : Blo 1813608 1813887 := bstep (se 1 (by rfl) ⟨1360415, by rfl⟩ : syracuseStep 1813887 = 2720831) B2720831
theorem B1813915 : Blo 1813608 1813915 := bstep (se 1 (by rfl) ⟨1360436, by rfl⟩ : syracuseStep 1813915 = 2720873) B2720873
theorem B7753121 : Blo 1813608 7753121 := bstep (se 2 (by rfl) ⟨2907420, by rfl⟩ : syracuseStep 7753121 = 5814841) B5814841
theorem B1813983 : Blo 1813608 1813983 := bstep (se 1 (by rfl) ⟨1360487, by rfl⟩ : syracuseStep 1813983 = 2720975) B2720975
theorem B15502823 : Blo 1813608 15502823 := bstep (se 1 (by rfl) ⟨11627117, by rfl⟩ : syracuseStep 15502823 = 23254235) B23254235
theorem B1814119 : Blo 1813608 1814119 := bstep (se 1 (by rfl) ⟨1360589, by rfl⟩ : syracuseStep 1814119 = 2721179) B2721179
theorem B141422219 : Blo 1813608 141422219 := bstep (se 1 (by rfl) ⟨106066664, by rfl⟩ : syracuseStep 141422219 = 212133329) B212133329
theorem B5164715 : Blo 1813608 5164715 := bstep (se 1 (by rfl) ⟨3873536, by rfl⟩ : syracuseStep 5164715 = 7747073) B7747073
theorem B4083371 : Blo 1813608 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B4140791 : Blo 1813608 4140791 := bstep (se 1 (by rfl) ⟨3105593, by rfl⟩ : syracuseStep 4140791 = 6211187) B6211187
theorem B1814267 : Blo 1813608 1814267 := bstep (se 1 (by rfl) ⟨1360700, by rfl⟩ : syracuseStep 1814267 = 2721401) B2721401
theorem B1814335 : Blo 1813608 1814335 := bstep (se 1 (by rfl) ⟨1360751, by rfl⟩ : syracuseStep 1814335 = 2721503) B2721503
theorem B14708567 : Blo 1813608 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1814399 : Blo 1813608 1814399 := bstep (se 1 (by rfl) ⟨1360799, by rfl⟩ : syracuseStep 1814399 = 2721599) B2721599
theorem B1814511 : Blo 1813608 1814511 := bstep (se 1 (by rfl) ⟨1360883, by rfl⟩ : syracuseStep 1814511 = 2721767) B2721767
theorem B4083695 : Blo 1813608 4083695 := bstep (se 1 (by rfl) ⟨3062771, by rfl⟩ : syracuseStep 4083695 = 6125543) B6125543
theorem B1814523 : Blo 1813608 1814523 := bstep (se 1 (by rfl) ⟨1360892, by rfl⟩ : syracuseStep 1814523 = 2721785) B2721785
theorem B4083767 : Blo 1813608 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B1814591 : Blo 1813608 1814591 := bstep (se 1 (by rfl) ⟨1360943, by rfl⟩ : syracuseStep 1814591 = 2721887) B2721887
theorem B1814631 : Blo 1813608 1814631 := bstep (se 1 (by rfl) ⟨1360973, by rfl⟩ : syracuseStep 1814631 = 2721947) B2721947
theorem B1814655 : Blo 1813608 1814655 := bstep (se 1 (by rfl) ⟨1360991, by rfl⟩ : syracuseStep 1814655 = 2721983) B2721983
theorem B1814683 : Blo 1813608 1814683 := bstep (se 1 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 1814683 = 2722025) B2722025
theorem B4083911 : Blo 1813608 4083911 := bstep (se 1 (by rfl) ⟨3062933, by rfl⟩ : syracuseStep 4083911 = 6125867) B6125867
theorem B31002911 : Blo 1813608 31002911 := bstep (se 1 (by rfl) ⟨23252183, by rfl⟩ : syracuseStep 31002911 = 46504367) B46504367
theorem B5812523 : Blo 1813608 5812523 := bstep (se 1 (by rfl) ⟨4359392, by rfl⟩ : syracuseStep 5812523 = 8718785) B8718785
theorem B1814887 : Blo 1813608 1814887 := bstep (se 1 (by rfl) ⟨1361165, by rfl⟩ : syracuseStep 1814887 = 2722331) B2722331
theorem B4084091 : Blo 1813608 4084091 := bstep (se 1 (by rfl) ⟨3063068, by rfl⟩ : syracuseStep 4084091 = 6126137) B6126137
theorem B1814939 : Blo 1813608 1814939 := bstep (se 1 (by rfl) ⟨1361204, by rfl⟩ : syracuseStep 1814939 = 2722409) B2722409
theorem B70734323 : Blo 1813608 70734323 := bstep (se 1 (by rfl) ⟨53050742, by rfl⟩ : syracuseStep 70734323 = 106101485) B106101485
theorem B41906747 : Blo 1813608 41906747 := bstep (se 1 (by rfl) ⟨31430060, by rfl⟩ : syracuseStep 41906747 = 62860121) B62860121
theorem B31429241 : Blo 1813608 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B4084361 : Blo 1813608 4084361 := bstep (se 2 (by rfl) ⟨1531635, by rfl⟩ : syracuseStep 4084361 = 3063271) B3063271
theorem B1815291 : Blo 1813608 1815291 := bstep (se 1 (by rfl) ⟨1361468, by rfl⟩ : syracuseStep 1815291 = 2722937) B2722937
theorem B6984505 : Blo 1813608 6984505 := bstep (se 2 (by rfl) ⟨2619189, by rfl⟩ : syracuseStep 6984505 = 5238379) B5238379
theorem B12415805 : Blo 1813608 12415805 := bstep (se 3 (by rfl) ⟨2327963, by rfl⟩ : syracuseStep 12415805 = 4655927) B4655927
theorem B1815359 : Blo 1813608 1815359 := bstep (se 1 (by rfl) ⟨1361519, by rfl⟩ : syracuseStep 1815359 = 2723039) B2723039
theorem B1815387 : Blo 1813608 1815387 := bstep (se 1 (by rfl) ⟨1361540, by rfl⟩ : syracuseStep 1815387 = 2723081) B2723081
theorem B1815455 : Blo 1813608 1815455 := bstep (se 1 (by rfl) ⟨1361591, by rfl⟩ : syracuseStep 1815455 = 2723183) B2723183
theorem B1815535 : Blo 1813608 1815535 := bstep (se 1 (by rfl) ⟨1361651, by rfl⟩ : syracuseStep 1815535 = 2723303) B2723303
theorem B66237587 : Blo 1813608 66237587 := bstep (se 1 (by rfl) ⟨49678190, by rfl⟩ : syracuseStep 66237587 = 99356381) B99356381
theorem B3445915 : Blo 1813608 3445915 := bstep (se 1 (by rfl) ⟨2584436, by rfl⟩ : syracuseStep 3445915 = 5168873) B5168873
theorem B4592801 : Blo 1813608 4592801 := bstep (se 2 (by rfl) ⟨1722300, by rfl⟩ : syracuseStep 4592801 = 3444601) B3444601
theorem B8721569 : Blo 1813608 8721569 := bstep (se 2 (by rfl) ⟨3270588, by rfl⟩ : syracuseStep 8721569 = 6541177) B6541177
theorem B62837977 : Blo 1813608 62837977 := bstep (se 2 (by rfl) ⟨23564241, by rfl⟩ : syracuseStep 62837977 = 47128483) B47128483
theorem B15496535 : Blo 1813608 15496535 := bstep (se 1 (by rfl) ⟨11622401, by rfl⟩ : syracuseStep 15496535 = 23244803) B23244803
theorem B4085099 : Blo 1813608 4085099 := bstep (se 1 (by rfl) ⟨3063824, by rfl⟩ : syracuseStep 4085099 = 6127649) B6127649
theorem B31020407 : Blo 1813608 31020407 := bstep (se 1 (by rfl) ⟨23265305, by rfl⟩ : syracuseStep 31020407 = 46530611) B46530611
theorem B4593307 : Blo 1813608 4593307 := bstep (se 1 (by rfl) ⟨3444980, by rfl⟩ : syracuseStep 4593307 = 6889961) B6889961
theorem B13784903 : Blo 1813608 13784903 := bstep (se 1 (by rfl) ⟨10338677, by rfl⟩ : syracuseStep 13784903 = 20677355) B20677355
theorem B3446651 : Blo 1813608 3446651 := bstep (se 1 (by rfl) ⟨2584988, by rfl⟩ : syracuseStep 3446651 = 5169977) B5169977
theorem B34863209 : Blo 1813608 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B9189611 : Blo 1813608 9189611 := bstep (se 1 (by rfl) ⟨6892208, by rfl⟩ : syracuseStep 9189611 = 13784417) B13784417
theorem B28309763 : Blo 1813608 28309763 := bstep (se 1 (by rfl) ⟨21232322, by rfl⟩ : syracuseStep 28309763 = 42464645) B42464645
theorem B41908589 : Blo 1813608 41908589 := bstep (se 3 (by rfl) ⟨7857860, by rfl⟩ : syracuseStep 41908589 = 15715721) B15715721
theorem B44726843 : Blo 1813608 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B9182159 : Blo 1813608 9182159 := bstep (se 1 (by rfl) ⟨6886619, by rfl⟩ : syracuseStep 9182159 = 13773239) B13773239
theorem B6888473 : Blo 1813608 6888473 := bstep (se 2 (by rfl) ⟨2583177, by rfl⟩ : syracuseStep 6888473 = 5166355) B5166355
theorem B7453949 : Blo 1813608 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B10329383 : Blo 1813608 10329383 := bstep (se 1 (by rfl) ⟨7747037, by rfl⟩ : syracuseStep 10329383 = 15494075) B15494075
theorem B14712197 : Blo 1813608 14712197 := bstep (se 4 (by rfl) ⟨1379268, by rfl⟩ : syracuseStep 14712197 = 2758537) B2758537
theorem B6127055 : Blo 1813608 6127055 := bstep (se 1 (by rfl) ⟨4595291, by rfl⟩ : syracuseStep 6127055 = 9190583) B9190583
theorem B16547503 : Blo 1813608 16547503 := bstep (se 1 (by rfl) ⟨12410627, by rfl⟩ : syracuseStep 16547503 = 24821255) B24821255
theorem B15507197 : Blo 1813608 15507197 := bstep (se 3 (by rfl) ⟨2907599, by rfl⟩ : syracuseStep 15507197 = 5815199) B5815199
theorem B7749431 : Blo 1813608 7749431 := bstep (se 1 (by rfl) ⟨5812073, by rfl⟩ : syracuseStep 7749431 = 11624147) B11624147
theorem B15499133 : Blo 1813608 15499133 := bstep (se 3 (by rfl) ⟨2906087, by rfl⟩ : syracuseStep 15499133 = 5812175) B5812175
theorem B3678107 : Blo 1813608 3678107 := bstep (se 1 (by rfl) ⟨2758580, by rfl⟩ : syracuseStep 3678107 = 5517161) B5517161
theorem B20668607 : Blo 1813608 20668607 := bstep (se 1 (by rfl) ⟨15501455, by rfl⟩ : syracuseStep 20668607 = 31002911) B31002911
theorem B3875015 : Blo 1813608 3875015 := bstep (se 1 (by rfl) ⟨2906261, by rfl⟩ : syracuseStep 3875015 = 5812523) B5812523
theorem B19882493 : Blo 1813608 19882493 := bstep (se 3 (by rfl) ⟨3727967, by rfl⟩ : syracuseStep 19882493 = 7455935) B7455935
theorem B2720423 : Blo 1813608 2720423 := bstep (se 1 (by rfl) ⟨2040317, by rfl⟩ : syracuseStep 2720423 = 4080635) B4080635
theorem B2720543 : Blo 1813608 2720543 := bstep (se 1 (by rfl) ⟨2040407, by rfl⟩ : syracuseStep 2720543 = 4080815) B4080815
theorem B2720567 : Blo 1813608 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B6980489 : Blo 1813608 6980489 := bstep (se 2 (by rfl) ⟨2617683, by rfl⟩ : syracuseStep 6980489 = 5235367) B5235367
theorem B10331023 : Blo 1813608 10331023 := bstep (se 1 (by rfl) ⟨7748267, by rfl⟩ : syracuseStep 10331023 = 15496535) B15496535
theorem B2720747 : Blo 1813608 2720747 := bstep (se 1 (by rfl) ⟨2040560, by rfl⟩ : syracuseStep 2720747 = 4081121) B4081121
theorem B39232525 : Blo 1813608 39232525 := bstep (se 3 (by rfl) ⟨7356098, by rfl⟩ : syracuseStep 39232525 = 14712197) B14712197
theorem B4654255 : Blo 1813608 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B23250239 : Blo 1813608 23250239 := bstep (se 1 (by rfl) ⟨17437679, by rfl⟩ : syracuseStep 23250239 = 34875359) B34875359
theorem B23242139 : Blo 1813608 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B2721257 : Blo 1813608 2721257 := bstep (se 2 (by rfl) ⟨1020471, by rfl⟩ : syracuseStep 2721257 = 2040943) B2040943
theorem B17434217 : Blo 1813608 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B37250693 : Blo 1813608 37250693 := bstep (se 4 (by rfl) ⟨3492252, by rfl⟩ : syracuseStep 37250693 = 6984505) B6984505
theorem B2295535 : Blo 1813608 2295535 := bstep (se 1 (by rfl) ⟨1721651, by rfl⟩ : syracuseStep 2295535 = 3443303) B3443303
theorem B2721647 : Blo 1813608 2721647 := bstep (se 1 (by rfl) ⟨2041235, by rfl⟩ : syracuseStep 2721647 = 4082471) B4082471
theorem B6121439 : Blo 1813608 6121439 := bstep (se 1 (by rfl) ⟨4591079, by rfl⟩ : syracuseStep 6121439 = 9182159) B9182159
theorem B2721833 : Blo 1813608 2721833 := bstep (se 2 (by rfl) ⟨1020687, by rfl⟩ : syracuseStep 2721833 = 2041375) B2041375
theorem B2721863 : Blo 1813608 2721863 := bstep (se 1 (by rfl) ⟨2041397, by rfl⟩ : syracuseStep 2721863 = 4082795) B4082795
theorem B6539447 : Blo 1813608 6539447 := bstep (se 1 (by rfl) ⟨4904585, by rfl⟩ : syracuseStep 6539447 = 9809171) B9809171
theorem B22063337 : Blo 1813608 22063337 := bstep (se 2 (by rfl) ⟨8273751, by rfl⟩ : syracuseStep 22063337 = 16547503) B16547503
theorem B2722043 : Blo 1813608 2722043 := bstep (se 1 (by rfl) ⟨2041532, by rfl⟩ : syracuseStep 2722043 = 4083065) B4083065
theorem B9808285 : Blo 1813608 9808285 := bstep (se 3 (by rfl) ⟨1839053, by rfl⟩ : syracuseStep 9808285 = 3678107) B3678107
theorem B3443143 : Blo 1813608 3443143 := bstep (se 1 (by rfl) ⟨2582357, by rfl⟩ : syracuseStep 3443143 = 5164715) B5164715
theorem B2722247 : Blo 1813608 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B10332755 : Blo 1813608 10332755 := bstep (se 1 (by rfl) ⟨7749566, by rfl⟩ : syracuseStep 10332755 = 15499133) B15499133
theorem B43657829 : Blo 1813608 43657829 := bstep (se 4 (by rfl) ⟨4092921, by rfl⟩ : syracuseStep 43657829 = 8185843) B8185843
theorem B2722463 : Blo 1813608 2722463 := bstep (se 1 (by rfl) ⟨2041847, by rfl⟩ : syracuseStep 2722463 = 4083695) B4083695
theorem B2722511 : Blo 1813608 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B2722607 : Blo 1813608 2722607 := bstep (se 1 (by rfl) ⟨2041955, by rfl⟩ : syracuseStep 2722607 = 4083911) B4083911
theorem B2485115 : Blo 1813608 2485115 := bstep (se 1 (by rfl) ⟨1863836, by rfl⟩ : syracuseStep 2485115 = 3727673) B3727673
theorem B2722727 : Blo 1813608 2722727 := bstep (se 1 (by rfl) ⟨2042045, by rfl⟩ : syracuseStep 2722727 = 4084091) B4084091
theorem B47156215 : Blo 1813608 47156215 := bstep (se 1 (by rfl) ⟨35367161, by rfl⟩ : syracuseStep 47156215 = 70734323) B70734323
theorem B27937831 : Blo 1813608 27937831 := bstep (se 1 (by rfl) ⟨20953373, by rfl⟩ : syracuseStep 27937831 = 41906747) B41906747
theorem B2722907 : Blo 1813608 2722907 := bstep (se 1 (by rfl) ⟨2042180, by rfl⟩ : syracuseStep 2722907 = 4084361) B4084361
theorem B2722985 : Blo 1813608 2722985 := bstep (se 2 (by rfl) ⟨1021119, by rfl⟩ : syracuseStep 2722985 = 2042239) B2042239
theorem B8277203 : Blo 1813608 8277203 := bstep (se 1 (by rfl) ⟨6207902, by rfl⟩ : syracuseStep 8277203 = 12415805) B12415805
theorem B1813807 : Blo 1813608 1813807 := bstep (se 1 (by rfl) ⟨1360355, by rfl⟩ : syracuseStep 1813807 = 2720711) B2720711
theorem B4140379 : Blo 1813608 4140379 := bstep (se 1 (by rfl) ⟨3105284, by rfl⟩ : syracuseStep 4140379 = 6210569) B6210569
theorem B1813919 : Blo 1813608 1813919 := bstep (se 1 (by rfl) ⟨1360439, by rfl⟩ : syracuseStep 1813919 = 2720879) B2720879
theorem B44158391 : Blo 1813608 44158391 := bstep (se 1 (by rfl) ⟨33118793, by rfl⟩ : syracuseStep 44158391 = 66237587) B66237587
theorem B1814047 : Blo 1813608 1814047 := bstep (se 1 (by rfl) ⟨1360535, by rfl⟩ : syracuseStep 1814047 = 2721071) B2721071
theorem B2723399 : Blo 1813608 2723399 := bstep (se 1 (by rfl) ⟨2042549, by rfl⟩ : syracuseStep 2723399 = 4085099) B4085099
theorem B20680271 : Blo 1813608 20680271 := bstep (se 1 (by rfl) ⟨15510203, by rfl⟩ : syracuseStep 20680271 = 31020407) B31020407
theorem B11628197 : Blo 1813608 11628197 := bstep (se 4 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 11628197 = 2180287) B2180287
theorem B1814183 : Blo 1813608 1814183 := bstep (se 1 (by rfl) ⟨1360637, by rfl⟩ : syracuseStep 1814183 = 2721275) B2721275
theorem B1814207 : Blo 1813608 1814207 := bstep (se 1 (by rfl) ⟨1360655, by rfl⟩ : syracuseStep 1814207 = 2721311) B2721311
theorem B1814303 : Blo 1813608 1814303 := bstep (se 1 (by rfl) ⟨1360727, by rfl⟩ : syracuseStep 1814303 = 2721455) B2721455
theorem B1814383 : Blo 1813608 1814383 := bstep (se 1 (by rfl) ⟨1360787, by rfl⟩ : syracuseStep 1814383 = 2721575) B2721575
theorem B11038679 : Blo 1813608 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B1814751 : Blo 1813608 1814751 := bstep (se 1 (by rfl) ⟨1361063, by rfl⟩ : syracuseStep 1814751 = 2722127) B2722127
theorem B4591849 : Blo 1813608 4591849 := bstep (se 2 (by rfl) ⟨1721943, by rfl⟩ : syracuseStep 4591849 = 3443887) B3443887
theorem B27939059 : Blo 1813608 27939059 := bstep (se 1 (by rfl) ⟨20954294, by rfl⟩ : syracuseStep 27939059 = 41908589) B41908589
theorem B1814783 : Blo 1813608 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B1814811 : Blo 1813608 1814811 := bstep (se 1 (by rfl) ⟨1361108, by rfl⟩ : syracuseStep 1814811 = 2722217) B2722217
theorem B83783969 : Blo 1813608 83783969 := bstep (se 2 (by rfl) ⟨31418988, by rfl⟩ : syracuseStep 83783969 = 62837977) B62837977
theorem B1815067 : Blo 1813608 1815067 := bstep (se 1 (by rfl) ⟨1361300, by rfl⟩ : syracuseStep 1815067 = 2722601) B2722601
theorem B1815207 : Blo 1813608 1815207 := bstep (se 1 (by rfl) ⟨1361405, by rfl⟩ : syracuseStep 1815207 = 2722811) B2722811
theorem B4592315 : Blo 1813608 4592315 := bstep (se 1 (by rfl) ⟨3444236, by rfl⟩ : syracuseStep 4592315 = 6888473) B6888473
theorem B1815247 : Blo 1813608 1815247 := bstep (se 1 (by rfl) ⟨1361435, by rfl⟩ : syracuseStep 1815247 = 2722871) B2722871
theorem B1815327 : Blo 1813608 1815327 := bstep (se 1 (by rfl) ⟨1361495, by rfl⟩ : syracuseStep 1815327 = 2722991) B2722991
theorem B132363071 : Blo 1813608 132363071 := bstep (se 1 (by rfl) ⟨99272303, by rfl⟩ : syracuseStep 132363071 = 198544607) B198544607
theorem B31011659 : Blo 1813608 31011659 := bstep (se 1 (by rfl) ⟨23258744, by rfl⟩ : syracuseStep 31011659 = 46517489) B46517489
theorem B6886255 : Blo 1813608 6886255 := bstep (se 1 (by rfl) ⟨5164691, by rfl⟩ : syracuseStep 6886255 = 10329383) B10329383
theorem B6124409 : Blo 1813608 6124409 := bstep (se 2 (by rfl) ⟨2296653, by rfl⟩ : syracuseStep 6124409 = 4593307) B4593307
theorem B4084703 : Blo 1813608 4084703 := bstep (se 1 (by rfl) ⟨3063527, by rfl⟩ : syracuseStep 4084703 = 6127055) B6127055
theorem B10335215 : Blo 1813608 10335215 := bstep (se 1 (by rfl) ⟨7751411, by rfl⟩ : syracuseStep 10335215 = 15502823) B15502823
theorem B5166287 : Blo 1813608 5166287 := bstep (se 1 (by rfl) ⟨3874715, by rfl⟩ : syracuseStep 5166287 = 7749431) B7749431
theorem B79508789 : Blo 1813608 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B6632761 : Blo 1813608 6632761 := bstep (se 2 (by rfl) ⟨2487285, by rfl⟩ : syracuseStep 6632761 = 4974571) B4974571
theorem B3446363 : Blo 1813608 3446363 := bstep (se 1 (by rfl) ⟨2584772, by rfl⟩ : syracuseStep 3446363 = 5169545) B5169545
theorem B20952827 : Blo 1813608 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B3061867 : Blo 1813608 3061867 := bstep (se 1 (by rfl) ⟨2296400, by rfl⟩ : syracuseStep 3061867 = 4592801) B4592801
theorem B5814379 : Blo 1813608 5814379 := bstep (se 1 (by rfl) ⟨4360784, by rfl⟩ : syracuseStep 5814379 = 8721569) B8721569
theorem B9189935 : Blo 1813608 9189935 := bstep (se 1 (by rfl) ⟨6892451, by rfl⟩ : syracuseStep 9189935 = 13784903) B13784903
theorem B2906857 : Blo 1813608 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B6126407 : Blo 1813608 6126407 := bstep (se 1 (by rfl) ⟨4594805, by rfl⟩ : syracuseStep 6126407 = 9189611) B9189611
theorem B18873175 : Blo 1813608 18873175 := bstep (se 1 (by rfl) ⟨14154881, by rfl⟩ : syracuseStep 18873175 = 28309763) B28309763
theorem B10337129 : Blo 1813608 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B4594553 : Blo 1813608 4594553 := bstep (se 2 (by rfl) ⟨1722957, by rfl⟩ : syracuseStep 4594553 = 3445915) B3445915
theorem B29817895 : Blo 1813608 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B3103849 : Blo 1813608 3103849 := bstep (se 2 (by rfl) ⟨1163943, by rfl⟩ : syracuseStep 3103849 = 2327887) B2327887
theorem B13786361 : Blo 1813608 13786361 := bstep (se 2 (by rfl) ⟨5169885, by rfl⟩ : syracuseStep 13786361 = 10339771) B10339771
theorem B19881409 : Blo 1813608 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B5168747 : Blo 1813608 5168747 := bstep (se 1 (by rfl) ⟨3876560, by rfl⟩ : syracuseStep 5168747 = 7753121) B7753121
theorem B9191069 : Blo 1813608 9191069 := bstep (se 3 (by rfl) ⟨1723325, by rfl⟩ : syracuseStep 9191069 = 3446651) B3446651
theorem B94281479 : Blo 1813608 94281479 := bstep (se 1 (by rfl) ⟨70711109, by rfl⟩ : syracuseStep 94281479 = 141422219) B141422219
theorem B2760527 : Blo 1813608 2760527 := bstep (se 1 (by rfl) ⟨2070395, by rfl⟩ : syracuseStep 2760527 = 4140791) B4140791
theorem B10338131 : Blo 1813608 10338131 := bstep (se 1 (by rfl) ⟨7753598, by rfl⟩ : syracuseStep 10338131 = 15507197) B15507197
theorem B9805711 : Blo 1813608 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B13779071 : Blo 1813608 13779071 := bstep (se 1 (by rfl) ⟨10334303, by rfl⟩ : syracuseStep 13779071 = 20668607) B20668607
theorem B13254995 : Blo 1813608 13254995 := bstep (se 1 (by rfl) ⟨9941246, by rfl⟩ : syracuseStep 13254995 = 19882493) B19882493
theorem B4653659 : Blo 1813608 4653659 := bstep (se 1 (by rfl) ⟨3490244, by rfl⟩ : syracuseStep 4653659 = 6980489) B6980489
theorem B6890143 : Blo 1813608 6890143 := bstep (se 1 (by rfl) ⟨5167607, by rfl⟩ : syracuseStep 6890143 = 10335215) B10335215
theorem B15500159 : Blo 1813608 15500159 := bstep (se 1 (by rfl) ⟨11625119, by rfl⟩ : syracuseStep 15500159 = 23250239) B23250239
theorem B3875809 : Blo 1813608 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B13968551 : Blo 1813608 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B4080959 : Blo 1813608 4080959 := bstep (se 1 (by rfl) ⟨3060719, by rfl⟩ : syracuseStep 4080959 = 6121439) B6121439
theorem B62874953 : Blo 1813608 62874953 := bstep (se 2 (by rfl) ⟨23578107, by rfl⟩ : syracuseStep 62874953 = 47156215) B47156215
theorem B39757193 : Blo 1813608 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B37250441 : Blo 1813608 37250441 := bstep (se 2 (by rfl) ⟨13968915, by rfl⟩ : syracuseStep 37250441 = 27937831) B27937831
theorem B4359631 : Blo 1813608 4359631 := bstep (se 1 (by rfl) ⟨3269723, by rfl⟩ : syracuseStep 4359631 = 6539447) B6539447
theorem B4138465 : Blo 1813608 4138465 := bstep (se 2 (by rfl) ⟨1551924, by rfl⟩ : syracuseStep 4138465 = 3103849) B3103849
theorem B46491245 : Blo 1813608 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B6891419 : Blo 1813608 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B7752131 : Blo 1813608 7752131 := bstep (se 1 (by rfl) ⟨5814098, by rfl⟩ : syracuseStep 7752131 = 11628197) B11628197
theorem B6892087 : Blo 1813608 6892087 := bstep (se 1 (by rfl) ⟨5169065, by rfl⟩ : syracuseStep 6892087 = 10338131) B10338131
theorem B7359119 : Blo 1813608 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B2583343 : Blo 1813608 2583343 := bstep (se 1 (by rfl) ⟨1937507, by rfl⟩ : syracuseStep 2583343 = 3875015) B3875015
theorem B4082489 : Blo 1813608 4082489 := bstep (se 2 (by rfl) ⟨1530933, by rfl⟩ : syracuseStep 4082489 = 3061867) B3061867
theorem B7752505 : Blo 1813608 7752505 := bstep (se 2 (by rfl) ⟨2907189, by rfl⟩ : syracuseStep 7752505 = 5814379) B5814379
theorem B55855979 : Blo 1813608 55855979 := bstep (se 1 (by rfl) ⟨41891984, by rfl⟩ : syracuseStep 55855979 = 83783969) B83783969
theorem B6122465 : Blo 1813608 6122465 := bstep (se 2 (by rfl) ⟨2295924, by rfl⟩ : syracuseStep 6122465 = 4591849) B4591849
theorem B1813615 : Blo 1813608 1813615 := bstep (se 1 (by rfl) ⟨1360211, by rfl⟩ : syracuseStep 1813615 = 2720423) B2720423
theorem B1813695 : Blo 1813608 1813695 := bstep (se 1 (by rfl) ⟨1360271, by rfl⟩ : syracuseStep 1813695 = 2720543) B2720543
theorem B1813711 : Blo 1813608 1813711 := bstep (se 1 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 1813711 = 2720567) B2720567
theorem B13077713 : Blo 1813608 13077713 := bstep (se 2 (by rfl) ⟨4904142, by rfl⟩ : syracuseStep 13077713 = 9808285) B9808285
theorem B4082939 : Blo 1813608 4082939 := bstep (se 1 (by rfl) ⟨3062204, by rfl⟩ : syracuseStep 4082939 = 6124409) B6124409
theorem B4590857 : Blo 1813608 4590857 := bstep (se 2 (by rfl) ⟨1721571, by rfl⟩ : syracuseStep 4590857 = 3443143) B3443143
theorem B2723135 : Blo 1813608 2723135 := bstep (se 1 (by rfl) ⟨2042351, by rfl⟩ : syracuseStep 2723135 = 4084703) B4084703
theorem B1813831 : Blo 1813608 1813831 := bstep (se 1 (by rfl) ⟨1360373, by rfl⟩ : syracuseStep 1813831 = 2720747) B2720747
theorem B3444191 : Blo 1813608 3444191 := bstep (se 1 (by rfl) ⟨2583143, by rfl⟩ : syracuseStep 3444191 = 5166287) B5166287
theorem B53005859 : Blo 1813608 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B15494759 : Blo 1813608 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B1814171 : Blo 1813608 1814171 := bstep (se 1 (by rfl) ⟨1360628, by rfl⟩ : syracuseStep 1814171 = 2721257) B2721257
theorem B2297575 : Blo 1813608 2297575 := bstep (se 1 (by rfl) ⟨1723181, by rfl⟩ : syracuseStep 2297575 = 3446363) B3446363
theorem B24833795 : Blo 1813608 24833795 := bstep (se 1 (by rfl) ⟨18625346, by rfl⟩ : syracuseStep 24833795 = 37250693) B37250693
theorem B13774697 : Blo 1813608 13774697 := bstep (se 2 (by rfl) ⟨5165511, by rfl⟩ : syracuseStep 13774697 = 10331023) B10331023
theorem B1814431 : Blo 1813608 1814431 := bstep (se 1 (by rfl) ⟨1360823, by rfl⟩ : syracuseStep 1814431 = 2721647) B2721647
theorem B52310033 : Blo 1813608 52310033 := bstep (se 2 (by rfl) ⟨19616262, by rfl⟩ : syracuseStep 52310033 = 39232525) B39232525
theorem B1814555 : Blo 1813608 1814555 := bstep (se 1 (by rfl) ⟨1360916, by rfl⟩ : syracuseStep 1814555 = 2721833) B2721833
theorem B1814575 : Blo 1813608 1814575 := bstep (se 1 (by rfl) ⟨1360931, by rfl⟩ : syracuseStep 1814575 = 2721863) B2721863
theorem B14708891 : Blo 1813608 14708891 := bstep (se 1 (by rfl) ⟨11031668, by rfl⟩ : syracuseStep 14708891 = 22063337) B22063337
theorem B1814695 : Blo 1813608 1814695 := bstep (se 1 (by rfl) ⟨1361021, by rfl⟩ : syracuseStep 1814695 = 2722043) B2722043
theorem B6205673 : Blo 1813608 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B1814831 : Blo 1813608 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B8843681 : Blo 1813608 8843681 := bstep (se 2 (by rfl) ⟨3316380, by rfl⟩ : syracuseStep 8843681 = 6632761) B6632761
theorem B1814975 : Blo 1813608 1814975 := bstep (se 1 (by rfl) ⟨1361231, by rfl⟩ : syracuseStep 1814975 = 2722463) B2722463
theorem B1815007 : Blo 1813608 1815007 := bstep (se 1 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 1815007 = 2722511) B2722511
theorem B22082021 : Blo 1813608 22082021 := bstep (se 4 (by rfl) ⟨2070189, by rfl⟩ : syracuseStep 22082021 = 4140379) B4140379
theorem B1815071 : Blo 1813608 1815071 := bstep (se 1 (by rfl) ⟨1361303, by rfl⟩ : syracuseStep 1815071 = 2722607) B2722607
theorem B4084271 : Blo 1813608 4084271 := bstep (se 1 (by rfl) ⟨3063203, by rfl⟩ : syracuseStep 4084271 = 6126407) B6126407
theorem B1815151 : Blo 1813608 1815151 := bstep (se 1 (by rfl) ⟨1361363, by rfl⟩ : syracuseStep 1815151 = 2722727) B2722727
theorem B1815271 : Blo 1813608 1815271 := bstep (se 1 (by rfl) ⟨1361453, by rfl⟩ : syracuseStep 1815271 = 2722907) B2722907
theorem B1815323 : Blo 1813608 1815323 := bstep (se 1 (by rfl) ⟨1361492, by rfl⟩ : syracuseStep 1815323 = 2722985) B2722985
theorem B5518135 : Blo 1813608 5518135 := bstep (se 1 (by rfl) ⟨4138601, by rfl⟩ : syracuseStep 5518135 = 8277203) B8277203
theorem B7361405 : Blo 1813608 7361405 := bstep (se 3 (by rfl) ⟨1380263, by rfl⟩ : syracuseStep 7361405 = 2760527) B2760527
theorem B29438927 : Blo 1813608 29438927 := bstep (se 1 (by rfl) ⟨22079195, by rfl⟩ : syracuseStep 29438927 = 44158391) B44158391
theorem B3060713 : Blo 1813608 3060713 := bstep (se 2 (by rfl) ⟨1147767, by rfl⟩ : syracuseStep 3060713 = 2295535) B2295535
theorem B1815599 : Blo 1813608 1815599 := bstep (se 1 (by rfl) ⟨1361699, by rfl⟩ : syracuseStep 1815599 = 2723399) B2723399
theorem B3445831 : Blo 1813608 3445831 := bstep (se 1 (by rfl) ⟨2584373, by rfl⟩ : syracuseStep 3445831 = 5168747) B5168747
theorem B62854319 : Blo 1813608 62854319 := bstep (se 1 (by rfl) ⟨47140739, by rfl⟩ : syracuseStep 62854319 = 94281479) B94281479
theorem B18626039 : Blo 1813608 18626039 := bstep (se 1 (by rfl) ⟨13969529, by rfl⟩ : syracuseStep 18626039 = 27939059) B27939059
theorem B3061543 : Blo 1813608 3061543 := bstep (se 1 (by rfl) ⟨2296157, by rfl⟩ : syracuseStep 3061543 = 4592315) B4592315
theorem B88242047 : Blo 1813608 88242047 := bstep (se 1 (by rfl) ⟨66181535, by rfl⟩ : syracuseStep 88242047 = 132363071) B132363071
theorem B20674439 : Blo 1813608 20674439 := bstep (se 1 (by rfl) ⟨15505829, by rfl⟩ : syracuseStep 20674439 = 31011659) B31011659
theorem B25164233 : Blo 1813608 25164233 := bstep (se 2 (by rfl) ⟨9436587, by rfl⟩ : syracuseStep 25164233 = 18873175) B18873175
theorem B9181673 : Blo 1813608 9181673 := bstep (se 2 (by rfl) ⟨3443127, by rfl⟩ : syracuseStep 9181673 = 6886255) B6886255
theorem B26507893 : Blo 1813608 26507893 := bstep (se 5 (by rfl) ⟨1242557, by rfl⟩ : syracuseStep 26507893 = 2485115) B2485115
theorem B6126623 : Blo 1813608 6126623 := bstep (se 1 (by rfl) ⟨4594967, by rfl⟩ : syracuseStep 6126623 = 9189935) B9189935
theorem B6888503 : Blo 1813608 6888503 := bstep (se 1 (by rfl) ⟨5166377, by rfl⟩ : syracuseStep 6888503 = 10332755) B10332755
theorem B29105219 : Blo 1813608 29105219 := bstep (se 1 (by rfl) ⟨21828914, by rfl⟩ : syracuseStep 29105219 = 43657829) B43657829
theorem B3063035 : Blo 1813608 3063035 := bstep (se 1 (by rfl) ⟨2297276, by rfl⟩ : syracuseStep 3063035 = 4594553) B4594553
theorem B26508545 : Blo 1813608 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B9190907 : Blo 1813608 9190907 := bstep (se 1 (by rfl) ⟨6893180, by rfl⟩ : syracuseStep 9190907 = 13786361) B13786361
theorem B13786847 : Blo 1813608 13786847 := bstep (se 1 (by rfl) ⟨10340135, by rfl⟩ : syracuseStep 13786847 = 20680271) B20680271
theorem B6127379 : Blo 1813608 6127379 := bstep (se 1 (by rfl) ⟨4595534, by rfl⟩ : syracuseStep 6127379 = 9191069) B9191069
theorem B13074281 : Blo 1813608 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B34873355 : Blo 1813608 34873355 := bstep (se 1 (by rfl) ⟨26155016, by rfl⟩ : syracuseStep 34873355 = 52310033) B52310033
theorem B14721347 : Blo 1813608 14721347 := bstep (se 1 (by rfl) ⟨11041010, by rfl⟩ : syracuseStep 14721347 = 22082021) B22082021
theorem B39223709 : Blo 1813608 39223709 := bstep (se 3 (by rfl) ⟨7354445, by rfl⟩ : syracuseStep 39223709 = 14708891) B14708891
theorem B34873901 : Blo 1813608 34873901 := bstep (se 3 (by rfl) ⟨6538856, by rfl⟩ : syracuseStep 34873901 = 13077713) B13077713
theorem B4907603 : Blo 1813608 4907603 := bstep (se 1 (by rfl) ⟨3680702, by rfl⟩ : syracuseStep 4907603 = 7361405) B7361405
theorem B16548461 : Blo 1813608 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B2040475 : Blo 1813608 2040475 := bstep (se 1 (by rfl) ⟨1530356, by rfl⟩ : syracuseStep 2040475 = 3060713) B3060713
theorem B41902879 : Blo 1813608 41902879 := bstep (se 1 (by rfl) ⟨31427159, by rfl⟩ : syracuseStep 41902879 = 62854319) B62854319
theorem B2720639 : Blo 1813608 2720639 := bstep (se 1 (by rfl) ⟨2040479, by rfl⟩ : syracuseStep 2720639 = 4080959) B4080959
theorem B7357513 : Blo 1813608 7357513 := bstep (se 2 (by rfl) ⟨2759067, by rfl⟩ : syracuseStep 7357513 = 5518135) B5518135
theorem B58828031 : Blo 1813608 58828031 := bstep (se 1 (by rfl) ⟨44121023, by rfl⟩ : syracuseStep 58828031 = 88242047) B88242047
theorem B6121115 : Blo 1813608 6121115 := bstep (se 1 (by rfl) ⟨4590836, by rfl⟩ : syracuseStep 6121115 = 9181673) B9181673
theorem B2721659 : Blo 1813608 2721659 := bstep (se 1 (by rfl) ⟨2041244, by rfl⟩ : syracuseStep 2721659 = 4082489) B4082489
theorem B4081643 : Blo 1813608 4081643 := bstep (se 1 (by rfl) ⟨3061232, by rfl⟩ : syracuseStep 4081643 = 6122465) B6122465
theorem B2721959 : Blo 1813608 2721959 := bstep (se 1 (by rfl) ⟨2041469, by rfl⟩ : syracuseStep 2721959 = 4082939) B4082939
theorem B2042023 : Blo 1813608 2042023 := bstep (se 1 (by rfl) ⟨1531517, by rfl⟩ : syracuseStep 2042023 = 3063035) B3063035
theorem B17672363 : Blo 1813608 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B2296127 : Blo 1813608 2296127 := bstep (se 1 (by rfl) ⟨1722095, by rfl⟩ : syracuseStep 2296127 = 3444191) B3444191
theorem B4082057 : Blo 1813608 4082057 := bstep (se 2 (by rfl) ⟨1530771, by rfl⟩ : syracuseStep 4082057 = 3061543) B3061543
theorem B9186047 : Blo 1813608 9186047 := bstep (se 1 (by rfl) ⟨6889535, by rfl⟩ : syracuseStep 9186047 = 13779071) B13779071
theorem B2722847 : Blo 1813608 2722847 := bstep (se 1 (by rfl) ⟨2042135, by rfl⟩ : syracuseStep 2722847 = 4084271) B4084271
theorem B10333439 : Blo 1813608 10333439 := bstep (se 1 (by rfl) ⟨7750079, by rfl⟩ : syracuseStep 10333439 = 15500159) B15500159
theorem B35343857 : Blo 1813608 35343857 := bstep (se 2 (by rfl) ⟨13253946, by rfl⟩ : syracuseStep 35343857 = 26507893) B26507893
theorem B9186857 : Blo 1813608 9186857 := bstep (se 2 (by rfl) ⟨3445071, by rfl⟩ : syracuseStep 9186857 = 6890143) B6890143
theorem B26504795 : Blo 1813608 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B24833627 : Blo 1813608 24833627 := bstep (se 1 (by rfl) ⟨18625220, by rfl⟩ : syracuseStep 24833627 = 37250441) B37250441
theorem B3444457 : Blo 1813608 3444457 := bstep (se 2 (by rfl) ⟨1291671, by rfl⟩ : syracuseStep 3444457 = 2583343) B2583343
theorem B30994163 : Blo 1813608 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B13782959 : Blo 1813608 13782959 := bstep (se 1 (by rfl) ⟨10337219, by rfl⟩ : syracuseStep 13782959 = 20674439) B20674439
theorem B37237319 : Blo 1813608 37237319 := bstep (se 1 (by rfl) ⟨27927989, by rfl⟩ : syracuseStep 37237319 = 55855979) B55855979
theorem B5812841 : Blo 1813608 5812841 := bstep (se 2 (by rfl) ⟨2179815, by rfl⟩ : syracuseStep 5812841 = 4359631) B4359631
theorem B5517953 : Blo 1813608 5517953 := bstep (se 2 (by rfl) ⟨2069232, by rfl⟩ : syracuseStep 5517953 = 4138465) B4138465
theorem B4084415 : Blo 1813608 4084415 := bstep (se 1 (by rfl) ⟨3063311, by rfl⟩ : syracuseStep 4084415 = 6126623) B6126623
theorem B4592335 : Blo 1813608 4592335 := bstep (se 1 (by rfl) ⟨3444251, by rfl⟩ : syracuseStep 4592335 = 6888503) B6888503
theorem B19403479 : Blo 1813608 19403479 := bstep (se 1 (by rfl) ⟨14552609, by rfl⟩ : syracuseStep 19403479 = 29105219) B29105219
theorem B3060571 : Blo 1813608 3060571 := bstep (se 1 (by rfl) ⟨2295428, by rfl⟩ : syracuseStep 3060571 = 4590857) B4590857
theorem B1815423 : Blo 1813608 1815423 := bstep (se 1 (by rfl) ⟨1361567, by rfl⟩ : syracuseStep 1815423 = 2723135) B2723135
theorem B35337239 : Blo 1813608 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B4084919 : Blo 1813608 4084919 := bstep (se 1 (by rfl) ⟨3063689, by rfl⟩ : syracuseStep 4084919 = 6127379) B6127379
theorem B8836663 : Blo 1813608 8836663 := bstep (se 1 (by rfl) ⟨6627497, by rfl⟩ : syracuseStep 8836663 = 13254995) B13254995
theorem B19625951 : Blo 1813608 19625951 := bstep (se 1 (by rfl) ⟨14719463, by rfl⟩ : syracuseStep 19625951 = 29438927) B29438927
theorem B9189449 : Blo 1813608 9189449 := bstep (se 2 (by rfl) ⟨3446043, by rfl⟩ : syracuseStep 9189449 = 6892087) B6892087
theorem B9312367 : Blo 1813608 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B41916635 : Blo 1813608 41916635 := bstep (se 1 (by rfl) ⟨31437476, by rfl⟩ : syracuseStep 41916635 = 62874953) B62874953
theorem B12417359 : Blo 1813608 12417359 := bstep (se 1 (by rfl) ⟨9313019, by rfl⟩ : syracuseStep 12417359 = 18626039) B18626039
theorem B10336673 : Blo 1813608 10336673 := bstep (se 2 (by rfl) ⟨3876252, by rfl⟩ : syracuseStep 10336673 = 7752505) B7752505
theorem B23583149 : Blo 1813608 23583149 := bstep (se 3 (by rfl) ⟨4421840, by rfl⟩ : syracuseStep 23583149 = 8843681) B8843681
theorem B4594279 : Blo 1813608 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B5167745 : Blo 1813608 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B4594441 : Blo 1813608 4594441 := bstep (se 2 (by rfl) ⟨1722915, by rfl⟩ : syracuseStep 4594441 = 3445831) B3445831
theorem B12409757 : Blo 1813608 12409757 := bstep (se 3 (by rfl) ⟨2326829, by rfl⟩ : syracuseStep 12409757 = 4653659) B4653659
theorem B5168087 : Blo 1813608 5168087 := bstep (se 1 (by rfl) ⟨3876065, by rfl⟩ : syracuseStep 5168087 = 7752131) B7752131
theorem B16776155 : Blo 1813608 16776155 := bstep (se 1 (by rfl) ⟨12582116, by rfl⟩ : syracuseStep 16776155 = 25164233) B25164233
theorem B4906079 : Blo 1813608 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B66223453 : Blo 1813608 66223453 := bstep (se 3 (by rfl) ⟨12416897, by rfl⟩ : syracuseStep 66223453 = 24833795) B24833795
theorem B3063433 : Blo 1813608 3063433 := bstep (se 2 (by rfl) ⟨1148787, by rfl⟩ : syracuseStep 3063433 = 2297575) B2297575
theorem B6127271 : Blo 1813608 6127271 := bstep (se 1 (by rfl) ⟨4595453, by rfl⟩ : syracuseStep 6127271 = 9190907) B9190907
theorem B10329839 : Blo 1813608 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B9191231 : Blo 1813608 9191231 := bstep (se 1 (by rfl) ⟨6893423, by rfl⟩ : syracuseStep 9191231 = 13786847) B13786847
theorem B8716187 : Blo 1813608 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B9183131 : Blo 1813608 9183131 := bstep (se 1 (by rfl) ⟨6887348, by rfl⟩ : syracuseStep 9183131 = 13774697) B13774697
theorem B23248903 : Blo 1813608 23248903 := bstep (se 1 (by rfl) ⟨17436677, by rfl⟩ : syracuseStep 23248903 = 34873355) B34873355
theorem B9814231 : Blo 1813608 9814231 := bstep (se 1 (by rfl) ⟨7360673, by rfl⟩ : syracuseStep 9814231 = 14721347) B14721347
theorem B26149139 : Blo 1813608 26149139 := bstep (se 1 (by rfl) ⟨19611854, by rfl⟩ : syracuseStep 26149139 = 39223709) B39223709
theorem B23249267 : Blo 1813608 23249267 := bstep (se 1 (by rfl) ⟨17436950, by rfl⟩ : syracuseStep 23249267 = 34873901) B34873901
theorem B3678635 : Blo 1813608 3678635 := bstep (se 1 (by rfl) ⟨2758976, by rfl⟩ : syracuseStep 3678635 = 5517953) B5517953
theorem B2720633 : Blo 1813608 2720633 := bstep (se 2 (by rfl) ⟨1020237, by rfl⟩ : syracuseStep 2720633 = 2040475) B2040475
theorem B33112957 : Blo 1813608 33112957 := bstep (se 3 (by rfl) ⟨6208679, by rfl⟩ : syracuseStep 33112957 = 12417359) B12417359
theorem B25871305 : Blo 1813608 25871305 := bstep (se 2 (by rfl) ⟨9701739, by rfl⟩ : syracuseStep 25871305 = 19403479) B19403479
theorem B55870505 : Blo 1813608 55870505 := bstep (se 2 (by rfl) ⟨20951439, by rfl⟩ : syracuseStep 55870505 = 41902879) B41902879
theorem B4080743 : Blo 1813608 4080743 := bstep (se 1 (by rfl) ⟨3060557, by rfl⟩ : syracuseStep 4080743 = 6121115) B6121115
theorem B4080761 : Blo 1813608 4080761 := bstep (se 2 (by rfl) ⟨1530285, by rfl⟩ : syracuseStep 4080761 = 3060571) B3060571
theorem B13083967 : Blo 1813608 13083967 := bstep (se 1 (by rfl) ⟨9812975, by rfl⟩ : syracuseStep 13083967 = 19625951) B19625951
theorem B2721095 : Blo 1813608 2721095 := bstep (se 1 (by rfl) ⟨2040821, by rfl⟩ : syracuseStep 2721095 = 4081643) B4081643
theorem B11781575 : Blo 1813608 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B27944423 : Blo 1813608 27944423 := bstep (se 1 (by rfl) ⟨20958317, by rfl⟩ : syracuseStep 27944423 = 41916635) B41916635
theorem B2721371 : Blo 1813608 2721371 := bstep (se 1 (by rfl) ⟨2041028, by rfl⟩ : syracuseStep 2721371 = 4082057) B4082057
theorem B6891115 : Blo 1813608 6891115 := bstep (se 1 (by rfl) ⟨5168336, by rfl⟩ : syracuseStep 6891115 = 10336673) B10336673
theorem B15500909 : Blo 1813608 15500909 := bstep (se 3 (by rfl) ⟨2906420, by rfl⟩ : syracuseStep 15500909 = 5812841) B5812841
theorem B15722099 : Blo 1813608 15722099 := bstep (se 1 (by rfl) ⟨11791574, by rfl⟩ : syracuseStep 15722099 = 23583149) B23583149
theorem B11184103 : Blo 1813608 11184103 := bstep (se 1 (by rfl) ⟨8388077, by rfl⟩ : syracuseStep 11184103 = 16776155) B16776155
theorem B3270719 : Blo 1813608 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B11782217 : Blo 1813608 11782217 := bstep (se 2 (by rfl) ⟨4418331, by rfl⟩ : syracuseStep 11782217 = 8836663) B8836663
theorem B23562571 : Blo 1813608 23562571 := bstep (se 1 (by rfl) ⟨17671928, by rfl⟩ : syracuseStep 23562571 = 35343857) B35343857
theorem B20662775 : Blo 1813608 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B5810791 : Blo 1813608 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B6122087 : Blo 1813608 6122087 := bstep (se 1 (by rfl) ⟨4591565, by rfl⟩ : syracuseStep 6122087 = 9183131) B9183131
theorem B2722697 : Blo 1813608 2722697 := bstep (se 2 (by rfl) ⟨1021011, by rfl⟩ : syracuseStep 2722697 = 2042023) B2042023
theorem B24824879 : Blo 1813608 24824879 := bstep (se 1 (by rfl) ⟨18618659, by rfl⟩ : syracuseStep 24824879 = 37237319) B37237319
theorem B3271735 : Blo 1813608 3271735 := bstep (se 1 (by rfl) ⟨2453801, by rfl⟩ : syracuseStep 3271735 = 4907603) B4907603
theorem B2722943 : Blo 1813608 2722943 := bstep (se 1 (by rfl) ⟨2042207, by rfl⟩ : syracuseStep 2722943 = 4084415) B4084415
theorem B1813759 : Blo 1813608 1813759 := bstep (se 1 (by rfl) ⟨1360319, by rfl⟩ : syracuseStep 1813759 = 2720639) B2720639
theorem B2723279 : Blo 1813608 2723279 := bstep (se 1 (by rfl) ⟨2042459, by rfl⟩ : syracuseStep 2723279 = 4084919) B4084919
theorem B6123005 : Blo 1813608 6123005 := bstep (se 3 (by rfl) ⟨1148063, by rfl⟩ : syracuseStep 6123005 = 2296127) B2296127
theorem B39218687 : Blo 1813608 39218687 := bstep (se 1 (by rfl) ⟨29414015, by rfl⟩ : syracuseStep 39218687 = 58828031) B58828031
theorem B6123113 : Blo 1813608 6123113 := bstep (se 2 (by rfl) ⟨2296167, by rfl⟩ : syracuseStep 6123113 = 4592335) B4592335
theorem B1814439 : Blo 1813608 1814439 := bstep (se 1 (by rfl) ⟨1360829, by rfl⟩ : syracuseStep 1814439 = 2721659) B2721659
theorem B9810017 : Blo 1813608 9810017 := bstep (se 2 (by rfl) ⟨3678756, by rfl⟩ : syracuseStep 9810017 = 7357513) B7357513
theorem B1814639 : Blo 1813608 1814639 := bstep (se 1 (by rfl) ⟨1360979, by rfl⟩ : syracuseStep 1814639 = 2721959) B2721959
theorem B3445163 : Blo 1813608 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B88297937 : Blo 1813608 88297937 := bstep (se 2 (by rfl) ⟨33111726, by rfl⟩ : syracuseStep 88297937 = 66223453) B66223453
theorem B6124031 : Blo 1813608 6124031 := bstep (se 1 (by rfl) ⟨4593023, by rfl⟩ : syracuseStep 6124031 = 9186047) B9186047
theorem B3445391 : Blo 1813608 3445391 := bstep (se 1 (by rfl) ⟨2584043, by rfl⟩ : syracuseStep 3445391 = 5168087) B5168087
theorem B1815231 : Blo 1813608 1815231 := bstep (se 1 (by rfl) ⟨1361423, by rfl⟩ : syracuseStep 1815231 = 2722847) B2722847
theorem B4084577 : Blo 1813608 4084577 := bstep (se 2 (by rfl) ⟨1531716, by rfl⟩ : syracuseStep 4084577 = 3063433) B3063433
theorem B4592609 : Blo 1813608 4592609 := bstep (se 2 (by rfl) ⟨1722228, by rfl⟩ : syracuseStep 4592609 = 3444457) B3444457
theorem B6124571 : Blo 1813608 6124571 := bstep (se 1 (by rfl) ⟨4593428, by rfl⟩ : syracuseStep 6124571 = 9186857) B9186857
theorem B4084847 : Blo 1813608 4084847 := bstep (se 1 (by rfl) ⟨3063635, by rfl⟩ : syracuseStep 4084847 = 6127271) B6127271
theorem B6886559 : Blo 1813608 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B9188639 : Blo 1813608 9188639 := bstep (se 1 (by rfl) ⟨6891479, by rfl⟩ : syracuseStep 9188639 = 13782959) B13782959
theorem B12416489 : Blo 1813608 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B11032307 : Blo 1813608 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B23558159 : Blo 1813608 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B6125705 : Blo 1813608 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B6125921 : Blo 1813608 6125921 := bstep (se 2 (by rfl) ⟨2297220, by rfl⟩ : syracuseStep 6125921 = 4594441) B4594441
theorem B6126299 : Blo 1813608 6126299 := bstep (se 1 (by rfl) ⟨4594724, by rfl⟩ : syracuseStep 6126299 = 9189449) B9189449
theorem B8273171 : Blo 1813608 8273171 := bstep (se 1 (by rfl) ⟨6204878, by rfl⟩ : syracuseStep 8273171 = 12409757) B12409757
theorem B6888959 : Blo 1813608 6888959 := bstep (se 1 (by rfl) ⟨5166719, by rfl⟩ : syracuseStep 6888959 = 10333439) B10333439
theorem B17669863 : Blo 1813608 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B16555751 : Blo 1813608 16555751 := bstep (se 1 (by rfl) ⟨12416813, by rfl⟩ : syracuseStep 16555751 = 24833627) B24833627
theorem B6127487 : Blo 1813608 6127487 := bstep (se 1 (by rfl) ⟨4595615, by rfl⟩ : syracuseStep 6127487 = 9191231) B9191231
theorem B30998537 : Blo 1813608 30998537 := bstep (se 2 (by rfl) ⟨11624451, by rfl⟩ : syracuseStep 30998537 = 23248903) B23248903
theorem B17432759 : Blo 1813608 17432759 := bstep (se 1 (by rfl) ⟨13074569, by rfl⟩ : syracuseStep 17432759 = 26149139) B26149139
theorem B15499511 : Blo 1813608 15499511 := bstep (se 1 (by rfl) ⟨11624633, by rfl⟩ : syracuseStep 15499511 = 23249267) B23249267
theorem B17449253 : Blo 1813608 17449253 := bstep (se 4 (by rfl) ⟨1635867, by rfl⟩ : syracuseStep 17449253 = 3271735) B3271735
theorem B31416761 : Blo 1813608 31416761 := bstep (se 2 (by rfl) ⟨11781285, by rfl⟩ : syracuseStep 31416761 = 23562571) B23562571
theorem B2720495 : Blo 1813608 2720495 := bstep (se 1 (by rfl) ⟨2040371, by rfl⟩ : syracuseStep 2720495 = 4080743) B4080743
theorem B2720507 : Blo 1813608 2720507 := bstep (se 1 (by rfl) ⟨2040380, by rfl⟩ : syracuseStep 2720507 = 4080761) B4080761
theorem B18629615 : Blo 1813608 18629615 := bstep (se 1 (by rfl) ⟨13972211, by rfl⟩ : syracuseStep 18629615 = 27944423) B27944423
theorem B4081391 : Blo 1813608 4081391 := bstep (se 1 (by rfl) ⟨3061043, by rfl⟩ : syracuseStep 4081391 = 6122087) B6122087
theorem B16549919 : Blo 1813608 16549919 := bstep (se 1 (by rfl) ⟨12412439, by rfl⟩ : syracuseStep 16549919 = 24824879) B24824879
theorem B5515447 : Blo 1813608 5515447 := bstep (se 1 (by rfl) ⟨4136585, by rfl⟩ : syracuseStep 5515447 = 8273171) B8273171
theorem B4082003 : Blo 1813608 4082003 := bstep (se 1 (by rfl) ⟨3061502, by rfl⟩ : syracuseStep 4082003 = 6123005) B6123005
theorem B4082075 : Blo 1813608 4082075 := bstep (se 1 (by rfl) ⟨3061556, by rfl⟩ : syracuseStep 4082075 = 6123113) B6123113
theorem B11037167 : Blo 1813608 11037167 := bstep (se 1 (by rfl) ⟨8277875, by rfl⟩ : syracuseStep 11037167 = 16555751) B16555751
theorem B14912137 : Blo 1813608 14912137 := bstep (se 2 (by rfl) ⟨5592051, by rfl⟩ : syracuseStep 14912137 = 11184103) B11184103
theorem B6540011 : Blo 1813608 6540011 := bstep (se 1 (by rfl) ⟨4905008, by rfl⟩ : syracuseStep 6540011 = 9810017) B9810017
theorem B31419245 : Blo 1813608 31419245 := bstep (se 3 (by rfl) ⟨5891108, by rfl⟩ : syracuseStep 31419245 = 11782217) B11782217
theorem B2452423 : Blo 1813608 2452423 := bstep (se 1 (by rfl) ⟨1839317, by rfl⟩ : syracuseStep 2452423 = 3678635) B3678635
theorem B2296775 : Blo 1813608 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B13085641 : Blo 1813608 13085641 := bstep (se 2 (by rfl) ⟨4907115, by rfl⟩ : syracuseStep 13085641 = 9814231) B9814231
theorem B4082687 : Blo 1813608 4082687 := bstep (se 1 (by rfl) ⟨3062015, by rfl⟩ : syracuseStep 4082687 = 6124031) B6124031
theorem B2296927 : Blo 1813608 2296927 := bstep (se 1 (by rfl) ⟨1722695, by rfl⟩ : syracuseStep 2296927 = 3445391) B3445391
theorem B2723051 : Blo 1813608 2723051 := bstep (se 1 (by rfl) ⟨2042288, by rfl⟩ : syracuseStep 2723051 = 4084577) B4084577
theorem B1813755 : Blo 1813608 1813755 := bstep (se 1 (by rfl) ⟨1360316, by rfl⟩ : syracuseStep 1813755 = 2720633) B2720633
theorem B4083047 : Blo 1813608 4083047 := bstep (se 1 (by rfl) ⟨3062285, by rfl⟩ : syracuseStep 4083047 = 6124571) B6124571
theorem B2723231 : Blo 1813608 2723231 := bstep (se 1 (by rfl) ⟨2042423, by rfl⟩ : syracuseStep 2723231 = 4084847) B4084847
theorem B4591039 : Blo 1813608 4591039 := bstep (se 1 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 4591039 = 6886559) B6886559
theorem B1814063 : Blo 1813608 1814063 := bstep (se 1 (by rfl) ⟨1360547, by rfl⟩ : syracuseStep 1814063 = 2721095) B2721095
theorem B8277659 : Blo 1813608 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B1814247 : Blo 1813608 1814247 := bstep (se 1 (by rfl) ⟨1360685, by rfl⟩ : syracuseStep 1814247 = 2721371) B2721371
theorem B10333939 : Blo 1813608 10333939 := bstep (se 1 (by rfl) ⟨7750454, by rfl⟩ : syracuseStep 10333939 = 15500909) B15500909
theorem B10481399 : Blo 1813608 10481399 := bstep (se 1 (by rfl) ⟨7861049, by rfl⟩ : syracuseStep 10481399 = 15722099) B15722099
theorem B44150609 : Blo 1813608 44150609 := bstep (se 2 (by rfl) ⟨16556478, by rfl⟩ : syracuseStep 44150609 = 33112957) B33112957
theorem B4083803 : Blo 1813608 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B4083947 : Blo 1813608 4083947 := bstep (se 1 (by rfl) ⟨3062960, by rfl⟩ : syracuseStep 4083947 = 6125921) B6125921
theorem B13775183 : Blo 1813608 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B17445289 : Blo 1813608 17445289 := bstep (se 2 (by rfl) ⟨6541983, by rfl⟩ : syracuseStep 17445289 = 13083967) B13083967
theorem B4084199 : Blo 1813608 4084199 := bstep (se 1 (by rfl) ⟨3063149, by rfl⟩ : syracuseStep 4084199 = 6126299) B6126299
theorem B1815131 : Blo 1813608 1815131 := bstep (se 1 (by rfl) ⟨1361348, by rfl⟩ : syracuseStep 1815131 = 2722697) B2722697
theorem B1815295 : Blo 1813608 1815295 := bstep (se 1 (by rfl) ⟨1361471, by rfl⟩ : syracuseStep 1815295 = 2722943) B2722943
theorem B9188153 : Blo 1813608 9188153 := bstep (se 2 (by rfl) ⟨3445557, by rfl⟩ : syracuseStep 9188153 = 6891115) B6891115
theorem B1815519 : Blo 1813608 1815519 := bstep (se 1 (by rfl) ⟨1361639, by rfl⟩ : syracuseStep 1815519 = 2723279) B2723279
theorem B26145791 : Blo 1813608 26145791 := bstep (se 1 (by rfl) ⟨19609343, by rfl⟩ : syracuseStep 26145791 = 39218687) B39218687
theorem B4592639 : Blo 1813608 4592639 := bstep (se 1 (by rfl) ⟨3444479, by rfl⟩ : syracuseStep 4592639 = 6888959) B6888959
theorem B4084991 : Blo 1813608 4084991 := bstep (se 1 (by rfl) ⟨3063743, by rfl⟩ : syracuseStep 4084991 = 6127487) B6127487
theorem B62821757 : Blo 1813608 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B8721917 : Blo 1813608 8721917 := bstep (se 3 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 8721917 = 3270719) B3270719
theorem B58865291 : Blo 1813608 58865291 := bstep (se 1 (by rfl) ⟨44148968, by rfl⟩ : syracuseStep 58865291 = 88297937) B88297937
theorem B3061739 : Blo 1813608 3061739 := bstep (se 1 (by rfl) ⟨2296304, by rfl⟩ : syracuseStep 3061739 = 4592609) B4592609
theorem B37247003 : Blo 1813608 37247003 := bstep (se 1 (by rfl) ⟨27935252, by rfl⟩ : syracuseStep 37247003 = 55870505) B55870505
theorem B7747721 : Blo 1813608 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B6125759 : Blo 1813608 6125759 := bstep (se 1 (by rfl) ⟨4594319, by rfl⟩ : syracuseStep 6125759 = 9188639) B9188639
theorem B7854383 : Blo 1813608 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B7354871 : Blo 1813608 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B34495073 : Blo 1813608 34495073 := bstep (se 2 (by rfl) ⟨12935652, by rfl⟩ : syracuseStep 34495073 = 25871305) B25871305
theorem B23559817 : Blo 1813608 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B11632835 : Blo 1813608 11632835 := bstep (se 1 (by rfl) ⟨8724626, by rfl⟩ : syracuseStep 11632835 = 17449253) B17449253
theorem B9183455 : Blo 1813608 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B12419743 : Blo 1813608 12419743 := bstep (se 1 (by rfl) ⟨9314807, by rfl⟩ : syracuseStep 12419743 = 18629615) B18629615
theorem B19882849 : Blo 1813608 19882849 := bstep (se 2 (by rfl) ⟨7456068, by rfl⟩ : syracuseStep 19882849 = 14912137) B14912137
theorem B2720927 : Blo 1813608 2720927 := bstep (se 1 (by rfl) ⟨2040695, by rfl⟩ : syracuseStep 2720927 = 4081391) B4081391
theorem B3269897 : Blo 1813608 3269897 := bstep (se 2 (by rfl) ⟨1226211, by rfl⟩ : syracuseStep 3269897 = 2452423) B2452423
theorem B2041159 : Blo 1813608 2041159 := bstep (se 1 (by rfl) ⟨1530869, by rfl⟩ : syracuseStep 2041159 = 3061739) B3061739
theorem B24831335 : Blo 1813608 24831335 := bstep (se 1 (by rfl) ⟨18623501, by rfl⟩ : syracuseStep 24831335 = 37247003) B37247003
theorem B5236255 : Blo 1813608 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B2721335 : Blo 1813608 2721335 := bstep (se 1 (by rfl) ⟨2041001, by rfl⟩ : syracuseStep 2721335 = 4082003) B4082003
theorem B2721383 : Blo 1813608 2721383 := bstep (se 1 (by rfl) ⟨2041037, by rfl⟩ : syracuseStep 2721383 = 4082075) B4082075
theorem B7358111 : Blo 1813608 7358111 := bstep (se 1 (by rfl) ⟨5518583, by rfl⟩ : syracuseStep 7358111 = 11037167) B11037167
theorem B22996715 : Blo 1813608 22996715 := bstep (se 1 (by rfl) ⟨17247536, by rfl⟩ : syracuseStep 22996715 = 34495073) B34495073
theorem B4360007 : Blo 1813608 4360007 := bstep (se 1 (by rfl) ⟨3270005, by rfl⟩ : syracuseStep 4360007 = 6540011) B6540011
theorem B6121385 : Blo 1813608 6121385 := bstep (se 2 (by rfl) ⟨2295519, by rfl⟩ : syracuseStep 6121385 = 4591039) B4591039
theorem B2721791 : Blo 1813608 2721791 := bstep (se 1 (by rfl) ⟨2041343, by rfl⟩ : syracuseStep 2721791 = 4082687) B4082687
theorem B2722031 : Blo 1813608 2722031 := bstep (se 1 (by rfl) ⟨2041523, by rfl⟩ : syracuseStep 2722031 = 4083047) B4083047
theorem B2722535 : Blo 1813608 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B2722631 : Blo 1813608 2722631 := bstep (se 1 (by rfl) ⟨2041973, by rfl⟩ : syracuseStep 2722631 = 4083947) B4083947
theorem B10333007 : Blo 1813608 10333007 := bstep (se 1 (by rfl) ⟨7749755, by rfl⟩ : syracuseStep 10333007 = 15499511) B15499511
theorem B2722799 : Blo 1813608 2722799 := bstep (se 1 (by rfl) ⟨2042099, by rfl⟩ : syracuseStep 2722799 = 4084199) B4084199
theorem B1813663 : Blo 1813608 1813663 := bstep (se 1 (by rfl) ⟨1360247, by rfl⟩ : syracuseStep 1813663 = 2720495) B2720495
theorem B1813671 : Blo 1813608 1813671 := bstep (se 1 (by rfl) ⟨1360253, by rfl⟩ : syracuseStep 1813671 = 2720507) B2720507
theorem B23260385 : Blo 1813608 23260385 := bstep (se 2 (by rfl) ⟨8722644, by rfl⟩ : syracuseStep 23260385 = 17445289) B17445289
theorem B2723327 : Blo 1813608 2723327 := bstep (se 1 (by rfl) ⟨2042495, by rfl⟩ : syracuseStep 2723327 = 4084991) B4084991
theorem B41881171 : Blo 1813608 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B39243527 : Blo 1813608 39243527 := bstep (se 1 (by rfl) ⟨29432645, by rfl⟩ : syracuseStep 39243527 = 58865291) B58865291
theorem B5165147 : Blo 1813608 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B4083839 : Blo 1813608 4083839 := bstep (se 1 (by rfl) ⟨3062879, by rfl⟩ : syracuseStep 4083839 = 6125759) B6125759
theorem B4903247 : Blo 1813608 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B1815367 : Blo 1813608 1815367 := bstep (se 1 (by rfl) ⟨1361525, by rfl⟩ : syracuseStep 1815367 = 2723051) B2723051
theorem B31413089 : Blo 1813608 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B1815487 : Blo 1813608 1815487 := bstep (se 1 (by rfl) ⟨1361615, by rfl⟩ : syracuseStep 1815487 = 2723231) B2723231
theorem B5518439 : Blo 1813608 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B6124733 : Blo 1813608 6124733 := bstep (se 3 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 6124733 = 2296775) B2296775
theorem B20665691 : Blo 1813608 20665691 := bstep (se 1 (by rfl) ⟨15499268, by rfl⟩ : syracuseStep 20665691 = 30998537) B30998537
theorem B11621839 : Blo 1813608 11621839 := bstep (se 1 (by rfl) ⟨8716379, by rfl⟩ : syracuseStep 11621839 = 17432759) B17432759
theorem B7353929 : Blo 1813608 7353929 := bstep (se 2 (by rfl) ⟨2757723, by rfl⟩ : syracuseStep 7353929 = 5515447) B5515447
theorem B20944507 : Blo 1813608 20944507 := bstep (se 1 (by rfl) ⟨15708380, by rfl⟩ : syracuseStep 20944507 = 31416761) B31416761
theorem B6125435 : Blo 1813608 6125435 := bstep (se 1 (by rfl) ⟨4594076, by rfl⟩ : syracuseStep 6125435 = 9188153) B9188153
theorem B3061759 : Blo 1813608 3061759 := bstep (se 1 (by rfl) ⟨2296319, by rfl⟩ : syracuseStep 3061759 = 4592639) B4592639
theorem B17430527 : Blo 1813608 17430527 := bstep (se 1 (by rfl) ⟨13072895, by rfl⟩ : syracuseStep 17430527 = 26145791) B26145791
theorem B5814611 : Blo 1813608 5814611 := bstep (se 1 (by rfl) ⟨4360958, by rfl⟩ : syracuseStep 5814611 = 8721917) B8721917
theorem B17447521 : Blo 1813608 17447521 := bstep (se 2 (by rfl) ⟨6542820, by rfl⟩ : syracuseStep 17447521 = 13085641) B13085641
theorem B11033279 : Blo 1813608 11033279 := bstep (se 1 (by rfl) ⟨8274959, by rfl⟩ : syracuseStep 11033279 = 16549919) B16549919
theorem B3062569 : Blo 1813608 3062569 := bstep (se 2 (by rfl) ⟨1148463, by rfl⟩ : syracuseStep 3062569 = 2296927) B2296927
theorem B20946163 : Blo 1813608 20946163 := bstep (se 1 (by rfl) ⟨15709622, by rfl⟩ : syracuseStep 20946163 = 31419245) B31419245
theorem B13778585 : Blo 1813608 13778585 := bstep (se 2 (by rfl) ⟨5166969, by rfl⟩ : syracuseStep 13778585 = 10333939) B10333939
theorem B6987599 : Blo 1813608 6987599 := bstep (se 1 (by rfl) ⟨5240699, by rfl⟩ : syracuseStep 6987599 = 10481399) B10481399
theorem B29433739 : Blo 1813608 29433739 := bstep (se 1 (by rfl) ⟨22075304, by rfl⟩ : syracuseStep 29433739 = 44150609) B44150609
theorem B27926693 : Blo 1813608 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B3268831 : Blo 1813608 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B3678959 : Blo 1813608 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B2179931 : Blo 1813608 2179931 := bstep (se 1 (by rfl) ⟨1634948, by rfl⟩ : syracuseStep 2179931 = 3269897) B3269897
theorem B26510465 : Blo 1813608 26510465 := bstep (se 2 (by rfl) ⟨9941424, by rfl⟩ : syracuseStep 26510465 = 19882849) B19882849
theorem B4080923 : Blo 1813608 4080923 := bstep (se 1 (by rfl) ⟨3060692, by rfl⟩ : syracuseStep 4080923 = 6121385) B6121385
theorem B3876407 : Blo 1813608 3876407 := bstep (se 1 (by rfl) ⟨2907305, by rfl⟩ : syracuseStep 3876407 = 5814611) B5814611
theorem B27928217 : Blo 1813608 27928217 := bstep (se 2 (by rfl) ⟨10473081, by rfl⟩ : syracuseStep 27928217 = 20946163) B20946163
theorem B2721545 : Blo 1813608 2721545 := bstep (se 2 (by rfl) ⟨1020579, by rfl⟩ : syracuseStep 2721545 = 2041159) B2041159
theorem B11626685 : Blo 1813608 11626685 := bstep (se 3 (by rfl) ⟨2180003, by rfl⟩ : syracuseStep 11626685 = 4360007) B4360007
theorem B9185723 : Blo 1813608 9185723 := bstep (se 1 (by rfl) ⟨6889292, by rfl⟩ : syracuseStep 9185723 = 13778585) B13778585
theorem B4082345 : Blo 1813608 4082345 := bstep (se 2 (by rfl) ⟨1530879, by rfl⟩ : syracuseStep 4082345 = 3061759) B3061759
theorem B2722559 : Blo 1813608 2722559 := bstep (se 1 (by rfl) ⟨2041919, by rfl⟩ : syracuseStep 2722559 = 4083839) B4083839
theorem B6122303 : Blo 1813608 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B13773725 : Blo 1813608 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B20942059 : Blo 1813608 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B1813951 : Blo 1813608 1813951 := bstep (se 1 (by rfl) ⟨1360463, by rfl⟩ : syracuseStep 1813951 = 2720927) B2720927
theorem B4083155 : Blo 1813608 4083155 := bstep (se 1 (by rfl) ⟨3062366, by rfl⟩ : syracuseStep 4083155 = 6124733) B6124733
theorem B16559657 : Blo 1813608 16559657 := bstep (se 2 (by rfl) ⟨6209871, by rfl⟩ : syracuseStep 16559657 = 12419743) B12419743
theorem B1814223 : Blo 1813608 1814223 := bstep (se 1 (by rfl) ⟨1360667, by rfl⟩ : syracuseStep 1814223 = 2721335) B2721335
theorem B4902619 : Blo 1813608 4902619 := bstep (se 1 (by rfl) ⟨3676964, by rfl⟩ : syracuseStep 4902619 = 7353929) B7353929
theorem B4083425 : Blo 1813608 4083425 := bstep (se 2 (by rfl) ⟨1531284, by rfl⟩ : syracuseStep 4083425 = 3062569) B3062569
theorem B1814255 : Blo 1813608 1814255 := bstep (se 1 (by rfl) ⟨1360691, by rfl⟩ : syracuseStep 1814255 = 2721383) B2721383
theorem B4083623 : Blo 1813608 4083623 := bstep (se 1 (by rfl) ⟨3062717, by rfl⟩ : syracuseStep 4083623 = 6125435) B6125435
theorem B11620351 : Blo 1813608 11620351 := bstep (se 1 (by rfl) ⟨8715263, by rfl⟩ : syracuseStep 11620351 = 17430527) B17430527
theorem B1814527 : Blo 1813608 1814527 := bstep (se 1 (by rfl) ⟨1360895, by rfl⟩ : syracuseStep 1814527 = 2721791) B2721791
theorem B1814687 : Blo 1813608 1814687 := bstep (se 1 (by rfl) ⟨1361015, by rfl⟩ : syracuseStep 1814687 = 2722031) B2722031
theorem B1815023 : Blo 1813608 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B1815087 : Blo 1813608 1815087 := bstep (se 1 (by rfl) ⟨1361315, by rfl⟩ : syracuseStep 1815087 = 2722631) B2722631
theorem B15495785 : Blo 1813608 15495785 := bstep (se 2 (by rfl) ⟨5810919, by rfl⟩ : syracuseStep 15495785 = 11621839) B11621839
theorem B1815199 : Blo 1813608 1815199 := bstep (se 1 (by rfl) ⟨1361399, by rfl⟩ : syracuseStep 1815199 = 2722799) B2722799
theorem B55841561 : Blo 1813608 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B1815551 : Blo 1813608 1815551 := bstep (se 1 (by rfl) ⟨1361663, by rfl⟩ : syracuseStep 1815551 = 2723327) B2723327
theorem B245298293 : Blo 1813608 245298293 := bstep (se 5 (by rfl) ⟨11498357, by rfl⟩ : syracuseStep 245298293 = 22996715) B22996715
theorem B26162351 : Blo 1813608 26162351 := bstep (se 1 (by rfl) ⟨19621763, by rfl⟩ : syracuseStep 26162351 = 39243527) B39243527
theorem B39244985 : Blo 1813608 39244985 := bstep (se 2 (by rfl) ⟨14716869, by rfl⟩ : syracuseStep 39244985 = 29433739) B29433739
theorem B4658399 : Blo 1813608 4658399 := bstep (se 1 (by rfl) ⟨3493799, by rfl⟩ : syracuseStep 4658399 = 6987599) B6987599
theorem B7755223 : Blo 1813608 7755223 := bstep (se 1 (by rfl) ⟨5816417, by rfl⟩ : syracuseStep 7755223 = 11632835) B11632835
theorem B23263361 : Blo 1813608 23263361 := bstep (se 2 (by rfl) ⟨8723760, by rfl⟩ : syracuseStep 23263361 = 17447521) B17447521
theorem B13777127 : Blo 1813608 13777127 := bstep (se 1 (by rfl) ⟨10332845, by rfl⟩ : syracuseStep 13777127 = 20665691) B20665691
theorem B16554223 : Blo 1813608 16554223 := bstep (se 1 (by rfl) ⟨12415667, by rfl⟩ : syracuseStep 16554223 = 24831335) B24831335
theorem B4905407 : Blo 1813608 4905407 := bstep (se 1 (by rfl) ⟨3679055, by rfl⟩ : syracuseStep 4905407 = 7358111) B7358111
theorem B7355519 : Blo 1813608 7355519 := bstep (se 1 (by rfl) ⟨5516639, by rfl⟩ : syracuseStep 7355519 = 11033279) B11033279
theorem B6888671 : Blo 1813608 6888671 := bstep (se 1 (by rfl) ⟨5166503, by rfl⟩ : syracuseStep 6888671 = 10333007) B10333007
theorem B15506923 : Blo 1813608 15506923 := bstep (se 1 (by rfl) ⟨11630192, by rfl⟩ : syracuseStep 15506923 = 23260385) B23260385
theorem B27926009 : Blo 1813608 27926009 := bstep (se 2 (by rfl) ⟨10472253, by rfl⟩ : syracuseStep 27926009 = 20944507) B20944507
theorem B4358441 : Blo 1813608 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B10330523 : Blo 1813608 10330523 := bstep (se 1 (by rfl) ⟨7747892, by rfl⟩ : syracuseStep 10330523 = 15495785) B15495785
theorem B17441567 : Blo 1813608 17441567 := bstep (se 1 (by rfl) ⟨13081175, by rfl⟩ : syracuseStep 17441567 = 26162351) B26162351
theorem B3105599 : Blo 1813608 3105599 := bstep (se 1 (by rfl) ⟨2329199, by rfl⟩ : syracuseStep 3105599 = 4658399) B4658399
theorem B2720615 : Blo 1813608 2720615 := bstep (se 1 (by rfl) ⟨2040461, by rfl⟩ : syracuseStep 2720615 = 4080923) B4080923
theorem B15508907 : Blo 1813608 15508907 := bstep (se 1 (by rfl) ⟨11631680, by rfl⟩ : syracuseStep 15508907 = 23263361) B23263361
theorem B7751123 : Blo 1813608 7751123 := bstep (se 1 (by rfl) ⟨5813342, by rfl⟩ : syracuseStep 7751123 = 11626685) B11626685
theorem B9184751 : Blo 1813608 9184751 := bstep (se 1 (by rfl) ⟨6888563, by rfl⟩ : syracuseStep 9184751 = 13777127) B13777127
theorem B2721563 : Blo 1813608 2721563 := bstep (se 1 (by rfl) ⟨2041172, by rfl⟩ : syracuseStep 2721563 = 4082345) B4082345
theorem B4081535 : Blo 1813608 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B10340297 : Blo 1813608 10340297 := bstep (se 2 (by rfl) ⟨3877611, by rfl⟩ : syracuseStep 10340297 = 7755223) B7755223
theorem B2722103 : Blo 1813608 2722103 := bstep (se 1 (by rfl) ⟨2041577, by rfl⟩ : syracuseStep 2722103 = 4083155) B4083155
theorem B2722283 : Blo 1813608 2722283 := bstep (se 1 (by rfl) ⟨2041712, by rfl⟩ : syracuseStep 2722283 = 4083425) B4083425
theorem B2722415 : Blo 1813608 2722415 := bstep (se 1 (by rfl) ⟨2041811, by rfl⟩ : syracuseStep 2722415 = 4083623) B4083623
theorem B15493801 : Blo 1813608 15493801 := bstep (se 2 (by rfl) ⟨5810175, by rfl⟩ : syracuseStep 15493801 = 11620351) B11620351
theorem B22072297 : Blo 1813608 22072297 := bstep (se 2 (by rfl) ⟨8277111, by rfl⟩ : syracuseStep 22072297 = 16554223) B16554223
theorem B37227707 : Blo 1813608 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B163532195 : Blo 1813608 163532195 := bstep (se 1 (by rfl) ⟨122649146, by rfl⟩ : syracuseStep 163532195 = 245298293) B245298293
theorem B17673643 : Blo 1813608 17673643 := bstep (se 1 (by rfl) ⟨13255232, by rfl⟩ : syracuseStep 17673643 = 26510465) B26510465
theorem B2584271 : Blo 1813608 2584271 := bstep (se 1 (by rfl) ⟨1938203, by rfl⟩ : syracuseStep 2584271 = 3876407) B3876407
theorem B1814363 : Blo 1813608 1814363 := bstep (se 1 (by rfl) ⟨1360772, by rfl⟩ : syracuseStep 1814363 = 2721545) B2721545
theorem B6123815 : Blo 1813608 6123815 := bstep (se 1 (by rfl) ⟨4592861, by rfl⟩ : syracuseStep 6123815 = 9185723) B9185723
theorem B27922745 : Blo 1813608 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B1815039 : Blo 1813608 1815039 := bstep (se 1 (by rfl) ⟨1361279, by rfl⟩ : syracuseStep 1815039 = 2722559) B2722559
theorem B9810557 : Blo 1813608 9810557 := bstep (se 3 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 9810557 = 3678959) B3678959
theorem B4903679 : Blo 1813608 4903679 := bstep (se 1 (by rfl) ⟨3677759, by rfl⟩ : syracuseStep 4903679 = 7355519) B7355519
theorem B4592447 : Blo 1813608 4592447 := bstep (se 1 (by rfl) ⟨3444335, by rfl⟩ : syracuseStep 4592447 = 6888671) B6888671
theorem B5813149 : Blo 1813608 5813149 := bstep (se 3 (by rfl) ⟨1089965, by rfl⟩ : syracuseStep 5813149 = 2179931) B2179931
theorem B18617339 : Blo 1813608 18617339 := bstep (se 1 (by rfl) ⟨13963004, by rfl⟩ : syracuseStep 18617339 = 27926009) B27926009
theorem B11039771 : Blo 1813608 11039771 := bstep (se 1 (by rfl) ⟨8279828, by rfl⟩ : syracuseStep 11039771 = 16559657) B16559657
theorem B18617795 : Blo 1813608 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B26163323 : Blo 1813608 26163323 := bstep (se 1 (by rfl) ⟨19622492, by rfl⟩ : syracuseStep 26163323 = 39244985) B39244985
theorem B18618811 : Blo 1813608 18618811 := bstep (se 1 (by rfl) ⟨13964108, by rfl⟩ : syracuseStep 18618811 = 27928217) B27928217
theorem B13081085 : Blo 1813608 13081085 := bstep (se 3 (by rfl) ⟨2452703, by rfl⟩ : syracuseStep 13081085 = 4905407) B4905407
theorem B9182483 : Blo 1813608 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B20675897 : Blo 1813608 20675897 := bstep (se 2 (by rfl) ⟨7753461, by rfl⟩ : syracuseStep 20675897 = 15506923) B15506923
theorem B6536825 : Blo 1813608 6536825 := bstep (se 2 (by rfl) ⟨2451309, by rfl⟩ : syracuseStep 6536825 = 4902619) B4902619
theorem B3269119 : Blo 1813608 3269119 := bstep (se 1 (by rfl) ⟨2451839, by rfl⟩ : syracuseStep 3269119 = 4903679) B4903679
theorem B12411559 : Blo 1813608 12411559 := bstep (se 1 (by rfl) ⟨9308669, by rfl⟩ : syracuseStep 12411559 = 18617339) B18617339
theorem B10339271 : Blo 1813608 10339271 := bstep (se 1 (by rfl) ⟨7754453, by rfl⟩ : syracuseStep 10339271 = 15508907) B15508907
theorem B12411863 : Blo 1813608 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B7750865 : Blo 1813608 7750865 := bstep (se 2 (by rfl) ⟨2906574, by rfl⟩ : syracuseStep 7750865 = 5813149) B5813149
theorem B2721023 : Blo 1813608 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B17442215 : Blo 1813608 17442215 := bstep (se 1 (by rfl) ⟨13081661, by rfl⟩ : syracuseStep 17442215 = 26163323) B26163323
theorem B6891389 : Blo 1813608 6891389 := bstep (se 3 (by rfl) ⟨1292135, by rfl⟩ : syracuseStep 6891389 = 2584271) B2584271
theorem B6121655 : Blo 1813608 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B109021463 : Blo 1813608 109021463 := bstep (se 1 (by rfl) ⟨81766097, by rfl⟩ : syracuseStep 109021463 = 163532195) B163532195
theorem B4082543 : Blo 1813608 4082543 := bstep (se 1 (by rfl) ⟨3061907, by rfl⟩ : syracuseStep 4082543 = 6123815) B6123815
theorem B6540371 : Blo 1813608 6540371 := bstep (se 1 (by rfl) ⟨4905278, by rfl⟩ : syracuseStep 6540371 = 9810557) B9810557
theorem B11627711 : Blo 1813608 11627711 := bstep (se 1 (by rfl) ⟨8720783, by rfl⟩ : syracuseStep 11627711 = 17441567) B17441567
theorem B1813743 : Blo 1813608 1813743 := bstep (se 1 (by rfl) ⟨1360307, by rfl⟩ : syracuseStep 1813743 = 2720615) B2720615
theorem B74460653 : Blo 1813608 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B6123167 : Blo 1813608 6123167 := bstep (se 1 (by rfl) ⟨4592375, by rfl⟩ : syracuseStep 6123167 = 9184751) B9184751
theorem B1814375 : Blo 1813608 1814375 := bstep (se 1 (by rfl) ⟨1360781, by rfl⟩ : syracuseStep 1814375 = 2721563) B2721563
theorem B6893531 : Blo 1813608 6893531 := bstep (se 1 (by rfl) ⟨5170148, by rfl⟩ : syracuseStep 6893531 = 10340297) B10340297
theorem B29429729 : Blo 1813608 29429729 := bstep (se 2 (by rfl) ⟨11036148, by rfl⟩ : syracuseStep 29429729 = 22072297) B22072297
theorem B1814735 : Blo 1813608 1814735 := bstep (se 1 (by rfl) ⟨1361051, by rfl⟩ : syracuseStep 1814735 = 2722103) B2722103
theorem B1814855 : Blo 1813608 1814855 := bstep (se 1 (by rfl) ⟨1361141, by rfl⟩ : syracuseStep 1814855 = 2722283) B2722283
theorem B8720723 : Blo 1813608 8720723 := bstep (se 1 (by rfl) ⟨6540542, by rfl⟩ : syracuseStep 8720723 = 13081085) B13081085
theorem B1814943 : Blo 1813608 1814943 := bstep (se 1 (by rfl) ⟨1361207, by rfl⟩ : syracuseStep 1814943 = 2722415) B2722415
theorem B23564857 : Blo 1813608 23564857 := bstep (se 2 (by rfl) ⟨8836821, by rfl⟩ : syracuseStep 23564857 = 17673643) B17673643
theorem B24818471 : Blo 1813608 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B13783931 : Blo 1813608 13783931 := bstep (se 1 (by rfl) ⟨10337948, by rfl⟩ : syracuseStep 13783931 = 20675897) B20675897
theorem B99300325 : Blo 1813608 99300325 := bstep (se 4 (by rfl) ⟨9309405, by rfl⟩ : syracuseStep 99300325 = 18618811) B18618811
theorem B29439389 : Blo 1813608 29439389 := bstep (se 3 (by rfl) ⟨5519885, by rfl⟩ : syracuseStep 29439389 = 11039771) B11039771
theorem B2905627 : Blo 1813608 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B6887015 : Blo 1813608 6887015 := bstep (se 1 (by rfl) ⟨5165261, by rfl⟩ : syracuseStep 6887015 = 10330523) B10330523
theorem B3061631 : Blo 1813608 3061631 := bstep (se 1 (by rfl) ⟨2296223, by rfl⟩ : syracuseStep 3061631 = 4592447) B4592447
theorem B20658401 : Blo 1813608 20658401 := bstep (se 2 (by rfl) ⟨7746900, by rfl⟩ : syracuseStep 20658401 = 15493801) B15493801
theorem B5167415 : Blo 1813608 5167415 := bstep (se 1 (by rfl) ⟨3875561, by rfl⟩ : syracuseStep 5167415 = 7751123) B7751123
theorem B8281597 : Blo 1813608 8281597 := bstep (se 3 (by rfl) ⟨1552799, by rfl⟩ : syracuseStep 8281597 = 3105599) B3105599
theorem B4357883 : Blo 1813608 4357883 := bstep (se 1 (by rfl) ⟨3268412, by rfl⟩ : syracuseStep 4357883 = 6536825) B6536825
theorem B8274575 : Blo 1813608 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B4358825 : Blo 1813608 4358825 := bstep (se 2 (by rfl) ⟨1634559, by rfl⟩ : syracuseStep 4358825 = 3269119) B3269119
theorem B16548745 : Blo 1813608 16548745 := bstep (se 2 (by rfl) ⟨6205779, by rfl⟩ : syracuseStep 16548745 = 12411559) B12411559
theorem B2041087 : Blo 1813608 2041087 := bstep (se 1 (by rfl) ⟨1530815, by rfl⟩ : syracuseStep 2041087 = 3061631) B3061631
theorem B132400433 : Blo 1813608 132400433 := bstep (se 2 (by rfl) ⟨49650162, by rfl⟩ : syracuseStep 132400433 = 99300325) B99300325
theorem B4081103 : Blo 1813608 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B13772267 : Blo 1813608 13772267 := bstep (se 1 (by rfl) ⟨10329200, by rfl⟩ : syracuseStep 13772267 = 20658401) B20658401
theorem B72680975 : Blo 1813608 72680975 := bstep (se 1 (by rfl) ⟨54510731, by rfl⟩ : syracuseStep 72680975 = 109021463) B109021463
theorem B2721695 : Blo 1813608 2721695 := bstep (se 1 (by rfl) ⟨2041271, by rfl⟩ : syracuseStep 2721695 = 4082543) B4082543
theorem B4360247 : Blo 1813608 4360247 := bstep (se 1 (by rfl) ⟨3270185, by rfl⟩ : syracuseStep 4360247 = 6540371) B6540371
theorem B7751807 : Blo 1813608 7751807 := bstep (se 1 (by rfl) ⟨5813855, by rfl⟩ : syracuseStep 7751807 = 11627711) B11627711
theorem B4082111 : Blo 1813608 4082111 := bstep (se 1 (by rfl) ⟨3061583, by rfl⟩ : syracuseStep 4082111 = 6123167) B6123167
theorem B6892847 : Blo 1813608 6892847 := bstep (se 1 (by rfl) ⟨5169635, by rfl⟩ : syracuseStep 6892847 = 10339271) B10339271
theorem B31419809 : Blo 1813608 31419809 := bstep (se 2 (by rfl) ⟨11782428, by rfl⟩ : syracuseStep 31419809 = 23564857) B23564857
theorem B1814015 : Blo 1813608 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B11628143 : Blo 1813608 11628143 := bstep (se 1 (by rfl) ⟨8721107, by rfl⟩ : syracuseStep 11628143 = 17442215) B17442215
theorem B4591343 : Blo 1813608 4591343 := bstep (se 1 (by rfl) ⟨3443507, by rfl⟩ : syracuseStep 4591343 = 6887015) B6887015
theorem B3444943 : Blo 1813608 3444943 := bstep (se 1 (by rfl) ⟨2583707, by rfl⟩ : syracuseStep 3444943 = 5167415) B5167415
theorem B49640435 : Blo 1813608 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B2905255 : Blo 1813608 2905255 := bstep (se 1 (by rfl) ⟨2178941, by rfl⟩ : syracuseStep 2905255 = 4357883) B4357883
theorem B16545647 : Blo 1813608 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B9189287 : Blo 1813608 9189287 := bstep (se 1 (by rfl) ⟨6891965, by rfl⟩ : syracuseStep 9189287 = 13783931) B13783931
theorem B5167243 : Blo 1813608 5167243 := bstep (se 1 (by rfl) ⟨3875432, by rfl⟩ : syracuseStep 5167243 = 7750865) B7750865
theorem B23255261 : Blo 1813608 23255261 := bstep (se 3 (by rfl) ⟨4360361, by rfl⟩ : syracuseStep 23255261 = 8720723) B8720723
theorem B19626259 : Blo 1813608 19626259 := bstep (se 1 (by rfl) ⟨14719694, by rfl⟩ : syracuseStep 19626259 = 29439389) B29439389
theorem B4594259 : Blo 1813608 4594259 := bstep (se 1 (by rfl) ⟨3445694, by rfl⟩ : syracuseStep 4594259 = 6891389) B6891389
theorem B11042129 : Blo 1813608 11042129 := bstep (se 2 (by rfl) ⟨4140798, by rfl⟩ : syracuseStep 11042129 = 8281597) B8281597
theorem B3874169 : Blo 1813608 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B4595687 : Blo 1813608 4595687 := bstep (se 1 (by rfl) ⟨3446765, by rfl⟩ : syracuseStep 4595687 = 6893531) B6893531
theorem B19619819 : Blo 1813608 19619819 := bstep (se 1 (by rfl) ⟨14714864, by rfl⟩ : syracuseStep 19619819 = 29429729) B29429729
theorem B6889657 : Blo 1813608 6889657 := bstep (se 2 (by rfl) ⟨2583621, by rfl⟩ : syracuseStep 6889657 = 5167243) B5167243
theorem B2720735 : Blo 1813608 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B2721407 : Blo 1813608 2721407 := bstep (se 1 (by rfl) ⟨2041055, by rfl⟩ : syracuseStep 2721407 = 4082111) B4082111
theorem B2721449 : Blo 1813608 2721449 := bstep (se 2 (by rfl) ⟨1020543, by rfl⟩ : syracuseStep 2721449 = 2041087) B2041087
theorem B2582779 : Blo 1813608 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B7752095 : Blo 1813608 7752095 := bstep (se 1 (by rfl) ⟨5814071, by rfl⟩ : syracuseStep 7752095 = 11628143) B11628143
theorem B26168345 : Blo 1813608 26168345 := bstep (se 2 (by rfl) ⟨9813129, by rfl⟩ : syracuseStep 26168345 = 19626259) B19626259
theorem B29445677 : Blo 1813608 29445677 := bstep (se 3 (by rfl) ⟨5521064, by rfl⟩ : syracuseStep 29445677 = 11042129) B11042129
theorem B22064993 : Blo 1813608 22064993 := bstep (se 2 (by rfl) ⟨8274372, by rfl⟩ : syracuseStep 22064993 = 16548745) B16548745
theorem B11030431 : Blo 1813608 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B1814463 : Blo 1813608 1814463 := bstep (se 1 (by rfl) ⟨1360847, by rfl⟩ : syracuseStep 1814463 = 2721695) B2721695
theorem B15503507 : Blo 1813608 15503507 := bstep (se 1 (by rfl) ⟨11627630, by rfl⟩ : syracuseStep 15503507 = 23255261) B23255261
theorem B22065533 : Blo 1813608 22065533 := bstep (se 3 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 22065533 = 8274575) B8274575
theorem B3060895 : Blo 1813608 3060895 := bstep (se 1 (by rfl) ⟨2295671, by rfl⟩ : syracuseStep 3060895 = 4591343) B4591343
theorem B13079879 : Blo 1813608 13079879 := bstep (se 1 (by rfl) ⟨9809909, by rfl⟩ : syracuseStep 13079879 = 19619819) B19619819
theorem B4593257 : Blo 1813608 4593257 := bstep (se 2 (by rfl) ⟨1722471, by rfl⟩ : syracuseStep 4593257 = 3444943) B3444943
theorem B2905883 : Blo 1813608 2905883 := bstep (se 1 (by rfl) ⟨2179412, by rfl⟩ : syracuseStep 2905883 = 4358825) B4358825
theorem B33093623 : Blo 1813608 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B88266955 : Blo 1813608 88266955 := bstep (se 1 (by rfl) ⟨66200216, by rfl⟩ : syracuseStep 88266955 = 132400433) B132400433
theorem B9181511 : Blo 1813608 9181511 := bstep (se 1 (by rfl) ⟨6886133, by rfl⟩ : syracuseStep 9181511 = 13772267) B13772267
theorem B48453983 : Blo 1813608 48453983 := bstep (se 1 (by rfl) ⟨36340487, by rfl⟩ : syracuseStep 48453983 = 72680975) B72680975
theorem B6126191 : Blo 1813608 6126191 := bstep (se 1 (by rfl) ⟨4594643, by rfl⟩ : syracuseStep 6126191 = 9189287) B9189287
theorem B2906831 : Blo 1813608 2906831 := bstep (se 1 (by rfl) ⟨2180123, by rfl⟩ : syracuseStep 2906831 = 4360247) B4360247
theorem B5167871 : Blo 1813608 5167871 := bstep (se 1 (by rfl) ⟨3875903, by rfl⟩ : syracuseStep 5167871 = 7751807) B7751807
theorem B3873673 : Blo 1813608 3873673 := bstep (se 2 (by rfl) ⟨1452627, by rfl⟩ : syracuseStep 3873673 = 2905255) B2905255
theorem B3062839 : Blo 1813608 3062839 := bstep (se 1 (by rfl) ⟨2297129, by rfl⟩ : syracuseStep 3062839 = 4594259) B4594259
theorem B4595231 : Blo 1813608 4595231 := bstep (se 1 (by rfl) ⟨3446423, by rfl⟩ : syracuseStep 4595231 = 6892847) B6892847
theorem B20946539 : Blo 1813608 20946539 := bstep (se 1 (by rfl) ⟨15709904, by rfl⟩ : syracuseStep 20946539 = 31419809) B31419809
theorem B3063791 : Blo 1813608 3063791 := bstep (se 1 (by rfl) ⟨2297843, by rfl⟩ : syracuseStep 3063791 = 4595687) B4595687
theorem B22062415 : Blo 1813608 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B4081193 : Blo 1813608 4081193 := bstep (se 2 (by rfl) ⟨1530447, by rfl⟩ : syracuseStep 4081193 = 3060895) B3060895
theorem B6121007 : Blo 1813608 6121007 := bstep (se 1 (by rfl) ⟨4590755, by rfl⟩ : syracuseStep 6121007 = 9181511) B9181511
theorem B32302655 : Blo 1813608 32302655 := bstep (se 1 (by rfl) ⟨24226991, by rfl⟩ : syracuseStep 32302655 = 48453983) B48453983
theorem B19630451 : Blo 1813608 19630451 := bstep (se 1 (by rfl) ⟨14722838, by rfl⟩ : syracuseStep 19630451 = 29445677) B29445677
theorem B14707241 : Blo 1813608 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B2042527 : Blo 1813608 2042527 := bstep (se 1 (by rfl) ⟨1531895, by rfl⟩ : syracuseStep 2042527 = 3063791) B3063791
theorem B9186209 : Blo 1813608 9186209 := bstep (se 2 (by rfl) ⟨3444828, by rfl⟩ : syracuseStep 9186209 = 6889657) B6889657
theorem B117689273 : Blo 1813608 117689273 := bstep (se 2 (by rfl) ⟨44133477, by rfl⟩ : syracuseStep 117689273 = 88266955) B88266955
theorem B3443705 : Blo 1813608 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B1813823 : Blo 1813608 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B8719919 : Blo 1813608 8719919 := bstep (se 1 (by rfl) ⟨6539939, by rfl⟩ : syracuseStep 8719919 = 13079879) B13079879
theorem B1814271 : Blo 1813608 1814271 := bstep (se 1 (by rfl) ⟨1360703, by rfl⟩ : syracuseStep 1814271 = 2721407) B2721407
theorem B1814299 : Blo 1813608 1814299 := bstep (se 1 (by rfl) ⟨1360724, by rfl⟩ : syracuseStep 1814299 = 2721449) B2721449
theorem B5164897 : Blo 1813608 5164897 := bstep (se 2 (by rfl) ⟨1936836, by rfl⟩ : syracuseStep 5164897 = 3873673) B3873673
theorem B1937255 : Blo 1813608 1937255 := bstep (se 1 (by rfl) ⟨1452941, by rfl⟩ : syracuseStep 1937255 = 2905883) B2905883
theorem B4083785 : Blo 1813608 4083785 := bstep (se 2 (by rfl) ⟨1531419, by rfl⟩ : syracuseStep 4083785 = 3062839) B3062839
theorem B55857437 : Blo 1813608 55857437 := bstep (se 3 (by rfl) ⟨10473269, by rfl⟩ : syracuseStep 55857437 = 20946539) B20946539
theorem B4084127 : Blo 1813608 4084127 := bstep (se 1 (by rfl) ⟨3063095, by rfl⟩ : syracuseStep 4084127 = 6126191) B6126191
theorem B1937887 : Blo 1813608 1937887 := bstep (se 1 (by rfl) ⟨1453415, by rfl⟩ : syracuseStep 1937887 = 2906831) B2906831
theorem B3445247 : Blo 1813608 3445247 := bstep (se 1 (by rfl) ⟨2583935, by rfl⟩ : syracuseStep 3445247 = 5167871) B5167871
theorem B17445563 : Blo 1813608 17445563 := bstep (se 1 (by rfl) ⟨13084172, by rfl⟩ : syracuseStep 17445563 = 26168345) B26168345
theorem B14709995 : Blo 1813608 14709995 := bstep (se 1 (by rfl) ⟨11032496, by rfl⟩ : syracuseStep 14709995 = 22064993) B22064993
theorem B10335671 : Blo 1813608 10335671 := bstep (se 1 (by rfl) ⟨7751753, by rfl⟩ : syracuseStep 10335671 = 15503507) B15503507
theorem B14710355 : Blo 1813608 14710355 := bstep (se 1 (by rfl) ⟨11032766, by rfl⟩ : syracuseStep 14710355 = 22065533) B22065533
theorem B3062171 : Blo 1813608 3062171 := bstep (se 1 (by rfl) ⟨2296628, by rfl⟩ : syracuseStep 3062171 = 4593257) B4593257
theorem B5168063 : Blo 1813608 5168063 := bstep (se 1 (by rfl) ⟨3876047, by rfl⟩ : syracuseStep 5168063 = 7752095) B7752095
theorem B3063487 : Blo 1813608 3063487 := bstep (se 1 (by rfl) ⟨2297615, by rfl⟩ : syracuseStep 3063487 = 4595231) B4595231
theorem B9806663 : Blo 1813608 9806663 := bstep (se 1 (by rfl) ⟨7354997, by rfl⟩ : syracuseStep 9806663 = 14709995) B14709995
theorem B6890447 : Blo 1813608 6890447 := bstep (se 1 (by rfl) ⟨5167835, by rfl⟩ : syracuseStep 6890447 = 10335671) B10335671
theorem B2720795 : Blo 1813608 2720795 := bstep (se 1 (by rfl) ⟨2040596, by rfl⟩ : syracuseStep 2720795 = 4081193) B4081193
theorem B4080671 : Blo 1813608 4080671 := bstep (se 1 (by rfl) ⟨3060503, by rfl⟩ : syracuseStep 4080671 = 6121007) B6121007
theorem B9806903 : Blo 1813608 9806903 := bstep (se 1 (by rfl) ⟨7355177, by rfl⟩ : syracuseStep 9806903 = 14710355) B14710355
theorem B2041447 : Blo 1813608 2041447 := bstep (se 1 (by rfl) ⟨1531085, by rfl⟩ : syracuseStep 2041447 = 3062171) B3062171
theorem B2295803 : Blo 1813608 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B13781501 : Blo 1813608 13781501 := bstep (se 3 (by rfl) ⟨2584031, by rfl⟩ : syracuseStep 13781501 = 5168063) B5168063
theorem B2722523 : Blo 1813608 2722523 := bstep (se 1 (by rfl) ⟨2041892, by rfl⟩ : syracuseStep 2722523 = 4083785) B4083785
theorem B2722751 : Blo 1813608 2722751 := bstep (se 1 (by rfl) ⟨2042063, by rfl⟩ : syracuseStep 2722751 = 4084127) B4084127
theorem B2296831 : Blo 1813608 2296831 := bstep (se 1 (by rfl) ⟨1722623, by rfl⟩ : syracuseStep 2296831 = 3445247) B3445247
theorem B2723369 : Blo 1813608 2723369 := bstep (se 2 (by rfl) ⟨1021263, by rfl⟩ : syracuseStep 2723369 = 2042527) B2042527
theorem B13086967 : Blo 1813608 13086967 := bstep (se 1 (by rfl) ⟨9815225, by rfl⟩ : syracuseStep 13086967 = 19630451) B19630451
theorem B6124139 : Blo 1813608 6124139 := bstep (se 1 (by rfl) ⟨4593104, by rfl⟩ : syracuseStep 6124139 = 9186209) B9186209
theorem B78459515 : Blo 1813608 78459515 := bstep (se 1 (by rfl) ⟨58844636, by rfl⟩ : syracuseStep 78459515 = 117689273) B117689273
theorem B4084649 : Blo 1813608 4084649 := bstep (se 2 (by rfl) ⟨1531743, by rfl⟩ : syracuseStep 4084649 = 3063487) B3063487
theorem B5166013 : Blo 1813608 5166013 := bstep (se 3 (by rfl) ⟨968627, by rfl⟩ : syracuseStep 5166013 = 1937255) B1937255
theorem B5813279 : Blo 1813608 5813279 := bstep (se 1 (by rfl) ⟨4359959, by rfl⟩ : syracuseStep 5813279 = 8719919) B8719919
theorem B6886529 : Blo 1813608 6886529 := bstep (se 2 (by rfl) ⟨2582448, by rfl⟩ : syracuseStep 6886529 = 5164897) B5164897
theorem B10335397 : Blo 1813608 10335397 := bstep (se 4 (by rfl) ⟨968943, by rfl⟩ : syracuseStep 10335397 = 1937887) B1937887
theorem B37238291 : Blo 1813608 37238291 := bstep (se 1 (by rfl) ⟨27928718, by rfl⟩ : syracuseStep 37238291 = 55857437) B55857437
theorem B11630375 : Blo 1813608 11630375 := bstep (se 1 (by rfl) ⟨8722781, by rfl⟩ : syracuseStep 11630375 = 17445563) B17445563
theorem B21535103 : Blo 1813608 21535103 := bstep (se 1 (by rfl) ⟨16151327, by rfl⟩ : syracuseStep 21535103 = 32302655) B32302655
theorem B9804827 : Blo 1813608 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B29416553 : Blo 1813608 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B17449289 : Blo 1813608 17449289 := bstep (se 2 (by rfl) ⟨6543483, by rfl⟩ : syracuseStep 17449289 = 13086967) B13086967
theorem B52306343 : Blo 1813608 52306343 := bstep (se 1 (by rfl) ⟨39229757, by rfl⟩ : syracuseStep 52306343 = 78459515) B78459515
theorem B6537775 : Blo 1813608 6537775 := bstep (se 1 (by rfl) ⟨4903331, by rfl⟩ : syracuseStep 6537775 = 9806663) B9806663
theorem B2720447 : Blo 1813608 2720447 := bstep (se 1 (by rfl) ⟨2040335, by rfl⟩ : syracuseStep 2720447 = 4080671) B4080671
theorem B3875519 : Blo 1813608 3875519 := bstep (se 1 (by rfl) ⟨2906639, by rfl⟩ : syracuseStep 3875519 = 5813279) B5813279
theorem B6537935 : Blo 1813608 6537935 := bstep (se 1 (by rfl) ⟨4903451, by rfl⟩ : syracuseStep 6537935 = 9806903) B9806903
theorem B57426941 : Blo 1813608 57426941 := bstep (se 3 (by rfl) ⟨10767551, by rfl⟩ : syracuseStep 57426941 = 21535103) B21535103
theorem B13780529 : Blo 1813608 13780529 := bstep (se 2 (by rfl) ⟨5167698, by rfl⟩ : syracuseStep 13780529 = 10335397) B10335397
theorem B2721929 : Blo 1813608 2721929 := bstep (se 2 (by rfl) ⟨1020723, by rfl⟩ : syracuseStep 2721929 = 2041447) B2041447
theorem B6122141 : Blo 1813608 6122141 := bstep (se 3 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 6122141 = 2295803) B2295803
theorem B4082759 : Blo 1813608 4082759 := bstep (se 1 (by rfl) ⟨3062069, by rfl⟩ : syracuseStep 4082759 = 6124139) B6124139
theorem B2723099 : Blo 1813608 2723099 := bstep (se 1 (by rfl) ⟨2042324, by rfl⟩ : syracuseStep 2723099 = 4084649) B4084649
theorem B1813863 : Blo 1813608 1813863 := bstep (se 1 (by rfl) ⟨1360397, by rfl⟩ : syracuseStep 1813863 = 2720795) B2720795
theorem B4591019 : Blo 1813608 4591019 := bstep (se 1 (by rfl) ⟨3443264, by rfl⟩ : syracuseStep 4591019 = 6886529) B6886529
theorem B24825527 : Blo 1813608 24825527 := bstep (se 1 (by rfl) ⟨18619145, by rfl⟩ : syracuseStep 24825527 = 37238291) B37238291
theorem B7753583 : Blo 1813608 7753583 := bstep (se 1 (by rfl) ⟨5815187, by rfl⟩ : syracuseStep 7753583 = 11630375) B11630375
theorem B9187667 : Blo 1813608 9187667 := bstep (se 1 (by rfl) ⟨6890750, by rfl⟩ : syracuseStep 9187667 = 13781501) B13781501
theorem B1815015 : Blo 1813608 1815015 := bstep (se 1 (by rfl) ⟨1361261, by rfl⟩ : syracuseStep 1815015 = 2722523) B2722523
theorem B1815167 : Blo 1813608 1815167 := bstep (se 1 (by rfl) ⟨1361375, by rfl⟩ : syracuseStep 1815167 = 2722751) B2722751
theorem B1815579 : Blo 1813608 1815579 := bstep (se 1 (by rfl) ⟨1361684, by rfl⟩ : syracuseStep 1815579 = 2723369) B2723369
theorem B4593631 : Blo 1813608 4593631 := bstep (se 1 (by rfl) ⟨3445223, by rfl⟩ : syracuseStep 4593631 = 6890447) B6890447
theorem B6888017 : Blo 1813608 6888017 := bstep (se 2 (by rfl) ⟨2583006, by rfl⟩ : syracuseStep 6888017 = 5166013) B5166013
theorem B3062441 : Blo 1813608 3062441 := bstep (se 2 (by rfl) ⟨1148415, by rfl⟩ : syracuseStep 3062441 = 2296831) B2296831
theorem B6536551 : Blo 1813608 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B19611035 : Blo 1813608 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B11632859 : Blo 1813608 11632859 := bstep (se 1 (by rfl) ⟨8724644, by rfl⟩ : syracuseStep 11632859 = 17449289) B17449289
theorem B4358623 : Blo 1813608 4358623 := bstep (se 1 (by rfl) ⟨3268967, by rfl⟩ : syracuseStep 4358623 = 6537935) B6537935
theorem B8717033 : Blo 1813608 8717033 := bstep (se 2 (by rfl) ⟨3268887, by rfl⟩ : syracuseStep 8717033 = 6537775) B6537775
theorem B4081427 : Blo 1813608 4081427 := bstep (se 1 (by rfl) ⟨3061070, by rfl⟩ : syracuseStep 4081427 = 6122141) B6122141
theorem B2041627 : Blo 1813608 2041627 := bstep (se 1 (by rfl) ⟨1531220, by rfl⟩ : syracuseStep 2041627 = 3062441) B3062441
theorem B2721839 : Blo 1813608 2721839 := bstep (se 1 (by rfl) ⟨2041379, by rfl⟩ : syracuseStep 2721839 = 4082759) B4082759
theorem B16550351 : Blo 1813608 16550351 := bstep (se 1 (by rfl) ⟨12412763, by rfl⟩ : syracuseStep 16550351 = 24825527) B24825527
theorem B1813631 : Blo 1813608 1813631 := bstep (se 1 (by rfl) ⟨1360223, by rfl⟩ : syracuseStep 1813631 = 2720447) B2720447
theorem B2583679 : Blo 1813608 2583679 := bstep (se 1 (by rfl) ⟨1937759, by rfl⟩ : syracuseStep 2583679 = 3875519) B3875519
theorem B9187019 : Blo 1813608 9187019 := bstep (se 1 (by rfl) ⟨6890264, by rfl⟩ : syracuseStep 9187019 = 13780529) B13780529
theorem B1814619 : Blo 1813608 1814619 := bstep (se 1 (by rfl) ⟨1360964, by rfl⟩ : syracuseStep 1814619 = 2721929) B2721929
theorem B4592011 : Blo 1813608 4592011 := bstep (se 1 (by rfl) ⟨3444008, by rfl⟩ : syracuseStep 4592011 = 6888017) B6888017
theorem B1815399 : Blo 1813608 1815399 := bstep (se 1 (by rfl) ⟨1361549, by rfl⟩ : syracuseStep 1815399 = 2723099) B2723099
theorem B3060679 : Blo 1813608 3060679 := bstep (se 1 (by rfl) ⟨2295509, by rfl⟩ : syracuseStep 3060679 = 4591019) B4591019
theorem B6124841 : Blo 1813608 6124841 := bstep (se 2 (by rfl) ⟨2296815, by rfl⟩ : syracuseStep 6124841 = 4593631) B4593631
theorem B153138509 : Blo 1813608 153138509 := bstep (se 3 (by rfl) ⟨28713470, by rfl⟩ : syracuseStep 153138509 = 57426941) B57426941
theorem B6125111 : Blo 1813608 6125111 := bstep (se 1 (by rfl) ⟨4593833, by rfl⟩ : syracuseStep 6125111 = 9187667) B9187667
theorem B34870895 : Blo 1813608 34870895 := bstep (se 1 (by rfl) ⟨26153171, by rfl⟩ : syracuseStep 34870895 = 52306343) B52306343
theorem B8715401 : Blo 1813608 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B13074023 : Blo 1813608 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B5169055 : Blo 1813608 5169055 := bstep (se 1 (by rfl) ⟨3876791, by rfl⟩ : syracuseStep 5169055 = 7753583) B7753583
theorem B2720951 : Blo 1813608 2720951 := bstep (se 1 (by rfl) ⟨2040713, by rfl⟩ : syracuseStep 2720951 = 4081427) B4081427
theorem B4080905 : Blo 1813608 4080905 := bstep (se 2 (by rfl) ⟨1530339, by rfl⟩ : syracuseStep 4080905 = 3060679) B3060679
theorem B5810267 : Blo 1813608 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B2722169 : Blo 1813608 2722169 := bstep (se 2 (by rfl) ⟨1020813, by rfl⟩ : syracuseStep 2722169 = 2041627) B2041627
theorem B6892073 : Blo 1813608 6892073 := bstep (se 2 (by rfl) ⟨2584527, by rfl⟩ : syracuseStep 6892073 = 5169055) B5169055
theorem B5811355 : Blo 1813608 5811355 := bstep (se 1 (by rfl) ⟨4358516, by rfl⟩ : syracuseStep 5811355 = 8717033) B8717033
theorem B6122681 : Blo 1813608 6122681 := bstep (se 2 (by rfl) ⟨2296005, by rfl⟩ : syracuseStep 6122681 = 4592011) B4592011
theorem B5811497 : Blo 1813608 5811497 := bstep (se 2 (by rfl) ⟨2179311, by rfl⟩ : syracuseStep 5811497 = 4358623) B4358623
theorem B4083227 : Blo 1813608 4083227 := bstep (se 1 (by rfl) ⟨3062420, by rfl⟩ : syracuseStep 4083227 = 6124841) B6124841
theorem B102092339 : Blo 1813608 102092339 := bstep (se 1 (by rfl) ⟨76569254, by rfl⟩ : syracuseStep 102092339 = 153138509) B153138509
theorem B4083407 : Blo 1813608 4083407 := bstep (se 1 (by rfl) ⟨3062555, by rfl⟩ : syracuseStep 4083407 = 6125111) B6125111
theorem B1814559 : Blo 1813608 1814559 := bstep (se 1 (by rfl) ⟨1360919, by rfl⟩ : syracuseStep 1814559 = 2721839) B2721839
theorem B3444905 : Blo 1813608 3444905 := bstep (se 2 (by rfl) ⟨1291839, by rfl⟩ : syracuseStep 3444905 = 2583679) B2583679
theorem B6124679 : Blo 1813608 6124679 := bstep (se 1 (by rfl) ⟨4593509, by rfl⟩ : syracuseStep 6124679 = 9187019) B9187019
theorem B7755239 : Blo 1813608 7755239 := bstep (se 1 (by rfl) ⟨5816429, by rfl⟩ : syracuseStep 7755239 = 11632859) B11632859
theorem B23247263 : Blo 1813608 23247263 := bstep (se 1 (by rfl) ⟨17435447, by rfl⟩ : syracuseStep 23247263 = 34870895) B34870895
theorem B11033567 : Blo 1813608 11033567 := bstep (se 1 (by rfl) ⟨8275175, by rfl⟩ : syracuseStep 11033567 = 16550351) B16550351
theorem B8716015 : Blo 1813608 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B2720603 : Blo 1813608 2720603 := bstep (se 1 (by rfl) ⟨2040452, by rfl⟩ : syracuseStep 2720603 = 4080905) B4080905
theorem B5170159 : Blo 1813608 5170159 := bstep (se 1 (by rfl) ⟨3877619, by rfl⟩ : syracuseStep 5170159 = 7755239) B7755239
theorem B4081787 : Blo 1813608 4081787 := bstep (se 1 (by rfl) ⟨3061340, by rfl⟩ : syracuseStep 4081787 = 6122681) B6122681
theorem B2722151 : Blo 1813608 2722151 := bstep (se 1 (by rfl) ⟨2041613, by rfl⟩ : syracuseStep 2722151 = 4083227) B4083227
theorem B68061559 : Blo 1813608 68061559 := bstep (se 1 (by rfl) ⟨51046169, by rfl⟩ : syracuseStep 68061559 = 102092339) B102092339
theorem B2722271 : Blo 1813608 2722271 := bstep (se 1 (by rfl) ⟨2041703, by rfl⟩ : syracuseStep 2722271 = 4083407) B4083407
theorem B2296603 : Blo 1813608 2296603 := bstep (se 1 (by rfl) ⟨1722452, by rfl⟩ : syracuseStep 2296603 = 3444905) B3444905
theorem B4083119 : Blo 1813608 4083119 := bstep (se 1 (by rfl) ⟨3062339, by rfl⟩ : syracuseStep 4083119 = 6124679) B6124679
theorem B1813967 : Blo 1813608 1813967 := bstep (se 1 (by rfl) ⟨1360475, by rfl⟩ : syracuseStep 1813967 = 2720951) B2720951
theorem B1814779 : Blo 1813608 1814779 := bstep (se 1 (by rfl) ⟨1361084, by rfl⟩ : syracuseStep 1814779 = 2722169) B2722169
theorem B11621353 : Blo 1813608 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B3873511 : Blo 1813608 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B7748473 : Blo 1813608 7748473 := bstep (se 2 (by rfl) ⟨2905677, by rfl⟩ : syracuseStep 7748473 = 5811355) B5811355
theorem B15498175 : Blo 1813608 15498175 := bstep (se 1 (by rfl) ⟨11623631, by rfl⟩ : syracuseStep 15498175 = 23247263) B23247263
theorem B4594715 : Blo 1813608 4594715 := bstep (se 1 (by rfl) ⟨3446036, by rfl⟩ : syracuseStep 4594715 = 6892073) B6892073
theorem B7355711 : Blo 1813608 7355711 := bstep (se 1 (by rfl) ⟨5516783, by rfl⟩ : syracuseStep 7355711 = 11033567) B11033567
theorem B3874331 : Blo 1813608 3874331 := bstep (se 1 (by rfl) ⟨2905748, by rfl⟩ : syracuseStep 3874331 = 5811497) B5811497
theorem B10331297 : Blo 1813608 10331297 := bstep (se 2 (by rfl) ⟨3874236, by rfl⟩ : syracuseStep 10331297 = 7748473) B7748473
theorem B10331549 : Blo 1813608 10331549 := bstep (se 3 (by rfl) ⟨1937165, by rfl⟩ : syracuseStep 10331549 = 3874331) B3874331
theorem B2721191 : Blo 1813608 2721191 := bstep (se 1 (by rfl) ⟨2040893, by rfl⟩ : syracuseStep 2721191 = 4081787) B4081787
theorem B2722079 : Blo 1813608 2722079 := bstep (se 1 (by rfl) ⟨2041559, by rfl⟩ : syracuseStep 2722079 = 4083119) B4083119
theorem B1813735 : Blo 1813608 1813735 := bstep (se 1 (by rfl) ⟨1360301, by rfl⟩ : syracuseStep 1813735 = 2720603) B2720603
theorem B5164681 : Blo 1813608 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B20664233 : Blo 1813608 20664233 := bstep (se 2 (by rfl) ⟨7749087, by rfl⟩ : syracuseStep 20664233 = 15498175) B15498175
theorem B15495137 : Blo 1813608 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B6893545 : Blo 1813608 6893545 := bstep (se 2 (by rfl) ⟨2585079, by rfl⟩ : syracuseStep 6893545 = 5170159) B5170159
theorem B1814767 : Blo 1813608 1814767 := bstep (se 1 (by rfl) ⟨1361075, by rfl⟩ : syracuseStep 1814767 = 2722151) B2722151
theorem B1814847 : Blo 1813608 1814847 := bstep (se 1 (by rfl) ⟨1361135, by rfl⟩ : syracuseStep 1814847 = 2722271) B2722271
theorem B4903807 : Blo 1813608 4903807 := bstep (se 1 (by rfl) ⟨3677855, by rfl⟩ : syracuseStep 4903807 = 7355711) B7355711
theorem B90748745 : Blo 1813608 90748745 := bstep (se 2 (by rfl) ⟨34030779, by rfl⟩ : syracuseStep 90748745 = 68061559) B68061559
theorem B3062137 : Blo 1813608 3062137 := bstep (se 2 (by rfl) ⟨1148301, by rfl⟩ : syracuseStep 3062137 = 2296603) B2296603
theorem B3063143 : Blo 1813608 3063143 := bstep (se 1 (by rfl) ⟨2297357, by rfl⟩ : syracuseStep 3063143 = 4594715) B4594715
theorem B6538409 : Blo 1813608 6538409 := bstep (se 2 (by rfl) ⟨2451903, by rfl⟩ : syracuseStep 6538409 = 4903807) B4903807
theorem B60499163 : Blo 1813608 60499163 := bstep (se 1 (by rfl) ⟨45374372, by rfl⟩ : syracuseStep 60499163 = 90748745) B90748745
theorem B2042095 : Blo 1813608 2042095 := bstep (se 1 (by rfl) ⟨1531571, by rfl⟩ : syracuseStep 2042095 = 3063143) B3063143
theorem B4082849 : Blo 1813608 4082849 := bstep (se 2 (by rfl) ⟨1531068, by rfl⟩ : syracuseStep 4082849 = 3062137) B3062137
theorem B1814127 : Blo 1813608 1814127 := bstep (se 1 (by rfl) ⟨1360595, by rfl⟩ : syracuseStep 1814127 = 2721191) B2721191
theorem B1814719 : Blo 1813608 1814719 := bstep (se 1 (by rfl) ⟨1361039, by rfl⟩ : syracuseStep 1814719 = 2722079) B2722079
theorem B6886241 : Blo 1813608 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B13776155 : Blo 1813608 13776155 := bstep (se 1 (by rfl) ⟨10332116, by rfl⟩ : syracuseStep 13776155 = 20664233) B20664233
theorem B6887531 : Blo 1813608 6887531 := bstep (se 1 (by rfl) ⟨5165648, by rfl⟩ : syracuseStep 6887531 = 10331297) B10331297
theorem B6887699 : Blo 1813608 6887699 := bstep (se 1 (by rfl) ⟨5165774, by rfl⟩ : syracuseStep 6887699 = 10331549) B10331549
theorem B9191393 : Blo 1813608 9191393 := bstep (se 2 (by rfl) ⟨3446772, by rfl⟩ : syracuseStep 9191393 = 6893545) B6893545
theorem B10330091 : Blo 1813608 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B4358939 : Blo 1813608 4358939 := bstep (se 1 (by rfl) ⟨3269204, by rfl⟩ : syracuseStep 4358939 = 6538409) B6538409
theorem B9184103 : Blo 1813608 9184103 := bstep (se 1 (by rfl) ⟨6888077, by rfl⟩ : syracuseStep 9184103 = 13776155) B13776155
theorem B2721899 : Blo 1813608 2721899 := bstep (se 1 (by rfl) ⟨2041424, by rfl⟩ : syracuseStep 2721899 = 4082849) B4082849
theorem B2722793 : Blo 1813608 2722793 := bstep (se 2 (by rfl) ⟨1021047, by rfl⟩ : syracuseStep 2722793 = 2042095) B2042095
theorem B4590827 : Blo 1813608 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B40332775 : Blo 1813608 40332775 := bstep (se 1 (by rfl) ⟨30249581, by rfl⟩ : syracuseStep 40332775 = 60499163) B60499163
theorem B4591687 : Blo 1813608 4591687 := bstep (se 1 (by rfl) ⟨3443765, by rfl⟩ : syracuseStep 4591687 = 6887531) B6887531
theorem B4591799 : Blo 1813608 4591799 := bstep (se 1 (by rfl) ⟨3443849, by rfl⟩ : syracuseStep 4591799 = 6887699) B6887699
theorem B6886727 : Blo 1813608 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B6127595 : Blo 1813608 6127595 := bstep (se 1 (by rfl) ⟨4595696, by rfl⟩ : syracuseStep 6127595 = 9191393) B9191393
theorem B6122249 : Blo 1813608 6122249 := bstep (se 2 (by rfl) ⟨2295843, by rfl⟩ : syracuseStep 6122249 = 4591687) B4591687
theorem B6122735 : Blo 1813608 6122735 := bstep (se 1 (by rfl) ⟨4592051, by rfl⟩ : syracuseStep 6122735 = 9184103) B9184103
theorem B4591151 : Blo 1813608 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B1814599 : Blo 1813608 1814599 := bstep (se 1 (by rfl) ⟨1360949, by rfl⟩ : syracuseStep 1814599 = 2721899) B2721899
theorem B53777033 : Blo 1813608 53777033 := bstep (se 2 (by rfl) ⟨20166387, by rfl⟩ : syracuseStep 53777033 = 40332775) B40332775
theorem B1815195 : Blo 1813608 1815195 := bstep (se 1 (by rfl) ⟨1361396, by rfl⟩ : syracuseStep 1815195 = 2722793) B2722793
theorem B3060551 : Blo 1813608 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B4085063 : Blo 1813608 4085063 := bstep (se 1 (by rfl) ⟨3063797, by rfl⟩ : syracuseStep 4085063 = 6127595) B6127595
theorem B3061199 : Blo 1813608 3061199 := bstep (se 1 (by rfl) ⟨2295899, by rfl⟩ : syracuseStep 3061199 = 4591799) B4591799
theorem B11623837 : Blo 1813608 11623837 := bstep (se 3 (by rfl) ⟨2179469, by rfl⟩ : syracuseStep 11623837 = 4358939) B4358939
theorem B2040367 : Blo 1813608 2040367 := bstep (se 1 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 2040367 = 3060551) B3060551
theorem B2040799 : Blo 1813608 2040799 := bstep (se 1 (by rfl) ⟨1530599, by rfl⟩ : syracuseStep 2040799 = 3061199) B3061199
theorem B4081499 : Blo 1813608 4081499 := bstep (se 1 (by rfl) ⟨3061124, by rfl⟩ : syracuseStep 4081499 = 6122249) B6122249
theorem B4081823 : Blo 1813608 4081823 := bstep (se 1 (by rfl) ⟨3061367, by rfl⟩ : syracuseStep 4081823 = 6122735) B6122735
theorem B35851355 : Blo 1813608 35851355 := bstep (se 1 (by rfl) ⟨26888516, by rfl⟩ : syracuseStep 35851355 = 53777033) B53777033
theorem B2723375 : Blo 1813608 2723375 := bstep (se 1 (by rfl) ⟨2042531, by rfl⟩ : syracuseStep 2723375 = 4085063) B4085063
theorem B3060767 : Blo 1813608 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B15498449 : Blo 1813608 15498449 := bstep (se 2 (by rfl) ⟨5811918, by rfl⟩ : syracuseStep 15498449 = 11623837) B11623837
theorem B2040511 : Blo 1813608 2040511 := bstep (se 1 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 2040511 = 3060767) B3060767
theorem B2720489 : Blo 1813608 2720489 := bstep (se 2 (by rfl) ⟨1020183, by rfl⟩ : syracuseStep 2720489 = 2040367) B2040367
theorem B2720999 : Blo 1813608 2720999 := bstep (se 1 (by rfl) ⟨2040749, by rfl⟩ : syracuseStep 2720999 = 4081499) B4081499
theorem B2721065 : Blo 1813608 2721065 := bstep (se 2 (by rfl) ⟨1020399, by rfl⟩ : syracuseStep 2721065 = 2040799) B2040799
theorem B2721215 : Blo 1813608 2721215 := bstep (se 1 (by rfl) ⟨2040911, by rfl⟩ : syracuseStep 2721215 = 4081823) B4081823
theorem B10332299 : Blo 1813608 10332299 := bstep (se 1 (by rfl) ⟨7749224, by rfl⟩ : syracuseStep 10332299 = 15498449) B15498449
theorem B23900903 : Blo 1813608 23900903 := bstep (se 1 (by rfl) ⟨17925677, by rfl⟩ : syracuseStep 23900903 = 35851355) B35851355
theorem B1815583 : Blo 1813608 1815583 := bstep (se 1 (by rfl) ⟨1361687, by rfl⟩ : syracuseStep 1815583 = 2723375) B2723375
theorem B15933935 : Blo 1813608 15933935 := bstep (se 1 (by rfl) ⟨11950451, by rfl⟩ : syracuseStep 15933935 = 23900903) B23900903
theorem B2720681 : Blo 1813608 2720681 := bstep (se 2 (by rfl) ⟨1020255, by rfl⟩ : syracuseStep 2720681 = 2040511) B2040511
theorem B1813659 : Blo 1813608 1813659 := bstep (se 1 (by rfl) ⟨1360244, by rfl⟩ : syracuseStep 1813659 = 2720489) B2720489
theorem B1813999 : Blo 1813608 1813999 := bstep (se 1 (by rfl) ⟨1360499, by rfl⟩ : syracuseStep 1813999 = 2720999) B2720999
theorem B1814043 : Blo 1813608 1814043 := bstep (se 1 (by rfl) ⟨1360532, by rfl⟩ : syracuseStep 1814043 = 2721065) B2721065
theorem B1814143 : Blo 1813608 1814143 := bstep (se 1 (by rfl) ⟨1360607, by rfl⟩ : syracuseStep 1814143 = 2721215) B2721215
theorem B6888199 : Blo 1813608 6888199 := bstep (se 1 (by rfl) ⟨5166149, by rfl⟩ : syracuseStep 6888199 = 10332299) B10332299
theorem B9184265 : Blo 1813608 9184265 := bstep (se 2 (by rfl) ⟨3444099, by rfl⟩ : syracuseStep 9184265 = 6888199) B6888199
theorem B1813787 : Blo 1813608 1813787 := bstep (se 1 (by rfl) ⟨1360340, by rfl⟩ : syracuseStep 1813787 = 2720681) B2720681
theorem B42490493 : Blo 1813608 42490493 := bstep (se 3 (by rfl) ⟨7966967, by rfl⟩ : syracuseStep 42490493 = 15933935) B15933935
theorem B6122843 : Blo 1813608 6122843 := bstep (se 1 (by rfl) ⟨4592132, by rfl⟩ : syracuseStep 6122843 = 9184265) B9184265
theorem B28326995 : Blo 1813608 28326995 := bstep (se 1 (by rfl) ⟨21245246, by rfl⟩ : syracuseStep 28326995 = 42490493) B42490493
theorem B18884663 : Blo 1813608 18884663 := bstep (se 1 (by rfl) ⟨14163497, by rfl⟩ : syracuseStep 18884663 = 28326995) B28326995
theorem B4081895 : Blo 1813608 4081895 := bstep (se 1 (by rfl) ⟨3061421, by rfl⟩ : syracuseStep 4081895 = 6122843) B6122843
theorem B2721263 : Blo 1813608 2721263 := bstep (se 1 (by rfl) ⟨2040947, by rfl⟩ : syracuseStep 2721263 = 4081895) B4081895
theorem B12589775 : Blo 1813608 12589775 := bstep (se 1 (by rfl) ⟨9442331, by rfl⟩ : syracuseStep 12589775 = 18884663) B18884663
theorem B1814175 : Blo 1813608 1814175 := bstep (se 1 (by rfl) ⟨1360631, by rfl⟩ : syracuseStep 1814175 = 2721263) B2721263
theorem B8393183 : Blo 1813608 8393183 := bstep (se 1 (by rfl) ⟨6294887, by rfl⟩ : syracuseStep 8393183 = 12589775) B12589775
theorem B5595455 : Blo 1813608 5595455 := bstep (se 1 (by rfl) ⟨4196591, by rfl⟩ : syracuseStep 5595455 = 8393183) B8393183
theorem B3730303 : Blo 1813608 3730303 := bstep (se 1 (by rfl) ⟨2797727, by rfl⟩ : syracuseStep 3730303 = 5595455) B5595455
theorem B4973737 : Blo 1813608 4973737 := bstep (se 2 (by rfl) ⟨1865151, by rfl⟩ : syracuseStep 4973737 = 3730303) B3730303
theorem B6631649 : Blo 1813608 6631649 := bstep (se 2 (by rfl) ⟨2486868, by rfl⟩ : syracuseStep 6631649 = 4973737) B4973737
theorem B4421099 : Blo 1813608 4421099 := bstep (se 1 (by rfl) ⟨3315824, by rfl⟩ : syracuseStep 4421099 = 6631649) B6631649
theorem B2947399 : Blo 1813608 2947399 := bstep (se 1 (by rfl) ⟨2210549, by rfl⟩ : syracuseStep 2947399 = 4421099) B4421099
theorem B62877845 : Blo 1813608 62877845 := bstep (se 6 (by rfl) ⟨1473699, by rfl⟩ : syracuseStep 62877845 = 2947399) B2947399
theorem B41918563 : Blo 1813608 41918563 := bstep (se 1 (by rfl) ⟨31438922, by rfl⟩ : syracuseStep 41918563 = 62877845) B62877845
theorem B55891417 : Blo 1813608 55891417 := bstep (se 2 (by rfl) ⟨20959281, by rfl⟩ : syracuseStep 55891417 = 41918563) B41918563
theorem B74521889 : Blo 1813608 74521889 := bstep (se 2 (by rfl) ⟨27945708, by rfl⟩ : syracuseStep 74521889 = 55891417) B55891417
theorem B49681259 : Blo 1813608 49681259 := bstep (se 1 (by rfl) ⟨37260944, by rfl⟩ : syracuseStep 49681259 = 74521889) B74521889
theorem B33120839 : Blo 1813608 33120839 := bstep (se 1 (by rfl) ⟨24840629, by rfl⟩ : syracuseStep 33120839 = 49681259) B49681259
theorem B88322237 : Blo 1813608 88322237 := bstep (se 3 (by rfl) ⟨16560419, by rfl⟩ : syracuseStep 88322237 = 33120839) B33120839
theorem B58881491 : Blo 1813608 58881491 := bstep (se 1 (by rfl) ⟨44161118, by rfl⟩ : syracuseStep 58881491 = 88322237) B88322237
theorem B39254327 : Blo 1813608 39254327 := bstep (se 1 (by rfl) ⟨29440745, by rfl⟩ : syracuseStep 39254327 = 58881491) B58881491
theorem B26169551 : Blo 1813608 26169551 := bstep (se 1 (by rfl) ⟨19627163, by rfl⟩ : syracuseStep 26169551 = 39254327) B39254327
theorem B17446367 : Blo 1813608 17446367 := bstep (se 1 (by rfl) ⟨13084775, by rfl⟩ : syracuseStep 17446367 = 26169551) B26169551
theorem B11630911 : Blo 1813608 11630911 := bstep (se 1 (by rfl) ⟨8723183, by rfl⟩ : syracuseStep 11630911 = 17446367) B17446367
theorem B15507881 : Blo 1813608 15507881 := bstep (se 2 (by rfl) ⟨5815455, by rfl⟩ : syracuseStep 15507881 = 11630911) B11630911
theorem B10338587 : Blo 1813608 10338587 := bstep (se 1 (by rfl) ⟨7753940, by rfl⟩ : syracuseStep 10338587 = 15507881) B15507881
theorem B6892391 : Blo 1813608 6892391 := bstep (se 1 (by rfl) ⟨5169293, by rfl⟩ : syracuseStep 6892391 = 10338587) B10338587
theorem B4594927 : Blo 1813608 4594927 := bstep (se 1 (by rfl) ⟨3446195, by rfl⟩ : syracuseStep 4594927 = 6892391) B6892391
theorem B6126569 : Blo 1813608 6126569 := bstep (se 2 (by rfl) ⟨2297463, by rfl⟩ : syracuseStep 6126569 = 4594927) B4594927
theorem B4084379 : Blo 1813608 4084379 := bstep (se 1 (by rfl) ⟨3063284, by rfl⟩ : syracuseStep 4084379 = 6126569) B6126569
theorem B2722919 : Blo 1813608 2722919 := bstep (se 1 (by rfl) ⟨2042189, by rfl⟩ : syracuseStep 2722919 = 4084379) B4084379
theorem B1815279 : Blo 1813608 1815279 := bstep (se 1 (by rfl) ⟨1361459, by rfl⟩ : syracuseStep 1815279 = 2722919) B2722919

theorem C0 (j : ℕ) (h1 : 453402 ≤ j) (h2 : j ≤ 453901) : Blo 1813608 (4 * j + 3) := by
  interval_cases j
  · exact B1813611
  · exact B1813615
  · exact B1813619
  · exact B1813623
  · exact B1813627
  · exact B1813631
  · exact B1813635
  · exact B1813639
  · exact B1813643
  · exact B1813647
  · exact B1813651
  · exact B1813655
  · exact B1813659
  · exact B1813663
  · exact B1813667
  · exact B1813671
  · exact B1813675
  · exact B1813679
  · exact B1813683
  · exact B1813687
  · exact B1813691
  · exact B1813695
  · exact B1813699
  · exact B1813703
  · exact B1813707
  · exact B1813711
  · exact B1813715
  · exact B1813719
  · exact B1813723
  · exact B1813727
  · exact B1813731
  · exact B1813735
  · exact B1813739
  · exact B1813743
  · exact B1813747
  · exact B1813751
  · exact B1813755
  · exact B1813759
  · exact B1813763
  · exact B1813767
  · exact B1813771
  · exact B1813775
  · exact B1813779
  · exact B1813783
  · exact B1813787
  · exact B1813791
  · exact B1813795
  · exact B1813799
  · exact B1813803
  · exact B1813807
  · exact B1813811
  · exact B1813815
  · exact B1813819
  · exact B1813823
  · exact B1813827
  · exact B1813831
  · exact B1813835
  · exact B1813839
  · exact B1813843
  · exact B1813847
  · exact B1813851
  · exact B1813855
  · exact B1813859
  · exact B1813863
  · exact B1813867
  · exact B1813871
  · exact B1813875
  · exact B1813879
  · exact B1813883
  · exact B1813887
  · exact B1813891
  · exact B1813895
  · exact B1813899
  · exact B1813903
  · exact B1813907
  · exact B1813911
  · exact B1813915
  · exact B1813919
  · exact B1813923
  · exact B1813927
  · exact B1813931
  · exact B1813935
  · exact B1813939
  · exact B1813943
  · exact B1813947
  · exact B1813951
  · exact B1813955
  · exact B1813959
  · exact B1813963
  · exact B1813967
  · exact B1813971
  · exact B1813975
  · exact B1813979
  · exact B1813983
  · exact B1813987
  · exact B1813991
  · exact B1813995
  · exact B1813999
  · exact B1814003
  · exact B1814007
  · exact B1814011
  · exact B1814015
  · exact B1814019
  · exact B1814023
  · exact B1814027
  · exact B1814031
  · exact B1814035
  · exact B1814039
  · exact B1814043
  · exact B1814047
  · exact B1814051
  · exact B1814055
  · exact B1814059
  · exact B1814063
  · exact B1814067
  · exact B1814071
  · exact B1814075
  · exact B1814079
  · exact B1814083
  · exact B1814087
  · exact B1814091
  · exact B1814095
  · exact B1814099
  · exact B1814103
  · exact B1814107
  · exact B1814111
  · exact B1814115
  · exact B1814119
  · exact B1814123
  · exact B1814127
  · exact B1814131
  · exact B1814135
  · exact B1814139
  · exact B1814143
  · exact B1814147
  · exact B1814151
  · exact B1814155
  · exact B1814159
  · exact B1814163
  · exact B1814167
  · exact B1814171
  · exact B1814175
  · exact B1814179
  · exact B1814183
  · exact B1814187
  · exact B1814191
  · exact B1814195
  · exact B1814199
  · exact B1814203
  · exact B1814207
  · exact B1814211
  · exact B1814215
  · exact B1814219
  · exact B1814223
  · exact B1814227
  · exact B1814231
  · exact B1814235
  · exact B1814239
  · exact B1814243
  · exact B1814247
  · exact B1814251
  · exact B1814255
  · exact B1814259
  · exact B1814263
  · exact B1814267
  · exact B1814271
  · exact B1814275
  · exact B1814279
  · exact B1814283
  · exact B1814287
  · exact B1814291
  · exact B1814295
  · exact B1814299
  · exact B1814303
  · exact B1814307
  · exact B1814311
  · exact B1814315
  · exact B1814319
  · exact B1814323
  · exact B1814327
  · exact B1814331
  · exact B1814335
  · exact B1814339
  · exact B1814343
  · exact B1814347
  · exact B1814351
  · exact B1814355
  · exact B1814359
  · exact B1814363
  · exact B1814367
  · exact B1814371
  · exact B1814375
  · exact B1814379
  · exact B1814383
  · exact B1814387
  · exact B1814391
  · exact B1814395
  · exact B1814399
  · exact B1814403
  · exact B1814407
  · exact B1814411
  · exact B1814415
  · exact B1814419
  · exact B1814423
  · exact B1814427
  · exact B1814431
  · exact B1814435
  · exact B1814439
  · exact B1814443
  · exact B1814447
  · exact B1814451
  · exact B1814455
  · exact B1814459
  · exact B1814463
  · exact B1814467
  · exact B1814471
  · exact B1814475
  · exact B1814479
  · exact B1814483
  · exact B1814487
  · exact B1814491
  · exact B1814495
  · exact B1814499
  · exact B1814503
  · exact B1814507
  · exact B1814511
  · exact B1814515
  · exact B1814519
  · exact B1814523
  · exact B1814527
  · exact B1814531
  · exact B1814535
  · exact B1814539
  · exact B1814543
  · exact B1814547
  · exact B1814551
  · exact B1814555
  · exact B1814559
  · exact B1814563
  · exact B1814567
  · exact B1814571
  · exact B1814575
  · exact B1814579
  · exact B1814583
  · exact B1814587
  · exact B1814591
  · exact B1814595
  · exact B1814599
  · exact B1814603
  · exact B1814607
  · exact B1814611
  · exact B1814615
  · exact B1814619
  · exact B1814623
  · exact B1814627
  · exact B1814631
  · exact B1814635
  · exact B1814639
  · exact B1814643
  · exact B1814647
  · exact B1814651
  · exact B1814655
  · exact B1814659
  · exact B1814663
  · exact B1814667
  · exact B1814671
  · exact B1814675
  · exact B1814679
  · exact B1814683
  · exact B1814687
  · exact B1814691
  · exact B1814695
  · exact B1814699
  · exact B1814703
  · exact B1814707
  · exact B1814711
  · exact B1814715
  · exact B1814719
  · exact B1814723
  · exact B1814727
  · exact B1814731
  · exact B1814735
  · exact B1814739
  · exact B1814743
  · exact B1814747
  · exact B1814751
  · exact B1814755
  · exact B1814759
  · exact B1814763
  · exact B1814767
  · exact B1814771
  · exact B1814775
  · exact B1814779
  · exact B1814783
  · exact B1814787
  · exact B1814791
  · exact B1814795
  · exact B1814799
  · exact B1814803
  · exact B1814807
  · exact B1814811
  · exact B1814815
  · exact B1814819
  · exact B1814823
  · exact B1814827
  · exact B1814831
  · exact B1814835
  · exact B1814839
  · exact B1814843
  · exact B1814847
  · exact B1814851
  · exact B1814855
  · exact B1814859
  · exact B1814863
  · exact B1814867
  · exact B1814871
  · exact B1814875
  · exact B1814879
  · exact B1814883
  · exact B1814887
  · exact B1814891
  · exact B1814895
  · exact B1814899
  · exact B1814903
  · exact B1814907
  · exact B1814911
  · exact B1814915
  · exact B1814919
  · exact B1814923
  · exact B1814927
  · exact B1814931
  · exact B1814935
  · exact B1814939
  · exact B1814943
  · exact B1814947
  · exact B1814951
  · exact B1814955
  · exact B1814959
  · exact B1814963
  · exact B1814967
  · exact B1814971
  · exact B1814975
  · exact B1814979
  · exact B1814983
  · exact B1814987
  · exact B1814991
  · exact B1814995
  · exact B1814999
  · exact B1815003
  · exact B1815007
  · exact B1815011
  · exact B1815015
  · exact B1815019
  · exact B1815023
  · exact B1815027
  · exact B1815031
  · exact B1815035
  · exact B1815039
  · exact B1815043
  · exact B1815047
  · exact B1815051
  · exact B1815055
  · exact B1815059
  · exact B1815063
  · exact B1815067
  · exact B1815071
  · exact B1815075
  · exact B1815079
  · exact B1815083
  · exact B1815087
  · exact B1815091
  · exact B1815095
  · exact B1815099
  · exact B1815103
  · exact B1815107
  · exact B1815111
  · exact B1815115
  · exact B1815119
  · exact B1815123
  · exact B1815127
  · exact B1815131
  · exact B1815135
  · exact B1815139
  · exact B1815143
  · exact B1815147
  · exact B1815151
  · exact B1815155
  · exact B1815159
  · exact B1815163
  · exact B1815167
  · exact B1815171
  · exact B1815175
  · exact B1815179
  · exact B1815183
  · exact B1815187
  · exact B1815191
  · exact B1815195
  · exact B1815199
  · exact B1815203
  · exact B1815207
  · exact B1815211
  · exact B1815215
  · exact B1815219
  · exact B1815223
  · exact B1815227
  · exact B1815231
  · exact B1815235
  · exact B1815239
  · exact B1815243
  · exact B1815247
  · exact B1815251
  · exact B1815255
  · exact B1815259
  · exact B1815263
  · exact B1815267
  · exact B1815271
  · exact B1815275
  · exact B1815279
  · exact B1815283
  · exact B1815287
  · exact B1815291
  · exact B1815295
  · exact B1815299
  · exact B1815303
  · exact B1815307
  · exact B1815311
  · exact B1815315
  · exact B1815319
  · exact B1815323
  · exact B1815327
  · exact B1815331
  · exact B1815335
  · exact B1815339
  · exact B1815343
  · exact B1815347
  · exact B1815351
  · exact B1815355
  · exact B1815359
  · exact B1815363
  · exact B1815367
  · exact B1815371
  · exact B1815375
  · exact B1815379
  · exact B1815383
  · exact B1815387
  · exact B1815391
  · exact B1815395
  · exact B1815399
  · exact B1815403
  · exact B1815407
  · exact B1815411
  · exact B1815415
  · exact B1815419
  · exact B1815423
  · exact B1815427
  · exact B1815431
  · exact B1815435
  · exact B1815439
  · exact B1815443
  · exact B1815447
  · exact B1815451
  · exact B1815455
  · exact B1815459
  · exact B1815463
  · exact B1815467
  · exact B1815471
  · exact B1815475
  · exact B1815479
  · exact B1815483
  · exact B1815487
  · exact B1815491
  · exact B1815495
  · exact B1815499
  · exact B1815503
  · exact B1815507
  · exact B1815511
  · exact B1815515
  · exact B1815519
  · exact B1815523
  · exact B1815527
  · exact B1815531
  · exact B1815535
  · exact B1815539
  · exact B1815543
  · exact B1815547
  · exact B1815551
  · exact B1815555
  · exact B1815559
  · exact B1815563
  · exact B1815567
  · exact B1815571
  · exact B1815575
  · exact B1815579
  · exact B1815583
  · exact B1815587
  · exact B1815591
  · exact B1815595
  · exact B1815599
  · exact B1815603
  · exact B1815607

theorem solution (m : ℕ) (hlo : 1813608 ≤ m) (hhi : m ≤ 1815608) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 453402 ≤ j := by omega
    have hj2 : j ≤ 453901 := by omega
    have hb : Blo 1813608 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
