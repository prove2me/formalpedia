-- Prove2me | solution 1 for syracuse_descends_range_417772_421772
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:51.935252+00:00
-- url     : https://prove2.me/submissions/529d75ea-fdc6-4574-8294-66dfdd985ce7

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


theorem B2392213 : Blo 417772 2392213 := bbase (se 6 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 2392213 = 112135) (by norm_num)
theorem B753965 : Blo 417772 753965 := bbase (se 3 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 753965 = 282737) (by norm_num)
theorem B491917 : Blo 417772 491917 := bbase (se 3 (by rfl) ⟨92234, by rfl⟩ : syracuseStep 491917 = 184469) (by norm_num)
theorem B426421 : Blo 417772 426421 := bbase (se 5 (by rfl) ⟨19988, by rfl⟩ : syracuseStep 426421 = 39977) (by norm_num)
theorem B1410101 : Blo 417772 1410101 := bbase (se 5 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 1410101 = 132197) (by norm_num)
theorem B2131109 : Blo 417772 2131109 := bbase (se 4 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 2131109 = 399583) (by norm_num)
theorem B853181 : Blo 417772 853181 := bbase (se 3 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 853181 = 319943) (by norm_num)
theorem B1344725 : Blo 417772 1344725 := bbase (se 7 (by rfl) ⟨15758, by rfl⟩ : syracuseStep 1344725 = 31517) (by norm_num)
theorem B427361 : Blo 417772 427361 := bbase (se 2 (by rfl) ⟨160260, by rfl⟩ : syracuseStep 427361 = 320521) (by norm_num)
theorem B1410533 : Blo 417772 1410533 := bbase (se 4 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 1410533 = 264475) (by norm_num)
theorem B460513 : Blo 417772 460513 := bbase (se 2 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 460513 = 345385) (by norm_num)
theorem B853789 : Blo 417772 853789 := bbase (se 3 (by rfl) ⟨160085, by rfl⟩ : syracuseStep 853789 = 320171) (by norm_num)
theorem B1410965 : Blo 417772 1410965 := bbase (se 6 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 1410965 = 66139) (by norm_num)
theorem B2394197 : Blo 417772 2394197 := bbase (se 8 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 2394197 = 28057) (by norm_num)
theorem B854309 : Blo 417772 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B1411397 : Blo 417772 1411397 := bbase (se 4 (by rfl) ⟨132318, by rfl⟩ : syracuseStep 1411397 = 264637) (by norm_num)
theorem B2132405 : Blo 417772 2132405 := bbase (se 5 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 2132405 = 199913) (by norm_num)
theorem B3410581 : Blo 417772 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B1411829 : Blo 417772 1411829 := bbase (se 5 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 1411829 = 132359) (by norm_num)
theorem B1018621 : Blo 417772 1018621 := bbase (se 3 (by rfl) ⟨190991, by rfl⟩ : syracuseStep 1018621 = 381983) (by norm_num)
theorem B756869 : Blo 417772 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B1412261 : Blo 417772 1412261 := bbase (se 4 (by rfl) ⟨132399, by rfl⟩ : syracuseStep 1412261 = 264799) (by norm_num)
theorem B2428181 : Blo 417772 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B757021 : Blo 417772 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B691573 : Blo 417772 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B2068021 : Blo 417772 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B1412693 : Blo 417772 1412693 := bbase (se 8 (by rfl) ⟨8277, by rfl⟩ : syracuseStep 1412693 = 16555) (by norm_num)
theorem B2133701 : Blo 417772 2133701 := bbase (se 4 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 2133701 = 400069) (by norm_num)
theorem B1609541 : Blo 417772 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B1740629 : Blo 417772 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B2723701 : Blo 417772 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B430057 : Blo 417772 430057 := bbase (se 2 (by rfl) ⟨161271, by rfl⟩ : syracuseStep 430057 = 322543) (by norm_num)
theorem B626669 : Blo 417772 626669 := bbase (se 3 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 626669 = 235001) (by norm_num)
theorem B626693 : Blo 417772 626693 := bbase (se 4 (by rfl) ⟨58752, by rfl⟩ : syracuseStep 626693 = 117505) (by norm_num)
theorem B1413125 : Blo 417772 1413125 := bbase (se 4 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 1413125 = 264961) (by norm_num)
theorem B626717 : Blo 417772 626717 := bbase (se 3 (by rfl) ⟨117509, by rfl⟩ : syracuseStep 626717 = 235019) (by norm_num)
theorem B626741 : Blo 417772 626741 := bbase (se 5 (by rfl) ⟨29378, by rfl⟩ : syracuseStep 626741 = 58757) (by norm_num)
theorem B626765 : Blo 417772 626765 := bbase (se 3 (by rfl) ⟨117518, by rfl⟩ : syracuseStep 626765 = 235037) (by norm_num)
theorem B430157 : Blo 417772 430157 := bbase (se 3 (by rfl) ⟨80654, by rfl⟩ : syracuseStep 430157 = 161309) (by norm_num)
theorem B8065109 : Blo 417772 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B626789 : Blo 417772 626789 := bbase (se 4 (by rfl) ⟨58761, by rfl⟩ : syracuseStep 626789 = 117523) (by norm_num)
theorem B626813 : Blo 417772 626813 := bbase (se 3 (by rfl) ⟨117527, by rfl⟩ : syracuseStep 626813 = 235055) (by norm_num)
theorem B626837 : Blo 417772 626837 := bbase (se 6 (by rfl) ⟨14691, by rfl⟩ : syracuseStep 626837 = 29383) (by norm_num)
theorem B626861 : Blo 417772 626861 := bbase (se 3 (by rfl) ⟨117536, by rfl⟩ : syracuseStep 626861 = 235073) (by norm_num)
theorem B626885 : Blo 417772 626885 := bbase (se 4 (by rfl) ⟨58770, by rfl⟩ : syracuseStep 626885 = 117541) (by norm_num)
theorem B1511621 : Blo 417772 1511621 := bbase (se 4 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 1511621 = 283429) (by norm_num)
theorem B626909 : Blo 417772 626909 := bbase (se 3 (by rfl) ⟨117545, by rfl⟩ : syracuseStep 626909 = 235091) (by norm_num)
theorem B626933 : Blo 417772 626933 := bbase (se 5 (by rfl) ⟨29387, by rfl⟩ : syracuseStep 626933 = 58775) (by norm_num)
theorem B2396405 : Blo 417772 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B626957 : Blo 417772 626957 := bbase (se 3 (by rfl) ⟨117554, by rfl⟩ : syracuseStep 626957 = 235109) (by norm_num)
theorem B626981 : Blo 417772 626981 := bbase (se 4 (by rfl) ⟨58779, by rfl⟩ : syracuseStep 626981 = 117559) (by norm_num)
theorem B627005 : Blo 417772 627005 := bbase (se 3 (by rfl) ⟨117563, by rfl⟩ : syracuseStep 627005 = 235127) (by norm_num)
theorem B627029 : Blo 417772 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B627053 : Blo 417772 627053 := bbase (se 3 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 627053 = 235145) (by norm_num)
theorem B627077 : Blo 417772 627077 := bbase (se 4 (by rfl) ⟨58788, by rfl⟩ : syracuseStep 627077 = 117577) (by norm_num)
theorem B954757 : Blo 417772 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B627101 : Blo 417772 627101 := bbase (se 3 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 627101 = 235163) (by norm_num)
theorem B627125 : Blo 417772 627125 := bbase (se 5 (by rfl) ⟨29396, by rfl⟩ : syracuseStep 627125 = 58793) (by norm_num)
theorem B1413557 : Blo 417772 1413557 := bbase (se 5 (by rfl) ⟨66260, by rfl⟩ : syracuseStep 1413557 = 132521) (by norm_num)
theorem B627149 : Blo 417772 627149 := bbase (se 3 (by rfl) ⟨117590, by rfl⟩ : syracuseStep 627149 = 235181) (by norm_num)
theorem B528869 : Blo 417772 528869 := bbase (se 4 (by rfl) ⟨49581, by rfl⟩ : syracuseStep 528869 = 99163) (by norm_num)
theorem B627173 : Blo 417772 627173 := bbase (se 4 (by rfl) ⟨58797, by rfl⟩ : syracuseStep 627173 = 117595) (by norm_num)
theorem B627197 : Blo 417772 627197 := bbase (se 3 (by rfl) ⟨117599, by rfl⟩ : syracuseStep 627197 = 235199) (by norm_num)
theorem B627221 : Blo 417772 627221 := bbase (se 6 (by rfl) ⟨14700, by rfl⟩ : syracuseStep 627221 = 29401) (by norm_num)
theorem B8098325 : Blo 417772 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B1217045 : Blo 417772 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B528925 : Blo 417772 528925 := bbase (se 3 (by rfl) ⟨99173, by rfl⟩ : syracuseStep 528925 = 198347) (by norm_num)
theorem B627245 : Blo 417772 627245 := bbase (se 3 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 627245 = 235217) (by norm_num)
theorem B627269 : Blo 417772 627269 := bbase (se 4 (by rfl) ⟨58806, by rfl⟩ : syracuseStep 627269 = 117613) (by norm_num)
theorem B627293 : Blo 417772 627293 := bbase (se 3 (by rfl) ⟨117617, by rfl⟩ : syracuseStep 627293 = 235235) (by norm_num)
theorem B1512037 : Blo 417772 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B627317 : Blo 417772 627317 := bbase (se 5 (by rfl) ⟨29405, by rfl⟩ : syracuseStep 627317 = 58811) (by norm_num)
theorem B529021 : Blo 417772 529021 := bbase (se 3 (by rfl) ⟨99191, by rfl⟩ : syracuseStep 529021 = 198383) (by norm_num)
theorem B627341 : Blo 417772 627341 := bbase (se 3 (by rfl) ⟨117626, by rfl⟩ : syracuseStep 627341 = 235253) (by norm_num)
theorem B627365 : Blo 417772 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B627389 : Blo 417772 627389 := bbase (se 3 (by rfl) ⟨117635, by rfl⟩ : syracuseStep 627389 = 235271) (by norm_num)
theorem B627413 : Blo 417772 627413 := bbase (se 7 (by rfl) ⟨7352, by rfl⟩ : syracuseStep 627413 = 14705) (by norm_num)
theorem B627437 : Blo 417772 627437 := bbase (se 3 (by rfl) ⟨117644, by rfl⟩ : syracuseStep 627437 = 235289) (by norm_num)
theorem B627461 : Blo 417772 627461 := bbase (se 4 (by rfl) ⟨58824, by rfl⟩ : syracuseStep 627461 = 117649) (by norm_num)
theorem B627485 : Blo 417772 627485 := bbase (se 3 (by rfl) ⟨117653, by rfl⟩ : syracuseStep 627485 = 235307) (by norm_num)
theorem B529193 : Blo 417772 529193 := bbase (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) (by norm_num)
theorem B627509 : Blo 417772 627509 := bbase (se 5 (by rfl) ⟨29414, by rfl⟩ : syracuseStep 627509 = 58829) (by norm_num)
theorem B627533 : Blo 417772 627533 := bbase (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) (by norm_num)
theorem B529249 : Blo 417772 529249 := bbase (se 2 (by rfl) ⟨198468, by rfl⟩ : syracuseStep 529249 = 396937) (by norm_num)
theorem B627557 : Blo 417772 627557 := bbase (se 4 (by rfl) ⟨58833, by rfl⟩ : syracuseStep 627557 = 117667) (by norm_num)
theorem B1413989 : Blo 417772 1413989 := bbase (se 4 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 1413989 = 265123) (by norm_num)
theorem B627581 : Blo 417772 627581 := bbase (se 3 (by rfl) ⟨117671, by rfl⟩ : syracuseStep 627581 = 235343) (by norm_num)
theorem B627605 : Blo 417772 627605 := bbase (se 6 (by rfl) ⟨14709, by rfl⟩ : syracuseStep 627605 = 29419) (by norm_num)
theorem B758693 : Blo 417772 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B627629 : Blo 417772 627629 := bbase (se 3 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 627629 = 235361) (by norm_num)
theorem B529345 : Blo 417772 529345 := bbase (se 2 (by rfl) ⟨198504, by rfl⟩ : syracuseStep 529345 = 397009) (by norm_num)
theorem B627653 : Blo 417772 627653 := bbase (se 4 (by rfl) ⟨58842, by rfl⟩ : syracuseStep 627653 = 117685) (by norm_num)
theorem B2134997 : Blo 417772 2134997 := bbase (se 7 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 2134997 = 50039) (by norm_num)
theorem B627677 : Blo 417772 627677 := bbase (se 3 (by rfl) ⟨117689, by rfl⟩ : syracuseStep 627677 = 235379) (by norm_num)
theorem B627701 : Blo 417772 627701 := bbase (se 5 (by rfl) ⟨29423, by rfl⟩ : syracuseStep 627701 = 58847) (by norm_num)
theorem B627725 : Blo 417772 627725 := bbase (se 3 (by rfl) ⟨117698, by rfl⟩ : syracuseStep 627725 = 235397) (by norm_num)
theorem B627749 : Blo 417772 627749 := bbase (se 4 (by rfl) ⟨58851, by rfl⟩ : syracuseStep 627749 = 117703) (by norm_num)
theorem B1348645 : Blo 417772 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B627773 : Blo 417772 627773 := bbase (se 3 (by rfl) ⟨117707, by rfl⟩ : syracuseStep 627773 = 235415) (by norm_num)
theorem B627797 : Blo 417772 627797 := bbase (se 8 (by rfl) ⟨3678, by rfl⟩ : syracuseStep 627797 = 7357) (by norm_num)
theorem B529517 : Blo 417772 529517 := bbase (se 3 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 529517 = 198569) (by norm_num)
theorem B627821 : Blo 417772 627821 := bbase (se 3 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 627821 = 235433) (by norm_num)
theorem B627845 : Blo 417772 627845 := bbase (se 4 (by rfl) ⟨58860, by rfl⟩ : syracuseStep 627845 = 117721) (by norm_num)
theorem B627869 : Blo 417772 627869 := bbase (se 3 (by rfl) ⟨117725, by rfl⟩ : syracuseStep 627869 = 235451) (by norm_num)
theorem B529573 : Blo 417772 529573 := bbase (se 4 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 529573 = 99295) (by norm_num)
theorem B627893 : Blo 417772 627893 := bbase (se 5 (by rfl) ⟨29432, by rfl⟩ : syracuseStep 627893 = 58865) (by norm_num)
theorem B627917 : Blo 417772 627917 := bbase (se 3 (by rfl) ⟨117734, by rfl⟩ : syracuseStep 627917 = 235469) (by norm_num)
theorem B627941 : Blo 417772 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B627965 : Blo 417772 627965 := bbase (se 3 (by rfl) ⟨117743, by rfl⟩ : syracuseStep 627965 = 235487) (by norm_num)
theorem B529669 : Blo 417772 529669 := bbase (se 4 (by rfl) ⟨49656, by rfl⟩ : syracuseStep 529669 = 99313) (by norm_num)
theorem B627989 : Blo 417772 627989 := bbase (se 6 (by rfl) ⟨14718, by rfl⟩ : syracuseStep 627989 = 29437) (by norm_num)
theorem B1414421 : Blo 417772 1414421 := bbase (se 6 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 1414421 = 66301) (by norm_num)
theorem B1348901 : Blo 417772 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B628013 : Blo 417772 628013 := bbase (se 3 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 628013 = 235505) (by norm_num)
theorem B628037 : Blo 417772 628037 := bbase (se 4 (by rfl) ⟨58878, by rfl⟩ : syracuseStep 628037 = 117757) (by norm_num)
theorem B628061 : Blo 417772 628061 := bbase (se 3 (by rfl) ⟨117761, by rfl⟩ : syracuseStep 628061 = 235523) (by norm_num)
theorem B955741 : Blo 417772 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B628085 : Blo 417772 628085 := bbase (se 5 (by rfl) ⟨29441, by rfl⟩ : syracuseStep 628085 = 58883) (by norm_num)
theorem B628109 : Blo 417772 628109 := bbase (se 3 (by rfl) ⟨117770, by rfl⟩ : syracuseStep 628109 = 235541) (by norm_num)
theorem B628133 : Blo 417772 628133 := bbase (se 4 (by rfl) ⟨58887, by rfl⟩ : syracuseStep 628133 = 117775) (by norm_num)
theorem B529841 : Blo 417772 529841 := bbase (se 2 (by rfl) ⟨198690, by rfl⟩ : syracuseStep 529841 = 397381) (by norm_num)
theorem B628157 : Blo 417772 628157 := bbase (se 3 (by rfl) ⟨117779, by rfl⟩ : syracuseStep 628157 = 235559) (by norm_num)
theorem B628181 : Blo 417772 628181 := bbase (se 7 (by rfl) ⟨7361, by rfl⟩ : syracuseStep 628181 = 14723) (by norm_num)
theorem B529897 : Blo 417772 529897 := bbase (se 2 (by rfl) ⟨198711, by rfl⟩ : syracuseStep 529897 = 397423) (by norm_num)
theorem B628205 : Blo 417772 628205 := bbase (se 3 (by rfl) ⟨117788, by rfl⟩ : syracuseStep 628205 = 235577) (by norm_num)
theorem B628229 : Blo 417772 628229 := bbase (se 4 (by rfl) ⟨58896, by rfl⟩ : syracuseStep 628229 = 117793) (by norm_num)
theorem B955925 : Blo 417772 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B628253 : Blo 417772 628253 := bbase (se 3 (by rfl) ⟨117797, by rfl⟩ : syracuseStep 628253 = 235595) (by norm_num)
theorem B628277 : Blo 417772 628277 := bbase (se 5 (by rfl) ⟨29450, by rfl⟩ : syracuseStep 628277 = 58901) (by norm_num)
theorem B595525 : Blo 417772 595525 := bbase (se 4 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 595525 = 111661) (by norm_num)
theorem B529993 : Blo 417772 529993 := bbase (se 2 (by rfl) ⟨198747, by rfl⟩ : syracuseStep 529993 = 397495) (by norm_num)
theorem B628301 : Blo 417772 628301 := bbase (se 3 (by rfl) ⟨117806, by rfl⟩ : syracuseStep 628301 = 235613) (by norm_num)
theorem B628325 : Blo 417772 628325 := bbase (se 4 (by rfl) ⟨58905, by rfl⟩ : syracuseStep 628325 = 117811) (by norm_num)
theorem B628349 : Blo 417772 628349 := bbase (se 3 (by rfl) ⟨117815, by rfl⟩ : syracuseStep 628349 = 235631) (by norm_num)
theorem B628373 : Blo 417772 628373 := bbase (se 6 (by rfl) ⟨14727, by rfl⟩ : syracuseStep 628373 = 29455) (by norm_num)
theorem B628397 : Blo 417772 628397 := bbase (se 3 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 628397 = 235649) (by norm_num)
theorem B628421 : Blo 417772 628421 := bbase (se 4 (by rfl) ⟨58914, by rfl⟩ : syracuseStep 628421 = 117829) (by norm_num)
theorem B1414853 : Blo 417772 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B628445 : Blo 417772 628445 := bbase (se 3 (by rfl) ⟨117833, by rfl⟩ : syracuseStep 628445 = 235667) (by norm_num)
theorem B530165 : Blo 417772 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B628469 : Blo 417772 628469 := bbase (se 5 (by rfl) ⟨29459, by rfl⟩ : syracuseStep 628469 = 58919) (by norm_num)
theorem B628493 : Blo 417772 628493 := bbase (se 3 (by rfl) ⟨117842, by rfl⟩ : syracuseStep 628493 = 235685) (by norm_num)
theorem B5117717 : Blo 417772 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B628517 : Blo 417772 628517 := bbase (se 4 (by rfl) ⟨58923, by rfl⟩ : syracuseStep 628517 = 117847) (by norm_num)
theorem B530221 : Blo 417772 530221 := bbase (se 3 (by rfl) ⟨99416, by rfl⟩ : syracuseStep 530221 = 198833) (by norm_num)
theorem B628541 : Blo 417772 628541 := bbase (se 3 (by rfl) ⟨117851, by rfl⟩ : syracuseStep 628541 = 235703) (by norm_num)
theorem B628565 : Blo 417772 628565 := bbase (se 9 (by rfl) ⟨1841, by rfl⟩ : syracuseStep 628565 = 3683) (by norm_num)
theorem B628589 : Blo 417772 628589 := bbase (se 3 (by rfl) ⟨117860, by rfl⟩ : syracuseStep 628589 = 235721) (by norm_num)
theorem B628613 : Blo 417772 628613 := bbase (se 4 (by rfl) ⟨58932, by rfl⟩ : syracuseStep 628613 = 117865) (by norm_num)
theorem B530317 : Blo 417772 530317 := bbase (se 3 (by rfl) ⟨99434, by rfl⟩ : syracuseStep 530317 = 198869) (by norm_num)
theorem B628637 : Blo 417772 628637 := bbase (se 3 (by rfl) ⟨117869, by rfl⟩ : syracuseStep 628637 = 235739) (by norm_num)
theorem B759709 : Blo 417772 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B628661 : Blo 417772 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B628685 : Blo 417772 628685 := bbase (se 3 (by rfl) ⟨117878, by rfl⟩ : syracuseStep 628685 = 235757) (by norm_num)
theorem B628709 : Blo 417772 628709 := bbase (se 4 (by rfl) ⟨58941, by rfl⟩ : syracuseStep 628709 = 117883) (by norm_num)
theorem B628733 : Blo 417772 628733 := bbase (se 3 (by rfl) ⟨117887, by rfl⟩ : syracuseStep 628733 = 235775) (by norm_num)
theorem B628757 : Blo 417772 628757 := bbase (se 6 (by rfl) ⟨14736, by rfl⟩ : syracuseStep 628757 = 29473) (by norm_num)
theorem B628781 : Blo 417772 628781 := bbase (se 3 (by rfl) ⟨117896, by rfl⟩ : syracuseStep 628781 = 235793) (by norm_num)
theorem B530489 : Blo 417772 530489 := bbase (se 2 (by rfl) ⟨198933, by rfl⟩ : syracuseStep 530489 = 397867) (by norm_num)
theorem B628805 : Blo 417772 628805 := bbase (se 4 (by rfl) ⟨58950, by rfl⟩ : syracuseStep 628805 = 117901) (by norm_num)
theorem B25860181 : Blo 417772 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B628829 : Blo 417772 628829 := bbase (se 3 (by rfl) ⟨117905, by rfl⟩ : syracuseStep 628829 = 235811) (by norm_num)
theorem B530545 : Blo 417772 530545 := bbase (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) (by norm_num)
theorem B628853 : Blo 417772 628853 := bbase (se 5 (by rfl) ⟨29477, by rfl⟩ : syracuseStep 628853 = 58955) (by norm_num)
theorem B1415285 : Blo 417772 1415285 := bbase (se 5 (by rfl) ⟨66341, by rfl⟩ : syracuseStep 1415285 = 132683) (by norm_num)
theorem B3184757 : Blo 417772 3184757 := bbase (se 5 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 3184757 = 298571) (by norm_num)
theorem B628877 : Blo 417772 628877 := bbase (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) (by norm_num)
theorem B596117 : Blo 417772 596117 := bbase (se 6 (by rfl) ⟨13971, by rfl⟩ : syracuseStep 596117 = 27943) (by norm_num)
theorem B628901 : Blo 417772 628901 := bbase (se 4 (by rfl) ⟨58959, by rfl⟩ : syracuseStep 628901 = 117919) (by norm_num)
theorem B628925 : Blo 417772 628925 := bbase (se 3 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 628925 = 235847) (by norm_num)
theorem B530641 : Blo 417772 530641 := bbase (se 2 (by rfl) ⟨198990, by rfl⟩ : syracuseStep 530641 = 397981) (by norm_num)
theorem B628949 : Blo 417772 628949 := bbase (se 7 (by rfl) ⟨7370, by rfl⟩ : syracuseStep 628949 = 14741) (by norm_num)
theorem B596197 : Blo 417772 596197 := bbase (se 4 (by rfl) ⟨55893, by rfl⟩ : syracuseStep 596197 = 111787) (by norm_num)
theorem B628973 : Blo 417772 628973 := bbase (se 3 (by rfl) ⟨117932, by rfl⟩ : syracuseStep 628973 = 235865) (by norm_num)
theorem B628997 : Blo 417772 628997 := bbase (se 4 (by rfl) ⟨58968, by rfl⟩ : syracuseStep 628997 = 117937) (by norm_num)
theorem B629021 : Blo 417772 629021 := bbase (se 3 (by rfl) ⟨117941, by rfl⟩ : syracuseStep 629021 = 235883) (by norm_num)
theorem B629045 : Blo 417772 629045 := bbase (se 5 (by rfl) ⟨29486, by rfl⟩ : syracuseStep 629045 = 58973) (by norm_num)
theorem B629069 : Blo 417772 629069 := bbase (se 3 (by rfl) ⟨117950, by rfl⟩ : syracuseStep 629069 = 235901) (by norm_num)
theorem B596317 : Blo 417772 596317 := bbase (se 3 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 596317 = 223619) (by norm_num)
theorem B629093 : Blo 417772 629093 := bbase (se 4 (by rfl) ⟨58977, by rfl⟩ : syracuseStep 629093 = 117955) (by norm_num)
theorem B530813 : Blo 417772 530813 := bbase (se 3 (by rfl) ⟨99527, by rfl⟩ : syracuseStep 530813 = 199055) (by norm_num)
theorem B629117 : Blo 417772 629117 := bbase (se 3 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 629117 = 235919) (by norm_num)
theorem B629141 : Blo 417772 629141 := bbase (se 6 (by rfl) ⟨14745, by rfl⟩ : syracuseStep 629141 = 29491) (by norm_num)
theorem B629165 : Blo 417772 629165 := bbase (se 3 (by rfl) ⟨117968, by rfl⟩ : syracuseStep 629165 = 235937) (by norm_num)
theorem B530869 : Blo 417772 530869 := bbase (se 5 (by rfl) ⟨24884, by rfl⟩ : syracuseStep 530869 = 49769) (by norm_num)
theorem B596413 : Blo 417772 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B629189 : Blo 417772 629189 := bbase (se 4 (by rfl) ⟨58986, by rfl⟩ : syracuseStep 629189 = 117973) (by norm_num)
theorem B629213 : Blo 417772 629213 := bbase (se 3 (by rfl) ⟨117977, by rfl⟩ : syracuseStep 629213 = 235955) (by norm_num)
theorem B629237 : Blo 417772 629237 := bbase (se 5 (by rfl) ⟨29495, by rfl⟩ : syracuseStep 629237 = 58991) (by norm_num)
theorem B629261 : Blo 417772 629261 := bbase (se 3 (by rfl) ⟨117986, by rfl⟩ : syracuseStep 629261 = 235973) (by norm_num)
theorem B530965 : Blo 417772 530965 := bbase (se 6 (by rfl) ⟨12444, by rfl⟩ : syracuseStep 530965 = 24889) (by norm_num)
theorem B2595349 : Blo 417772 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B1415717 : Blo 417772 1415717 := bbase (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) (by norm_num)
theorem B629285 : Blo 417772 629285 := bbase (se 4 (by rfl) ⟨58995, by rfl⟩ : syracuseStep 629285 = 117991) (by norm_num)
theorem B629309 : Blo 417772 629309 := bbase (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) (by norm_num)
theorem B629333 : Blo 417772 629333 := bbase (se 8 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 629333 = 7375) (by norm_num)
theorem B629357 : Blo 417772 629357 := bbase (se 3 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 629357 = 236009) (by norm_num)
theorem B629381 : Blo 417772 629381 := bbase (se 4 (by rfl) ⟨59004, by rfl⟩ : syracuseStep 629381 = 118009) (by norm_num)
theorem B3054229 : Blo 417772 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B629405 : Blo 417772 629405 := bbase (se 3 (by rfl) ⟨118013, by rfl⟩ : syracuseStep 629405 = 236027) (by norm_num)
theorem B629429 : Blo 417772 629429 := bbase (se 5 (by rfl) ⟨29504, by rfl⟩ : syracuseStep 629429 = 59009) (by norm_num)
theorem B531137 : Blo 417772 531137 := bbase (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) (by norm_num)
theorem B629453 : Blo 417772 629453 := bbase (se 3 (by rfl) ⟨118022, by rfl⟩ : syracuseStep 629453 = 236045) (by norm_num)
theorem B629477 : Blo 417772 629477 := bbase (se 4 (by rfl) ⟨59013, by rfl⟩ : syracuseStep 629477 = 118027) (by norm_num)
theorem B531193 : Blo 417772 531193 := bbase (se 2 (by rfl) ⟨199197, by rfl⟩ : syracuseStep 531193 = 398395) (by norm_num)
theorem B629501 : Blo 417772 629501 := bbase (se 3 (by rfl) ⟨118031, by rfl⟩ : syracuseStep 629501 = 236063) (by norm_num)
theorem B629525 : Blo 417772 629525 := bbase (se 6 (by rfl) ⟨14754, by rfl⟩ : syracuseStep 629525 = 29509) (by norm_num)
theorem B629549 : Blo 417772 629549 := bbase (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) (by norm_num)
theorem B629573 : Blo 417772 629573 := bbase (se 4 (by rfl) ⟨59022, by rfl⟩ : syracuseStep 629573 = 118045) (by norm_num)
theorem B531289 : Blo 417772 531289 := bbase (se 2 (by rfl) ⟨199233, by rfl⟩ : syracuseStep 531289 = 398467) (by norm_num)
theorem B629597 : Blo 417772 629597 := bbase (se 3 (by rfl) ⟨118049, by rfl⟩ : syracuseStep 629597 = 236099) (by norm_num)
theorem B629621 : Blo 417772 629621 := bbase (se 5 (by rfl) ⟨29513, by rfl⟩ : syracuseStep 629621 = 59027) (by norm_num)
theorem B629645 : Blo 417772 629645 := bbase (se 3 (by rfl) ⟨118058, by rfl⟩ : syracuseStep 629645 = 236117) (by norm_num)
theorem B629669 : Blo 417772 629669 := bbase (se 4 (by rfl) ⟨59031, by rfl⟩ : syracuseStep 629669 = 118063) (by norm_num)
theorem B596909 : Blo 417772 596909 := bbase (se 3 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 596909 = 223841) (by norm_num)
theorem B629693 : Blo 417772 629693 := bbase (se 3 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 629693 = 236135) (by norm_num)
theorem B1416149 : Blo 417772 1416149 := bbase (se 7 (by rfl) ⟨16595, by rfl⟩ : syracuseStep 1416149 = 33191) (by norm_num)
theorem B629717 : Blo 417772 629717 := bbase (se 7 (by rfl) ⟨7379, by rfl⟩ : syracuseStep 629717 = 14759) (by norm_num)
theorem B629741 : Blo 417772 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B629765 : Blo 417772 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B531461 : Blo 417772 531461 := bbase (se 4 (by rfl) ⟨49824, by rfl⟩ : syracuseStep 531461 = 99649) (by norm_num)
theorem B629789 : Blo 417772 629789 := bbase (se 3 (by rfl) ⟨118085, by rfl⟩ : syracuseStep 629789 = 236171) (by norm_num)
theorem B629813 : Blo 417772 629813 := bbase (se 5 (by rfl) ⟨29522, by rfl⟩ : syracuseStep 629813 = 59045) (by norm_num)
theorem B531517 : Blo 417772 531517 := bbase (se 3 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 531517 = 199319) (by norm_num)
theorem B629837 : Blo 417772 629837 := bbase (se 3 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 629837 = 236189) (by norm_num)
theorem B629861 : Blo 417772 629861 := bbase (se 4 (by rfl) ⟨59049, by rfl⟩ : syracuseStep 629861 = 118099) (by norm_num)
theorem B629885 : Blo 417772 629885 := bbase (se 3 (by rfl) ⟨118103, by rfl⟩ : syracuseStep 629885 = 236207) (by norm_num)
theorem B629909 : Blo 417772 629909 := bbase (se 6 (by rfl) ⟨14763, by rfl⟩ : syracuseStep 629909 = 29527) (by norm_num)
theorem B2694293 : Blo 417772 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B531613 : Blo 417772 531613 := bbase (se 3 (by rfl) ⟨99677, by rfl⟩ : syracuseStep 531613 = 199355) (by norm_num)
theorem B629933 : Blo 417772 629933 := bbase (se 3 (by rfl) ⟨118112, by rfl⟩ : syracuseStep 629933 = 236225) (by norm_num)
theorem B629957 : Blo 417772 629957 := bbase (se 4 (by rfl) ⟨59058, by rfl⟩ : syracuseStep 629957 = 118117) (by norm_num)
theorem B793813 : Blo 417772 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B629981 : Blo 417772 629981 := bbase (se 3 (by rfl) ⟨118121, by rfl⟩ : syracuseStep 629981 = 236243) (by norm_num)
theorem B630005 : Blo 417772 630005 := bbase (se 5 (by rfl) ⟨29531, by rfl⟩ : syracuseStep 630005 = 59063) (by norm_num)
theorem B630029 : Blo 417772 630029 := bbase (se 3 (by rfl) ⟨118130, by rfl⟩ : syracuseStep 630029 = 236261) (by norm_num)
theorem B630053 : Blo 417772 630053 := bbase (se 4 (by rfl) ⟨59067, by rfl⟩ : syracuseStep 630053 = 118135) (by norm_num)
theorem B630077 : Blo 417772 630077 := bbase (se 3 (by rfl) ⟨118139, by rfl⟩ : syracuseStep 630077 = 236279) (by norm_num)
theorem B531785 : Blo 417772 531785 := bbase (se 2 (by rfl) ⟨199419, by rfl⟩ : syracuseStep 531785 = 398839) (by norm_num)
theorem B630101 : Blo 417772 630101 := bbase (se 11 (by rfl) ⟨461, by rfl⟩ : syracuseStep 630101 = 923) (by norm_num)
theorem B793957 : Blo 417772 793957 := bbase (se 4 (by rfl) ⟨74433, by rfl⟩ : syracuseStep 793957 = 148867) (by norm_num)
theorem B630125 : Blo 417772 630125 := bbase (se 3 (by rfl) ⟨118148, by rfl⟩ : syracuseStep 630125 = 236297) (by norm_num)
theorem B531841 : Blo 417772 531841 := bbase (se 2 (by rfl) ⟨199440, by rfl⟩ : syracuseStep 531841 = 398881) (by norm_num)
theorem B1416581 : Blo 417772 1416581 := bbase (se 4 (by rfl) ⟨132804, by rfl⟩ : syracuseStep 1416581 = 265609) (by norm_num)
theorem B630149 : Blo 417772 630149 := bbase (se 4 (by rfl) ⟨59076, by rfl⟩ : syracuseStep 630149 = 118153) (by norm_num)
theorem B630173 : Blo 417772 630173 := bbase (se 3 (by rfl) ⟨118157, by rfl⟩ : syracuseStep 630173 = 236315) (by norm_num)
theorem B630197 : Blo 417772 630197 := bbase (se 5 (by rfl) ⟨29540, by rfl⟩ : syracuseStep 630197 = 59081) (by norm_num)
theorem B630221 : Blo 417772 630221 := bbase (se 3 (by rfl) ⟨118166, by rfl⟩ : syracuseStep 630221 = 236333) (by norm_num)
theorem B597461 : Blo 417772 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B531937 : Blo 417772 531937 := bbase (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) (by norm_num)
theorem B630245 : Blo 417772 630245 := bbase (se 4 (by rfl) ⟨59085, by rfl⟩ : syracuseStep 630245 = 118171) (by norm_num)
theorem B630269 : Blo 417772 630269 := bbase (se 3 (by rfl) ⟨118175, by rfl⟩ : syracuseStep 630269 = 236351) (by norm_num)
theorem B794117 : Blo 417772 794117 := bbase (se 4 (by rfl) ⟨74448, by rfl⟩ : syracuseStep 794117 = 148897) (by norm_num)
theorem B630293 : Blo 417772 630293 := bbase (se 6 (by rfl) ⟨14772, by rfl⟩ : syracuseStep 630293 = 29545) (by norm_num)
theorem B630317 : Blo 417772 630317 := bbase (se 3 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 630317 = 236369) (by norm_num)
theorem B630341 : Blo 417772 630341 := bbase (se 4 (by rfl) ⟨59094, by rfl⟩ : syracuseStep 630341 = 118189) (by norm_num)
theorem B630365 : Blo 417772 630365 := bbase (se 3 (by rfl) ⟨118193, by rfl⟩ : syracuseStep 630365 = 236387) (by norm_num)
theorem B958061 : Blo 417772 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B630389 : Blo 417772 630389 := bbase (se 5 (by rfl) ⟨29549, by rfl⟩ : syracuseStep 630389 = 59099) (by norm_num)
theorem B630413 : Blo 417772 630413 := bbase (se 3 (by rfl) ⟨118202, by rfl⟩ : syracuseStep 630413 = 236405) (by norm_num)
theorem B532109 : Blo 417772 532109 := bbase (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) (by norm_num)
theorem B794261 : Blo 417772 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B630437 : Blo 417772 630437 := bbase (se 4 (by rfl) ⟨59103, by rfl⟩ : syracuseStep 630437 = 118207) (by norm_num)
theorem B630461 : Blo 417772 630461 := bbase (se 3 (by rfl) ⟨118211, by rfl⟩ : syracuseStep 630461 = 236423) (by norm_num)
theorem B532165 : Blo 417772 532165 := bbase (se 4 (by rfl) ⟨49890, by rfl⟩ : syracuseStep 532165 = 99781) (by norm_num)
theorem B630485 : Blo 417772 630485 := bbase (se 7 (by rfl) ⟨7388, by rfl⟩ : syracuseStep 630485 = 14777) (by norm_num)
theorem B630509 : Blo 417772 630509 := bbase (se 3 (by rfl) ⟨118220, by rfl⟩ : syracuseStep 630509 = 236441) (by norm_num)
theorem B630533 : Blo 417772 630533 := bbase (se 4 (by rfl) ⟨59112, by rfl⟩ : syracuseStep 630533 = 118225) (by norm_num)
theorem B630557 : Blo 417772 630557 := bbase (se 3 (by rfl) ⟨118229, by rfl⟩ : syracuseStep 630557 = 236459) (by norm_num)
theorem B532261 : Blo 417772 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B1417013 : Blo 417772 1417013 := bbase (se 5 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 1417013 = 132845) (by norm_num)
theorem B630581 : Blo 417772 630581 := bbase (se 5 (by rfl) ⟨29558, by rfl⟩ : syracuseStep 630581 = 59117) (by norm_num)
theorem B892741 : Blo 417772 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B630605 : Blo 417772 630605 := bbase (se 3 (by rfl) ⟨118238, by rfl⟩ : syracuseStep 630605 = 236477) (by norm_num)
theorem B630629 : Blo 417772 630629 := bbase (se 4 (by rfl) ⟨59121, by rfl⟩ : syracuseStep 630629 = 118243) (by norm_num)
theorem B630653 : Blo 417772 630653 := bbase (se 3 (by rfl) ⟨118247, by rfl⟩ : syracuseStep 630653 = 236495) (by norm_num)
theorem B630677 : Blo 417772 630677 := bbase (se 6 (by rfl) ⟨14781, by rfl⟩ : syracuseStep 630677 = 29563) (by norm_num)
theorem B630701 : Blo 417772 630701 := bbase (se 3 (by rfl) ⟨118256, by rfl⟩ : syracuseStep 630701 = 236513) (by norm_num)
theorem B794549 : Blo 417772 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B630725 : Blo 417772 630725 := bbase (se 4 (by rfl) ⟨59130, by rfl⟩ : syracuseStep 630725 = 118261) (by norm_num)
theorem B532433 : Blo 417772 532433 := bbase (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) (by norm_num)
theorem B16981973 : Blo 417772 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B630749 : Blo 417772 630749 := bbase (se 3 (by rfl) ⟨118265, by rfl⟩ : syracuseStep 630749 = 236531) (by norm_num)
theorem B630773 : Blo 417772 630773 := bbase (se 5 (by rfl) ⟨29567, by rfl⟩ : syracuseStep 630773 = 59135) (by norm_num)
theorem B532489 : Blo 417772 532489 := bbase (se 2 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 532489 = 399367) (by norm_num)
theorem B630797 : Blo 417772 630797 := bbase (se 3 (by rfl) ⟨118274, by rfl⟩ : syracuseStep 630797 = 236549) (by norm_num)
theorem B630821 : Blo 417772 630821 := bbase (se 4 (by rfl) ⟨59139, by rfl⟩ : syracuseStep 630821 = 118279) (by norm_num)
theorem B630845 : Blo 417772 630845 := bbase (se 3 (by rfl) ⟨118283, by rfl⟩ : syracuseStep 630845 = 236567) (by norm_num)
theorem B794701 : Blo 417772 794701 := bbase (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) (by norm_num)
theorem B630869 : Blo 417772 630869 := bbase (se 8 (by rfl) ⟨3696, by rfl⟩ : syracuseStep 630869 = 7393) (by norm_num)
theorem B532585 : Blo 417772 532585 := bbase (se 2 (by rfl) ⟨199719, by rfl⟩ : syracuseStep 532585 = 399439) (by norm_num)
theorem B630893 : Blo 417772 630893 := bbase (se 3 (by rfl) ⟨118292, by rfl⟩ : syracuseStep 630893 = 236585) (by norm_num)
theorem B630917 : Blo 417772 630917 := bbase (se 4 (by rfl) ⟨59148, by rfl⟩ : syracuseStep 630917 = 118297) (by norm_num)
theorem B630941 : Blo 417772 630941 := bbase (se 3 (by rfl) ⟨118301, by rfl⟩ : syracuseStep 630941 = 236603) (by norm_num)
theorem B630965 : Blo 417772 630965 := bbase (se 5 (by rfl) ⟨29576, by rfl⟩ : syracuseStep 630965 = 59153) (by norm_num)
theorem B598213 : Blo 417772 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B630989 : Blo 417772 630989 := bbase (se 3 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 630989 = 236621) (by norm_num)
theorem B1417445 : Blo 417772 1417445 := bbase (se 4 (by rfl) ⟨132885, by rfl⟩ : syracuseStep 1417445 = 265771) (by norm_num)
theorem B631013 : Blo 417772 631013 := bbase (se 4 (by rfl) ⟨59157, by rfl⟩ : syracuseStep 631013 = 118315) (by norm_num)
theorem B631037 : Blo 417772 631037 := bbase (se 3 (by rfl) ⟨118319, by rfl⟩ : syracuseStep 631037 = 236639) (by norm_num)
theorem B631061 : Blo 417772 631061 := bbase (se 6 (by rfl) ⟨14790, by rfl⟩ : syracuseStep 631061 = 29581) (by norm_num)
theorem B532757 : Blo 417772 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B631085 : Blo 417772 631085 := bbase (se 3 (by rfl) ⟨118328, by rfl⟩ : syracuseStep 631085 = 236657) (by norm_num)
theorem B631109 : Blo 417772 631109 := bbase (se 4 (by rfl) ⟨59166, by rfl⟩ : syracuseStep 631109 = 118333) (by norm_num)
theorem B532813 : Blo 417772 532813 := bbase (se 3 (by rfl) ⟨99902, by rfl⟩ : syracuseStep 532813 = 199805) (by norm_num)
theorem B631133 : Blo 417772 631133 := bbase (se 3 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 631133 = 236675) (by norm_num)
theorem B631157 : Blo 417772 631157 := bbase (se 5 (by rfl) ⟨29585, by rfl⟩ : syracuseStep 631157 = 59171) (by norm_num)
theorem B795005 : Blo 417772 795005 := bbase (se 3 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 795005 = 298127) (by norm_num)
theorem B631181 : Blo 417772 631181 := bbase (se 3 (by rfl) ⟨118346, by rfl⟩ : syracuseStep 631181 = 236693) (by norm_num)
theorem B631205 : Blo 417772 631205 := bbase (se 4 (by rfl) ⟨59175, by rfl⟩ : syracuseStep 631205 = 118351) (by norm_num)
theorem B532909 : Blo 417772 532909 := bbase (se 3 (by rfl) ⟨99920, by rfl⟩ : syracuseStep 532909 = 199841) (by norm_num)
theorem B631229 : Blo 417772 631229 := bbase (se 3 (by rfl) ⟨118355, by rfl⟩ : syracuseStep 631229 = 236711) (by norm_num)
theorem B631253 : Blo 417772 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B631277 : Blo 417772 631277 := bbase (se 3 (by rfl) ⟨118364, by rfl⟩ : syracuseStep 631277 = 236729) (by norm_num)
theorem B631301 : Blo 417772 631301 := bbase (se 4 (by rfl) ⟨59184, by rfl⟩ : syracuseStep 631301 = 118369) (by norm_num)
theorem B631325 : Blo 417772 631325 := bbase (se 3 (by rfl) ⟨118373, by rfl⟩ : syracuseStep 631325 = 236747) (by norm_num)
theorem B631349 : Blo 417772 631349 := bbase (se 5 (by rfl) ⟨29594, by rfl⟩ : syracuseStep 631349 = 59189) (by norm_num)
theorem B1450565 : Blo 417772 1450565 := bbase (se 4 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 1450565 = 271981) (by norm_num)
theorem B631373 : Blo 417772 631373 := bbase (se 3 (by rfl) ⟨118382, by rfl⟩ : syracuseStep 631373 = 236765) (by norm_num)
theorem B533081 : Blo 417772 533081 := bbase (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) (by norm_num)
theorem B631397 : Blo 417772 631397 := bbase (se 4 (by rfl) ⟨59193, by rfl⟩ : syracuseStep 631397 = 118387) (by norm_num)
theorem B631421 : Blo 417772 631421 := bbase (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) (by norm_num)
theorem B533137 : Blo 417772 533137 := bbase (se 2 (by rfl) ⟨199926, by rfl⟩ : syracuseStep 533137 = 399853) (by norm_num)
theorem B1417877 : Blo 417772 1417877 := bbase (se 6 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 1417877 = 66463) (by norm_num)
theorem B631445 : Blo 417772 631445 := bbase (se 6 (by rfl) ⟨14799, by rfl⟩ : syracuseStep 631445 = 29599) (by norm_num)
theorem B631469 : Blo 417772 631469 := bbase (se 3 (by rfl) ⟨118400, by rfl⟩ : syracuseStep 631469 = 236801) (by norm_num)
theorem B893629 : Blo 417772 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B631493 : Blo 417772 631493 := bbase (se 4 (by rfl) ⟨59202, by rfl⟩ : syracuseStep 631493 = 118405) (by norm_num)
theorem B631517 : Blo 417772 631517 := bbase (se 3 (by rfl) ⟨118409, by rfl⟩ : syracuseStep 631517 = 236819) (by norm_num)
theorem B533233 : Blo 417772 533233 := bbase (se 2 (by rfl) ⟨199962, by rfl⟩ : syracuseStep 533233 = 399925) (by norm_num)
theorem B631541 : Blo 417772 631541 := bbase (se 5 (by rfl) ⟨29603, by rfl⟩ : syracuseStep 631541 = 59207) (by norm_num)
theorem B631565 : Blo 417772 631565 := bbase (se 3 (by rfl) ⟨118418, by rfl⟩ : syracuseStep 631565 = 236837) (by norm_num)
theorem B631589 : Blo 417772 631589 := bbase (se 4 (by rfl) ⟨59211, by rfl⟩ : syracuseStep 631589 = 118423) (by norm_num)
theorem B893749 : Blo 417772 893749 := bbase (se 5 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 893749 = 83789) (by norm_num)
theorem B631613 : Blo 417772 631613 := bbase (se 3 (by rfl) ⟨118427, by rfl⟩ : syracuseStep 631613 = 236855) (by norm_num)
theorem B631637 : Blo 417772 631637 := bbase (se 9 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 631637 = 3701) (by norm_num)
theorem B1057637 : Blo 417772 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B2040677 : Blo 417772 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B631661 : Blo 417772 631661 := bbase (se 3 (by rfl) ⟨118436, by rfl⟩ : syracuseStep 631661 = 236873) (by norm_num)
theorem B631685 : Blo 417772 631685 := bbase (se 4 (by rfl) ⟨59220, by rfl⟩ : syracuseStep 631685 = 118441) (by norm_num)
theorem B3449749 : Blo 417772 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B631709 : Blo 417772 631709 := bbase (se 3 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 631709 = 236891) (by norm_num)
theorem B533405 : Blo 417772 533405 := bbase (se 3 (by rfl) ⟨100013, by rfl⟩ : syracuseStep 533405 = 200027) (by norm_num)
theorem B631733 : Blo 417772 631733 := bbase (se 5 (by rfl) ⟨29612, by rfl⟩ : syracuseStep 631733 = 59225) (by norm_num)
theorem B631757 : Blo 417772 631757 := bbase (se 3 (by rfl) ⟨118454, by rfl⟩ : syracuseStep 631757 = 236909) (by norm_num)
theorem B533461 : Blo 417772 533461 := bbase (se 7 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 533461 = 12503) (by norm_num)
theorem B599005 : Blo 417772 599005 := bbase (se 3 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 599005 = 224627) (by norm_num)
theorem B631781 : Blo 417772 631781 := bbase (se 4 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 631781 = 118459) (by norm_num)
theorem B2270197 : Blo 417772 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B631805 : Blo 417772 631805 := bbase (se 3 (by rfl) ⟨118463, by rfl⟩ : syracuseStep 631805 = 236927) (by norm_num)
theorem B631829 : Blo 417772 631829 := bbase (se 6 (by rfl) ⟨14808, by rfl⟩ : syracuseStep 631829 = 29617) (by norm_num)
theorem B631853 : Blo 417772 631853 := bbase (se 3 (by rfl) ⟨118472, by rfl⟩ : syracuseStep 631853 = 236945) (by norm_num)
theorem B894005 : Blo 417772 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B2270261 : Blo 417772 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B533557 : Blo 417772 533557 := bbase (se 5 (by rfl) ⟨25010, by rfl⟩ : syracuseStep 533557 = 50021) (by norm_num)
theorem B1418309 : Blo 417772 1418309 := bbase (se 4 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 1418309 = 265933) (by norm_num)
theorem B631877 : Blo 417772 631877 := bbase (se 4 (by rfl) ⟨59238, by rfl⟩ : syracuseStep 631877 = 118477) (by norm_num)
theorem B631901 : Blo 417772 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B795757 : Blo 417772 795757 := bbase (se 3 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 795757 = 298409) (by norm_num)
theorem B631925 : Blo 417772 631925 := bbase (se 5 (by rfl) ⟨29621, by rfl⟩ : syracuseStep 631925 = 59243) (by norm_num)
theorem B631949 : Blo 417772 631949 := bbase (se 3 (by rfl) ⟨118490, by rfl⟩ : syracuseStep 631949 = 236981) (by norm_num)
theorem B631973 : Blo 417772 631973 := bbase (se 4 (by rfl) ⟨59247, by rfl⟩ : syracuseStep 631973 = 118495) (by norm_num)
theorem B2270389 : Blo 417772 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B1057981 : Blo 417772 1057981 := bbase (se 3 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 1057981 = 396743) (by norm_num)
theorem B631997 : Blo 417772 631997 := bbase (se 3 (by rfl) ⟨118499, by rfl⟩ : syracuseStep 631997 = 236999) (by norm_num)
theorem B632021 : Blo 417772 632021 := bbase (se 7 (by rfl) ⟨7406, by rfl⟩ : syracuseStep 632021 = 14813) (by norm_num)
theorem B533729 : Blo 417772 533729 := bbase (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) (by norm_num)
theorem B632045 : Blo 417772 632045 := bbase (se 3 (by rfl) ⟨118508, by rfl⟩ : syracuseStep 632045 = 237017) (by norm_num)
theorem B795901 : Blo 417772 795901 := bbase (se 3 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 795901 = 298463) (by norm_num)
theorem B632069 : Blo 417772 632069 := bbase (se 4 (by rfl) ⟨59256, by rfl⟩ : syracuseStep 632069 = 118513) (by norm_num)
theorem B533785 : Blo 417772 533785 := bbase (se 2 (by rfl) ⟨200169, by rfl⟩ : syracuseStep 533785 = 400339) (by norm_num)
theorem B632093 : Blo 417772 632093 := bbase (se 3 (by rfl) ⟨118517, by rfl⟩ : syracuseStep 632093 = 237035) (by norm_num)
theorem B1058093 : Blo 417772 1058093 := bbase (se 3 (by rfl) ⟨198392, by rfl⟩ : syracuseStep 1058093 = 396785) (by norm_num)
theorem B599341 : Blo 417772 599341 := bbase (se 3 (by rfl) ⟨112376, by rfl⟩ : syracuseStep 599341 = 224753) (by norm_num)
theorem B632117 : Blo 417772 632117 := bbase (se 5 (by rfl) ⟨29630, by rfl⟩ : syracuseStep 632117 = 59261) (by norm_num)
theorem B632141 : Blo 417772 632141 := bbase (se 3 (by rfl) ⟨118526, by rfl⟩ : syracuseStep 632141 = 237053) (by norm_num)
theorem B632165 : Blo 417772 632165 := bbase (se 4 (by rfl) ⟨59265, by rfl⟩ : syracuseStep 632165 = 118531) (by norm_num)
theorem B632189 : Blo 417772 632189 := bbase (se 3 (by rfl) ⟨118535, by rfl⟩ : syracuseStep 632189 = 237071) (by norm_num)
theorem B632213 : Blo 417772 632213 := bbase (se 6 (by rfl) ⟨14817, by rfl⟩ : syracuseStep 632213 = 29635) (by norm_num)
theorem B796061 : Blo 417772 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B632237 : Blo 417772 632237 := bbase (se 3 (by rfl) ⟨118544, by rfl⟩ : syracuseStep 632237 = 237089) (by norm_num)
theorem B632261 : Blo 417772 632261 := bbase (se 4 (by rfl) ⟨59274, by rfl⟩ : syracuseStep 632261 = 118549) (by norm_num)
theorem B632285 : Blo 417772 632285 := bbase (se 3 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 632285 = 237107) (by norm_num)
theorem B1058285 : Blo 417772 1058285 := bbase (se 3 (by rfl) ⟨198428, by rfl⟩ : syracuseStep 1058285 = 396857) (by norm_num)
theorem B1418741 : Blo 417772 1418741 := bbase (se 5 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 1418741 = 133007) (by norm_num)
theorem B632309 : Blo 417772 632309 := bbase (se 5 (by rfl) ⟨29639, by rfl⟩ : syracuseStep 632309 = 59279) (by norm_num)
theorem B599557 : Blo 417772 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B632333 : Blo 417772 632333 := bbase (se 3 (by rfl) ⟨118562, by rfl⟩ : syracuseStep 632333 = 237125) (by norm_num)
theorem B632357 : Blo 417772 632357 := bbase (se 4 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 632357 = 118567) (by norm_num)
theorem B796205 : Blo 417772 796205 := bbase (se 3 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 796205 = 298577) (by norm_num)
theorem B1025597 : Blo 417772 1025597 := bbase (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) (by norm_num)
theorem B632381 : Blo 417772 632381 := bbase (se 3 (by rfl) ⟨118571, by rfl⟩ : syracuseStep 632381 = 237143) (by norm_num)
theorem B632405 : Blo 417772 632405 := bbase (se 8 (by rfl) ⟨3705, by rfl⟩ : syracuseStep 632405 = 7411) (by norm_num)
theorem B632429 : Blo 417772 632429 := bbase (se 3 (by rfl) ⟨118580, by rfl⟩ : syracuseStep 632429 = 237161) (by norm_num)
theorem B632453 : Blo 417772 632453 := bbase (se 4 (by rfl) ⟨59292, by rfl⟩ : syracuseStep 632453 = 118585) (by norm_num)
theorem B632477 : Blo 417772 632477 := bbase (se 3 (by rfl) ⟨118589, by rfl⟩ : syracuseStep 632477 = 237179) (by norm_num)
theorem B632501 : Blo 417772 632501 := bbase (se 5 (by rfl) ⟨29648, by rfl⟩ : syracuseStep 632501 = 59297) (by norm_num)
theorem B632525 : Blo 417772 632525 := bbase (se 3 (by rfl) ⟨118598, by rfl⟩ : syracuseStep 632525 = 237197) (by norm_num)
theorem B3155669 : Blo 417772 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B960229 : Blo 417772 960229 := bbase (se 4 (by rfl) ⟨90021, by rfl⟩ : syracuseStep 960229 = 180043) (by norm_num)
theorem B632549 : Blo 417772 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B632573 : Blo 417772 632573 := bbase (se 3 (by rfl) ⟨118607, by rfl⟩ : syracuseStep 632573 = 237215) (by norm_num)
theorem B1910533 : Blo 417772 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B4073237 : Blo 417772 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B632597 : Blo 417772 632597 := bbase (se 6 (by rfl) ⟨14826, by rfl⟩ : syracuseStep 632597 = 29653) (by norm_num)
theorem B632621 : Blo 417772 632621 := bbase (se 3 (by rfl) ⟨118616, by rfl⟩ : syracuseStep 632621 = 237233) (by norm_num)
theorem B1058629 : Blo 417772 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B632645 : Blo 417772 632645 := bbase (se 4 (by rfl) ⟨59310, by rfl⟩ : syracuseStep 632645 = 118621) (by norm_num)
theorem B796493 : Blo 417772 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B1517429 : Blo 417772 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B599933 : Blo 417772 599933 := bbase (se 3 (by rfl) ⟨112487, by rfl⟩ : syracuseStep 599933 = 224975) (by norm_num)
theorem B1419173 : Blo 417772 1419173 := bbase (se 4 (by rfl) ⟨133047, by rfl⟩ : syracuseStep 1419173 = 266095) (by norm_num)
theorem B894893 : Blo 417772 894893 := bbase (se 3 (by rfl) ⟨167792, by rfl⟩ : syracuseStep 894893 = 335585) (by norm_num)
theorem B1058741 : Blo 417772 1058741 := bbase (se 5 (by rfl) ⟨49628, by rfl⟩ : syracuseStep 1058741 = 99257) (by norm_num)
theorem B796645 : Blo 417772 796645 := bbase (se 4 (by rfl) ⟨74685, by rfl⟩ : syracuseStep 796645 = 149371) (by norm_num)
theorem B1058933 : Blo 417772 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B501913 : Blo 417772 501913 := bbase (se 2 (by rfl) ⟨188217, by rfl⟩ : syracuseStep 501913 = 376435) (by norm_num)
theorem B895133 : Blo 417772 895133 := bbase (se 3 (by rfl) ⟨167837, by rfl⟩ : syracuseStep 895133 = 335675) (by norm_num)
theorem B796949 : Blo 417772 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B1419605 : Blo 417772 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B502105 : Blo 417772 502105 := bbase (se 2 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 502105 = 376579) (by norm_num)
theorem B960925 : Blo 417772 960925 := bbase (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) (by norm_num)
theorem B502205 : Blo 417772 502205 := bbase (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) (by norm_num)
theorem B1059277 : Blo 417772 1059277 := bbase (se 3 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 1059277 = 397229) (by norm_num)
theorem B960997 : Blo 417772 960997 := bbase (se 4 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 960997 = 180187) (by norm_num)
theorem B1190389 : Blo 417772 1190389 := bbase (se 5 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 1190389 = 111599) (by norm_num)
theorem B1059389 : Blo 417772 1059389 := bbase (se 3 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 1059389 = 397271) (by norm_num)
theorem B895637 : Blo 417772 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B895645 : Blo 417772 895645 := bbase (se 3 (by rfl) ⟨167933, by rfl⟩ : syracuseStep 895645 = 335867) (by norm_num)
theorem B1059581 : Blo 417772 1059581 := bbase (se 3 (by rfl) ⟨198671, by rfl⟩ : syracuseStep 1059581 = 397343) (by norm_num)
theorem B1420037 : Blo 417772 1420037 := bbase (se 4 (by rfl) ⟨133128, by rfl⟩ : syracuseStep 1420037 = 266257) (by norm_num)
theorem B797701 : Blo 417772 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B470029 : Blo 417772 470029 := bbase (se 3 (by rfl) ⟨88130, by rfl⟩ : syracuseStep 470029 = 176261) (by norm_num)
theorem B568333 : Blo 417772 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B470065 : Blo 417772 470065 := bbase (se 2 (by rfl) ⟨176274, by rfl⟩ : syracuseStep 470065 = 352549) (by norm_num)
theorem B470101 : Blo 417772 470101 := bbase (se 8 (by rfl) ⟨2754, by rfl⟩ : syracuseStep 470101 = 5509) (by norm_num)
theorem B1059925 : Blo 417772 1059925 := bbase (se 8 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 1059925 = 12421) (by norm_num)
theorem B470137 : Blo 417772 470137 := bbase (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) (by norm_num)
theorem B797845 : Blo 417772 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B470173 : Blo 417772 470173 := bbase (se 3 (by rfl) ⟨88157, by rfl⟩ : syracuseStep 470173 = 176315) (by norm_num)
theorem B1420469 : Blo 417772 1420469 := bbase (se 5 (by rfl) ⟨66584, by rfl⟩ : syracuseStep 1420469 = 133169) (by norm_num)
theorem B470209 : Blo 417772 470209 := bbase (se 2 (by rfl) ⟨176328, by rfl⟩ : syracuseStep 470209 = 352657) (by norm_num)
theorem B1060037 : Blo 417772 1060037 := bbase (se 4 (by rfl) ⟨99378, by rfl⟩ : syracuseStep 1060037 = 198757) (by norm_num)
theorem B502993 : Blo 417772 502993 := bbase (se 2 (by rfl) ⟨188622, by rfl⟩ : syracuseStep 502993 = 377245) (by norm_num)
theorem B470245 : Blo 417772 470245 := bbase (se 4 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 470245 = 88171) (by norm_num)
theorem B568549 : Blo 417772 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B470281 : Blo 417772 470281 := bbase (se 2 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 470281 = 352711) (by norm_num)
theorem B470317 : Blo 417772 470317 := bbase (se 3 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 470317 = 176369) (by norm_num)
theorem B798005 : Blo 417772 798005 := bbase (se 5 (by rfl) ⟨37406, by rfl⟩ : syracuseStep 798005 = 74813) (by norm_num)
theorem B470353 : Blo 417772 470353 := bbase (se 2 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 470353 = 352765) (by norm_num)
theorem B16100693 : Blo 417772 16100693 := bbase (se 11 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 16100693 = 23585) (by norm_num)
theorem B470389 : Blo 417772 470389 := bbase (se 5 (by rfl) ⟨22049, by rfl⟩ : syracuseStep 470389 = 44099) (by norm_num)
theorem B1060229 : Blo 417772 1060229 := bbase (se 4 (by rfl) ⟨99396, by rfl⟩ : syracuseStep 1060229 = 198793) (by norm_num)
theorem B470425 : Blo 417772 470425 := bbase (se 2 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 470425 = 352819) (by norm_num)
theorem B470461 : Blo 417772 470461 := bbase (se 3 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 470461 = 176423) (by norm_num)
theorem B798149 : Blo 417772 798149 := bbase (se 4 (by rfl) ⟨74826, by rfl⟩ : syracuseStep 798149 = 149653) (by norm_num)
theorem B2076101 : Blo 417772 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B470497 : Blo 417772 470497 := bbase (se 2 (by rfl) ⟨176436, by rfl⟩ : syracuseStep 470497 = 352873) (by norm_num)
theorem B470533 : Blo 417772 470533 := bbase (se 4 (by rfl) ⟨44112, by rfl⟩ : syracuseStep 470533 = 88225) (by norm_num)
theorem B470569 : Blo 417772 470569 := bbase (se 2 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 470569 = 352927) (by norm_num)
theorem B470605 : Blo 417772 470605 := bbase (se 3 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 470605 = 176477) (by norm_num)
theorem B831061 : Blo 417772 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B1420901 : Blo 417772 1420901 := bbase (se 4 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 1420901 = 266419) (by norm_num)
theorem B470641 : Blo 417772 470641 := bbase (se 2 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 470641 = 352981) (by norm_num)
theorem B568949 : Blo 417772 568949 := bbase (se 5 (by rfl) ⟨26669, by rfl⟩ : syracuseStep 568949 = 53339) (by norm_num)
theorem B4763285 : Blo 417772 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B470677 : Blo 417772 470677 := bbase (se 6 (by rfl) ⟨11031, by rfl⟩ : syracuseStep 470677 = 22063) (by norm_num)
theorem B470713 : Blo 417772 470713 := bbase (se 2 (by rfl) ⟨176517, by rfl⟩ : syracuseStep 470713 = 353035) (by norm_num)
theorem B470749 : Blo 417772 470749 := bbase (se 3 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 470749 = 176531) (by norm_num)
theorem B1060573 : Blo 417772 1060573 := bbase (se 3 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 1060573 = 397715) (by norm_num)
theorem B798437 : Blo 417772 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B765677 : Blo 417772 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B470785 : Blo 417772 470785 := bbase (se 2 (by rfl) ⟨176544, by rfl⟩ : syracuseStep 470785 = 353089) (by norm_num)
theorem B896773 : Blo 417772 896773 := bbase (se 4 (by rfl) ⟨84072, by rfl⟩ : syracuseStep 896773 = 168145) (by norm_num)
theorem B6893333 : Blo 417772 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B470821 : Blo 417772 470821 := bbase (se 4 (by rfl) ⟨44139, by rfl⟩ : syracuseStep 470821 = 88279) (by norm_num)
theorem B470857 : Blo 417772 470857 := bbase (se 2 (by rfl) ⟨176571, by rfl⟩ : syracuseStep 470857 = 353143) (by norm_num)
theorem B1060685 : Blo 417772 1060685 := bbase (se 3 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 1060685 = 397757) (by norm_num)
theorem B470893 : Blo 417772 470893 := bbase (se 3 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 470893 = 176585) (by norm_num)
theorem B798589 : Blo 417772 798589 := bbase (se 3 (by rfl) ⟨149735, by rfl⟩ : syracuseStep 798589 = 299471) (by norm_num)
theorem B470929 : Blo 417772 470929 := bbase (se 2 (by rfl) ⟨176598, by rfl⟩ : syracuseStep 470929 = 353197) (by norm_num)
theorem B503705 : Blo 417772 503705 := bbase (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) (by norm_num)
theorem B470965 : Blo 417772 470965 := bbase (se 5 (by rfl) ⟨22076, by rfl⟩ : syracuseStep 470965 = 44153) (by norm_num)
theorem B864197 : Blo 417772 864197 := bbase (se 4 (by rfl) ⟨81018, by rfl⟩ : syracuseStep 864197 = 162037) (by norm_num)
theorem B471001 : Blo 417772 471001 := bbase (se 2 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 471001 = 353251) (by norm_num)
theorem B471037 : Blo 417772 471037 := bbase (se 3 (by rfl) ⟨88319, by rfl⟩ : syracuseStep 471037 = 176639) (by norm_num)
theorem B1060877 : Blo 417772 1060877 := bbase (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) (by norm_num)
theorem B1421333 : Blo 417772 1421333 := bbase (se 6 (by rfl) ⟨33312, by rfl⟩ : syracuseStep 1421333 = 66625) (by norm_num)
theorem B471073 : Blo 417772 471073 := bbase (se 2 (by rfl) ⟨176652, by rfl⟩ : syracuseStep 471073 = 353305) (by norm_num)
theorem B471109 : Blo 417772 471109 := bbase (se 4 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 471109 = 88333) (by norm_num)
theorem B471145 : Blo 417772 471145 := bbase (se 2 (by rfl) ⟨176679, by rfl⟩ : syracuseStep 471145 = 353359) (by norm_num)
theorem B897149 : Blo 417772 897149 := bbase (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) (by norm_num)
theorem B471181 : Blo 417772 471181 := bbase (se 3 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 471181 = 176693) (by norm_num)
theorem B798893 : Blo 417772 798893 := bbase (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) (by norm_num)
theorem B471217 : Blo 417772 471217 := bbase (se 2 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 471217 = 353413) (by norm_num)
theorem B471253 : Blo 417772 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B504041 : Blo 417772 504041 := bbase (se 2 (by rfl) ⟨189015, by rfl⟩ : syracuseStep 504041 = 378031) (by norm_num)
theorem B471289 : Blo 417772 471289 := bbase (se 2 (by rfl) ⟨176733, by rfl⟩ : syracuseStep 471289 = 353467) (by norm_num)
theorem B471325 : Blo 417772 471325 := bbase (se 3 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 471325 = 176747) (by norm_num)
theorem B471361 : Blo 417772 471361 := bbase (se 2 (by rfl) ⟨176760, by rfl⟩ : syracuseStep 471361 = 353521) (by norm_num)
theorem B504157 : Blo 417772 504157 := bbase (se 3 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 504157 = 189059) (by norm_num)
theorem B2011493 : Blo 417772 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B471397 : Blo 417772 471397 := bbase (se 4 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 471397 = 88387) (by norm_num)
theorem B1061221 : Blo 417772 1061221 := bbase (se 4 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 1061221 = 198979) (by norm_num)
theorem B504181 : Blo 417772 504181 := bbase (se 5 (by rfl) ⟨23633, by rfl⟩ : syracuseStep 504181 = 47267) (by norm_num)
theorem B471433 : Blo 417772 471433 := bbase (se 2 (by rfl) ⟨176787, by rfl⟩ : syracuseStep 471433 = 353575) (by norm_num)
theorem B471469 : Blo 417772 471469 := bbase (se 3 (by rfl) ⟨88400, by rfl⟩ : syracuseStep 471469 = 176801) (by norm_num)
theorem B1421765 : Blo 417772 1421765 := bbase (se 4 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 1421765 = 266581) (by norm_num)
theorem B471505 : Blo 417772 471505 := bbase (se 2 (by rfl) ⟨176814, by rfl⟩ : syracuseStep 471505 = 353629) (by norm_num)
theorem B1061333 : Blo 417772 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B471541 : Blo 417772 471541 := bbase (se 5 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 471541 = 44207) (by norm_num)
theorem B471577 : Blo 417772 471577 := bbase (se 2 (by rfl) ⟨176841, by rfl⟩ : syracuseStep 471577 = 353683) (by norm_num)
theorem B471613 : Blo 417772 471613 := bbase (se 3 (by rfl) ⟨88427, by rfl⟩ : syracuseStep 471613 = 176855) (by norm_num)
theorem B471649 : Blo 417772 471649 := bbase (se 2 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 471649 = 353737) (by norm_num)
theorem B471685 : Blo 417772 471685 := bbase (se 4 (by rfl) ⟨44220, by rfl⟩ : syracuseStep 471685 = 88441) (by norm_num)
theorem B1061525 : Blo 417772 1061525 := bbase (se 6 (by rfl) ⟨24879, by rfl⟩ : syracuseStep 1061525 = 49759) (by norm_num)
theorem B471721 : Blo 417772 471721 := bbase (se 2 (by rfl) ⟨176895, by rfl⟩ : syracuseStep 471721 = 353791) (by norm_num)
theorem B471757 : Blo 417772 471757 := bbase (se 3 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 471757 = 176909) (by norm_num)
theorem B471793 : Blo 417772 471793 := bbase (se 2 (by rfl) ⟨176922, by rfl⟩ : syracuseStep 471793 = 353845) (by norm_num)
theorem B1815317 : Blo 417772 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B471829 : Blo 417772 471829 := bbase (se 6 (by rfl) ⟨11058, by rfl⟩ : syracuseStep 471829 = 22117) (by norm_num)
theorem B471865 : Blo 417772 471865 := bbase (se 2 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 471865 = 353899) (by norm_num)
theorem B471901 : Blo 417772 471901 := bbase (se 3 (by rfl) ⟨88481, by rfl⟩ : syracuseStep 471901 = 176963) (by norm_num)
theorem B1422197 : Blo 417772 1422197 := bbase (se 5 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 1422197 = 133331) (by norm_num)
theorem B471937 : Blo 417772 471937 := bbase (se 2 (by rfl) ⟨176976, by rfl⟩ : syracuseStep 471937 = 353953) (by norm_num)
theorem B799645 : Blo 417772 799645 := bbase (se 3 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 799645 = 299867) (by norm_num)
theorem B471973 : Blo 417772 471973 := bbase (se 4 (by rfl) ⟨44247, by rfl⟩ : syracuseStep 471973 = 88495) (by norm_num)
theorem B472009 : Blo 417772 472009 := bbase (se 2 (by rfl) ⟨177003, by rfl⟩ : syracuseStep 472009 = 354007) (by norm_num)
theorem B1061869 : Blo 417772 1061869 := bbase (se 3 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 1061869 = 398201) (by norm_num)
theorem B472045 : Blo 417772 472045 := bbase (se 3 (by rfl) ⟨88508, by rfl⟩ : syracuseStep 472045 = 177017) (by norm_num)
theorem B472081 : Blo 417772 472081 := bbase (se 2 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 472081 = 354061) (by norm_num)
theorem B537625 : Blo 417772 537625 := bbase (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) (by norm_num)
theorem B504877 : Blo 417772 504877 := bbase (se 3 (by rfl) ⟨94664, by rfl⟩ : syracuseStep 504877 = 189329) (by norm_num)
theorem B799789 : Blo 417772 799789 := bbase (se 3 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 799789 = 299921) (by norm_num)
theorem B472117 : Blo 417772 472117 := bbase (se 5 (by rfl) ⟨22130, by rfl⟩ : syracuseStep 472117 = 44261) (by norm_num)
theorem B472153 : Blo 417772 472153 := bbase (se 2 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 472153 = 354115) (by norm_num)
theorem B1061981 : Blo 417772 1061981 := bbase (se 3 (by rfl) ⟨199121, by rfl⟩ : syracuseStep 1061981 = 398243) (by norm_num)
theorem B472189 : Blo 417772 472189 := bbase (se 3 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 472189 = 177071) (by norm_num)
theorem B504973 : Blo 417772 504973 := bbase (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) (by norm_num)
theorem B472225 : Blo 417772 472225 := bbase (se 2 (by rfl) ⟨177084, by rfl⟩ : syracuseStep 472225 = 354169) (by norm_num)
theorem B472261 : Blo 417772 472261 := bbase (se 4 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 472261 = 88549) (by norm_num)
theorem B799949 : Blo 417772 799949 := bbase (se 3 (by rfl) ⟨149990, by rfl⟩ : syracuseStep 799949 = 299981) (by norm_num)
theorem B472297 : Blo 417772 472297 := bbase (se 2 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 472297 = 354223) (by norm_num)
theorem B472333 : Blo 417772 472333 := bbase (se 3 (by rfl) ⟨88562, by rfl⟩ : syracuseStep 472333 = 177125) (by norm_num)
theorem B1193237 : Blo 417772 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B1062173 : Blo 417772 1062173 := bbase (se 3 (by rfl) ⟨199157, by rfl⟩ : syracuseStep 1062173 = 398315) (by norm_num)
theorem B1422629 : Blo 417772 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B472369 : Blo 417772 472369 := bbase (se 2 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 472369 = 354277) (by norm_num)
theorem B472405 : Blo 417772 472405 := bbase (se 13 (by rfl) ⟨86, by rfl⟩ : syracuseStep 472405 = 173) (by norm_num)
theorem B800093 : Blo 417772 800093 := bbase (se 3 (by rfl) ⟨150017, by rfl⟩ : syracuseStep 800093 = 300035) (by norm_num)
theorem B537953 : Blo 417772 537953 := bbase (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) (by norm_num)
theorem B472441 : Blo 417772 472441 := bbase (se 2 (by rfl) ⟨177165, by rfl⟩ : syracuseStep 472441 = 354331) (by norm_num)
theorem B472477 : Blo 417772 472477 := bbase (se 3 (by rfl) ⟨88589, by rfl⟩ : syracuseStep 472477 = 177179) (by norm_num)
theorem B472513 : Blo 417772 472513 := bbase (se 2 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 472513 = 354385) (by norm_num)
theorem B472549 : Blo 417772 472549 := bbase (se 4 (by rfl) ⟨44301, by rfl⟩ : syracuseStep 472549 = 88603) (by norm_num)
theorem B472585 : Blo 417772 472585 := bbase (se 2 (by rfl) ⟨177219, by rfl⟩ : syracuseStep 472585 = 354439) (by norm_num)
theorem B669197 : Blo 417772 669197 := bbase (se 3 (by rfl) ⟨125474, by rfl⟩ : syracuseStep 669197 = 250949) (by norm_num)
theorem B472621 : Blo 417772 472621 := bbase (se 3 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 472621 = 177233) (by norm_num)
theorem B1619525 : Blo 417772 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B472657 : Blo 417772 472657 := bbase (se 2 (by rfl) ⟨177246, by rfl⟩ : syracuseStep 472657 = 354493) (by norm_num)
theorem B1062517 : Blo 417772 1062517 := bbase (se 5 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 1062517 = 99611) (by norm_num)
theorem B472693 : Blo 417772 472693 := bbase (se 5 (by rfl) ⟨22157, by rfl⟩ : syracuseStep 472693 = 44315) (by norm_num)
theorem B800381 : Blo 417772 800381 := bbase (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) (by norm_num)
theorem B669325 : Blo 417772 669325 := bbase (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) (by norm_num)
theorem B636565 : Blo 417772 636565 := bbase (se 6 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 636565 = 29839) (by norm_num)
theorem B472729 : Blo 417772 472729 := bbase (se 2 (by rfl) ⟨177273, by rfl⟩ : syracuseStep 472729 = 354547) (by norm_num)
theorem B472765 : Blo 417772 472765 := bbase (se 3 (by rfl) ⟨88643, by rfl⟩ : syracuseStep 472765 = 177287) (by norm_num)
theorem B669389 : Blo 417772 669389 := bbase (se 3 (by rfl) ⟨125510, by rfl⟩ : syracuseStep 669389 = 251021) (by norm_num)
theorem B3192533 : Blo 417772 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B1423061 : Blo 417772 1423061 := bbase (se 7 (by rfl) ⟨16676, by rfl⟩ : syracuseStep 1423061 = 33353) (by norm_num)
theorem B472801 : Blo 417772 472801 := bbase (se 2 (by rfl) ⟨177300, by rfl⟩ : syracuseStep 472801 = 354601) (by norm_num)
theorem B1062629 : Blo 417772 1062629 := bbase (se 4 (by rfl) ⟨99621, by rfl⟩ : syracuseStep 1062629 = 199243) (by norm_num)
theorem B898789 : Blo 417772 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B472837 : Blo 417772 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B800533 : Blo 417772 800533 := bbase (se 6 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 800533 = 37525) (by norm_num)
theorem B472873 : Blo 417772 472873 := bbase (se 2 (by rfl) ⟨177327, by rfl⟩ : syracuseStep 472873 = 354655) (by norm_num)
theorem B472909 : Blo 417772 472909 := bbase (se 3 (by rfl) ⟨88670, by rfl⟩ : syracuseStep 472909 = 177341) (by norm_num)
theorem B472945 : Blo 417772 472945 := bbase (se 2 (by rfl) ⟨177354, by rfl⟩ : syracuseStep 472945 = 354709) (by norm_num)
theorem B472981 : Blo 417772 472981 := bbase (se 6 (by rfl) ⟨11085, by rfl⟩ : syracuseStep 472981 = 22171) (by norm_num)
theorem B1062821 : Blo 417772 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B473017 : Blo 417772 473017 := bbase (se 2 (by rfl) ⟨177381, by rfl⟩ : syracuseStep 473017 = 354763) (by norm_num)
theorem B473053 : Blo 417772 473053 := bbase (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) (by norm_num)
theorem B473089 : Blo 417772 473089 := bbase (se 2 (by rfl) ⟨177408, by rfl⟩ : syracuseStep 473089 = 354817) (by norm_num)
theorem B473125 : Blo 417772 473125 := bbase (se 4 (by rfl) ⟨44355, by rfl⟩ : syracuseStep 473125 = 88711) (by norm_num)
theorem B473161 : Blo 417772 473161 := bbase (se 2 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 473161 = 354871) (by norm_num)
theorem B3586133 : Blo 417772 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B2046053 : Blo 417772 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B473197 : Blo 417772 473197 := bbase (se 3 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 473197 = 177449) (by norm_num)
theorem B505973 : Blo 417772 505973 := bbase (se 5 (by rfl) ⟨23717, by rfl⟩ : syracuseStep 505973 = 47435) (by norm_num)
theorem B473233 : Blo 417772 473233 := bbase (se 2 (by rfl) ⟨177462, by rfl⟩ : syracuseStep 473233 = 354925) (by norm_num)
theorem B2144405 : Blo 417772 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B473269 : Blo 417772 473269 := bbase (se 5 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 473269 = 44369) (by norm_num)
theorem B1587397 : Blo 417772 1587397 := bbase (se 4 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 1587397 = 297637) (by norm_num)
theorem B2865365 : Blo 417772 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B473305 : Blo 417772 473305 := bbase (se 2 (by rfl) ⟨177489, by rfl⟩ : syracuseStep 473305 = 354979) (by norm_num)
theorem B3029237 : Blo 417772 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B1063165 : Blo 417772 1063165 := bbase (se 3 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 1063165 = 398687) (by norm_num)
theorem B473341 : Blo 417772 473341 := bbase (se 3 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 473341 = 177503) (by norm_num)
theorem B735517 : Blo 417772 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B473377 : Blo 417772 473377 := bbase (se 2 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 473377 = 355033) (by norm_num)
theorem B473413 : Blo 417772 473413 := bbase (se 4 (by rfl) ⟨44382, by rfl⟩ : syracuseStep 473413 = 88765) (by norm_num)
theorem B473449 : Blo 417772 473449 := bbase (se 2 (by rfl) ⟨177543, by rfl⟩ : syracuseStep 473449 = 355087) (by norm_num)
theorem B1063277 : Blo 417772 1063277 := bbase (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) (by norm_num)
theorem B473485 : Blo 417772 473485 := bbase (se 3 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 473485 = 177557) (by norm_num)
theorem B506261 : Blo 417772 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B473521 : Blo 417772 473521 := bbase (se 2 (by rfl) ⟨177570, by rfl⟩ : syracuseStep 473521 = 355141) (by norm_num)
theorem B1194421 : Blo 417772 1194421 := bbase (se 5 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 1194421 = 111977) (by norm_num)
theorem B473557 : Blo 417772 473557 := bbase (se 7 (by rfl) ⟨5549, by rfl⟩ : syracuseStep 473557 = 11099) (by norm_num)
theorem B1587701 : Blo 417772 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B473593 : Blo 417772 473593 := bbase (se 2 (by rfl) ⟨177597, by rfl⟩ : syracuseStep 473593 = 355195) (by norm_num)
theorem B473629 : Blo 417772 473629 := bbase (se 3 (by rfl) ⟨88805, by rfl⟩ : syracuseStep 473629 = 177611) (by norm_num)
theorem B1063469 : Blo 417772 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B539185 : Blo 417772 539185 := bbase (se 2 (by rfl) ⟨202194, by rfl⟩ : syracuseStep 539185 = 404389) (by norm_num)
theorem B506425 : Blo 417772 506425 := bbase (se 2 (by rfl) ⟨189909, by rfl⟩ : syracuseStep 506425 = 379819) (by norm_num)
theorem B473665 : Blo 417772 473665 := bbase (se 2 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 473665 = 355249) (by norm_num)
theorem B1194581 : Blo 417772 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B506453 : Blo 417772 506453 := bbase (se 8 (by rfl) ⟨2967, by rfl⟩ : syracuseStep 506453 = 5935) (by norm_num)
theorem B899677 : Blo 417772 899677 := bbase (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) (by norm_num)
theorem B473701 : Blo 417772 473701 := bbase (se 4 (by rfl) ⟨44409, by rfl⟩ : syracuseStep 473701 = 88819) (by norm_num)
theorem B473737 : Blo 417772 473737 := bbase (se 2 (by rfl) ⟨177651, by rfl⟩ : syracuseStep 473737 = 355303) (by norm_num)
theorem B473773 : Blo 417772 473773 := bbase (se 3 (by rfl) ⟨88832, by rfl⟩ : syracuseStep 473773 = 177665) (by norm_num)
theorem B506569 : Blo 417772 506569 := bbase (se 2 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 506569 = 379927) (by norm_num)
theorem B473809 : Blo 417772 473809 := bbase (se 2 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 473809 = 355357) (by norm_num)
theorem B473845 : Blo 417772 473845 := bbase (se 5 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 473845 = 44423) (by norm_num)
theorem B473881 : Blo 417772 473881 := bbase (se 2 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 473881 = 355411) (by norm_num)
theorem B637733 : Blo 417772 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B506665 : Blo 417772 506665 := bbase (se 2 (by rfl) ⟨189999, by rfl⟩ : syracuseStep 506665 = 379999) (by norm_num)
theorem B473917 : Blo 417772 473917 := bbase (se 3 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 473917 = 177719) (by norm_num)
theorem B1194821 : Blo 417772 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B473953 : Blo 417772 473953 := bbase (se 2 (by rfl) ⟨177732, by rfl⟩ : syracuseStep 473953 = 355465) (by norm_num)
theorem B1063813 : Blo 417772 1063813 := bbase (se 4 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 1063813 = 199465) (by norm_num)
theorem B473989 : Blo 417772 473989 := bbase (se 4 (by rfl) ⟨44436, by rfl⟩ : syracuseStep 473989 = 88873) (by norm_num)
theorem B474025 : Blo 417772 474025 := bbase (se 2 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 474025 = 355519) (by norm_num)
theorem B474061 : Blo 417772 474061 := bbase (se 3 (by rfl) ⟨88886, by rfl⟩ : syracuseStep 474061 = 177773) (by norm_num)
theorem B474097 : Blo 417772 474097 := bbase (se 2 (by rfl) ⟨177786, by rfl⟩ : syracuseStep 474097 = 355573) (by norm_num)
theorem B670709 : Blo 417772 670709 := bbase (se 5 (by rfl) ⟨31439, by rfl⟩ : syracuseStep 670709 = 62879) (by norm_num)
theorem B1063925 : Blo 417772 1063925 := bbase (se 5 (by rfl) ⟨49871, by rfl⟩ : syracuseStep 1063925 = 99743) (by norm_num)
theorem B1195013 : Blo 417772 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B474133 : Blo 417772 474133 := bbase (se 6 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 474133 = 22225) (by norm_num)
theorem B474169 : Blo 417772 474169 := bbase (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) (by norm_num)
theorem B900173 : Blo 417772 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B539741 : Blo 417772 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B474205 : Blo 417772 474205 := bbase (se 3 (by rfl) ⟨88913, by rfl⟩ : syracuseStep 474205 = 177827) (by norm_num)
theorem B670837 : Blo 417772 670837 := bbase (se 5 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 670837 = 62891) (by norm_num)
theorem B474241 : Blo 417772 474241 := bbase (se 2 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 474241 = 355681) (by norm_num)
theorem B474277 : Blo 417772 474277 := bbase (se 4 (by rfl) ⟨44463, by rfl⟩ : syracuseStep 474277 = 88927) (by norm_num)
theorem B1064117 : Blo 417772 1064117 := bbase (se 5 (by rfl) ⟨49880, by rfl⟩ : syracuseStep 1064117 = 99761) (by norm_num)
theorem B474313 : Blo 417772 474313 := bbase (se 2 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 474313 = 355735) (by norm_num)
theorem B474349 : Blo 417772 474349 := bbase (se 3 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 474349 = 177881) (by norm_num)
theorem B474385 : Blo 417772 474385 := bbase (se 2 (by rfl) ⟨177894, by rfl⟩ : syracuseStep 474385 = 355789) (by norm_num)
theorem B1359125 : Blo 417772 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B474421 : Blo 417772 474421 := bbase (se 5 (by rfl) ⟨22238, by rfl⟩ : syracuseStep 474421 = 44477) (by norm_num)
theorem B539965 : Blo 417772 539965 := bbase (se 3 (by rfl) ⟨101243, by rfl⟩ : syracuseStep 539965 = 202487) (by norm_num)
theorem B474457 : Blo 417772 474457 := bbase (se 2 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 474457 = 355843) (by norm_num)
theorem B474493 : Blo 417772 474493 := bbase (se 3 (by rfl) ⟨88967, by rfl⟩ : syracuseStep 474493 = 177935) (by norm_num)
theorem B2145781 : Blo 417772 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B1064461 : Blo 417772 1064461 := bbase (se 3 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 1064461 = 399173) (by norm_num)
theorem B1064573 : Blo 417772 1064573 := bbase (se 3 (by rfl) ⟨199607, by rfl⟩ : syracuseStep 1064573 = 399215) (by norm_num)
theorem B1064765 : Blo 417772 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B671645 : Blo 417772 671645 := bbase (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) (by norm_num)
theorem B1196005 : Blo 417772 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B1065109 : Blo 417772 1065109 := bbase (se 6 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 1065109 = 49927) (by norm_num)
theorem B671933 : Blo 417772 671933 := bbase (se 3 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 671933 = 251975) (by norm_num)
theorem B1065221 : Blo 417772 1065221 := bbase (se 4 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 1065221 = 199729) (by norm_num)
theorem B1065413 : Blo 417772 1065413 := bbase (se 4 (by rfl) ⟨99882, by rfl⟩ : syracuseStep 1065413 = 199765) (by norm_num)
theorem B4047317 : Blo 417772 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B705037 : Blo 417772 705037 := bbase (se 3 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 705037 = 264389) (by norm_num)
theorem B1589813 : Blo 417772 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B672349 : Blo 417772 672349 := bbase (se 3 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 672349 = 252131) (by norm_num)
theorem B705125 : Blo 417772 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B705253 : Blo 417772 705253 := bbase (se 4 (by rfl) ⟨66117, by rfl⟩ : syracuseStep 705253 = 132235) (by norm_num)
theorem B1065757 : Blo 417772 1065757 := bbase (se 3 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 1065757 = 399659) (by norm_num)
theorem B705341 : Blo 417772 705341 := bbase (se 3 (by rfl) ⟨132251, by rfl⟩ : syracuseStep 705341 = 264503) (by norm_num)
theorem B1590101 : Blo 417772 1590101 := bbase (se 9 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 1590101 = 9317) (by norm_num)
theorem B1065869 : Blo 417772 1065869 := bbase (se 3 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 1065869 = 399701) (by norm_num)
theorem B705469 : Blo 417772 705469 := bbase (se 3 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 705469 = 264551) (by norm_num)
theorem B3589109 : Blo 417772 3589109 := bbase (se 5 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 3589109 = 336479) (by norm_num)
theorem B705557 : Blo 417772 705557 := bbase (se 6 (by rfl) ⟨16536, by rfl⟩ : syracuseStep 705557 = 33073) (by norm_num)
theorem B1197109 : Blo 417772 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B1066061 : Blo 417772 1066061 := bbase (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) (by norm_num)
theorem B705685 : Blo 417772 705685 := bbase (se 6 (by rfl) ⟨16539, by rfl⟩ : syracuseStep 705685 = 33079) (by norm_num)
theorem B705773 : Blo 417772 705773 := bbase (se 3 (by rfl) ⟨132332, by rfl⟩ : syracuseStep 705773 = 264665) (by norm_num)
theorem B705901 : Blo 417772 705901 := bbase (se 3 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 705901 = 264713) (by norm_num)
theorem B1066405 : Blo 417772 1066405 := bbase (se 4 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 1066405 = 199951) (by norm_num)
theorem B705989 : Blo 417772 705989 := bbase (se 4 (by rfl) ⟨66186, by rfl⟩ : syracuseStep 705989 = 132373) (by norm_num)
theorem B673285 : Blo 417772 673285 := bbase (se 4 (by rfl) ⟨63120, by rfl⟩ : syracuseStep 673285 = 126241) (by norm_num)
theorem B1066517 : Blo 417772 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B476717 : Blo 417772 476717 := bbase (se 3 (by rfl) ⟨89384, by rfl⟩ : syracuseStep 476717 = 178769) (by norm_num)
theorem B706117 : Blo 417772 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B706205 : Blo 417772 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B1066709 : Blo 417772 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B1787669 : Blo 417772 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B706333 : Blo 417772 706333 := bbase (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) (by norm_num)
theorem B476977 : Blo 417772 476977 := bbase (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) (by norm_num)
theorem B706421 : Blo 417772 706421 := bbase (se 5 (by rfl) ⟨33113, by rfl⟩ : syracuseStep 706421 = 66227) (by norm_num)
theorem B2115557 : Blo 417772 2115557 := bbase (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) (by norm_num)
theorem B706549 : Blo 417772 706549 := bbase (se 5 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 706549 = 66239) (by norm_num)
theorem B1591285 : Blo 417772 1591285 := bbase (se 5 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 1591285 = 149183) (by norm_num)
theorem B641053 : Blo 417772 641053 := bbase (se 3 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 641053 = 240395) (by norm_num)
theorem B1067053 : Blo 417772 1067053 := bbase (se 3 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 1067053 = 400145) (by norm_num)
theorem B706637 : Blo 417772 706637 := bbase (se 3 (by rfl) ⟨132494, by rfl⟩ : syracuseStep 706637 = 264989) (by norm_num)
theorem B12863573 : Blo 417772 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B1067165 : Blo 417772 1067165 := bbase (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) (by norm_num)
theorem B706765 : Blo 417772 706765 := bbase (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) (by norm_num)
theorem B2017493 : Blo 417772 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B706853 : Blo 417772 706853 := bbase (se 4 (by rfl) ⟨66267, by rfl⟩ : syracuseStep 706853 = 132535) (by norm_num)
theorem B1591589 : Blo 417772 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1067357 : Blo 417772 1067357 := bbase (se 3 (by rfl) ⟨200129, by rfl⟩ : syracuseStep 1067357 = 400259) (by norm_num)
theorem B706981 : Blo 417772 706981 := bbase (se 4 (by rfl) ⟨66279, by rfl⟩ : syracuseStep 706981 = 132559) (by norm_num)
theorem B3394037 : Blo 417772 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B707069 : Blo 417772 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B1198613 : Blo 417772 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B3394165 : Blo 417772 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B707197 : Blo 417772 707197 := bbase (se 3 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 707197 = 265199) (by norm_num)
theorem B674477 : Blo 417772 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B707285 : Blo 417772 707285 := bbase (se 7 (by rfl) ⟨8288, by rfl⟩ : syracuseStep 707285 = 16577) (by norm_num)
theorem B707413 : Blo 417772 707413 := bbase (se 9 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 707413 = 4145) (by norm_num)
theorem B674669 : Blo 417772 674669 := bbase (se 3 (by rfl) ⟨126500, by rfl⟩ : syracuseStep 674669 = 253001) (by norm_num)
theorem B707501 : Blo 417772 707501 := bbase (se 3 (by rfl) ⟨132656, by rfl⟩ : syracuseStep 707501 = 265313) (by norm_num)
theorem B8604629 : Blo 417772 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B707629 : Blo 417772 707629 := bbase (se 3 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 707629 = 265361) (by norm_num)
theorem B707717 : Blo 417772 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B2116853 : Blo 417772 2116853 := bbase (se 5 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 2116853 = 198455) (by norm_num)
theorem B707845 : Blo 417772 707845 := bbase (se 4 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 707845 = 132721) (by norm_num)
theorem B1035605 : Blo 417772 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B707933 : Blo 417772 707933 := bbase (se 3 (by rfl) ⟨132737, by rfl⟩ : syracuseStep 707933 = 265475) (by norm_num)
theorem B708061 : Blo 417772 708061 := bbase (se 3 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 708061 = 265523) (by norm_num)
theorem B1789445 : Blo 417772 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B708149 : Blo 417772 708149 := bbase (se 5 (by rfl) ⟨33194, by rfl⟩ : syracuseStep 708149 = 66389) (by norm_num)
theorem B708277 : Blo 417772 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B1789685 : Blo 417772 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B708365 : Blo 417772 708365 := bbase (se 3 (by rfl) ⟨132818, by rfl⟩ : syracuseStep 708365 = 265637) (by norm_num)
theorem B708493 : Blo 417772 708493 := bbase (se 3 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 708493 = 265685) (by norm_num)
theorem B446353 : Blo 417772 446353 := bbase (se 2 (by rfl) ⟨167382, by rfl⟩ : syracuseStep 446353 = 334765) (by norm_num)
theorem B806869 : Blo 417772 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B708581 : Blo 417772 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B446473 : Blo 417772 446473 := bbase (se 2 (by rfl) ⟨167427, by rfl⟩ : syracuseStep 446473 = 334855) (by norm_num)
theorem B1200197 : Blo 417772 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B708709 : Blo 417772 708709 := bbase (se 4 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 708709 = 132883) (by norm_num)
theorem B708797 : Blo 417772 708797 := bbase (se 3 (by rfl) ⟨132899, by rfl⟩ : syracuseStep 708797 = 265799) (by norm_num)
theorem B479477 : Blo 417772 479477 := bbase (se 5 (by rfl) ⟨22475, by rfl⟩ : syracuseStep 479477 = 44951) (by norm_num)
theorem B446725 : Blo 417772 446725 := bbase (se 4 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 446725 = 83761) (by norm_num)
theorem B446729 : Blo 417772 446729 := bbase (se 2 (by rfl) ⟨167523, by rfl⟩ : syracuseStep 446729 = 335047) (by norm_num)
theorem B708925 : Blo 417772 708925 := bbase (se 3 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 708925 = 265847) (by norm_num)
theorem B1593701 : Blo 417772 1593701 := bbase (se 4 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 1593701 = 298819) (by norm_num)
theorem B709013 : Blo 417772 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B2118149 : Blo 417772 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B709141 : Blo 417772 709141 := bbase (se 6 (by rfl) ⟨16620, by rfl⟩ : syracuseStep 709141 = 33241) (by norm_num)
theorem B1004141 : Blo 417772 1004141 := bbase (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) (by norm_num)
theorem B709229 : Blo 417772 709229 := bbase (se 3 (by rfl) ⟨132980, by rfl⟩ : syracuseStep 709229 = 265961) (by norm_num)
theorem B1593989 : Blo 417772 1593989 := bbase (se 4 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 1593989 = 298873) (by norm_num)
theorem B1200869 : Blo 417772 1200869 := bbase (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) (by norm_num)
theorem B709357 : Blo 417772 709357 := bbase (se 3 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 709357 = 266009) (by norm_num)
theorem B1430261 : Blo 417772 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B3068725 : Blo 417772 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B1299253 : Blo 417772 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B447293 : Blo 417772 447293 := bbase (se 3 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 447293 = 167735) (by norm_num)
theorem B709445 : Blo 417772 709445 := bbase (se 4 (by rfl) ⟨66510, by rfl⟩ : syracuseStep 709445 = 133021) (by norm_num)
theorem B971669 : Blo 417772 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1135541 : Blo 417772 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B709573 : Blo 417772 709573 := bbase (se 4 (by rfl) ⟨66522, by rfl⟩ : syracuseStep 709573 = 133045) (by norm_num)
theorem B447481 : Blo 417772 447481 := bbase (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) (by norm_num)
theorem B709661 : Blo 417772 709661 := bbase (se 3 (by rfl) ⟨133061, by rfl⟩ : syracuseStep 709661 = 266123) (by norm_num)
theorem B709789 : Blo 417772 709789 := bbase (se 3 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 709789 = 266171) (by norm_num)
theorem B709877 : Blo 417772 709877 := bbase (se 5 (by rfl) ⟨33275, by rfl⟩ : syracuseStep 709877 = 66551) (by norm_num)
theorem B3200309 : Blo 417772 3200309 := bbase (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) (by norm_num)
theorem B710005 : Blo 417772 710005 := bbase (se 5 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 710005 = 66563) (by norm_num)
theorem B710093 : Blo 417772 710093 := bbase (se 3 (by rfl) ⟨133142, by rfl⟩ : syracuseStep 710093 = 266285) (by norm_num)
theorem B710221 : Blo 417772 710221 := bbase (se 3 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 710221 = 266333) (by norm_num)
theorem B710309 : Blo 417772 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B2119445 : Blo 417772 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B1595173 : Blo 417772 1595173 := bbase (se 4 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 1595173 = 299095) (by norm_num)
theorem B710437 : Blo 417772 710437 := bbase (se 4 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 710437 = 133207) (by norm_num)
theorem B448301 : Blo 417772 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B710525 : Blo 417772 710525 := bbase (se 3 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 710525 = 266447) (by norm_num)
theorem B6805397 : Blo 417772 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B1791973 : Blo 417772 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B940013 : Blo 417772 940013 := bbase (se 3 (by rfl) ⟨176252, by rfl⟩ : syracuseStep 940013 = 352505) (by norm_num)
theorem B710653 : Blo 417772 710653 := bbase (se 3 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 710653 = 266495) (by norm_num)
theorem B2152469 : Blo 417772 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B940085 : Blo 417772 940085 := bbase (se 5 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 940085 = 88133) (by norm_num)
theorem B1595477 : Blo 417772 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710741 : Blo 417772 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B940157 : Blo 417772 940157 := bbase (se 3 (by rfl) ⟨176279, by rfl⟩ : syracuseStep 940157 = 352559) (by norm_num)
theorem B3037333 : Blo 417772 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B940229 : Blo 417772 940229 := bbase (se 4 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 940229 = 176293) (by norm_num)
theorem B710869 : Blo 417772 710869 := bbase (se 7 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 710869 = 16661) (by norm_num)
theorem B448745 : Blo 417772 448745 := bbase (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) (by norm_num)
theorem B612613 : Blo 417772 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B940301 : Blo 417772 940301 := bbase (se 3 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 940301 = 352613) (by norm_num)
theorem B1005853 : Blo 417772 1005853 := bbase (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) (by norm_num)
theorem B710957 : Blo 417772 710957 := bbase (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) (by norm_num)
theorem B940373 : Blo 417772 940373 := bbase (se 10 (by rfl) ⟨1377, by rfl⟩ : syracuseStep 940373 = 2755) (by norm_num)
theorem B6838613 : Blo 417772 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B809365 : Blo 417772 809365 := bbase (se 6 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 809365 = 37939) (by norm_num)
theorem B940445 : Blo 417772 940445 := bbase (se 3 (by rfl) ⟨176333, by rfl⟩ : syracuseStep 940445 = 352667) (by norm_num)
theorem B711085 : Blo 417772 711085 := bbase (se 3 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 711085 = 266657) (by norm_num)
theorem B448993 : Blo 417772 448993 := bbase (se 2 (by rfl) ⟨168372, by rfl⟩ : syracuseStep 448993 = 336745) (by norm_num)
theorem B940517 : Blo 417772 940517 := bbase (se 4 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 940517 = 176347) (by norm_num)
theorem B711173 : Blo 417772 711173 := bbase (se 4 (by rfl) ⟨66672, by rfl⟩ : syracuseStep 711173 = 133345) (by norm_num)
theorem B940589 : Blo 417772 940589 := bbase (se 3 (by rfl) ⟨176360, by rfl⟩ : syracuseStep 940589 = 352721) (by norm_num)
theorem B940661 : Blo 417772 940661 := bbase (se 5 (by rfl) ⟨44093, by rfl⟩ : syracuseStep 940661 = 88187) (by norm_num)
theorem B711301 : Blo 417772 711301 := bbase (se 4 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 711301 = 133369) (by norm_num)
theorem B940733 : Blo 417772 940733 := bbase (se 3 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 940733 = 352775) (by norm_num)
theorem B711389 : Blo 417772 711389 := bbase (se 3 (by rfl) ⟨133385, by rfl⟩ : syracuseStep 711389 = 266771) (by norm_num)
theorem B940805 : Blo 417772 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B940877 : Blo 417772 940877 := bbase (se 3 (by rfl) ⟨176414, by rfl⟩ : syracuseStep 940877 = 352829) (by norm_num)
theorem B711517 : Blo 417772 711517 := bbase (se 3 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 711517 = 266819) (by norm_num)
theorem B1006469 : Blo 417772 1006469 := bbase (se 4 (by rfl) ⟨94356, by rfl⟩ : syracuseStep 1006469 = 188713) (by norm_num)
theorem B449425 : Blo 417772 449425 := bbase (se 2 (by rfl) ⟨168534, by rfl⟩ : syracuseStep 449425 = 337069) (by norm_num)
theorem B940949 : Blo 417772 940949 := bbase (se 6 (by rfl) ⟨22053, by rfl⟩ : syracuseStep 940949 = 44107) (by norm_num)
theorem B711605 : Blo 417772 711605 := bbase (se 5 (by rfl) ⟨33356, by rfl⟩ : syracuseStep 711605 = 66713) (by norm_num)
theorem B449497 : Blo 417772 449497 := bbase (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) (by norm_num)
theorem B941021 : Blo 417772 941021 := bbase (se 3 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 941021 = 352883) (by norm_num)
theorem B941093 : Blo 417772 941093 := bbase (se 4 (by rfl) ⟨88227, by rfl⟩ : syracuseStep 941093 = 176455) (by norm_num)
theorem B2120741 : Blo 417772 2120741 := bbase (se 4 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 2120741 = 397639) (by norm_num)
theorem B711733 : Blo 417772 711733 := bbase (se 5 (by rfl) ⟨33362, by rfl⟩ : syracuseStep 711733 = 66725) (by norm_num)
theorem B941165 : Blo 417772 941165 := bbase (se 3 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 941165 = 352937) (by norm_num)
theorem B2382965 : Blo 417772 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B2022565 : Blo 417772 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B941237 : Blo 417772 941237 := bbase (se 5 (by rfl) ⟨44120, by rfl⟩ : syracuseStep 941237 = 88241) (by norm_num)
theorem B941309 : Blo 417772 941309 := bbase (se 3 (by rfl) ⟨176495, by rfl⟩ : syracuseStep 941309 = 352991) (by norm_num)
theorem B1072397 : Blo 417772 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B1006901 : Blo 417772 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B908597 : Blo 417772 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B941381 : Blo 417772 941381 := bbase (se 4 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 941381 = 176509) (by norm_num)
theorem B449869 : Blo 417772 449869 := bbase (se 3 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 449869 = 168701) (by norm_num)
theorem B941453 : Blo 417772 941453 := bbase (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) (by norm_num)
theorem B1793461 : Blo 417772 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B1793477 : Blo 417772 1793477 := bbase (se 4 (by rfl) ⟨168138, by rfl⟩ : syracuseStep 1793477 = 336277) (by norm_num)
theorem B941525 : Blo 417772 941525 := bbase (se 7 (by rfl) ⟨11033, by rfl⟩ : syracuseStep 941525 = 22067) (by norm_num)
theorem B941597 : Blo 417772 941597 := bbase (se 3 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 941597 = 353099) (by norm_num)
theorem B20012629 : Blo 417772 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B941669 : Blo 417772 941669 := bbase (se 4 (by rfl) ⟨88281, by rfl⟩ : syracuseStep 941669 = 176563) (by norm_num)
theorem B941741 : Blo 417772 941741 := bbase (se 3 (by rfl) ⟨176576, by rfl⟩ : syracuseStep 941741 = 353153) (by norm_num)
theorem B450245 : Blo 417772 450245 := bbase (se 4 (by rfl) ⟨42210, by rfl⟩ : syracuseStep 450245 = 84421) (by norm_num)
theorem B941813 : Blo 417772 941813 := bbase (se 5 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 941813 = 88295) (by norm_num)
theorem B450317 : Blo 417772 450317 := bbase (se 3 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 450317 = 168869) (by norm_num)
theorem B941885 : Blo 417772 941885 := bbase (se 3 (by rfl) ⟨176603, by rfl⟩ : syracuseStep 941885 = 353207) (by norm_num)
theorem B941957 : Blo 417772 941957 := bbase (se 4 (by rfl) ⟨88308, by rfl⟩ : syracuseStep 941957 = 176617) (by norm_num)
theorem B942029 : Blo 417772 942029 := bbase (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) (by norm_num)
theorem B810965 : Blo 417772 810965 := bbase (se 7 (by rfl) ⟨9503, by rfl⟩ : syracuseStep 810965 = 19007) (by norm_num)
theorem B1368037 : Blo 417772 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B942101 : Blo 417772 942101 := bbase (se 6 (by rfl) ⟨22080, by rfl⟩ : syracuseStep 942101 = 44161) (by norm_num)
theorem B942173 : Blo 417772 942173 := bbase (se 3 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 942173 = 353315) (by norm_num)
theorem B876653 : Blo 417772 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B1597589 : Blo 417772 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B942245 : Blo 417772 942245 := bbase (se 4 (by rfl) ⟨88335, by rfl⟩ : syracuseStep 942245 = 176671) (by norm_num)
theorem B942317 : Blo 417772 942317 := bbase (se 3 (by rfl) ⟨176684, by rfl⟩ : syracuseStep 942317 = 353369) (by norm_num)
theorem B942389 : Blo 417772 942389 := bbase (se 5 (by rfl) ⟨44174, by rfl⟩ : syracuseStep 942389 = 88349) (by norm_num)
theorem B2122037 : Blo 417772 2122037 := bbase (se 5 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 2122037 = 198941) (by norm_num)
theorem B942461 : Blo 417772 942461 := bbase (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) (by norm_num)
theorem B1597877 : Blo 417772 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B942533 : Blo 417772 942533 := bbase (se 4 (by rfl) ⟨88362, by rfl⟩ : syracuseStep 942533 = 176725) (by norm_num)
theorem B1008101 : Blo 417772 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B942605 : Blo 417772 942605 := bbase (se 3 (by rfl) ⟨176738, by rfl⟩ : syracuseStep 942605 = 353477) (by norm_num)
theorem B942677 : Blo 417772 942677 := bbase (se 8 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 942677 = 11047) (by norm_num)
theorem B942749 : Blo 417772 942749 := bbase (se 3 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 942749 = 353531) (by norm_num)
theorem B942821 : Blo 417772 942821 := bbase (se 4 (by rfl) ⟨88389, by rfl⟩ : syracuseStep 942821 = 176779) (by norm_num)
theorem B942893 : Blo 417772 942893 := bbase (se 3 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 942893 = 353585) (by norm_num)
theorem B877405 : Blo 417772 877405 := bbase (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) (by norm_num)
theorem B942965 : Blo 417772 942965 := bbase (se 5 (by rfl) ⟨44201, by rfl⟩ : syracuseStep 942965 = 88403) (by norm_num)
theorem B615325 : Blo 417772 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B943037 : Blo 417772 943037 := bbase (se 3 (by rfl) ⟨176819, by rfl⟩ : syracuseStep 943037 = 353639) (by norm_num)
theorem B943109 : Blo 417772 943109 := bbase (se 4 (by rfl) ⟨88416, by rfl⟩ : syracuseStep 943109 = 176833) (by norm_num)
theorem B943181 : Blo 417772 943181 := bbase (se 3 (by rfl) ⟨176846, by rfl⟩ : syracuseStep 943181 = 353693) (by norm_num)
theorem B943253 : Blo 417772 943253 := bbase (se 6 (by rfl) ⟨22107, by rfl⟩ : syracuseStep 943253 = 44215) (by norm_num)
theorem B943325 : Blo 417772 943325 := bbase (se 3 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 943325 = 353747) (by norm_num)
theorem B943397 : Blo 417772 943397 := bbase (se 4 (by rfl) ⟨88443, by rfl⟩ : syracuseStep 943397 = 176887) (by norm_num)
theorem B2876725 : Blo 417772 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B943469 : Blo 417772 943469 := bbase (se 3 (by rfl) ⟨176900, by rfl⟩ : syracuseStep 943469 = 353801) (by norm_num)
theorem B943541 : Blo 417772 943541 := bbase (se 5 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 943541 = 88457) (by norm_num)
theorem B943613 : Blo 417772 943613 := bbase (se 3 (by rfl) ⟨176927, by rfl⟩ : syracuseStep 943613 = 353855) (by norm_num)
theorem B943685 : Blo 417772 943685 := bbase (se 4 (by rfl) ⟨88470, by rfl⟩ : syracuseStep 943685 = 176941) (by norm_num)
theorem B2123333 : Blo 417772 2123333 := bbase (se 4 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 2123333 = 398125) (by norm_num)
theorem B1599061 : Blo 417772 1599061 := bbase (se 8 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 1599061 = 18739) (by norm_num)
theorem B943757 : Blo 417772 943757 := bbase (se 3 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 943757 = 353909) (by norm_num)
theorem B1795733 : Blo 417772 1795733 := bbase (se 6 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 1795733 = 84175) (by norm_num)
theorem B1271477 : Blo 417772 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B943829 : Blo 417772 943829 := bbase (se 7 (by rfl) ⟨11060, by rfl⟩ : syracuseStep 943829 = 22121) (by norm_num)
theorem B943901 : Blo 417772 943901 := bbase (se 3 (by rfl) ⟨176981, by rfl⟩ : syracuseStep 943901 = 353963) (by norm_num)
theorem B1206101 : Blo 417772 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B943973 : Blo 417772 943973 := bbase (se 4 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 943973 = 176995) (by norm_num)
theorem B1599365 : Blo 417772 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B944045 : Blo 417772 944045 := bbase (se 3 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 944045 = 354017) (by norm_num)
theorem B944117 : Blo 417772 944117 := bbase (se 5 (by rfl) ⟨44255, by rfl⟩ : syracuseStep 944117 = 88511) (by norm_num)
theorem B944189 : Blo 417772 944189 := bbase (se 3 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 944189 = 354071) (by norm_num)
theorem B682069 : Blo 417772 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B944261 : Blo 417772 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B944333 : Blo 417772 944333 := bbase (se 3 (by rfl) ⟨177062, by rfl⟩ : syracuseStep 944333 = 354125) (by norm_num)
theorem B944405 : Blo 417772 944405 := bbase (se 6 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 944405 = 44269) (by norm_num)
theorem B4811093 : Blo 417772 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B944477 : Blo 417772 944477 := bbase (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) (by norm_num)
theorem B1272181 : Blo 417772 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B944549 : Blo 417772 944549 := bbase (se 4 (by rfl) ⟨88551, by rfl⟩ : syracuseStep 944549 = 177103) (by norm_num)
theorem B944621 : Blo 417772 944621 := bbase (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) (by norm_num)
theorem B944693 : Blo 417772 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B2878037 : Blo 417772 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B944765 : Blo 417772 944765 := bbase (se 3 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 944765 = 354287) (by norm_num)
theorem B944837 : Blo 417772 944837 := bbase (se 4 (by rfl) ⟨88578, by rfl⟩ : syracuseStep 944837 = 177157) (by norm_num)
theorem B1010389 : Blo 417772 1010389 := bbase (se 7 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 1010389 = 23681) (by norm_num)
theorem B715493 : Blo 417772 715493 := bbase (se 4 (by rfl) ⟨67077, by rfl⟩ : syracuseStep 715493 = 134155) (by norm_num)
theorem B944909 : Blo 417772 944909 := bbase (se 3 (by rfl) ⟨177170, by rfl⟩ : syracuseStep 944909 = 354341) (by norm_num)
theorem B1010485 : Blo 417772 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B2124629 : Blo 417772 2124629 := bbase (se 9 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 2124629 = 12449) (by norm_num)
theorem B944981 : Blo 417772 944981 := bbase (se 9 (by rfl) ⟨2768, by rfl⟩ : syracuseStep 944981 = 5537) (by norm_num)
theorem B945053 : Blo 417772 945053 := bbase (se 3 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 945053 = 354395) (by norm_num)
theorem B945125 : Blo 417772 945125 := bbase (se 4 (by rfl) ⟨88605, by rfl⟩ : syracuseStep 945125 = 177211) (by norm_num)
theorem B1010677 : Blo 417772 1010677 := bbase (se 5 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 1010677 = 94751) (by norm_num)
theorem B2419733 : Blo 417772 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B945197 : Blo 417772 945197 := bbase (se 3 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 945197 = 354449) (by norm_num)
theorem B2026565 : Blo 417772 2026565 := bbase (se 4 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 2026565 = 379981) (by norm_num)
theorem B945269 : Blo 417772 945269 := bbase (se 5 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 945269 = 88619) (by norm_num)
theorem B519313 : Blo 417772 519313 := bbase (se 2 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 519313 = 389485) (by norm_num)
theorem B945341 : Blo 417772 945341 := bbase (se 3 (by rfl) ⟨177251, by rfl⟩ : syracuseStep 945341 = 354503) (by norm_num)
theorem B945413 : Blo 417772 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B1338677 : Blo 417772 1338677 := bbase (se 5 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 1338677 = 125501) (by norm_num)
theorem B1011005 : Blo 417772 1011005 := bbase (se 3 (by rfl) ⟨189563, by rfl⟩ : syracuseStep 1011005 = 379127) (by norm_num)
theorem B945485 : Blo 417772 945485 := bbase (se 3 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 945485 = 354557) (by norm_num)
theorem B945557 : Blo 417772 945557 := bbase (se 6 (by rfl) ⟨22161, by rfl⟩ : syracuseStep 945557 = 44323) (by norm_num)
theorem B847309 : Blo 417772 847309 := bbase (se 3 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 847309 = 317741) (by norm_num)
theorem B945629 : Blo 417772 945629 := bbase (se 3 (by rfl) ⟨177305, by rfl⟩ : syracuseStep 945629 = 354611) (by norm_num)
theorem B945701 : Blo 417772 945701 := bbase (se 4 (by rfl) ⟨88659, by rfl⟩ : syracuseStep 945701 = 177319) (by norm_num)
theorem B945773 : Blo 417772 945773 := bbase (se 3 (by rfl) ⟨177332, by rfl⟩ : syracuseStep 945773 = 354665) (by norm_num)
theorem B945845 : Blo 417772 945845 := bbase (se 5 (by rfl) ⟨44336, by rfl⟩ : syracuseStep 945845 = 88673) (by norm_num)
theorem B1011437 : Blo 417772 1011437 := bbase (se 3 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 1011437 = 379289) (by norm_num)
theorem B945917 : Blo 417772 945917 := bbase (se 3 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 945917 = 354719) (by norm_num)
theorem B945989 : Blo 417772 945989 := bbase (se 4 (by rfl) ⟨88686, by rfl⟩ : syracuseStep 945989 = 177373) (by norm_num)
theorem B683861 : Blo 417772 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B487253 : Blo 417772 487253 := bbase (se 9 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 487253 = 2855) (by norm_num)
theorem B946061 : Blo 417772 946061 := bbase (se 3 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 946061 = 354773) (by norm_num)
theorem B847829 : Blo 417772 847829 := bbase (se 7 (by rfl) ⟨9935, by rfl⟩ : syracuseStep 847829 = 19871) (by norm_num)
theorem B946133 : Blo 417772 946133 := bbase (se 7 (by rfl) ⟨11087, by rfl⟩ : syracuseStep 946133 = 22175) (by norm_num)
theorem B946205 : Blo 417772 946205 := bbase (se 3 (by rfl) ⟨177413, by rfl⟩ : syracuseStep 946205 = 354827) (by norm_num)
theorem B1011773 : Blo 417772 1011773 := bbase (se 3 (by rfl) ⟨189707, by rfl⟩ : syracuseStep 1011773 = 379415) (by norm_num)
theorem B2125925 : Blo 417772 2125925 := bbase (se 4 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 2125925 = 398611) (by norm_num)
theorem B946277 : Blo 417772 946277 := bbase (se 4 (by rfl) ⟨88713, by rfl⟩ : syracuseStep 946277 = 177427) (by norm_num)
theorem B946349 : Blo 417772 946349 := bbase (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) (by norm_num)
theorem B1274069 : Blo 417772 1274069 := bbase (se 7 (by rfl) ⟨14930, by rfl⟩ : syracuseStep 1274069 = 29861) (by norm_num)
theorem B946421 : Blo 417772 946421 := bbase (se 5 (by rfl) ⟨44363, by rfl⟩ : syracuseStep 946421 = 88727) (by norm_num)
theorem B946493 : Blo 417772 946493 := bbase (se 3 (by rfl) ⟨177467, by rfl⟩ : syracuseStep 946493 = 354935) (by norm_num)
theorem B946565 : Blo 417772 946565 := bbase (se 4 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 946565 = 177481) (by norm_num)
theorem B946637 : Blo 417772 946637 := bbase (se 3 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 946637 = 354989) (by norm_num)
theorem B946709 : Blo 417772 946709 := bbase (se 6 (by rfl) ⟨22188, by rfl⟩ : syracuseStep 946709 = 44377) (by norm_num)
theorem B946781 : Blo 417772 946781 := bbase (se 3 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 946781 = 355043) (by norm_num)
theorem B946853 : Blo 417772 946853 := bbase (se 4 (by rfl) ⟨88767, by rfl⟩ : syracuseStep 946853 = 177535) (by norm_num)
theorem B946925 : Blo 417772 946925 := bbase (se 3 (by rfl) ⟨177548, by rfl⟩ : syracuseStep 946925 = 355097) (by norm_num)
theorem B946997 : Blo 417772 946997 := bbase (se 5 (by rfl) ⟨44390, by rfl⟩ : syracuseStep 946997 = 88781) (by norm_num)
theorem B947069 : Blo 417772 947069 := bbase (se 3 (by rfl) ⟨177575, by rfl⟩ : syracuseStep 947069 = 355151) (by norm_num)
theorem B947141 : Blo 417772 947141 := bbase (se 4 (by rfl) ⟨88794, by rfl⟩ : syracuseStep 947141 = 177589) (by norm_num)
theorem B947213 : Blo 417772 947213 := bbase (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) (by norm_num)
theorem B947285 : Blo 417772 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B1012829 : Blo 417772 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B947357 : Blo 417772 947357 := bbase (se 3 (by rfl) ⟨177629, by rfl⟩ : syracuseStep 947357 = 355259) (by norm_num)
theorem B1340597 : Blo 417772 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B2684117 : Blo 417772 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B947429 : Blo 417772 947429 := bbase (se 4 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 947429 = 177643) (by norm_num)
theorem B947501 : Blo 417772 947501 := bbase (se 3 (by rfl) ⟨177656, by rfl⟩ : syracuseStep 947501 = 355313) (by norm_num)
theorem B2127221 : Blo 417772 2127221 := bbase (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) (by norm_num)
theorem B947573 : Blo 417772 947573 := bbase (se 5 (by rfl) ⟨44417, by rfl⟩ : syracuseStep 947573 = 88835) (by norm_num)
theorem B947645 : Blo 417772 947645 := bbase (se 3 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 947645 = 355367) (by norm_num)
theorem B947717 : Blo 417772 947717 := bbase (se 4 (by rfl) ⟨88848, by rfl⟩ : syracuseStep 947717 = 177697) (by norm_num)
theorem B947789 : Blo 417772 947789 := bbase (se 3 (by rfl) ⟨177710, by rfl⟩ : syracuseStep 947789 = 355421) (by norm_num)
theorem B1799765 : Blo 417772 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B947861 : Blo 417772 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B947933 : Blo 417772 947933 := bbase (se 3 (by rfl) ⟨177737, by rfl⟩ : syracuseStep 947933 = 355475) (by norm_num)
theorem B849637 : Blo 417772 849637 := bbase (se 4 (by rfl) ⟨79653, by rfl⟩ : syracuseStep 849637 = 159307) (by norm_num)
theorem B948005 : Blo 417772 948005 := bbase (se 4 (by rfl) ⟨88875, by rfl⟩ : syracuseStep 948005 = 177751) (by norm_num)
theorem B948077 : Blo 417772 948077 := bbase (se 3 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 948077 = 355529) (by norm_num)
theorem B948149 : Blo 417772 948149 := bbase (se 5 (by rfl) ⟨44444, by rfl⟩ : syracuseStep 948149 = 88889) (by norm_num)
theorem B948221 : Blo 417772 948221 := bbase (se 3 (by rfl) ⟨177791, by rfl⟩ : syracuseStep 948221 = 355583) (by norm_num)
theorem B948293 : Blo 417772 948293 := bbase (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) (by norm_num)
theorem B948365 : Blo 417772 948365 := bbase (se 3 (by rfl) ⟨177818, by rfl⟩ : syracuseStep 948365 = 355637) (by norm_num)
theorem B1145029 : Blo 417772 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B948437 : Blo 417772 948437 := bbase (se 7 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 948437 = 22229) (by norm_num)
theorem B948509 : Blo 417772 948509 := bbase (se 3 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 948509 = 355691) (by norm_num)
theorem B948581 : Blo 417772 948581 := bbase (se 4 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 948581 = 177859) (by norm_num)
theorem B948653 : Blo 417772 948653 := bbase (se 3 (by rfl) ⟨177872, by rfl⟩ : syracuseStep 948653 = 355745) (by norm_num)
theorem B948725 : Blo 417772 948725 := bbase (se 5 (by rfl) ⟨44471, by rfl⟩ : syracuseStep 948725 = 88943) (by norm_num)
theorem B3176981 : Blo 417772 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B948797 : Blo 417772 948797 := bbase (se 3 (by rfl) ⟨177899, by rfl⟩ : syracuseStep 948797 = 355799) (by norm_num)
theorem B1342021 : Blo 417772 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B490093 : Blo 417772 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B2128517 : Blo 417772 2128517 := bbase (se 4 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 2128517 = 399097) (by norm_num)
theorem B948869 : Blo 417772 948869 := bbase (se 4 (by rfl) ⟨88956, by rfl⟩ : syracuseStep 948869 = 177913) (by norm_num)
theorem B948941 : Blo 417772 948941 := bbase (se 3 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 948941 = 355853) (by norm_num)
theorem B424693 : Blo 417772 424693 := bbase (se 5 (by rfl) ⟨19907, by rfl⟩ : syracuseStep 424693 = 39815) (by norm_num)
theorem B4029173 : Blo 417772 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B1440661 : Blo 417772 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1276901 : Blo 417772 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B2391029 : Blo 417772 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B1342469 : Blo 417772 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B752933 : Blo 417772 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B1801541 : Blo 417772 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B7142741 : Blo 417772 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B851285 : Blo 417772 851285 := bbase (se 11 (by rfl) ⟨623, by rfl⟩ : syracuseStep 851285 = 1247) (by norm_num)
theorem B2293109 : Blo 417772 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B1703605 : Blo 417772 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B2129813 : Blo 417772 2129813 := bbase (se 6 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 2129813 = 99835) (by norm_num)
theorem B425893 : Blo 417772 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B1147085 : Blo 417772 1147085 := bstep (se 3 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 1147085 = 430157) B430157
theorem B1344109 : Blo 417772 1344109 := bstep (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) B504041
theorem B1278605 : Blo 417772 1278605 := bstep (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) B479477
theorem B2392739 : Blo 417772 2392739 := bstep (se 1 (by rfl) ⟨1794554, by rfl⟩ : syracuseStep 2392739 = 3589109) B3589109
theorem B41976917 : Blo 417772 41976917 := bstep (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) B491917
theorem B820433 : Blo 417772 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B1410317 : Blo 417772 1410317 := bstep (se 3 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 1410317 = 528869) B528869
theorem B1410371 : Blo 417772 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B1344995 : Blo 417772 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B1410641 : Blo 417772 1410641 := bstep (se 2 (by rfl) ⟨528990, by rfl⟩ : syracuseStep 1410641 = 1057981) B1057981
theorem B2262691 : Blo 417772 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B3835633 : Blo 417772 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B5736419 : Blo 417772 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B1411181 : Blo 417772 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B2132081 : Blo 417772 2132081 := bstep (se 2 (by rfl) ⟨799530, by rfl⟩ : syracuseStep 2132081 = 1599061) B1599061
theorem B1411235 : Blo 417772 1411235 := bstep (se 1 (by rfl) ⟨1058426, by rfl⟩ : syracuseStep 1411235 = 2116853) B2116853
theorem B10455317 : Blo 417772 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B1280305 : Blo 417772 1280305 := bstep (se 2 (by rfl) ⟨480114, by rfl⟩ : syracuseStep 1280305 = 960229) B960229
theorem B3180869 : Blo 417772 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B2591117 : Blo 417772 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B1411505 : Blo 417772 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B4786613 : Blo 417772 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B2394629 : Blo 417772 2394629 := bstep (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) B448993
theorem B5376739 : Blo 417772 5376739 := bstep (se 1 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 5376739 = 8065109) B8065109
theorem B1412045 : Blo 417772 1412045 := bstep (se 3 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 1412045 = 529517) B529517
theorem B1412099 : Blo 417772 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B3574925 : Blo 417772 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B953507 : Blo 417772 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B1281233 : Blo 417772 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B1412369 : Blo 417772 1412369 := bstep (se 2 (by rfl) ⟨529638, by rfl⟩ : syracuseStep 1412369 = 1059277) B1059277
theorem B757027 : Blo 417772 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B1281329 : Blo 417772 1281329 := bstep (se 2 (by rfl) ⟨480498, by rfl⟩ : syracuseStep 1281329 = 960997) B960997
theorem B16289221 : Blo 417772 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B4525553 : Blo 417772 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B2133539 : Blo 417772 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B1347185 : Blo 417772 1347185 := bstep (se 2 (by rfl) ⟨505194, by rfl⟩ : syracuseStep 1347185 = 1010389) B1010389
theorem B5738165 : Blo 417772 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B1347313 : Blo 417772 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B1412909 : Blo 417772 1412909 := bstep (se 3 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 1412909 = 529841) B529841
theorem B1412963 : Blo 417772 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B3411811 : Blo 417772 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B1347569 : Blo 417772 1347569 := bstep (se 2 (by rfl) ⟨505338, by rfl⟩ : syracuseStep 1347569 = 1010677) B1010677
theorem B626675 : Blo 417772 626675 := bstep (se 1 (by rfl) ⟨470006, by rfl⟩ : syracuseStep 626675 = 940013) B940013
theorem B626705 : Blo 417772 626705 := bstep (se 2 (by rfl) ⟨235014, by rfl⟩ : syracuseStep 626705 = 470029) B470029
theorem B757777 : Blo 417772 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B626723 : Blo 417772 626723 := bstep (se 1 (by rfl) ⟨470042, by rfl⟩ : syracuseStep 626723 = 940085) B940085
theorem B626753 : Blo 417772 626753 := bstep (se 2 (by rfl) ⟨235032, by rfl⟩ : syracuseStep 626753 = 470065) B470065
theorem B626771 : Blo 417772 626771 := bstep (se 1 (by rfl) ⟨470078, by rfl⟩ : syracuseStep 626771 = 940157) B940157
theorem B626801 : Blo 417772 626801 := bstep (se 2 (by rfl) ⟨235050, by rfl⟩ : syracuseStep 626801 = 470101) B470101
theorem B1413233 : Blo 417772 1413233 := bstep (se 2 (by rfl) ⟨529962, by rfl⟩ : syracuseStep 1413233 = 1059925) B1059925
theorem B626819 : Blo 417772 626819 := bstep (se 1 (by rfl) ⟨470114, by rfl⟩ : syracuseStep 626819 = 940229) B940229
theorem B626849 : Blo 417772 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B626867 : Blo 417772 626867 := bstep (se 1 (by rfl) ⟨470150, by rfl⟩ : syracuseStep 626867 = 940301) B940301
theorem B692417 : Blo 417772 692417 := bstep (se 2 (by rfl) ⟨259656, by rfl⟩ : syracuseStep 692417 = 519313) B519313
theorem B626897 : Blo 417772 626897 := bstep (se 2 (by rfl) ⟨235086, by rfl⟩ : syracuseStep 626897 = 470173) B470173
theorem B626915 : Blo 417772 626915 := bstep (se 1 (by rfl) ⟨470186, by rfl⟩ : syracuseStep 626915 = 940373) B940373
theorem B4559075 : Blo 417772 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B626945 : Blo 417772 626945 := bstep (se 2 (by rfl) ⟨235104, by rfl⟩ : syracuseStep 626945 = 470209) B470209
theorem B626963 : Blo 417772 626963 := bstep (se 1 (by rfl) ⟨470222, by rfl⟩ : syracuseStep 626963 = 940445) B940445
theorem B626993 : Blo 417772 626993 := bstep (se 2 (by rfl) ⟨235122, by rfl⟩ : syracuseStep 626993 = 470245) B470245
theorem B627011 : Blo 417772 627011 := bstep (se 1 (by rfl) ⟨470258, by rfl⟩ : syracuseStep 627011 = 940517) B940517
theorem B2134349 : Blo 417772 2134349 := bstep (se 3 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 2134349 = 800381) B800381
theorem B627041 : Blo 417772 627041 := bstep (se 2 (by rfl) ⟨235140, by rfl⟩ : syracuseStep 627041 = 470281) B470281
theorem B627059 : Blo 417772 627059 := bstep (se 1 (by rfl) ⟨470294, by rfl⟩ : syracuseStep 627059 = 940589) B940589
theorem B627089 : Blo 417772 627089 := bstep (se 2 (by rfl) ⟨235158, by rfl⟩ : syracuseStep 627089 = 470317) B470317
theorem B627107 : Blo 417772 627107 := bstep (se 1 (by rfl) ⟨470330, by rfl⟩ : syracuseStep 627107 = 940661) B940661
theorem B627137 : Blo 417772 627137 := bstep (se 2 (by rfl) ⟨235176, by rfl⟩ : syracuseStep 627137 = 470353) B470353
theorem B627155 : Blo 417772 627155 := bstep (se 1 (by rfl) ⟨470366, by rfl⟩ : syracuseStep 627155 = 940733) B940733
theorem B627185 : Blo 417772 627185 := bstep (se 2 (by rfl) ⟨235194, by rfl⟩ : syracuseStep 627185 = 470389) B470389
theorem B922097 : Blo 417772 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B627203 : Blo 417772 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B627233 : Blo 417772 627233 := bstep (se 2 (by rfl) ⟨235212, by rfl⟩ : syracuseStep 627233 = 470425) B470425
theorem B627251 : Blo 417772 627251 := bstep (se 1 (by rfl) ⟨470438, by rfl⟩ : syracuseStep 627251 = 940877) B940877
theorem B627281 : Blo 417772 627281 := bstep (se 2 (by rfl) ⟨235230, by rfl⟩ : syracuseStep 627281 = 470461) B470461
theorem B627299 : Blo 417772 627299 := bstep (se 1 (by rfl) ⟨470474, by rfl⟩ : syracuseStep 627299 = 940949) B940949
theorem B627329 : Blo 417772 627329 := bstep (se 2 (by rfl) ⟨235248, by rfl⟩ : syracuseStep 627329 = 470497) B470497
theorem B1413773 : Blo 417772 1413773 := bstep (se 3 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 1413773 = 530165) B530165
theorem B627347 : Blo 417772 627347 := bstep (se 1 (by rfl) ⟨470510, by rfl⟩ : syracuseStep 627347 = 941021) B941021
theorem B627377 : Blo 417772 627377 := bstep (se 2 (by rfl) ⟨235266, by rfl⟩ : syracuseStep 627377 = 470533) B470533
theorem B627395 : Blo 417772 627395 := bstep (se 1 (by rfl) ⟨470546, by rfl⟩ : syracuseStep 627395 = 941093) B941093
theorem B1413827 : Blo 417772 1413827 := bstep (se 1 (by rfl) ⟨1060370, by rfl⟩ : syracuseStep 1413827 = 2120741) B2120741
theorem B627425 : Blo 417772 627425 := bstep (se 2 (by rfl) ⟨235284, by rfl⟩ : syracuseStep 627425 = 470569) B470569
theorem B2757361 : Blo 417772 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B627443 : Blo 417772 627443 := bstep (se 1 (by rfl) ⟨470582, by rfl⟩ : syracuseStep 627443 = 941165) B941165
theorem B627473 : Blo 417772 627473 := bstep (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) B470605
theorem B627491 : Blo 417772 627491 := bstep (se 1 (by rfl) ⟨470618, by rfl⟩ : syracuseStep 627491 = 941237) B941237
theorem B627521 : Blo 417772 627521 := bstep (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) B470641
theorem B627539 : Blo 417772 627539 := bstep (se 1 (by rfl) ⟨470654, by rfl⟩ : syracuseStep 627539 = 941309) B941309
theorem B627569 : Blo 417772 627569 := bstep (se 2 (by rfl) ⟨235338, by rfl⟩ : syracuseStep 627569 = 470677) B470677
theorem B627587 : Blo 417772 627587 := bstep (se 1 (by rfl) ⟨470690, by rfl⟩ : syracuseStep 627587 = 941381) B941381
theorem B3216269 : Blo 417772 3216269 := bstep (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) B1206101
theorem B627617 : Blo 417772 627617 := bstep (se 2 (by rfl) ⟨235356, by rfl⟩ : syracuseStep 627617 = 470713) B470713
theorem B627635 : Blo 417772 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B627665 : Blo 417772 627665 := bstep (se 2 (by rfl) ⟨235374, by rfl⟩ : syracuseStep 627665 = 470749) B470749
theorem B1414097 : Blo 417772 1414097 := bstep (se 2 (by rfl) ⟨530286, by rfl⟩ : syracuseStep 1414097 = 1060573) B1060573
theorem B627683 : Blo 417772 627683 := bstep (se 1 (by rfl) ⟨470762, by rfl⟩ : syracuseStep 627683 = 941525) B941525
theorem B627713 : Blo 417772 627713 := bstep (se 2 (by rfl) ⟨235392, by rfl⟩ : syracuseStep 627713 = 470785) B470785
theorem B529411 : Blo 417772 529411 := bstep (se 1 (by rfl) ⟨397058, by rfl⟩ : syracuseStep 529411 = 794117) B794117
theorem B627731 : Blo 417772 627731 := bstep (se 1 (by rfl) ⟨470798, by rfl⟩ : syracuseStep 627731 = 941597) B941597
theorem B627761 : Blo 417772 627761 := bstep (se 2 (by rfl) ⟨235410, by rfl⟩ : syracuseStep 627761 = 470821) B470821
theorem B627779 : Blo 417772 627779 := bstep (se 1 (by rfl) ⟨470834, by rfl⟩ : syracuseStep 627779 = 941669) B941669
theorem B627809 : Blo 417772 627809 := bstep (se 2 (by rfl) ⟨235428, by rfl⟩ : syracuseStep 627809 = 470857) B470857
theorem B529507 : Blo 417772 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B627827 : Blo 417772 627827 := bstep (se 1 (by rfl) ⟨470870, by rfl⟩ : syracuseStep 627827 = 941741) B941741
theorem B627857 : Blo 417772 627857 := bstep (se 2 (by rfl) ⟨235446, by rfl⟩ : syracuseStep 627857 = 470893) B470893
theorem B627875 : Blo 417772 627875 := bstep (se 1 (by rfl) ⟨470906, by rfl⟩ : syracuseStep 627875 = 941813) B941813
theorem B627905 : Blo 417772 627905 := bstep (se 2 (by rfl) ⟨235464, by rfl⟩ : syracuseStep 627905 = 470929) B470929
theorem B627923 : Blo 417772 627923 := bstep (se 1 (by rfl) ⟨470942, by rfl⟩ : syracuseStep 627923 = 941885) B941885
theorem B627953 : Blo 417772 627953 := bstep (se 2 (by rfl) ⟨235482, by rfl⟩ : syracuseStep 627953 = 470965) B470965
theorem B627971 : Blo 417772 627971 := bstep (se 1 (by rfl) ⟨470978, by rfl⟩ : syracuseStep 627971 = 941957) B941957
theorem B628001 : Blo 417772 628001 := bstep (se 2 (by rfl) ⟨235500, by rfl⟩ : syracuseStep 628001 = 471001) B471001
theorem B628019 : Blo 417772 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B628049 : Blo 417772 628049 := bstep (se 2 (by rfl) ⟨235518, by rfl⟩ : syracuseStep 628049 = 471037) B471037
theorem B595297 : Blo 417772 595297 := bstep (se 2 (by rfl) ⟨223236, by rfl⟩ : syracuseStep 595297 = 446473) B446473
theorem B628067 : Blo 417772 628067 := bstep (se 1 (by rfl) ⟨471050, by rfl⟩ : syracuseStep 628067 = 942101) B942101
theorem B628097 : Blo 417772 628097 := bstep (se 2 (by rfl) ⟨235536, by rfl⟩ : syracuseStep 628097 = 471073) B471073
theorem B628115 : Blo 417772 628115 := bstep (se 1 (by rfl) ⟨471086, by rfl⟩ : syracuseStep 628115 = 942173) B942173
theorem B628145 : Blo 417772 628145 := bstep (se 2 (by rfl) ⟨235554, by rfl⟩ : syracuseStep 628145 = 471109) B471109
theorem B628163 : Blo 417772 628163 := bstep (se 1 (by rfl) ⟨471122, by rfl⟩ : syracuseStep 628163 = 942245) B942245
theorem B628193 : Blo 417772 628193 := bstep (se 2 (by rfl) ⟨235572, by rfl⟩ : syracuseStep 628193 = 471145) B471145
theorem B1414637 : Blo 417772 1414637 := bstep (se 3 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 1414637 = 530489) B530489
theorem B628211 : Blo 417772 628211 := bstep (se 1 (by rfl) ⟨471158, by rfl⟩ : syracuseStep 628211 = 942317) B942317
theorem B628241 : Blo 417772 628241 := bstep (se 2 (by rfl) ⟨235590, by rfl⟩ : syracuseStep 628241 = 471181) B471181
theorem B628259 : Blo 417772 628259 := bstep (se 1 (by rfl) ⟨471194, by rfl⟩ : syracuseStep 628259 = 942389) B942389
theorem B1414691 : Blo 417772 1414691 := bstep (se 1 (by rfl) ⟨1061018, by rfl⟩ : syracuseStep 1414691 = 2122037) B2122037
theorem B628289 : Blo 417772 628289 := bstep (se 2 (by rfl) ⟨235608, by rfl⟩ : syracuseStep 628289 = 471217) B471217
theorem B530003 : Blo 417772 530003 := bstep (se 1 (by rfl) ⟨397502, by rfl⟩ : syracuseStep 530003 = 795005) B795005
theorem B628307 : Blo 417772 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B628337 : Blo 417772 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B628355 : Blo 417772 628355 := bstep (se 1 (by rfl) ⟨471266, by rfl⟩ : syracuseStep 628355 = 942533) B942533
theorem B1349261 : Blo 417772 1349261 := bstep (se 3 (by rfl) ⟨252986, by rfl⟩ : syracuseStep 1349261 = 505973) B505973
theorem B628385 : Blo 417772 628385 := bstep (se 2 (by rfl) ⟨235644, by rfl⟩ : syracuseStep 628385 = 471289) B471289
theorem B628403 : Blo 417772 628403 := bstep (se 1 (by rfl) ⟨471302, by rfl⟩ : syracuseStep 628403 = 942605) B942605
theorem B628433 : Blo 417772 628433 := bstep (se 2 (by rfl) ⟨235662, by rfl⟩ : syracuseStep 628433 = 471325) B471325
theorem B628451 : Blo 417772 628451 := bstep (se 1 (by rfl) ⟨471338, by rfl⟩ : syracuseStep 628451 = 942677) B942677
theorem B628481 : Blo 417772 628481 := bstep (se 2 (by rfl) ⟨235680, by rfl⟩ : syracuseStep 628481 = 471361) B471361
theorem B628499 : Blo 417772 628499 := bstep (se 1 (by rfl) ⟨471374, by rfl⟩ : syracuseStep 628499 = 942749) B942749
theorem B628529 : Blo 417772 628529 := bstep (se 2 (by rfl) ⟨235698, by rfl⟩ : syracuseStep 628529 = 471397) B471397
theorem B1414961 : Blo 417772 1414961 := bstep (se 2 (by rfl) ⟨530610, by rfl⟩ : syracuseStep 1414961 = 1061221) B1061221
theorem B5084981 : Blo 417772 5084981 := bstep (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) B476717
theorem B628547 : Blo 417772 628547 := bstep (se 1 (by rfl) ⟨471410, by rfl⟩ : syracuseStep 628547 = 942821) B942821
theorem B628577 : Blo 417772 628577 := bstep (se 2 (by rfl) ⟨235716, by rfl⟩ : syracuseStep 628577 = 471433) B471433
theorem B628595 : Blo 417772 628595 := bstep (se 1 (by rfl) ⟨471446, by rfl⟩ : syracuseStep 628595 = 942893) B942893
theorem B628625 : Blo 417772 628625 := bstep (se 2 (by rfl) ⟨235734, by rfl⟩ : syracuseStep 628625 = 471469) B471469
theorem B628643 : Blo 417772 628643 := bstep (se 1 (by rfl) ⟨471482, by rfl⟩ : syracuseStep 628643 = 942965) B942965
theorem B628673 : Blo 417772 628673 := bstep (se 2 (by rfl) ⟨235752, by rfl⟩ : syracuseStep 628673 = 471505) B471505
theorem B628691 : Blo 417772 628691 := bstep (se 1 (by rfl) ⟨471518, by rfl⟩ : syracuseStep 628691 = 943037) B943037
theorem B628721 : Blo 417772 628721 := bstep (se 2 (by rfl) ⟨235770, by rfl⟩ : syracuseStep 628721 = 471541) B471541
theorem B628739 : Blo 417772 628739 := bstep (se 1 (by rfl) ⟨471554, by rfl⟩ : syracuseStep 628739 = 943109) B943109
theorem B628769 : Blo 417772 628769 := bstep (se 2 (by rfl) ⟨235788, by rfl⟩ : syracuseStep 628769 = 471577) B471577
theorem B596003 : Blo 417772 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B1513507 : Blo 417772 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B628787 : Blo 417772 628787 := bstep (se 1 (by rfl) ⟨471590, by rfl⟩ : syracuseStep 628787 = 943181) B943181
theorem B2693189 : Blo 417772 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B628817 : Blo 417772 628817 := bstep (se 2 (by rfl) ⟨235806, by rfl⟩ : syracuseStep 628817 = 471613) B471613
theorem B628835 : Blo 417772 628835 := bstep (se 1 (by rfl) ⟨471626, by rfl⟩ : syracuseStep 628835 = 943253) B943253
theorem B628865 : Blo 417772 628865 := bstep (se 2 (by rfl) ⟨235824, by rfl⟩ : syracuseStep 628865 = 471649) B471649
theorem B628883 : Blo 417772 628883 := bstep (se 1 (by rfl) ⟨471662, by rfl⟩ : syracuseStep 628883 = 943325) B943325
theorem B628913 : Blo 417772 628913 := bstep (se 2 (by rfl) ⟨235842, by rfl⟩ : syracuseStep 628913 = 471685) B471685
theorem B628931 : Blo 417772 628931 := bstep (se 1 (by rfl) ⟨471698, by rfl⟩ : syracuseStep 628931 = 943397) B943397
theorem B628961 : Blo 417772 628961 := bstep (se 2 (by rfl) ⟨235860, by rfl⟩ : syracuseStep 628961 = 471721) B471721
theorem B628979 : Blo 417772 628979 := bstep (se 1 (by rfl) ⟨471734, by rfl⟩ : syracuseStep 628979 = 943469) B943469
theorem B629009 : Blo 417772 629009 := bstep (se 2 (by rfl) ⟨235878, by rfl⟩ : syracuseStep 629009 = 471757) B471757
theorem B530707 : Blo 417772 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B629027 : Blo 417772 629027 := bstep (se 1 (by rfl) ⟨471770, by rfl⟩ : syracuseStep 629027 = 943541) B943541
theorem B629057 : Blo 417772 629057 := bstep (se 2 (by rfl) ⟨235896, by rfl⟩ : syracuseStep 629057 = 471793) B471793
theorem B1415501 : Blo 417772 1415501 := bstep (se 3 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 1415501 = 530813) B530813
theorem B629075 : Blo 417772 629075 := bstep (se 1 (by rfl) ⟨471806, by rfl⟩ : syracuseStep 629075 = 943613) B943613
theorem B629105 : Blo 417772 629105 := bstep (se 2 (by rfl) ⟨235914, by rfl⟩ : syracuseStep 629105 = 471829) B471829
theorem B530803 : Blo 417772 530803 := bstep (se 1 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 530803 = 796205) B796205
theorem B629123 : Blo 417772 629123 := bstep (se 1 (by rfl) ⟨471842, by rfl⟩ : syracuseStep 629123 = 943685) B943685
theorem B1415555 : Blo 417772 1415555 := bstep (se 1 (by rfl) ⟨1061666, by rfl⟩ : syracuseStep 1415555 = 2123333) B2123333
theorem B1350029 : Blo 417772 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B629153 : Blo 417772 629153 := bstep (se 2 (by rfl) ⟨235932, by rfl⟩ : syracuseStep 629153 = 471865) B471865
theorem B629171 : Blo 417772 629171 := bstep (se 1 (by rfl) ⟨471878, by rfl⟩ : syracuseStep 629171 = 943757) B943757
theorem B629201 : Blo 417772 629201 := bstep (se 2 (by rfl) ⟨235950, by rfl⟩ : syracuseStep 629201 = 471901) B471901
theorem B629219 : Blo 417772 629219 := bstep (se 1 (by rfl) ⟨471914, by rfl⟩ : syracuseStep 629219 = 943829) B943829
theorem B2103779 : Blo 417772 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B629249 : Blo 417772 629249 := bstep (se 2 (by rfl) ⟨235968, by rfl⟩ : syracuseStep 629249 = 471937) B471937
theorem B629267 : Blo 417772 629267 := bstep (se 1 (by rfl) ⟨471950, by rfl⟩ : syracuseStep 629267 = 943901) B943901
theorem B629297 : Blo 417772 629297 := bstep (se 2 (by rfl) ⟨235986, by rfl⟩ : syracuseStep 629297 = 471973) B471973
theorem B6068789 : Blo 417772 6068789 := bstep (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) B568949
theorem B629315 : Blo 417772 629315 := bstep (se 1 (by rfl) ⟨471986, by rfl⟩ : syracuseStep 629315 = 943973) B943973
theorem B629345 : Blo 417772 629345 := bstep (se 2 (by rfl) ⟨236004, by rfl⟩ : syracuseStep 629345 = 472009) B472009
theorem B629363 : Blo 417772 629363 := bstep (se 1 (by rfl) ⟨472022, by rfl⟩ : syracuseStep 629363 = 944045) B944045
theorem B1415825 : Blo 417772 1415825 := bstep (se 2 (by rfl) ⟨530934, by rfl⟩ : syracuseStep 1415825 = 1061869) B1061869
theorem B629393 : Blo 417772 629393 := bstep (se 2 (by rfl) ⟨236022, by rfl⟩ : syracuseStep 629393 = 472045) B472045
theorem B596641 : Blo 417772 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B629411 : Blo 417772 629411 := bstep (se 1 (by rfl) ⟨472058, by rfl⟩ : syracuseStep 629411 = 944117) B944117
theorem B629441 : Blo 417772 629441 := bstep (se 2 (by rfl) ⟨236040, by rfl⟩ : syracuseStep 629441 = 472081) B472081
theorem B629459 : Blo 417772 629459 := bstep (se 1 (by rfl) ⟨472094, by rfl⟩ : syracuseStep 629459 = 944189) B944189
theorem B629489 : Blo 417772 629489 := bstep (se 2 (by rfl) ⟨236058, by rfl⟩ : syracuseStep 629489 = 472117) B472117
theorem B629507 : Blo 417772 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B596755 : Blo 417772 596755 := bstep (se 1 (by rfl) ⟨447566, by rfl⟩ : syracuseStep 596755 = 895133) B895133
theorem B629537 : Blo 417772 629537 := bstep (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) B472153
theorem B629555 : Blo 417772 629555 := bstep (se 1 (by rfl) ⟨472166, by rfl⟩ : syracuseStep 629555 = 944333) B944333
theorem B629585 : Blo 417772 629585 := bstep (se 2 (by rfl) ⟨236094, by rfl⟩ : syracuseStep 629585 = 472189) B472189
theorem B629603 : Blo 417772 629603 := bstep (se 1 (by rfl) ⟨472202, by rfl⟩ : syracuseStep 629603 = 944405) B944405
theorem B531299 : Blo 417772 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B629633 : Blo 417772 629633 := bstep (se 2 (by rfl) ⟨236112, by rfl⟩ : syracuseStep 629633 = 472225) B472225
theorem B1350541 : Blo 417772 1350541 := bstep (se 3 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 1350541 = 506453) B506453
theorem B629651 : Blo 417772 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B629681 : Blo 417772 629681 := bstep (se 2 (by rfl) ⟨236130, by rfl⟩ : syracuseStep 629681 = 472261) B472261
theorem B629699 : Blo 417772 629699 := bstep (se 1 (by rfl) ⟨472274, by rfl⟩ : syracuseStep 629699 = 944549) B944549
theorem B629729 : Blo 417772 629729 := bstep (se 2 (by rfl) ⟨236148, by rfl⟩ : syracuseStep 629729 = 472297) B472297
theorem B629747 : Blo 417772 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B629777 : Blo 417772 629777 := bstep (se 2 (by rfl) ⟨236166, by rfl⟩ : syracuseStep 629777 = 472333) B472333
theorem B629795 : Blo 417772 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B629825 : Blo 417772 629825 := bstep (se 2 (by rfl) ⟨236184, by rfl⟩ : syracuseStep 629825 = 472369) B472369
theorem B629843 : Blo 417772 629843 := bstep (se 1 (by rfl) ⟨472382, by rfl⟩ : syracuseStep 629843 = 944765) B944765
theorem B629873 : Blo 417772 629873 := bstep (se 2 (by rfl) ⟨236202, by rfl⟩ : syracuseStep 629873 = 472405) B472405
theorem B629891 : Blo 417772 629891 := bstep (se 1 (by rfl) ⟨472418, by rfl⟩ : syracuseStep 629891 = 944837) B944837
theorem B629921 : Blo 417772 629921 := bstep (se 2 (by rfl) ⟨236220, by rfl⟩ : syracuseStep 629921 = 472441) B472441
theorem B1416365 : Blo 417772 1416365 := bstep (se 3 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 1416365 = 531137) B531137
theorem B629939 : Blo 417772 629939 := bstep (se 1 (by rfl) ⟨472454, by rfl⟩ : syracuseStep 629939 = 944909) B944909
theorem B629969 : Blo 417772 629969 := bstep (se 2 (by rfl) ⟨236238, by rfl⟩ : syracuseStep 629969 = 472477) B472477
theorem B1416419 : Blo 417772 1416419 := bstep (se 1 (by rfl) ⟨1062314, by rfl⟩ : syracuseStep 1416419 = 2124629) B2124629
theorem B629987 : Blo 417772 629987 := bstep (se 1 (by rfl) ⟨472490, by rfl⟩ : syracuseStep 629987 = 944981) B944981
theorem B630017 : Blo 417772 630017 := bstep (se 2 (by rfl) ⟨236256, by rfl⟩ : syracuseStep 630017 = 472513) B472513
theorem B1907981 : Blo 417772 1907981 := bstep (se 3 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 1907981 = 715493) B715493
theorem B630035 : Blo 417772 630035 := bstep (se 1 (by rfl) ⟨472526, by rfl⟩ : syracuseStep 630035 = 945053) B945053
theorem B630065 : Blo 417772 630065 := bstep (se 2 (by rfl) ⟨236274, by rfl⟩ : syracuseStep 630065 = 472549) B472549
theorem B630083 : Blo 417772 630083 := bstep (se 1 (by rfl) ⟨472562, by rfl⟩ : syracuseStep 630083 = 945125) B945125
theorem B630113 : Blo 417772 630113 := bstep (se 2 (by rfl) ⟨236292, by rfl⟩ : syracuseStep 630113 = 472585) B472585
theorem B630131 : Blo 417772 630131 := bstep (se 1 (by rfl) ⟨472598, by rfl⟩ : syracuseStep 630131 = 945197) B945197
theorem B1351043 : Blo 417772 1351043 := bstep (se 1 (by rfl) ⟨1013282, by rfl⟩ : syracuseStep 1351043 = 2026565) B2026565
theorem B630161 : Blo 417772 630161 := bstep (se 2 (by rfl) ⟨236310, by rfl⟩ : syracuseStep 630161 = 472621) B472621
theorem B630179 : Blo 417772 630179 := bstep (se 1 (by rfl) ⟨472634, by rfl⟩ : syracuseStep 630179 = 945269) B945269
theorem B794033 : Blo 417772 794033 := bstep (se 2 (by rfl) ⟨297762, by rfl⟩ : syracuseStep 794033 = 595525) B595525
theorem B630209 : Blo 417772 630209 := bstep (se 2 (by rfl) ⟨236328, by rfl⟩ : syracuseStep 630209 = 472657) B472657
theorem B630227 : Blo 417772 630227 := bstep (se 1 (by rfl) ⟨472670, by rfl⟩ : syracuseStep 630227 = 945341) B945341
theorem B1416689 : Blo 417772 1416689 := bstep (se 2 (by rfl) ⟨531258, by rfl⟩ : syracuseStep 1416689 = 1062517) B1062517
theorem B630257 : Blo 417772 630257 := bstep (se 2 (by rfl) ⟨236346, by rfl⟩ : syracuseStep 630257 = 472693) B472693
theorem B630275 : Blo 417772 630275 := bstep (se 1 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 630275 = 945413) B945413
theorem B892433 : Blo 417772 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B630305 : Blo 417772 630305 := bstep (se 2 (by rfl) ⟨236364, by rfl⟩ : syracuseStep 630305 = 472729) B472729
theorem B892451 : Blo 417772 892451 := bstep (se 1 (by rfl) ⟨669338, by rfl⟩ : syracuseStep 892451 = 1338677) B1338677
theorem B532003 : Blo 417772 532003 := bstep (se 1 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 532003 = 798005) B798005
theorem B630323 : Blo 417772 630323 := bstep (se 1 (by rfl) ⟨472742, by rfl⟩ : syracuseStep 630323 = 945485) B945485
theorem B630353 : Blo 417772 630353 := bstep (se 2 (by rfl) ⟨236382, by rfl⟩ : syracuseStep 630353 = 472765) B472765
theorem B630371 : Blo 417772 630371 := bstep (se 1 (by rfl) ⟨472778, by rfl⟩ : syracuseStep 630371 = 945557) B945557
theorem B630401 : Blo 417772 630401 := bstep (se 2 (by rfl) ⟨236400, by rfl⟩ : syracuseStep 630401 = 472801) B472801
theorem B532099 : Blo 417772 532099 := bstep (se 1 (by rfl) ⟨399074, by rfl⟩ : syracuseStep 532099 = 798149) B798149
theorem B1384067 : Blo 417772 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B630419 : Blo 417772 630419 := bstep (se 1 (by rfl) ⟨472814, by rfl⟩ : syracuseStep 630419 = 945629) B945629
theorem B630449 : Blo 417772 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B630467 : Blo 417772 630467 := bstep (se 1 (by rfl) ⟨472850, by rfl⟩ : syracuseStep 630467 = 945701) B945701
theorem B630497 : Blo 417772 630497 := bstep (se 2 (by rfl) ⟨236436, by rfl⟩ : syracuseStep 630497 = 472873) B472873
theorem B630515 : Blo 417772 630515 := bstep (se 1 (by rfl) ⟨472886, by rfl⟩ : syracuseStep 630515 = 945773) B945773
theorem B630545 : Blo 417772 630545 := bstep (se 2 (by rfl) ⟨236454, by rfl⟩ : syracuseStep 630545 = 472909) B472909
theorem B630563 : Blo 417772 630563 := bstep (se 1 (by rfl) ⟨472922, by rfl⟩ : syracuseStep 630563 = 945845) B945845
theorem B630593 : Blo 417772 630593 := bstep (se 2 (by rfl) ⟨236472, by rfl⟩ : syracuseStep 630593 = 472945) B472945
theorem B630611 : Blo 417772 630611 := bstep (se 1 (by rfl) ⟨472958, by rfl⟩ : syracuseStep 630611 = 945917) B945917
theorem B4595555 : Blo 417772 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B630641 : Blo 417772 630641 := bstep (se 2 (by rfl) ⟨236490, by rfl⟩ : syracuseStep 630641 = 472981) B472981
theorem B630659 : Blo 417772 630659 := bstep (se 1 (by rfl) ⟨472994, by rfl⟩ : syracuseStep 630659 = 945989) B945989
theorem B630689 : Blo 417772 630689 := bstep (se 2 (by rfl) ⟨236508, by rfl⟩ : syracuseStep 630689 = 473017) B473017
theorem B630707 : Blo 417772 630707 := bstep (se 1 (by rfl) ⟨473030, by rfl⟩ : syracuseStep 630707 = 946061) B946061
theorem B630737 : Blo 417772 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B565219 : Blo 417772 565219 := bstep (se 1 (by rfl) ⟨423914, by rfl⟩ : syracuseStep 565219 = 847829) B847829
theorem B630755 : Blo 417772 630755 := bstep (se 1 (by rfl) ⟨473066, by rfl⟩ : syracuseStep 630755 = 946133) B946133
theorem B630785 : Blo 417772 630785 := bstep (se 2 (by rfl) ⟨236544, by rfl⟩ : syracuseStep 630785 = 473089) B473089
theorem B3186701 : Blo 417772 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B1417229 : Blo 417772 1417229 := bstep (se 3 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 1417229 = 531461) B531461
theorem B630803 : Blo 417772 630803 := bstep (se 1 (by rfl) ⟨473102, by rfl⟩ : syracuseStep 630803 = 946205) B946205
theorem B630833 : Blo 417772 630833 := bstep (se 2 (by rfl) ⟨236562, by rfl⟩ : syracuseStep 630833 = 473125) B473125
theorem B1417283 : Blo 417772 1417283 := bstep (se 1 (by rfl) ⟨1062962, by rfl⟩ : syracuseStep 1417283 = 2125925) B2125925
theorem B630851 : Blo 417772 630851 := bstep (se 1 (by rfl) ⟨473138, by rfl⟩ : syracuseStep 630851 = 946277) B946277
theorem B598099 : Blo 417772 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B39297109 : Blo 417772 39297109 := bstep (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) B460513
theorem B630881 : Blo 417772 630881 := bstep (se 2 (by rfl) ⟨236580, by rfl⟩ : syracuseStep 630881 = 473161) B473161
theorem B34480241 : Blo 417772 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B532595 : Blo 417772 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B630899 : Blo 417772 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B630929 : Blo 417772 630929 := bstep (se 2 (by rfl) ⟨236598, by rfl⟩ : syracuseStep 630929 = 473197) B473197
theorem B630947 : Blo 417772 630947 := bstep (se 1 (by rfl) ⟨473210, by rfl⟩ : syracuseStep 630947 = 946421) B946421
theorem B630977 : Blo 417772 630977 := bstep (se 2 (by rfl) ⟨236616, by rfl⟩ : syracuseStep 630977 = 473233) B473233
theorem B2400461 : Blo 417772 2400461 := bstep (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) B900173
theorem B630995 : Blo 417772 630995 := bstep (se 1 (by rfl) ⟨473246, by rfl⟩ : syracuseStep 630995 = 946493) B946493
theorem B631025 : Blo 417772 631025 := bstep (se 2 (by rfl) ⟨236634, by rfl⟩ : syracuseStep 631025 = 473269) B473269
theorem B631043 : Blo 417772 631043 := bstep (se 1 (by rfl) ⟨473282, by rfl⟩ : syracuseStep 631043 = 946565) B946565
theorem B631073 : Blo 417772 631073 := bstep (se 2 (by rfl) ⟨236652, by rfl⟩ : syracuseStep 631073 = 473305) B473305
theorem B794929 : Blo 417772 794929 := bstep (se 2 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 794929 = 596197) B596197
theorem B631091 : Blo 417772 631091 := bstep (se 1 (by rfl) ⟨473318, by rfl⟩ : syracuseStep 631091 = 946637) B946637
theorem B1417553 : Blo 417772 1417553 := bstep (se 2 (by rfl) ⟨531582, by rfl⟩ : syracuseStep 1417553 = 1063165) B1063165
theorem B631121 : Blo 417772 631121 := bstep (se 2 (by rfl) ⟨236670, by rfl⟩ : syracuseStep 631121 = 473341) B473341
theorem B631139 : Blo 417772 631139 := bstep (se 1 (by rfl) ⟨473354, by rfl⟩ : syracuseStep 631139 = 946709) B946709
theorem B631169 : Blo 417772 631169 := bstep (se 2 (by rfl) ⟨236688, by rfl⟩ : syracuseStep 631169 = 473377) B473377
theorem B631187 : Blo 417772 631187 := bstep (se 1 (by rfl) ⟨473390, by rfl⟩ : syracuseStep 631187 = 946781) B946781
theorem B631217 : Blo 417772 631217 := bstep (se 2 (by rfl) ⟨236706, by rfl⟩ : syracuseStep 631217 = 473413) B473413
theorem B631235 : Blo 417772 631235 := bstep (se 1 (by rfl) ⟨473426, by rfl⟩ : syracuseStep 631235 = 946853) B946853
theorem B795089 : Blo 417772 795089 := bstep (se 2 (by rfl) ⟨298158, by rfl⟩ : syracuseStep 795089 = 596317) B596317
theorem B631265 : Blo 417772 631265 := bstep (se 2 (by rfl) ⟨236724, by rfl⟩ : syracuseStep 631265 = 473449) B473449
theorem B631283 : Blo 417772 631283 := bstep (se 1 (by rfl) ⟨473462, by rfl⟩ : syracuseStep 631283 = 946925) B946925
theorem B631313 : Blo 417772 631313 := bstep (se 2 (by rfl) ⟨236742, by rfl⟩ : syracuseStep 631313 = 473485) B473485
theorem B631331 : Blo 417772 631331 := bstep (se 1 (by rfl) ⟨473498, by rfl⟩ : syracuseStep 631331 = 946997) B946997
theorem B631361 : Blo 417772 631361 := bstep (se 2 (by rfl) ⟨236760, by rfl⟩ : syracuseStep 631361 = 473521) B473521
theorem B631379 : Blo 417772 631379 := bstep (se 1 (by rfl) ⟨473534, by rfl⟩ : syracuseStep 631379 = 947069) B947069
theorem B631409 : Blo 417772 631409 := bstep (se 2 (by rfl) ⟨236778, by rfl⟩ : syracuseStep 631409 = 473557) B473557
theorem B631427 : Blo 417772 631427 := bstep (se 1 (by rfl) ⟨473570, by rfl⟩ : syracuseStep 631427 = 947141) B947141
theorem B631457 : Blo 417772 631457 := bstep (se 2 (by rfl) ⟨236796, by rfl⟩ : syracuseStep 631457 = 473593) B473593
theorem B631475 : Blo 417772 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B2859725 : Blo 417772 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B631505 : Blo 417772 631505 := bstep (se 2 (by rfl) ⟨236814, by rfl⟩ : syracuseStep 631505 = 473629) B473629
theorem B631523 : Blo 417772 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B631553 : Blo 417772 631553 := bstep (se 2 (by rfl) ⟨236832, by rfl⟩ : syracuseStep 631553 = 473665) B473665
theorem B2007821 : Blo 417772 2007821 := bstep (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) B752933
theorem B631571 : Blo 417772 631571 := bstep (se 1 (by rfl) ⟨473678, by rfl⟩ : syracuseStep 631571 = 947357) B947357
theorem B631601 : Blo 417772 631601 := bstep (se 2 (by rfl) ⟨236850, by rfl⟩ : syracuseStep 631601 = 473701) B473701
theorem B533299 : Blo 417772 533299 := bstep (se 1 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 533299 = 799949) B799949
theorem B631619 : Blo 417772 631619 := bstep (se 1 (by rfl) ⟨473714, by rfl⟩ : syracuseStep 631619 = 947429) B947429
theorem B631649 : Blo 417772 631649 := bstep (se 2 (by rfl) ⟨236868, by rfl⟩ : syracuseStep 631649 = 473737) B473737
theorem B795491 : Blo 417772 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B1418093 : Blo 417772 1418093 := bstep (se 3 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 1418093 = 531785) B531785
theorem B631667 : Blo 417772 631667 := bstep (se 1 (by rfl) ⟨473750, by rfl⟩ : syracuseStep 631667 = 947501) B947501
theorem B2761613 : Blo 417772 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B631697 : Blo 417772 631697 := bstep (se 2 (by rfl) ⟨236886, by rfl⟩ : syracuseStep 631697 = 473773) B473773
theorem B533395 : Blo 417772 533395 := bstep (se 1 (by rfl) ⟨400046, by rfl⟩ : syracuseStep 533395 = 800093) B800093
theorem B1418147 : Blo 417772 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B631715 : Blo 417772 631715 := bstep (se 1 (by rfl) ⟨473786, by rfl⟩ : syracuseStep 631715 = 947573) B947573
theorem B631745 : Blo 417772 631745 := bstep (se 2 (by rfl) ⟨236904, by rfl⟩ : syracuseStep 631745 = 473809) B473809
theorem B631763 : Blo 417772 631763 := bstep (se 1 (by rfl) ⟨473822, by rfl⟩ : syracuseStep 631763 = 947645) B947645
theorem B566257 : Blo 417772 566257 := bstep (se 2 (by rfl) ⟨212346, by rfl⟩ : syracuseStep 566257 = 424693) B424693
theorem B631793 : Blo 417772 631793 := bstep (se 2 (by rfl) ⟨236922, by rfl⟩ : syracuseStep 631793 = 473845) B473845
theorem B631811 : Blo 417772 631811 := bstep (se 1 (by rfl) ⟨473858, by rfl⟩ : syracuseStep 631811 = 947717) B947717
theorem B631841 : Blo 417772 631841 := bstep (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) B473881
theorem B631859 : Blo 417772 631859 := bstep (se 1 (by rfl) ⟨473894, by rfl⟩ : syracuseStep 631859 = 947789) B947789
theorem B631889 : Blo 417772 631889 := bstep (se 2 (by rfl) ⟨236958, by rfl⟩ : syracuseStep 631889 = 473917) B473917
theorem B631907 : Blo 417772 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B631937 : Blo 417772 631937 := bstep (se 2 (by rfl) ⟨236976, by rfl⟩ : syracuseStep 631937 = 473953) B473953
theorem B631955 : Blo 417772 631955 := bstep (se 1 (by rfl) ⟨473966, by rfl⟩ : syracuseStep 631955 = 947933) B947933
theorem B1418417 : Blo 417772 1418417 := bstep (se 2 (by rfl) ⟨531906, by rfl⟩ : syracuseStep 1418417 = 1063813) B1063813
theorem B631985 : Blo 417772 631985 := bstep (se 2 (by rfl) ⟨236994, by rfl⟩ : syracuseStep 631985 = 473989) B473989
theorem B599233 : Blo 417772 599233 := bstep (se 2 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 599233 = 449425) B449425
theorem B632003 : Blo 417772 632003 := bstep (se 1 (by rfl) ⟨474002, by rfl⟩ : syracuseStep 632003 = 948005) B948005
theorem B632033 : Blo 417772 632033 := bstep (se 2 (by rfl) ⟨237012, by rfl⟩ : syracuseStep 632033 = 474025) B474025
theorem B632051 : Blo 417772 632051 := bstep (se 1 (by rfl) ⟨474038, by rfl⟩ : syracuseStep 632051 = 948077) B948077
theorem B632081 : Blo 417772 632081 := bstep (se 2 (by rfl) ⟨237030, by rfl⟩ : syracuseStep 632081 = 474061) B474061
theorem B599329 : Blo 417772 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B632099 : Blo 417772 632099 := bstep (se 1 (by rfl) ⟨474074, by rfl⟩ : syracuseStep 632099 = 948149) B948149
theorem B632129 : Blo 417772 632129 := bstep (se 2 (by rfl) ⟨237048, by rfl⟩ : syracuseStep 632129 = 474097) B474097
theorem B632147 : Blo 417772 632147 := bstep (se 1 (by rfl) ⟨474110, by rfl⟩ : syracuseStep 632147 = 948221) B948221
theorem B632177 : Blo 417772 632177 := bstep (se 2 (by rfl) ⟨237066, by rfl⟩ : syracuseStep 632177 = 474133) B474133
theorem B632195 : Blo 417772 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B632225 : Blo 417772 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B632243 : Blo 417772 632243 := bstep (se 1 (by rfl) ⟨474182, by rfl⟩ : syracuseStep 632243 = 948365) B948365
theorem B632273 : Blo 417772 632273 := bstep (se 2 (by rfl) ⟨237102, by rfl⟩ : syracuseStep 632273 = 474205) B474205
theorem B1910243 : Blo 417772 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B632291 : Blo 417772 632291 := bstep (se 1 (by rfl) ⟨474218, by rfl⟩ : syracuseStep 632291 = 948437) B948437
theorem B894449 : Blo 417772 894449 := bstep (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) B670837
theorem B632321 : Blo 417772 632321 := bstep (se 2 (by rfl) ⟨237120, by rfl⟩ : syracuseStep 632321 = 474241) B474241
theorem B632339 : Blo 417772 632339 := bstep (se 1 (by rfl) ⟨474254, by rfl⟩ : syracuseStep 632339 = 948509) B948509
theorem B2696753 : Blo 417772 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B632369 : Blo 417772 632369 := bstep (se 2 (by rfl) ⟨237138, by rfl⟩ : syracuseStep 632369 = 474277) B474277
theorem B632387 : Blo 417772 632387 := bstep (se 1 (by rfl) ⟨474290, by rfl⟩ : syracuseStep 632387 = 948581) B948581
theorem B632417 : Blo 417772 632417 := bstep (se 2 (by rfl) ⟨237156, by rfl⟩ : syracuseStep 632417 = 474313) B474313
theorem B1058417 : Blo 417772 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B632435 : Blo 417772 632435 := bstep (se 1 (by rfl) ⟨474326, by rfl⟩ : syracuseStep 632435 = 948653) B948653
theorem B632465 : Blo 417772 632465 := bstep (se 2 (by rfl) ⟨237174, by rfl⟩ : syracuseStep 632465 = 474349) B474349
theorem B1058467 : Blo 417772 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B632483 : Blo 417772 632483 := bstep (se 1 (by rfl) ⟨474362, by rfl⟩ : syracuseStep 632483 = 948725) B948725
theorem B632513 : Blo 417772 632513 := bstep (se 2 (by rfl) ⟨237192, by rfl⟩ : syracuseStep 632513 = 474385) B474385
theorem B1418957 : Blo 417772 1418957 := bstep (se 3 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 1418957 = 532109) B532109
theorem B632531 : Blo 417772 632531 := bstep (se 1 (by rfl) ⟨474398, by rfl⟩ : syracuseStep 632531 = 948797) B948797
theorem B796387 : Blo 417772 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B632561 : Blo 417772 632561 := bstep (se 2 (by rfl) ⟨237210, by rfl⟩ : syracuseStep 632561 = 474421) B474421
theorem B1419011 : Blo 417772 1419011 := bstep (se 1 (by rfl) ⟨1064258, by rfl⟩ : syracuseStep 1419011 = 2128517) B2128517
theorem B632579 : Blo 417772 632579 := bstep (se 1 (by rfl) ⟨474434, by rfl⟩ : syracuseStep 632579 = 948869) B948869
theorem B599825 : Blo 417772 599825 := bstep (se 2 (by rfl) ⟨224934, by rfl⟩ : syracuseStep 599825 = 449869) B449869
theorem B632609 : Blo 417772 632609 := bstep (se 2 (by rfl) ⟨237228, by rfl⟩ : syracuseStep 632609 = 474457) B474457
theorem B1058609 : Blo 417772 1058609 := bstep (se 2 (by rfl) ⟨396978, by rfl⟩ : syracuseStep 1058609 = 793957) B793957
theorem B632627 : Blo 417772 632627 := bstep (se 1 (by rfl) ⟨474470, by rfl⟩ : syracuseStep 632627 = 948941) B948941
theorem B632657 : Blo 417772 632657 := bstep (se 2 (by rfl) ⟨237246, by rfl⟩ : syracuseStep 632657 = 474493) B474493
theorem B796547 : Blo 417772 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B2861041 : Blo 417772 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B894979 : Blo 417772 894979 := bstep (se 1 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 894979 = 1342469) B1342469
theorem B1419281 : Blo 417772 1419281 := bstep (se 2 (by rfl) ⟨532230, by rfl⟩ : syracuseStep 1419281 = 1064461) B1064461
theorem B26683505 : Blo 417772 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B4761827 : Blo 417772 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B567523 : Blo 417772 567523 := bstep (se 1 (by rfl) ⟨425642, by rfl⟩ : syracuseStep 567523 = 851285) B851285
theorem B2271473 : Blo 417772 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B1190321 : Blo 417772 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B1419821 : Blo 417772 1419821 := bstep (se 3 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 1419821 = 532433) B532433
theorem B567857 : Blo 417772 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B1419875 : Blo 417772 1419875 := bstep (se 1 (by rfl) ⟨1064906, by rfl⟩ : syracuseStep 1419875 = 2129813) B2129813
theorem B1059601 : Blo 417772 1059601 := bstep (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) B794701
theorem B3418949 : Blo 417772 3418949 := bstep (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) B641053
theorem B3189617 : Blo 417772 3189617 := bstep (se 2 (by rfl) ⟨1196106, by rfl⟩ : syracuseStep 3189617 = 2392213) B2392213
theorem B1420145 : Blo 417772 1420145 := bstep (se 2 (by rfl) ⟨532554, by rfl⟩ : syracuseStep 1420145 = 1065109) B1065109
theorem B502643 : Blo 417772 502643 := bstep (se 1 (by rfl) ⟨376982, by rfl⟩ : syracuseStep 502643 = 753965) B753965
theorem B797617 : Blo 417772 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B2698211 : Blo 417772 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B1059875 : Blo 417772 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B470083 : Blo 417772 470083 := bstep (se 1 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 470083 = 705125) B705125
theorem B470227 : Blo 417772 470227 := bstep (se 1 (by rfl) ⟨352670, by rfl⟩ : syracuseStep 470227 = 705341) B705341
theorem B1060067 : Blo 417772 1060067 := bstep (se 1 (by rfl) ⟨795050, by rfl⟩ : syracuseStep 1060067 = 1590101) B1590101
theorem B568561 : Blo 417772 568561 := bstep (se 2 (by rfl) ⟨213210, by rfl⟩ : syracuseStep 568561 = 426421) B426421
theorem B470371 : Blo 417772 470371 := bstep (se 1 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 470371 = 705557) B705557
theorem B1191277 : Blo 417772 1191277 := bstep (se 3 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 1191277 = 446729) B446729
theorem B1420685 : Blo 417772 1420685 := bstep (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) B532757
theorem B1420739 : Blo 417772 1420739 := bstep (se 1 (by rfl) ⟨1065554, by rfl⟩ : syracuseStep 1420739 = 2131109) B2131109
theorem B896465 : Blo 417772 896465 := bstep (se 2 (by rfl) ⟨336174, by rfl⟩ : syracuseStep 896465 = 672349) B672349
theorem B568787 : Blo 417772 568787 := bstep (se 1 (by rfl) ⟨426590, by rfl⟩ : syracuseStep 568787 = 853181) B853181
theorem B896483 : Blo 417772 896483 := bstep (se 1 (by rfl) ⟨672362, by rfl⟩ : syracuseStep 896483 = 1344725) B1344725
theorem B470515 : Blo 417772 470515 := bstep (se 1 (by rfl) ⟨352886, by rfl⟩ : syracuseStep 470515 = 705773) B705773
theorem B1191505 : Blo 417772 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B470659 : Blo 417772 470659 := bstep (se 1 (by rfl) ⟨352994, by rfl⟩ : syracuseStep 470659 = 705989) B705989
theorem B1421009 : Blo 417772 1421009 := bstep (se 2 (by rfl) ⟨532878, by rfl⟩ : syracuseStep 1421009 = 1065757) B1065757
theorem B1191665 : Blo 417772 1191665 := bstep (se 2 (by rfl) ⟨446874, by rfl⟩ : syracuseStep 1191665 = 893749) B893749
theorem B470803 : Blo 417772 470803 := bstep (se 1 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 470803 = 706205) B706205
theorem B1191779 : Blo 417772 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B4599665 : Blo 417772 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B470947 : Blo 417772 470947 := bstep (se 1 (by rfl) ⟨353210, by rfl⟩ : syracuseStep 470947 = 706421) B706421
theorem B798673 : Blo 417772 798673 := bstep (se 2 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 798673 = 599005) B599005
theorem B3026929 : Blo 417772 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B471091 : Blo 417772 471091 := bstep (se 1 (by rfl) ⟨353318, by rfl⟩ : syracuseStep 471091 = 706637) B706637
theorem B1061009 : Blo 417772 1061009 := bstep (se 2 (by rfl) ⟨397878, by rfl⟩ : syracuseStep 1061009 = 795757) B795757
theorem B471235 : Blo 417772 471235 := bstep (se 1 (by rfl) ⟨353426, by rfl⟩ : syracuseStep 471235 = 706853) B706853
theorem B1061059 : Blo 417772 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B569539 : Blo 417772 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B1421549 : Blo 417772 1421549 := bstep (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) B533081
theorem B3027185 : Blo 417772 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B1421603 : Blo 417772 1421603 := bstep (se 1 (by rfl) ⟨1066202, by rfl⟩ : syracuseStep 1421603 = 2132405) B2132405
theorem B1061201 : Blo 417772 1061201 := bstep (se 2 (by rfl) ⟨397950, by rfl⟩ : syracuseStep 1061201 = 795901) B795901
theorem B471379 : Blo 417772 471379 := bstep (se 1 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 471379 = 707069) B707069
theorem B799075 : Blo 417772 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B799121 : Blo 417772 799121 := bstep (se 2 (by rfl) ⟨299670, by rfl⟩ : syracuseStep 799121 = 599341) B599341
theorem B471523 : Blo 417772 471523 := bstep (se 1 (by rfl) ⟨353642, by rfl⟩ : syracuseStep 471523 = 707285) B707285
theorem B1421873 : Blo 417772 1421873 := bstep (se 2 (by rfl) ⟨533202, by rfl⟩ : syracuseStep 1421873 = 1066405) B1066405
theorem B471667 : Blo 417772 471667 := bstep (se 1 (by rfl) ⟨353750, by rfl⟩ : syracuseStep 471667 = 707501) B707501
theorem B897713 : Blo 417772 897713 := bstep (se 2 (by rfl) ⟨336642, by rfl⟩ : syracuseStep 897713 = 673285) B673285
theorem B799409 : Blo 417772 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B471811 : Blo 417772 471811 := bstep (se 1 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 471811 = 707717) B707717
theorem B1192781 : Blo 417772 1192781 := bstep (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) B447293
theorem B1618787 : Blo 417772 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B471955 : Blo 417772 471955 := bstep (se 1 (by rfl) ⟨353966, by rfl⟩ : syracuseStep 471955 = 707933) B707933
theorem B1192963 : Blo 417772 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B472099 : Blo 417772 472099 := bstep (se 1 (by rfl) ⟨354074, by rfl⟩ : syracuseStep 472099 = 708149) B708149
theorem B635969 : Blo 417772 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B1422413 : Blo 417772 1422413 := bstep (se 3 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 1422413 = 533405) B533405
theorem B1422467 : Blo 417772 1422467 := bstep (se 1 (by rfl) ⟨1066850, by rfl⟩ : syracuseStep 1422467 = 2133701) B2133701
theorem B1193123 : Blo 417772 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B472243 : Blo 417772 472243 := bstep (se 1 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 472243 = 708365) B708365
theorem B1062193 : Blo 417772 1062193 := bstep (se 2 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 1062193 = 796645) B796645
theorem B472387 : Blo 417772 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B800131 : Blo 417772 800131 := bstep (se 1 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 800131 = 1200197) B1200197
theorem B1422737 : Blo 417772 1422737 := bstep (se 2 (by rfl) ⟨533526, by rfl⟩ : syracuseStep 1422737 = 1067053) B1067053
theorem B472531 : Blo 417772 472531 := bstep (se 1 (by rfl) ⟨354398, by rfl⟩ : syracuseStep 472531 = 708797) B708797
theorem B669217 : Blo 417772 669217 := bstep (se 2 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 669217 = 501913) B501913
theorem B1062467 : Blo 417772 1062467 := bstep (se 1 (by rfl) ⟨796850, by rfl⟩ : syracuseStep 1062467 = 1593701) B1593701
theorem B2700877 : Blo 417772 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B472675 : Blo 417772 472675 := bstep (se 1 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 472675 = 709013) B709013
theorem B669427 : Blo 417772 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B472819 : Blo 417772 472819 := bstep (se 1 (by rfl) ⟨354614, by rfl⟩ : syracuseStep 472819 = 709229) B709229
theorem B1062659 : Blo 417772 1062659 := bstep (se 1 (by rfl) ⟨796994, by rfl⟩ : syracuseStep 1062659 = 1593989) B1593989
theorem B669473 : Blo 417772 669473 := bstep (se 2 (by rfl) ⟨251052, by rfl⟩ : syracuseStep 669473 = 502105) B502105
theorem B800579 : Blo 417772 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B4798277 : Blo 417772 4798277 := bstep (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) B899677
theorem B472963 : Blo 417772 472963 := bstep (se 1 (by rfl) ⟨354722, by rfl⟩ : syracuseStep 472963 = 709445) B709445
theorem B1423277 : Blo 417772 1423277 := bstep (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) B533729
theorem B1423331 : Blo 417772 1423331 := bstep (se 1 (by rfl) ⟨1067498, by rfl⟩ : syracuseStep 1423331 = 2134997) B2134997
theorem B1587185 : Blo 417772 1587185 := bstep (se 2 (by rfl) ⟨595194, by rfl⟩ : syracuseStep 1587185 = 1190389) B1190389
theorem B473107 : Blo 417772 473107 := bstep (se 1 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 473107 = 709661) B709661
theorem B473251 : Blo 417772 473251 := bstep (se 1 (by rfl) ⟨354938, by rfl⟩ : syracuseStep 473251 = 709877) B709877
theorem B899267 : Blo 417772 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B1194193 : Blo 417772 1194193 := bstep (se 2 (by rfl) ⟨447822, by rfl⟩ : syracuseStep 1194193 = 895645) B895645
theorem B473395 : Blo 417772 473395 := bstep (se 1 (by rfl) ⟨355046, by rfl⟩ : syracuseStep 473395 = 710093) B710093
theorem B637283 : Blo 417772 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B473539 : Blo 417772 473539 := bstep (se 1 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 473539 = 710309) B710309
theorem B473683 : Blo 417772 473683 := bstep (se 1 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 473683 = 710525) B710525
theorem B1063601 : Blo 417772 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B1063651 : Blo 417772 1063651 := bstep (se 1 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 1063651 = 1595477) B1595477
theorem B473827 : Blo 417772 473827 := bstep (se 1 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 473827 = 710741) B710741
theorem B1063793 : Blo 417772 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B473971 : Blo 417772 473971 := bstep (se 1 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 473971 = 710957) B710957
theorem B474115 : Blo 417772 474115 := bstep (se 1 (by rfl) ⟨355586, by rfl⟩ : syracuseStep 474115 = 711173) B711173
theorem B474259 : Blo 417772 474259 := bstep (se 1 (by rfl) ⟨355694, by rfl⟩ : syracuseStep 474259 = 711389) B711389
theorem B1785037 : Blo 417772 1785037 := bstep (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) B669389
theorem B670979 : Blo 417772 670979 := bstep (se 1 (by rfl) ⟨503234, by rfl⟩ : syracuseStep 670979 = 1006469) B1006469
theorem B1129745 : Blo 417772 1129745 := bstep (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) B847309
theorem B474403 : Blo 417772 474403 := bstep (se 1 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 474403 = 711605) B711605
theorem B5356853 : Blo 417772 5356853 := bstep (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) B502205
theorem B1588643 : Blo 417772 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B1195469 : Blo 417772 1195469 := bstep (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) B448301
theorem B671267 : Blo 417772 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B605731 : Blo 417772 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B1195651 : Blo 417772 1195651 := bstep (se 1 (by rfl) ⟨896738, by rfl⟩ : syracuseStep 1195651 = 1793477) B1793477
theorem B1195697 : Blo 417772 1195697 := bstep (se 2 (by rfl) ⟨448386, by rfl⟩ : syracuseStep 1195697 = 896773) B896773
theorem B638707 : Blo 417772 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B1064785 : Blo 417772 1064785 := bstep (se 2 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 1064785 = 798589) B798589
theorem B573409 : Blo 417772 573409 := bstep (se 2 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 573409 = 430057) B430057
theorem B11321315 : Blo 417772 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B540643 : Blo 417772 540643 := bstep (se 1 (by rfl) ⟨405482, by rfl⟩ : syracuseStep 540643 = 810965) B810965
theorem B1065059 : Blo 417772 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B1065251 : Blo 417772 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B672067 : Blo 417772 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B967043 : Blo 417772 967043 := bstep (se 1 (by rfl) ⟨725282, by rfl⟩ : syracuseStep 967043 = 1450565) B1450565
theorem B5718413 : Blo 417772 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B1589645 : Blo 417772 1589645 := bstep (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) B596117
theorem B672209 : Blo 417772 672209 := bstep (se 2 (by rfl) ⟨252078, by rfl⟩ : syracuseStep 672209 = 504157) B504157
theorem B672241 : Blo 417772 672241 := bstep (se 2 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 672241 = 504181) B504181
theorem B705091 : Blo 417772 705091 := bstep (se 1 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 705091 = 1057637) B1057637
theorem B1360451 : Blo 417772 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B705233 : Blo 417772 705233 := bstep (se 2 (by rfl) ⟨264462, by rfl⟩ : syracuseStep 705233 = 528925) B528925
theorem B2016049 : Blo 417772 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B705361 : Blo 417772 705361 := bstep (se 2 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 705361 = 529021) B529021
theorem B705395 : Blo 417772 705395 := bstep (se 1 (by rfl) ⟨529046, by rfl⟩ : syracuseStep 705395 = 1058093) B1058093
theorem B705523 : Blo 417772 705523 := bstep (se 1 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 705523 = 1058285) B1058285
theorem B1197155 : Blo 417772 1197155 := bstep (se 1 (by rfl) ⟨897866, by rfl⟩ : syracuseStep 1197155 = 1795733) B1795733
theorem B705665 : Blo 417772 705665 := bstep (se 2 (by rfl) ⟨264624, by rfl⟩ : syracuseStep 705665 = 529249) B529249
theorem B3032261 : Blo 417772 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B1066193 : Blo 417772 1066193 := bstep (se 2 (by rfl) ⟨399822, by rfl⟩ : syracuseStep 1066193 = 799645) B799645
theorem B705793 : Blo 417772 705793 := bstep (se 2 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 705793 = 529345) B529345
theorem B1066243 : Blo 417772 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B705827 : Blo 417772 705827 := bstep (se 1 (by rfl) ⟨529370, by rfl⟩ : syracuseStep 705827 = 1058741) B1058741
theorem B673169 : Blo 417772 673169 := bstep (se 2 (by rfl) ⟨252438, by rfl⟩ : syracuseStep 673169 = 504877) B504877
theorem B1066385 : Blo 417772 1066385 := bstep (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) B799789
theorem B705955 : Blo 417772 705955 := bstep (se 1 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 705955 = 1058933) B1058933
theorem B706097 : Blo 417772 706097 := bstep (se 2 (by rfl) ⟨264786, by rfl⟩ : syracuseStep 706097 = 529573) B529573
theorem B706225 : Blo 417772 706225 := bstep (se 2 (by rfl) ⟨264834, by rfl⟩ : syracuseStep 706225 = 529669) B529669
theorem B706259 : Blo 417772 706259 := bstep (se 1 (by rfl) ⟨529694, by rfl⟩ : syracuseStep 706259 = 1059389) B1059389
theorem B1918691 : Blo 417772 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B706387 : Blo 417772 706387 := bstep (se 1 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 706387 = 1059581) B1059581
theorem B706529 : Blo 417772 706529 := bstep (se 2 (by rfl) ⟨264948, by rfl⟩ : syracuseStep 706529 = 529897) B529897
theorem B706657 : Blo 417772 706657 := bstep (se 2 (by rfl) ⟨264996, by rfl⟩ : syracuseStep 706657 = 529993) B529993
theorem B706691 : Blo 417772 706691 := bstep (se 1 (by rfl) ⟨530018, by rfl⟩ : syracuseStep 706691 = 1060037) B1060037
theorem B674003 : Blo 417772 674003 := bstep (se 1 (by rfl) ⟨505502, by rfl⟩ : syracuseStep 674003 = 1011005) B1011005
theorem B10733795 : Blo 417772 10733795 := bstep (se 1 (by rfl) ⟨8050346, by rfl⟩ : syracuseStep 10733795 = 16100693) B16100693
theorem B706819 : Blo 417772 706819 := bstep (se 1 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 706819 = 1060229) B1060229
theorem B1132849 : Blo 417772 1132849 := bstep (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) B849637
theorem B1198385 : Blo 417772 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B1067377 : Blo 417772 1067377 := bstep (se 2 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 1067377 = 800533) B800533
theorem B706961 : Blo 417772 706961 := bstep (se 2 (by rfl) ⟨265110, by rfl⟩ : syracuseStep 706961 = 530221) B530221
theorem B1591757 : Blo 417772 1591757 := bstep (se 3 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 1591757 = 596909) B596909
theorem B510451 : Blo 417772 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B674291 : Blo 417772 674291 := bstep (se 1 (by rfl) ⟨505718, by rfl⟩ : syracuseStep 674291 = 1011437) B1011437
theorem B707089 : Blo 417772 707089 := bstep (se 2 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 707089 = 530317) B530317
theorem B707123 : Blo 417772 707123 := bstep (se 1 (by rfl) ⟨530342, by rfl⟩ : syracuseStep 707123 = 1060685) B1060685
theorem B576131 : Blo 417772 576131 := bstep (se 1 (by rfl) ⟨432098, by rfl⟩ : syracuseStep 576131 = 864197) B864197
theorem B707251 : Blo 417772 707251 := bstep (se 1 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 707251 = 1060877) B1060877
theorem B674515 : Blo 417772 674515 := bstep (se 1 (by rfl) ⟨505886, by rfl⟩ : syracuseStep 674515 = 1011773) B1011773
theorem B707393 : Blo 417772 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B4049777 : Blo 417772 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B1526705 : Blo 417772 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B2116529 : Blo 417772 2116529 := bstep (se 2 (by rfl) ⟨793698, by rfl⟩ : syracuseStep 2116529 = 1587397) B1587397
theorem B707521 : Blo 417772 707521 := bstep (se 2 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 707521 = 530641) B530641
theorem B707555 : Blo 417772 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B2018317 : Blo 417772 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B707683 : Blo 417772 707683 := bstep (se 1 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 707683 = 1061525) B1061525
theorem B1592561 : Blo 417772 1592561 := bstep (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) B1194421
theorem B707825 : Blo 417772 707825 := bstep (se 2 (by rfl) ⟨265434, by rfl⟩ : syracuseStep 707825 = 530869) B530869
theorem B707953 : Blo 417772 707953 := bstep (se 2 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 707953 = 530965) B530965
theorem B3460465 : Blo 417772 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B707987 : Blo 417772 707987 := bstep (se 1 (by rfl) ⟨530990, by rfl⟩ : syracuseStep 707987 = 1061981) B1061981
theorem B675233 : Blo 417772 675233 := bstep (se 2 (by rfl) ⟨253212, by rfl⟩ : syracuseStep 675233 = 506425) B506425
theorem B1789361 : Blo 417772 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B1789411 : Blo 417772 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B4804109 : Blo 417772 4804109 := bstep (se 3 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 4804109 = 1801541) B1801541
theorem B708115 : Blo 417772 708115 := bstep (se 1 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 708115 = 1062173) B1062173
theorem B675425 : Blo 417772 675425 := bstep (se 2 (by rfl) ⟨253284, by rfl⟩ : syracuseStep 675425 = 506569) B506569
theorem B708257 : Blo 417772 708257 := bstep (se 2 (by rfl) ⟨265596, by rfl⟩ : syracuseStep 708257 = 531193) B531193
theorem B446131 : Blo 417772 446131 := bstep (se 1 (by rfl) ⟨334598, by rfl⟩ : syracuseStep 446131 = 669197) B669197
theorem B675553 : Blo 417772 675553 := bstep (se 2 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 675553 = 506665) B506665
theorem B1199843 : Blo 417772 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B708385 : Blo 417772 708385 := bstep (se 2 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 708385 = 531289) B531289
theorem B708419 : Blo 417772 708419 := bstep (se 1 (by rfl) ⟨531314, by rfl⟩ : syracuseStep 708419 = 1062629) B1062629
theorem B1920881 : Blo 417772 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1593229 : Blo 417772 1593229 := bstep (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) B597461
theorem B708547 : Blo 417772 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B1364035 : Blo 417772 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B708689 : Blo 417772 708689 := bstep (se 2 (by rfl) ⟨265758, by rfl⟩ : syracuseStep 708689 = 531517) B531517
theorem B2019491 : Blo 417772 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B708817 : Blo 417772 708817 := bstep (se 2 (by rfl) ⟨265806, by rfl⟩ : syracuseStep 708817 = 531613) B531613
theorem B708851 : Blo 417772 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B2117987 : Blo 417772 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B708979 : Blo 417772 708979 := bstep (se 1 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 708979 = 1063469) B1063469
theorem B709121 : Blo 417772 709121 := bstep (se 2 (by rfl) ⟨265920, by rfl⟩ : syracuseStep 709121 = 531841) B531841
theorem B1200653 : Blo 417772 1200653 := bstep (se 3 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 1200653 = 450245) B450245
theorem B709249 : Blo 417772 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B447139 : Blo 417772 447139 := bstep (se 1 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 447139 = 670709) B670709
theorem B1594019 : Blo 417772 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B709283 : Blo 417772 709283 := bstep (se 1 (by rfl) ⟨531962, by rfl⟩ : syracuseStep 709283 = 1063925) B1063925
theorem B1200845 : Blo 417772 1200845 := bstep (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) B450317
theorem B2380549 : Blo 417772 2380549 := bstep (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) B446353
theorem B709411 : Blo 417772 709411 := bstep (se 1 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 709411 = 1064117) B1064117
theorem B4051781 : Blo 417772 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B906083 : Blo 417772 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B4641677 : Blo 417772 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1823629 : Blo 417772 1823629 := bstep (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) B683861
theorem B1299341 : Blo 417772 1299341 := bstep (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) B487253
theorem B1528739 : Blo 417772 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B709553 : Blo 417772 709553 := bstep (se 2 (by rfl) ⟨266082, by rfl⟩ : syracuseStep 709553 = 532165) B532165
theorem B709681 : Blo 417772 709681 := bstep (se 2 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 709681 = 532261) B532261
theorem B709715 : Blo 417772 709715 := bstep (se 1 (by rfl) ⟨532286, by rfl⟩ : syracuseStep 709715 = 1064573) B1064573
theorem B2118797 : Blo 417772 2118797 := bstep (se 3 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 2118797 = 794549) B794549
theorem B709843 : Blo 417772 709843 := bstep (se 1 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 709843 = 1064765) B1064765
theorem B447763 : Blo 417772 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B1594673 : Blo 417772 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B1824049 : Blo 417772 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B709985 : Blo 417772 709985 := bstep (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) B532489
theorem B710113 : Blo 417772 710113 := bstep (se 2 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 710113 = 532585) B532585
theorem B710147 : Blo 417772 710147 := bstep (se 1 (by rfl) ⟨532610, by rfl⟩ : syracuseStep 710147 = 1065221) B1065221
theorem B710275 : Blo 417772 710275 := bstep (se 1 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 710275 = 1065413) B1065413
theorem B710417 : Blo 417772 710417 := bstep (se 2 (by rfl) ⟨266406, by rfl⟩ : syracuseStep 710417 = 532813) B532813
theorem B1791821 : Blo 417772 1791821 := bstep (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) B671933
theorem B710545 : Blo 417772 710545 := bstep (se 2 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 710545 = 532909) B532909
theorem B710579 : Blo 417772 710579 := bstep (se 1 (by rfl) ⟨532934, by rfl⟩ : syracuseStep 710579 = 1065869) B1065869
theorem B940049 : Blo 417772 940049 := bstep (se 2 (by rfl) ⟨352518, by rfl⟩ : syracuseStep 940049 = 705037) B705037
theorem B940067 : Blo 417772 940067 := bstep (se 1 (by rfl) ⟨705050, by rfl⟩ : syracuseStep 940067 = 1410101) B1410101
theorem B710707 : Blo 417772 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B710849 : Blo 417772 710849 := bstep (se 2 (by rfl) ⟨266568, by rfl⟩ : syracuseStep 710849 = 533137) B533137
theorem B5363981 : Blo 417772 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B940337 : Blo 417772 940337 := bstep (se 2 (by rfl) ⟨352626, by rfl⟩ : syracuseStep 940337 = 705253) B705253
theorem B710977 : Blo 417772 710977 := bstep (se 2 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 710977 = 533233) B533233
theorem B940355 : Blo 417772 940355 := bstep (se 1 (by rfl) ⟨705266, by rfl⟩ : syracuseStep 940355 = 1410533) B1410533
theorem B711011 : Blo 417772 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B1169873 : Blo 417772 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B711139 : Blo 417772 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B940625 : Blo 417772 940625 := bstep (se 2 (by rfl) ⟨352734, by rfl⟩ : syracuseStep 940625 = 705469) B705469
theorem B940643 : Blo 417772 940643 := bstep (se 1 (by rfl) ⟨705482, by rfl⟩ : syracuseStep 940643 = 1410965) B1410965
theorem B711281 : Blo 417772 711281 := bstep (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) B533461
theorem B2382533 : Blo 417772 2382533 := bstep (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) B446725
theorem B8575715 : Blo 417772 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B1596131 : Blo 417772 1596131 := bstep (se 1 (by rfl) ⟨1197098, by rfl⟩ : syracuseStep 1596131 = 2394197) B2394197
theorem B1596145 : Blo 417772 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B711409 : Blo 417772 711409 := bstep (se 2 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 711409 = 533557) B533557
theorem B711443 : Blo 417772 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B940913 : Blo 417772 940913 := bstep (se 2 (by rfl) ⟨352842, by rfl⟩ : syracuseStep 940913 = 705685) B705685
theorem B940931 : Blo 417772 940931 := bstep (se 1 (by rfl) ⟨705698, by rfl⟩ : syracuseStep 940931 = 1411397) B1411397
theorem B711571 : Blo 417772 711571 := bstep (se 1 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 711571 = 1067357) B1067357
theorem B711713 : Blo 417772 711713 := bstep (se 2 (by rfl) ⟨266892, by rfl⟩ : syracuseStep 711713 = 533785) B533785
theorem B449651 : Blo 417772 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B941201 : Blo 417772 941201 := bstep (se 2 (by rfl) ⟨352950, by rfl⟩ : syracuseStep 941201 = 705901) B705901
theorem B941219 : Blo 417772 941219 := bstep (se 1 (by rfl) ⟨705914, by rfl⟩ : syracuseStep 941219 = 1411829) B1411829
theorem B941489 : Blo 417772 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B941507 : Blo 417772 941507 := bstep (se 1 (by rfl) ⟨706130, by rfl⟩ : syracuseStep 941507 = 1412261) B1412261
theorem B2547377 : Blo 417772 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B941777 : Blo 417772 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B1138385 : Blo 417772 1138385 := bstep (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) B853789
theorem B941795 : Blo 417772 941795 := bstep (se 1 (by rfl) ⟨706346, by rfl⟩ : syracuseStep 941795 = 1412693) B1412693
theorem B2023181 : Blo 417772 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B1073027 : Blo 417772 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B942065 : Blo 417772 942065 := bstep (se 2 (by rfl) ⟨353274, by rfl⟩ : syracuseStep 942065 = 706549) B706549
theorem B2121713 : Blo 417772 2121713 := bstep (se 2 (by rfl) ⟨795642, by rfl⟩ : syracuseStep 2121713 = 1591285) B1591285
theorem B417779 : Blo 417772 417779 := bstep (se 1 (by rfl) ⟨313334, by rfl⟩ : syracuseStep 417779 = 626669) B626669
theorem B417795 : Blo 417772 417795 := bstep (se 1 (by rfl) ⟨313346, by rfl⟩ : syracuseStep 417795 = 626693) B626693
theorem B942083 : Blo 417772 942083 := bstep (se 1 (by rfl) ⟨706562, by rfl⟩ : syracuseStep 942083 = 1413125) B1413125
theorem B417811 : Blo 417772 417811 := bstep (se 1 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 417811 = 626717) B626717
theorem B417827 : Blo 417772 417827 := bstep (se 1 (by rfl) ⟨313370, by rfl⟩ : syracuseStep 417827 = 626741) B626741
theorem B417843 : Blo 417772 417843 := bstep (se 1 (by rfl) ⟨313382, by rfl⟩ : syracuseStep 417843 = 626765) B626765
theorem B417859 : Blo 417772 417859 := bstep (se 1 (by rfl) ⟨313394, by rfl⟩ : syracuseStep 417859 = 626789) B626789
theorem B417875 : Blo 417772 417875 := bstep (se 1 (by rfl) ⟨313406, by rfl⟩ : syracuseStep 417875 = 626813) B626813
theorem B417891 : Blo 417772 417891 := bstep (se 1 (by rfl) ⟨313418, by rfl⟩ : syracuseStep 417891 = 626837) B626837
theorem B909425 : Blo 417772 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B417907 : Blo 417772 417907 := bstep (se 1 (by rfl) ⟨313430, by rfl⟩ : syracuseStep 417907 = 626861) B626861
theorem B417923 : Blo 417772 417923 := bstep (se 1 (by rfl) ⟨313442, by rfl⟩ : syracuseStep 417923 = 626885) B626885
theorem B1007747 : Blo 417772 1007747 := bstep (se 1 (by rfl) ⟨755810, by rfl⟩ : syracuseStep 1007747 = 1511621) B1511621
theorem B417939 : Blo 417772 417939 := bstep (se 1 (by rfl) ⟨313454, by rfl⟩ : syracuseStep 417939 = 626909) B626909
theorem B417955 : Blo 417772 417955 := bstep (se 1 (by rfl) ⟨313466, by rfl⟩ : syracuseStep 417955 = 626933) B626933
theorem B1597603 : Blo 417772 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B417971 : Blo 417772 417971 := bstep (se 1 (by rfl) ⟨313478, by rfl⟩ : syracuseStep 417971 = 626957) B626957
theorem B417987 : Blo 417772 417987 := bstep (se 1 (by rfl) ⟨313490, by rfl⟩ : syracuseStep 417987 = 626981) B626981
theorem B418003 : Blo 417772 418003 := bstep (se 1 (by rfl) ⟨313502, by rfl⟩ : syracuseStep 418003 = 627005) B627005
theorem B418019 : Blo 417772 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B418035 : Blo 417772 418035 := bstep (se 1 (by rfl) ⟨313526, by rfl⟩ : syracuseStep 418035 = 627053) B627053
theorem B418051 : Blo 417772 418051 := bstep (se 1 (by rfl) ⟨313538, by rfl⟩ : syracuseStep 418051 = 627077) B627077
theorem B942353 : Blo 417772 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B418067 : Blo 417772 418067 := bstep (se 1 (by rfl) ⟨313550, by rfl⟩ : syracuseStep 418067 = 627101) B627101
theorem B418083 : Blo 417772 418083 := bstep (se 1 (by rfl) ⟨313562, by rfl⟩ : syracuseStep 418083 = 627125) B627125
theorem B942371 : Blo 417772 942371 := bstep (se 1 (by rfl) ⟨706778, by rfl⟩ : syracuseStep 942371 = 1413557) B1413557
theorem B418099 : Blo 417772 418099 := bstep (se 1 (by rfl) ⟨313574, by rfl⟩ : syracuseStep 418099 = 627149) B627149
theorem B418115 : Blo 417772 418115 := bstep (se 1 (by rfl) ⟨313586, by rfl⟩ : syracuseStep 418115 = 627173) B627173
theorem B418131 : Blo 417772 418131 := bstep (se 1 (by rfl) ⟨313598, by rfl⟩ : syracuseStep 418131 = 627197) B627197
theorem B418147 : Blo 417772 418147 := bstep (se 1 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 418147 = 627221) B627221
theorem B5398883 : Blo 417772 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B811363 : Blo 417772 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B418163 : Blo 417772 418163 := bstep (se 1 (by rfl) ⟨313622, by rfl⟩ : syracuseStep 418163 = 627245) B627245
theorem B418179 : Blo 417772 418179 := bstep (se 1 (by rfl) ⟨313634, by rfl⟩ : syracuseStep 418179 = 627269) B627269
theorem B418195 : Blo 417772 418195 := bstep (se 1 (by rfl) ⟨313646, by rfl⟩ : syracuseStep 418195 = 627293) B627293
theorem B418211 : Blo 417772 418211 := bstep (se 1 (by rfl) ⟨313658, by rfl⟩ : syracuseStep 418211 = 627317) B627317
theorem B418227 : Blo 417772 418227 := bstep (se 1 (by rfl) ⟨313670, by rfl⟩ : syracuseStep 418227 = 627341) B627341
theorem B418243 : Blo 417772 418243 := bstep (se 1 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 418243 = 627365) B627365
theorem B418259 : Blo 417772 418259 := bstep (se 1 (by rfl) ⟨313694, by rfl⟩ : syracuseStep 418259 = 627389) B627389
theorem B418275 : Blo 417772 418275 := bstep (se 1 (by rfl) ⟨313706, by rfl⟩ : syracuseStep 418275 = 627413) B627413
theorem B1696241 : Blo 417772 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B418291 : Blo 417772 418291 := bstep (se 1 (by rfl) ⟨313718, by rfl⟩ : syracuseStep 418291 = 627437) B627437
theorem B418307 : Blo 417772 418307 := bstep (se 1 (by rfl) ⟨313730, by rfl⟩ : syracuseStep 418307 = 627461) B627461
theorem B418323 : Blo 417772 418323 := bstep (se 1 (by rfl) ⟨313742, by rfl⟩ : syracuseStep 418323 = 627485) B627485
theorem B418339 : Blo 417772 418339 := bstep (se 1 (by rfl) ⟨313754, by rfl⟩ : syracuseStep 418339 = 627509) B627509
theorem B942641 : Blo 417772 942641 := bstep (se 2 (by rfl) ⟨353490, by rfl⟩ : syracuseStep 942641 = 706981) B706981
theorem B418355 : Blo 417772 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B418371 : Blo 417772 418371 := bstep (se 1 (by rfl) ⟨313778, by rfl⟩ : syracuseStep 418371 = 627557) B627557
theorem B942659 : Blo 417772 942659 := bstep (se 1 (by rfl) ⟨706994, by rfl⟩ : syracuseStep 942659 = 1413989) B1413989
theorem B418387 : Blo 417772 418387 := bstep (se 1 (by rfl) ⟨313790, by rfl⟩ : syracuseStep 418387 = 627581) B627581
theorem B418403 : Blo 417772 418403 := bstep (se 1 (by rfl) ⟨313802, by rfl⟩ : syracuseStep 418403 = 627605) B627605
theorem B418419 : Blo 417772 418419 := bstep (se 1 (by rfl) ⟨313814, by rfl⟩ : syracuseStep 418419 = 627629) B627629
theorem B418435 : Blo 417772 418435 := bstep (se 1 (by rfl) ⟨313826, by rfl⟩ : syracuseStep 418435 = 627653) B627653
theorem B418451 : Blo 417772 418451 := bstep (se 1 (by rfl) ⟨313838, by rfl⟩ : syracuseStep 418451 = 627677) B627677
theorem B418467 : Blo 417772 418467 := bstep (se 1 (by rfl) ⟨313850, by rfl⟩ : syracuseStep 418467 = 627701) B627701
theorem B418483 : Blo 417772 418483 := bstep (se 1 (by rfl) ⟨313862, by rfl⟩ : syracuseStep 418483 = 627725) B627725
theorem B418499 : Blo 417772 418499 := bstep (se 1 (by rfl) ⟨313874, by rfl⟩ : syracuseStep 418499 = 627749) B627749
theorem B418515 : Blo 417772 418515 := bstep (se 1 (by rfl) ⟨313886, by rfl⟩ : syracuseStep 418515 = 627773) B627773
theorem B418531 : Blo 417772 418531 := bstep (se 1 (by rfl) ⟨313898, by rfl⟩ : syracuseStep 418531 = 627797) B627797
theorem B418547 : Blo 417772 418547 := bstep (se 1 (by rfl) ⟨313910, by rfl⟩ : syracuseStep 418547 = 627821) B627821
theorem B418563 : Blo 417772 418563 := bstep (se 1 (by rfl) ⟨313922, by rfl⟩ : syracuseStep 418563 = 627845) B627845
theorem B418579 : Blo 417772 418579 := bstep (se 1 (by rfl) ⟨313934, by rfl⟩ : syracuseStep 418579 = 627869) B627869
theorem B418595 : Blo 417772 418595 := bstep (se 1 (by rfl) ⟨313946, by rfl⟩ : syracuseStep 418595 = 627893) B627893
theorem B418611 : Blo 417772 418611 := bstep (se 1 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 418611 = 627917) B627917
theorem B418627 : Blo 417772 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B942929 : Blo 417772 942929 := bstep (se 2 (by rfl) ⟨353598, by rfl⟩ : syracuseStep 942929 = 707197) B707197
theorem B418643 : Blo 417772 418643 := bstep (se 1 (by rfl) ⟨313982, by rfl⟩ : syracuseStep 418643 = 627965) B627965
theorem B418659 : Blo 417772 418659 := bstep (se 1 (by rfl) ⟨313994, by rfl⟩ : syracuseStep 418659 = 627989) B627989
theorem B942947 : Blo 417772 942947 := bstep (se 1 (by rfl) ⟨707210, by rfl⟩ : syracuseStep 942947 = 1414421) B1414421
theorem B4547441 : Blo 417772 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B418675 : Blo 417772 418675 := bstep (se 1 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 418675 = 628013) B628013
theorem B418691 : Blo 417772 418691 := bstep (se 1 (by rfl) ⟨314018, by rfl⟩ : syracuseStep 418691 = 628037) B628037
theorem B418707 : Blo 417772 418707 := bstep (se 1 (by rfl) ⟨314030, by rfl⟩ : syracuseStep 418707 = 628061) B628061
theorem B418723 : Blo 417772 418723 := bstep (se 1 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 418723 = 628085) B628085
theorem B1139629 : Blo 417772 1139629 := bstep (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) B427361
theorem B418739 : Blo 417772 418739 := bstep (se 1 (by rfl) ⟨314054, by rfl⟩ : syracuseStep 418739 = 628109) B628109
theorem B418755 : Blo 417772 418755 := bstep (se 1 (by rfl) ⟨314066, by rfl⟩ : syracuseStep 418755 = 628133) B628133
theorem B418771 : Blo 417772 418771 := bstep (se 1 (by rfl) ⟨314078, by rfl⟩ : syracuseStep 418771 = 628157) B628157
theorem B418787 : Blo 417772 418787 := bstep (se 1 (by rfl) ⟨314090, by rfl⟩ : syracuseStep 418787 = 628181) B628181
theorem B418803 : Blo 417772 418803 := bstep (se 1 (by rfl) ⟨314102, by rfl⟩ : syracuseStep 418803 = 628205) B628205
theorem B418819 : Blo 417772 418819 := bstep (se 1 (by rfl) ⟨314114, by rfl⟩ : syracuseStep 418819 = 628229) B628229
theorem B418835 : Blo 417772 418835 := bstep (se 1 (by rfl) ⟨314126, by rfl⟩ : syracuseStep 418835 = 628253) B628253
theorem B418851 : Blo 417772 418851 := bstep (se 1 (by rfl) ⟨314138, by rfl⟩ : syracuseStep 418851 = 628277) B628277
theorem B418867 : Blo 417772 418867 := bstep (se 1 (by rfl) ⟨314150, by rfl⟩ : syracuseStep 418867 = 628301) B628301
theorem B418883 : Blo 417772 418883 := bstep (se 1 (by rfl) ⟨314162, by rfl⟩ : syracuseStep 418883 = 628325) B628325
theorem B418899 : Blo 417772 418899 := bstep (se 1 (by rfl) ⟨314174, by rfl⟩ : syracuseStep 418899 = 628349) B628349
theorem B418915 : Blo 417772 418915 := bstep (se 1 (by rfl) ⟨314186, by rfl⟩ : syracuseStep 418915 = 628373) B628373
theorem B943217 : Blo 417772 943217 := bstep (se 2 (by rfl) ⟨353706, by rfl⟩ : syracuseStep 943217 = 707413) B707413
theorem B418931 : Blo 417772 418931 := bstep (se 1 (by rfl) ⟨314198, by rfl⟩ : syracuseStep 418931 = 628397) B628397
theorem B418947 : Blo 417772 418947 := bstep (se 1 (by rfl) ⟨314210, by rfl⟩ : syracuseStep 418947 = 628421) B628421
theorem B943235 : Blo 417772 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B418963 : Blo 417772 418963 := bstep (se 1 (by rfl) ⟨314222, by rfl⟩ : syracuseStep 418963 = 628445) B628445
theorem B418979 : Blo 417772 418979 := bstep (se 1 (by rfl) ⟨314234, by rfl⟩ : syracuseStep 418979 = 628469) B628469
theorem B418995 : Blo 417772 418995 := bstep (se 1 (by rfl) ⟨314246, by rfl⟩ : syracuseStep 418995 = 628493) B628493
theorem B419011 : Blo 417772 419011 := bstep (se 1 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 419011 = 628517) B628517
theorem B419027 : Blo 417772 419027 := bstep (se 1 (by rfl) ⟨314270, by rfl⟩ : syracuseStep 419027 = 628541) B628541
theorem B419043 : Blo 417772 419043 := bstep (se 1 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 419043 = 628565) B628565
theorem B419059 : Blo 417772 419059 := bstep (se 1 (by rfl) ⟨314294, by rfl⟩ : syracuseStep 419059 = 628589) B628589
theorem B419075 : Blo 417772 419075 := bstep (se 1 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 419075 = 628613) B628613
theorem B419091 : Blo 417772 419091 := bstep (se 1 (by rfl) ⟨314318, by rfl⟩ : syracuseStep 419091 = 628637) B628637
theorem B419107 : Blo 417772 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B419123 : Blo 417772 419123 := bstep (se 1 (by rfl) ⟨314342, by rfl⟩ : syracuseStep 419123 = 628685) B628685
theorem B419139 : Blo 417772 419139 := bstep (se 1 (by rfl) ⟨314354, by rfl⟩ : syracuseStep 419139 = 628709) B628709
theorem B5432645 : Blo 417772 5432645 := bstep (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) B1018621
theorem B419155 : Blo 417772 419155 := bstep (se 1 (by rfl) ⟨314366, by rfl⟩ : syracuseStep 419155 = 628733) B628733
theorem B419171 : Blo 417772 419171 := bstep (se 1 (by rfl) ⟨314378, by rfl⟩ : syracuseStep 419171 = 628757) B628757
theorem B1434979 : Blo 417772 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B419187 : Blo 417772 419187 := bstep (se 1 (by rfl) ⟨314390, by rfl⟩ : syracuseStep 419187 = 628781) B628781
theorem B419203 : Blo 417772 419203 := bstep (se 1 (by rfl) ⟨314402, by rfl⟩ : syracuseStep 419203 = 628805) B628805
theorem B943505 : Blo 417772 943505 := bstep (se 2 (by rfl) ⟨353814, by rfl⟩ : syracuseStep 943505 = 707629) B707629
theorem B419219 : Blo 417772 419219 := bstep (se 1 (by rfl) ⟨314414, by rfl⟩ : syracuseStep 419219 = 628829) B628829
theorem B419235 : Blo 417772 419235 := bstep (se 1 (by rfl) ⟨314426, by rfl⟩ : syracuseStep 419235 = 628853) B628853
theorem B943523 : Blo 417772 943523 := bstep (se 1 (by rfl) ⟨707642, by rfl⟩ : syracuseStep 943523 = 1415285) B1415285
theorem B2123171 : Blo 417772 2123171 := bstep (se 1 (by rfl) ⟨1592378, by rfl⟩ : syracuseStep 2123171 = 3184757) B3184757
theorem B419251 : Blo 417772 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B419267 : Blo 417772 419267 := bstep (se 1 (by rfl) ⟨314450, by rfl⟩ : syracuseStep 419267 = 628901) B628901
theorem B419283 : Blo 417772 419283 := bstep (se 1 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 419283 = 628925) B628925
theorem B419299 : Blo 417772 419299 := bstep (se 1 (by rfl) ⟨314474, by rfl⟩ : syracuseStep 419299 = 628949) B628949
theorem B419315 : Blo 417772 419315 := bstep (se 1 (by rfl) ⟨314486, by rfl⟩ : syracuseStep 419315 = 628973) B628973
theorem B419331 : Blo 417772 419331 := bstep (se 1 (by rfl) ⟨314498, by rfl⟩ : syracuseStep 419331 = 628997) B628997
theorem B4318733 : Blo 417772 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B419347 : Blo 417772 419347 := bstep (se 1 (by rfl) ⟨314510, by rfl⟩ : syracuseStep 419347 = 629021) B629021
theorem B419363 : Blo 417772 419363 := bstep (se 1 (by rfl) ⟨314522, by rfl⟩ : syracuseStep 419363 = 629045) B629045
theorem B419379 : Blo 417772 419379 := bstep (se 1 (by rfl) ⟨314534, by rfl⟩ : syracuseStep 419379 = 629069) B629069
theorem B419395 : Blo 417772 419395 := bstep (se 1 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 419395 = 629093) B629093
theorem B419411 : Blo 417772 419411 := bstep (se 1 (by rfl) ⟨314558, by rfl⟩ : syracuseStep 419411 = 629117) B629117
theorem B419427 : Blo 417772 419427 := bstep (se 1 (by rfl) ⟨314570, by rfl⟩ : syracuseStep 419427 = 629141) B629141
theorem B419443 : Blo 417772 419443 := bstep (se 1 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 419443 = 629165) B629165
theorem B419459 : Blo 417772 419459 := bstep (se 1 (by rfl) ⟨314594, by rfl⟩ : syracuseStep 419459 = 629189) B629189
theorem B419475 : Blo 417772 419475 := bstep (se 1 (by rfl) ⟨314606, by rfl⟩ : syracuseStep 419475 = 629213) B629213
theorem B419491 : Blo 417772 419491 := bstep (se 1 (by rfl) ⟨314618, by rfl⟩ : syracuseStep 419491 = 629237) B629237
theorem B943793 : Blo 417772 943793 := bstep (se 2 (by rfl) ⟨353922, by rfl⟩ : syracuseStep 943793 = 707845) B707845
theorem B419507 : Blo 417772 419507 := bstep (se 1 (by rfl) ⟨314630, by rfl⟩ : syracuseStep 419507 = 629261) B629261
theorem B943811 : Blo 417772 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B419523 : Blo 417772 419523 := bstep (se 1 (by rfl) ⟨314642, by rfl⟩ : syracuseStep 419523 = 629285) B629285
theorem B1009361 : Blo 417772 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B419539 : Blo 417772 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B419555 : Blo 417772 419555 := bstep (se 1 (by rfl) ⟨314666, by rfl⟩ : syracuseStep 419555 = 629333) B629333
theorem B419571 : Blo 417772 419571 := bstep (se 1 (by rfl) ⟨314678, by rfl⟩ : syracuseStep 419571 = 629357) B629357
theorem B419587 : Blo 417772 419587 := bstep (se 1 (by rfl) ⟨314690, by rfl⟩ : syracuseStep 419587 = 629381) B629381
theorem B419603 : Blo 417772 419603 := bstep (se 1 (by rfl) ⟨314702, by rfl⟩ : syracuseStep 419603 = 629405) B629405
theorem B419619 : Blo 417772 419619 := bstep (se 1 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 419619 = 629429) B629429
theorem B419635 : Blo 417772 419635 := bstep (se 1 (by rfl) ⟨314726, by rfl⟩ : syracuseStep 419635 = 629453) B629453
theorem B419651 : Blo 417772 419651 := bstep (se 1 (by rfl) ⟨314738, by rfl⟩ : syracuseStep 419651 = 629477) B629477
theorem B419667 : Blo 417772 419667 := bstep (se 1 (by rfl) ⟨314750, by rfl⟩ : syracuseStep 419667 = 629501) B629501
theorem B419683 : Blo 417772 419683 := bstep (se 1 (by rfl) ⟨314762, by rfl⟩ : syracuseStep 419683 = 629525) B629525
theorem B419699 : Blo 417772 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B419715 : Blo 417772 419715 := bstep (se 1 (by rfl) ⟨314786, by rfl⟩ : syracuseStep 419715 = 629573) B629573
theorem B419731 : Blo 417772 419731 := bstep (se 1 (by rfl) ⟨314798, by rfl⟩ : syracuseStep 419731 = 629597) B629597
theorem B419747 : Blo 417772 419747 := bstep (se 1 (by rfl) ⟨314810, by rfl⟩ : syracuseStep 419747 = 629621) B629621
theorem B419763 : Blo 417772 419763 := bstep (se 1 (by rfl) ⟨314822, by rfl⟩ : syracuseStep 419763 = 629645) B629645
theorem B419779 : Blo 417772 419779 := bstep (se 1 (by rfl) ⟨314834, by rfl⟩ : syracuseStep 419779 = 629669) B629669
theorem B944081 : Blo 417772 944081 := bstep (se 2 (by rfl) ⟨354030, by rfl⟩ : syracuseStep 944081 = 708061) B708061
theorem B419795 : Blo 417772 419795 := bstep (se 1 (by rfl) ⟨314846, by rfl⟩ : syracuseStep 419795 = 629693) B629693
theorem B944099 : Blo 417772 944099 := bstep (se 1 (by rfl) ⟨708074, by rfl⟩ : syracuseStep 944099 = 1416149) B1416149
theorem B419811 : Blo 417772 419811 := bstep (se 1 (by rfl) ⟨314858, by rfl⟩ : syracuseStep 419811 = 629717) B629717
theorem B419827 : Blo 417772 419827 := bstep (se 1 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 419827 = 629741) B629741
theorem B419843 : Blo 417772 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B419859 : Blo 417772 419859 := bstep (se 1 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 419859 = 629789) B629789
theorem B419875 : Blo 417772 419875 := bstep (se 1 (by rfl) ⟨314906, by rfl⟩ : syracuseStep 419875 = 629813) B629813
theorem B419891 : Blo 417772 419891 := bstep (se 1 (by rfl) ⟨314918, by rfl⟩ : syracuseStep 419891 = 629837) B629837
theorem B419907 : Blo 417772 419907 := bstep (se 1 (by rfl) ⟨314930, by rfl⟩ : syracuseStep 419907 = 629861) B629861
theorem B419923 : Blo 417772 419923 := bstep (se 1 (by rfl) ⟨314942, by rfl⟩ : syracuseStep 419923 = 629885) B629885
theorem B419939 : Blo 417772 419939 := bstep (se 1 (by rfl) ⟨314954, by rfl⟩ : syracuseStep 419939 = 629909) B629909
theorem B1796195 : Blo 417772 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1108081 : Blo 417772 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B419955 : Blo 417772 419955 := bstep (se 1 (by rfl) ⟨314966, by rfl⟩ : syracuseStep 419955 = 629933) B629933
theorem B419971 : Blo 417772 419971 := bstep (se 1 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 419971 = 629957) B629957
theorem B419987 : Blo 417772 419987 := bstep (se 1 (by rfl) ⟨314990, by rfl⟩ : syracuseStep 419987 = 629981) B629981
theorem B420003 : Blo 417772 420003 := bstep (se 1 (by rfl) ⟨315002, by rfl⟩ : syracuseStep 420003 = 630005) B630005
theorem B420019 : Blo 417772 420019 := bstep (se 1 (by rfl) ⟨315014, by rfl⟩ : syracuseStep 420019 = 630029) B630029
theorem B420035 : Blo 417772 420035 := bstep (se 1 (by rfl) ⟨315026, by rfl⟩ : syracuseStep 420035 = 630053) B630053
theorem B2123981 : Blo 417772 2123981 := bstep (se 3 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 2123981 = 796493) B796493
theorem B420051 : Blo 417772 420051 := bstep (se 1 (by rfl) ⟨315038, by rfl⟩ : syracuseStep 420051 = 630077) B630077
theorem B420067 : Blo 417772 420067 := bstep (se 1 (by rfl) ⟨315050, by rfl⟩ : syracuseStep 420067 = 630101) B630101
theorem B944369 : Blo 417772 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B420083 : Blo 417772 420083 := bstep (se 1 (by rfl) ⟨315062, by rfl⟩ : syracuseStep 420083 = 630125) B630125
theorem B944387 : Blo 417772 944387 := bstep (se 1 (by rfl) ⟨708290, by rfl⟩ : syracuseStep 944387 = 1416581) B1416581
theorem B420099 : Blo 417772 420099 := bstep (se 1 (by rfl) ⟨315074, by rfl⟩ : syracuseStep 420099 = 630149) B630149
theorem B420115 : Blo 417772 420115 := bstep (se 1 (by rfl) ⟨315086, by rfl⟩ : syracuseStep 420115 = 630173) B630173
theorem B420131 : Blo 417772 420131 := bstep (se 1 (by rfl) ⟨315098, by rfl⟩ : syracuseStep 420131 = 630197) B630197
theorem B420147 : Blo 417772 420147 := bstep (se 1 (by rfl) ⟨315110, by rfl⟩ : syracuseStep 420147 = 630221) B630221
theorem B420163 : Blo 417772 420163 := bstep (se 1 (by rfl) ⟨315122, by rfl⟩ : syracuseStep 420163 = 630245) B630245
theorem B1599821 : Blo 417772 1599821 := bstep (se 3 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 1599821 = 599933) B599933
theorem B420179 : Blo 417772 420179 := bstep (se 1 (by rfl) ⟨315134, by rfl⟩ : syracuseStep 420179 = 630269) B630269
theorem B420195 : Blo 417772 420195 := bstep (se 1 (by rfl) ⟨315146, by rfl⟩ : syracuseStep 420195 = 630293) B630293
theorem B420211 : Blo 417772 420211 := bstep (se 1 (by rfl) ⟨315158, by rfl⟩ : syracuseStep 420211 = 630317) B630317
theorem B420227 : Blo 417772 420227 := bstep (se 1 (by rfl) ⟨315170, by rfl⟩ : syracuseStep 420227 = 630341) B630341
theorem B18147725 : Blo 417772 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B420243 : Blo 417772 420243 := bstep (se 1 (by rfl) ⟨315182, by rfl⟩ : syracuseStep 420243 = 630365) B630365
theorem B420259 : Blo 417772 420259 := bstep (se 1 (by rfl) ⟨315194, by rfl⟩ : syracuseStep 420259 = 630389) B630389
theorem B420275 : Blo 417772 420275 := bstep (se 1 (by rfl) ⟨315206, by rfl⟩ : syracuseStep 420275 = 630413) B630413
theorem B420291 : Blo 417772 420291 := bstep (se 1 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 420291 = 630437) B630437
theorem B2386381 : Blo 417772 2386381 := bstep (se 3 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 2386381 = 894893) B894893
theorem B420307 : Blo 417772 420307 := bstep (se 1 (by rfl) ⟨315230, by rfl⟩ : syracuseStep 420307 = 630461) B630461
theorem B420323 : Blo 417772 420323 := bstep (se 1 (by rfl) ⟨315242, by rfl⟩ : syracuseStep 420323 = 630485) B630485
theorem B3631601 : Blo 417772 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B420339 : Blo 417772 420339 := bstep (se 1 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 420339 = 630509) B630509
theorem B420355 : Blo 417772 420355 := bstep (se 1 (by rfl) ⟨315266, by rfl⟩ : syracuseStep 420355 = 630533) B630533
theorem B944657 : Blo 417772 944657 := bstep (se 2 (by rfl) ⟨354246, by rfl⟩ : syracuseStep 944657 = 708493) B708493
theorem B420371 : Blo 417772 420371 := bstep (se 1 (by rfl) ⟨315278, by rfl⟩ : syracuseStep 420371 = 630557) B630557
theorem B944675 : Blo 417772 944675 := bstep (se 1 (by rfl) ⟨708506, by rfl⟩ : syracuseStep 944675 = 1417013) B1417013
theorem B420387 : Blo 417772 420387 := bstep (se 1 (by rfl) ⟨315290, by rfl⟩ : syracuseStep 420387 = 630581) B630581
theorem B420403 : Blo 417772 420403 := bstep (se 1 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 420403 = 630605) B630605
theorem B420419 : Blo 417772 420419 := bstep (se 1 (by rfl) ⟨315314, by rfl⟩ : syracuseStep 420419 = 630629) B630629
theorem B420435 : Blo 417772 420435 := bstep (se 1 (by rfl) ⟨315326, by rfl⟩ : syracuseStep 420435 = 630653) B630653
theorem B420451 : Blo 417772 420451 := bstep (se 1 (by rfl) ⟨315338, by rfl⟩ : syracuseStep 420451 = 630677) B630677
theorem B1075825 : Blo 417772 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B420467 : Blo 417772 420467 := bstep (se 1 (by rfl) ⟨315350, by rfl⟩ : syracuseStep 420467 = 630701) B630701
theorem B420483 : Blo 417772 420483 := bstep (se 1 (by rfl) ⟨315362, by rfl⟩ : syracuseStep 420483 = 630725) B630725
theorem B420499 : Blo 417772 420499 := bstep (se 1 (by rfl) ⟨315374, by rfl⟩ : syracuseStep 420499 = 630749) B630749
theorem B420515 : Blo 417772 420515 := bstep (se 1 (by rfl) ⟨315386, by rfl⟩ : syracuseStep 420515 = 630773) B630773
theorem B420531 : Blo 417772 420531 := bstep (se 1 (by rfl) ⟨315398, by rfl⟩ : syracuseStep 420531 = 630797) B630797
theorem B420547 : Blo 417772 420547 := bstep (se 1 (by rfl) ⟨315410, by rfl⟩ : syracuseStep 420547 = 630821) B630821
theorem B420563 : Blo 417772 420563 := bstep (se 1 (by rfl) ⟨315422, by rfl⟩ : syracuseStep 420563 = 630845) B630845
theorem B420579 : Blo 417772 420579 := bstep (se 1 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 420579 = 630869) B630869
theorem B420595 : Blo 417772 420595 := bstep (se 1 (by rfl) ⟨315446, by rfl⟩ : syracuseStep 420595 = 630893) B630893
theorem B584435 : Blo 417772 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B420611 : Blo 417772 420611 := bstep (se 1 (by rfl) ⟨315458, by rfl⟩ : syracuseStep 420611 = 630917) B630917
theorem B420627 : Blo 417772 420627 := bstep (se 1 (by rfl) ⟨315470, by rfl⟩ : syracuseStep 420627 = 630941) B630941
theorem B420643 : Blo 417772 420643 := bstep (se 1 (by rfl) ⟨315482, by rfl⟩ : syracuseStep 420643 = 630965) B630965
theorem B944945 : Blo 417772 944945 := bstep (se 2 (by rfl) ⟨354354, by rfl⟩ : syracuseStep 944945 = 708709) B708709
theorem B420659 : Blo 417772 420659 := bstep (se 1 (by rfl) ⟨315494, by rfl⟩ : syracuseStep 420659 = 630989) B630989
theorem B944963 : Blo 417772 944963 := bstep (se 1 (by rfl) ⟨708722, by rfl⟩ : syracuseStep 944963 = 1417445) B1417445
theorem B420675 : Blo 417772 420675 := bstep (se 1 (by rfl) ⟨315506, by rfl⟩ : syracuseStep 420675 = 631013) B631013
theorem B420691 : Blo 417772 420691 := bstep (se 1 (by rfl) ⟨315518, by rfl⟩ : syracuseStep 420691 = 631037) B631037
theorem B420707 : Blo 417772 420707 := bstep (se 1 (by rfl) ⟨315530, by rfl⟩ : syracuseStep 420707 = 631061) B631061
theorem B420723 : Blo 417772 420723 := bstep (se 1 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 420723 = 631085) B631085
theorem B420739 : Blo 417772 420739 := bstep (se 1 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 420739 = 631109) B631109
theorem B420755 : Blo 417772 420755 := bstep (se 1 (by rfl) ⟨315566, by rfl⟩ : syracuseStep 420755 = 631133) B631133
theorem B420771 : Blo 417772 420771 := bstep (se 1 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 420771 = 631157) B631157
theorem B420787 : Blo 417772 420787 := bstep (se 1 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 420787 = 631181) B631181
theorem B420803 : Blo 417772 420803 := bstep (se 1 (by rfl) ⟨315602, by rfl⟩ : syracuseStep 420803 = 631205) B631205
theorem B420819 : Blo 417772 420819 := bstep (se 1 (by rfl) ⟨315614, by rfl⟩ : syracuseStep 420819 = 631229) B631229
theorem B420835 : Blo 417772 420835 := bstep (se 1 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 420835 = 631253) B631253
theorem B420851 : Blo 417772 420851 := bstep (se 1 (by rfl) ⟨315638, by rfl⟩ : syracuseStep 420851 = 631277) B631277
theorem B420867 : Blo 417772 420867 := bstep (se 1 (by rfl) ⟨315650, by rfl⟩ : syracuseStep 420867 = 631301) B631301
theorem B420883 : Blo 417772 420883 := bstep (se 1 (by rfl) ⟨315662, by rfl⟩ : syracuseStep 420883 = 631325) B631325
theorem B420899 : Blo 417772 420899 := bstep (se 1 (by rfl) ⟨315674, by rfl⟩ : syracuseStep 420899 = 631349) B631349
theorem B420915 : Blo 417772 420915 := bstep (se 1 (by rfl) ⟨315686, by rfl⟩ : syracuseStep 420915 = 631373) B631373
theorem B420931 : Blo 417772 420931 := bstep (se 1 (by rfl) ⟨315698, by rfl⟩ : syracuseStep 420931 = 631397) B631397
theorem B945233 : Blo 417772 945233 := bstep (se 2 (by rfl) ⟨354462, by rfl⟩ : syracuseStep 945233 = 708925) B708925
theorem B420947 : Blo 417772 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B945251 : Blo 417772 945251 := bstep (se 1 (by rfl) ⟨708938, by rfl⟩ : syracuseStep 945251 = 1417877) B1417877
theorem B420963 : Blo 417772 420963 := bstep (se 1 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 420963 = 631445) B631445
theorem B420979 : Blo 417772 420979 := bstep (se 1 (by rfl) ⟨315734, by rfl⟩ : syracuseStep 420979 = 631469) B631469
theorem B420995 : Blo 417772 420995 := bstep (se 1 (by rfl) ⟨315746, by rfl⟩ : syracuseStep 420995 = 631493) B631493
theorem B421011 : Blo 417772 421011 := bstep (se 1 (by rfl) ⟨315758, by rfl⟩ : syracuseStep 421011 = 631517) B631517
theorem B421027 : Blo 417772 421027 := bstep (se 1 (by rfl) ⟨315770, by rfl⟩ : syracuseStep 421027 = 631541) B631541
theorem B1273009 : Blo 417772 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B421043 : Blo 417772 421043 := bstep (se 1 (by rfl) ⟨315782, by rfl⟩ : syracuseStep 421043 = 631565) B631565
theorem B421059 : Blo 417772 421059 := bstep (se 1 (by rfl) ⟨315794, by rfl⟩ : syracuseStep 421059 = 631589) B631589
theorem B421075 : Blo 417772 421075 := bstep (se 1 (by rfl) ⟨315806, by rfl⟩ : syracuseStep 421075 = 631613) B631613
theorem B421091 : Blo 417772 421091 := bstep (se 1 (by rfl) ⟨315818, by rfl⟩ : syracuseStep 421091 = 631637) B631637
theorem B421107 : Blo 417772 421107 := bstep (se 1 (by rfl) ⟨315830, by rfl⟩ : syracuseStep 421107 = 631661) B631661
theorem B421123 : Blo 417772 421123 := bstep (se 1 (by rfl) ⟨315842, by rfl⟩ : syracuseStep 421123 = 631685) B631685
theorem B421139 : Blo 417772 421139 := bstep (se 1 (by rfl) ⟨315854, by rfl⟩ : syracuseStep 421139 = 631709) B631709
theorem B421155 : Blo 417772 421155 := bstep (se 1 (by rfl) ⟨315866, by rfl⟩ : syracuseStep 421155 = 631733) B631733
theorem B421171 : Blo 417772 421171 := bstep (se 1 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 421171 = 631757) B631757
theorem B421187 : Blo 417772 421187 := bstep (se 1 (by rfl) ⟨315890, by rfl⟩ : syracuseStep 421187 = 631781) B631781
theorem B421203 : Blo 417772 421203 := bstep (se 1 (by rfl) ⟨315902, by rfl⟩ : syracuseStep 421203 = 631805) B631805
theorem B421219 : Blo 417772 421219 := bstep (se 1 (by rfl) ⟨315914, by rfl⟩ : syracuseStep 421219 = 631829) B631829
theorem B945521 : Blo 417772 945521 := bstep (se 2 (by rfl) ⟨354570, by rfl⟩ : syracuseStep 945521 = 709141) B709141
theorem B421235 : Blo 417772 421235 := bstep (se 1 (by rfl) ⟨315926, by rfl⟩ : syracuseStep 421235 = 631853) B631853
theorem B945539 : Blo 417772 945539 := bstep (se 1 (by rfl) ⟨709154, by rfl⟩ : syracuseStep 945539 = 1418309) B1418309
theorem B421251 : Blo 417772 421251 := bstep (se 1 (by rfl) ⟨315938, by rfl⟩ : syracuseStep 421251 = 631877) B631877
theorem B421267 : Blo 417772 421267 := bstep (se 1 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 421267 = 631901) B631901
theorem B421283 : Blo 417772 421283 := bstep (se 1 (by rfl) ⟨315962, by rfl⟩ : syracuseStep 421283 = 631925) B631925
theorem B421299 : Blo 417772 421299 := bstep (se 1 (by rfl) ⟨315974, by rfl⟩ : syracuseStep 421299 = 631949) B631949
theorem B421315 : Blo 417772 421315 := bstep (se 1 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 421315 = 631973) B631973
theorem B421331 : Blo 417772 421331 := bstep (se 1 (by rfl) ⟨315998, by rfl⟩ : syracuseStep 421331 = 631997) B631997
theorem B421347 : Blo 417772 421347 := bstep (se 1 (by rfl) ⟨316010, by rfl⟩ : syracuseStep 421347 = 632021) B632021
theorem B421363 : Blo 417772 421363 := bstep (se 1 (by rfl) ⟨316022, by rfl⟩ : syracuseStep 421363 = 632045) B632045
theorem B421379 : Blo 417772 421379 := bstep (se 1 (by rfl) ⟨316034, by rfl⟩ : syracuseStep 421379 = 632069) B632069
theorem B421395 : Blo 417772 421395 := bstep (se 1 (by rfl) ⟨316046, by rfl⟩ : syracuseStep 421395 = 632093) B632093
theorem B421411 : Blo 417772 421411 := bstep (se 1 (by rfl) ⟨316058, by rfl⟩ : syracuseStep 421411 = 632117) B632117
theorem B421427 : Blo 417772 421427 := bstep (se 1 (by rfl) ⟨316070, by rfl⟩ : syracuseStep 421427 = 632141) B632141
theorem B421443 : Blo 417772 421443 := bstep (se 1 (by rfl) ⟨316082, by rfl⟩ : syracuseStep 421443 = 632165) B632165
theorem B421459 : Blo 417772 421459 := bstep (se 1 (by rfl) ⟨316094, by rfl⟩ : syracuseStep 421459 = 632189) B632189
theorem B421475 : Blo 417772 421475 := bstep (se 1 (by rfl) ⟨316106, by rfl⟩ : syracuseStep 421475 = 632213) B632213
theorem B421491 : Blo 417772 421491 := bstep (se 1 (by rfl) ⟨316118, by rfl⟩ : syracuseStep 421491 = 632237) B632237
theorem B421507 : Blo 417772 421507 := bstep (se 1 (by rfl) ⟨316130, by rfl⟩ : syracuseStep 421507 = 632261) B632261
theorem B945809 : Blo 417772 945809 := bstep (se 2 (by rfl) ⟨354678, by rfl⟩ : syracuseStep 945809 = 709357) B709357
theorem B421523 : Blo 417772 421523 := bstep (se 1 (by rfl) ⟨316142, by rfl⟩ : syracuseStep 421523 = 632285) B632285
theorem B945827 : Blo 417772 945827 := bstep (se 1 (by rfl) ⟨709370, by rfl⟩ : syracuseStep 945827 = 1418741) B1418741
theorem B421539 : Blo 417772 421539 := bstep (se 1 (by rfl) ⟨316154, by rfl⟩ : syracuseStep 421539 = 632309) B632309
theorem B421555 : Blo 417772 421555 := bstep (se 1 (by rfl) ⟨316166, by rfl⟩ : syracuseStep 421555 = 632333) B632333
theorem B421571 : Blo 417772 421571 := bstep (se 1 (by rfl) ⟨316178, by rfl⟩ : syracuseStep 421571 = 632357) B632357
theorem B683731 : Blo 417772 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B421587 : Blo 417772 421587 := bstep (se 1 (by rfl) ⟨316190, by rfl⟩ : syracuseStep 421587 = 632381) B632381
theorem B421603 : Blo 417772 421603 := bstep (se 1 (by rfl) ⟨316202, by rfl⟩ : syracuseStep 421603 = 632405) B632405
theorem B4091633 : Blo 417772 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B1732337 : Blo 417772 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B421619 : Blo 417772 421619 := bstep (se 1 (by rfl) ⟨316214, by rfl⟩ : syracuseStep 421619 = 632429) B632429
theorem B421635 : Blo 417772 421635 := bstep (se 1 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 421635 = 632453) B632453
theorem B2682629 : Blo 417772 2682629 := bstep (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) B502993
theorem B421651 : Blo 417772 421651 := bstep (se 1 (by rfl) ⟨316238, by rfl⟩ : syracuseStep 421651 = 632477) B632477
theorem B847651 : Blo 417772 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B421667 : Blo 417772 421667 := bstep (se 1 (by rfl) ⟨316250, by rfl⟩ : syracuseStep 421667 = 632501) B632501
theorem B421683 : Blo 417772 421683 := bstep (se 1 (by rfl) ⟨316262, by rfl⟩ : syracuseStep 421683 = 632525) B632525
theorem B421699 : Blo 417772 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B421715 : Blo 417772 421715 := bstep (se 1 (by rfl) ⟨316286, by rfl⟩ : syracuseStep 421715 = 632573) B632573
theorem B2715491 : Blo 417772 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B421731 : Blo 417772 421731 := bstep (se 1 (by rfl) ⟨316298, by rfl⟩ : syracuseStep 421731 = 632597) B632597
theorem B421747 : Blo 417772 421747 := bstep (se 1 (by rfl) ⟨316310, by rfl⟩ : syracuseStep 421747 = 632621) B632621
theorem B421763 : Blo 417772 421763 := bstep (se 1 (by rfl) ⟨316322, by rfl⟩ : syracuseStep 421763 = 632645) B632645
theorem B1011619 : Blo 417772 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B946097 : Blo 417772 946097 := bstep (se 2 (by rfl) ⟨354786, by rfl⟩ : syracuseStep 946097 = 709573) B709573
theorem B946115 : Blo 417772 946115 := bstep (se 1 (by rfl) ⟨709586, by rfl⟩ : syracuseStep 946115 = 1419173) B1419173
theorem B716833 : Blo 417772 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B1798193 : Blo 417772 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B946385 : Blo 417772 946385 := bstep (se 2 (by rfl) ⟨354894, by rfl⟩ : syracuseStep 946385 = 709789) B709789
theorem B946403 : Blo 417772 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B3207395 : Blo 417772 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B2879813 : Blo 417772 2879813 := bstep (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) B539965
theorem B2388365 : Blo 417772 2388365 := bstep (se 3 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 2388365 = 895637) B895637
theorem B1274321 : Blo 417772 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B946673 : Blo 417772 946673 := bstep (se 2 (by rfl) ⟨355002, by rfl⟩ : syracuseStep 946673 = 710005) B710005
theorem B946691 : Blo 417772 946691 := bstep (se 1 (by rfl) ⟨710018, by rfl⟩ : syracuseStep 946691 = 1420037) B1420037
theorem B1700621 : Blo 417772 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B946961 : Blo 417772 946961 := bstep (se 2 (by rfl) ⟨355110, by rfl⟩ : syracuseStep 946961 = 710221) B710221
theorem B946979 : Blo 417772 946979 := bstep (se 1 (by rfl) ⟨710234, by rfl⟩ : syracuseStep 946979 = 1420469) B1420469
theorem B848753 : Blo 417772 848753 := bstep (se 2 (by rfl) ⟨318282, by rfl⟩ : syracuseStep 848753 = 636565) B636565
theorem B1799117 : Blo 417772 1799117 := bstep (se 3 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 1799117 = 674669) B674669
theorem B2126897 : Blo 417772 2126897 := bstep (se 2 (by rfl) ⟨797586, by rfl⟩ : syracuseStep 2126897 = 1595173) B1595173
theorem B947249 : Blo 417772 947249 := bstep (se 2 (by rfl) ⟨355218, by rfl⟩ : syracuseStep 947249 = 710437) B710437
theorem B947267 : Blo 417772 947267 := bstep (se 1 (by rfl) ⟨710450, by rfl⟩ : syracuseStep 947267 = 1420901) B1420901
theorem B3175523 : Blo 417772 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B2389297 : Blo 417772 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B947537 : Blo 417772 947537 := bstep (se 2 (by rfl) ⟨355326, by rfl⟩ : syracuseStep 947537 = 710653) B710653
theorem B947555 : Blo 417772 947555 := bstep (se 1 (by rfl) ⟨710666, by rfl⟩ : syracuseStep 947555 = 1421333) B1421333
theorem B6452621 : Blo 417772 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B849379 : Blo 417772 849379 := bstep (se 1 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 849379 = 1274069) B1274069
theorem B1439309 : Blo 417772 1439309 := bstep (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) B539741
theorem B947825 : Blo 417772 947825 := bstep (se 2 (by rfl) ⟨355434, by rfl⟩ : syracuseStep 947825 = 710869) B710869
theorem B947843 : Blo 417772 947843 := bstep (se 1 (by rfl) ⟨710882, by rfl⟩ : syracuseStep 947843 = 1421765) B1421765
theorem B816817 : Blo 417772 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B980689 : Blo 417772 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B1341137 : Blo 417772 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B1210211 : Blo 417772 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B1079153 : Blo 417772 1079153 := bstep (se 2 (by rfl) ⟨404682, by rfl⟩ : syracuseStep 1079153 = 809365) B809365
theorem B948113 : Blo 417772 948113 := bstep (se 2 (by rfl) ⟨355542, by rfl⟩ : syracuseStep 948113 = 711085) B711085
theorem B948131 : Blo 417772 948131 := bstep (se 1 (by rfl) ⟨711098, by rfl⟩ : syracuseStep 948131 = 1422197) B1422197
theorem B718913 : Blo 417772 718913 := bstep (se 2 (by rfl) ⟨269592, by rfl⟩ : syracuseStep 718913 = 539185) B539185
theorem B948401 : Blo 417772 948401 := bstep (se 2 (by rfl) ⟨355650, by rfl⟩ : syracuseStep 948401 = 711301) B711301
theorem B948419 : Blo 417772 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B948689 : Blo 417772 948689 := bstep (se 2 (by rfl) ⟨355758, by rfl⟩ : syracuseStep 948689 = 711517) B711517
theorem B2128355 : Blo 417772 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B948707 : Blo 417772 948707 := bstep (se 1 (by rfl) ⟨711530, by rfl⟩ : syracuseStep 948707 = 1423061) B1423061
theorem B2390755 : Blo 417772 2390755 := bstep (se 1 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 2390755 = 3586133) B3586133
theorem B948977 : Blo 417772 948977 := bstep (se 2 (by rfl) ⟨355866, by rfl⟩ : syracuseStep 948977 = 711733) B711733
theorem B2686115 : Blo 417772 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B2391281 : Blo 417772 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B2129165 : Blo 417772 2129165 := bstep (se 3 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 2129165 = 798437) B798437
theorem B851267 : Blo 417772 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B1343213 : Blo 417772 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B52396145 : Blo 417772 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B2130137 : Blo 417772 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B2425133 : Blo 417772 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B852403 : Blo 417772 852403 := bstep (se 1 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 852403 = 1278605) B1278605
theorem B1081817 : Blo 417772 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B8553053 : Blo 417772 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B27984611 : Blo 417772 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B2688065 : Blo 417772 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B1279127 : Blo 417772 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B4523309 : Blo 417772 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B2458925 : Blo 417772 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B755009 : Blo 417772 755009 := bstep (se 2 (by rfl) ⟨283128, by rfl⟩ : syracuseStep 755009 = 566257) B566257
theorem B2131757 : Blo 417772 2131757 := bstep (se 3 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 2131757 = 799409) B799409
theorem B1017803 : Blo 417772 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B1411019 : Blo 417772 1411019 := bstep (se 1 (by rfl) ⟨1058264, by rfl⟩ : syracuseStep 1411019 = 2116529) B2116529
theorem B854155 : Blo 417772 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B854219 : Blo 417772 854219 := bstep (se 1 (by rfl) ⟨640664, by rfl⟩ : syracuseStep 854219 = 1281329) B1281329
theorem B1411289 : Blo 417772 1411289 := bstep (se 2 (by rfl) ⟨529233, by rfl⟩ : syracuseStep 1411289 = 1058467) B1058467
theorem B3016921 : Blo 417772 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B5114177 : Blo 417772 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B3017035 : Blo 417772 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B2722405 : Blo 417772 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B1346327 : Blo 417772 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B461611 : Blo 417772 461611 := bstep (se 1 (by rfl) ⟨346208, by rfl⟩ : syracuseStep 461611 = 692417) B692417
theorem B1477441 : Blo 417772 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1411991 : Blo 417772 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B756697 : Blo 417772 756697 := bstep (se 2 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 756697 = 567523) B567523
theorem B3181841 : Blo 417772 3181841 := bstep (se 2 (by rfl) ⟨1193190, by rfl⟩ : syracuseStep 3181841 = 2386381) B2386381
theorem B1019159 : Blo 417772 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B1412531 : Blo 417772 1412531 := bstep (se 1 (by rfl) ⟨1059398, by rfl⟩ : syracuseStep 1412531 = 2118797) B2118797
theorem B1412801 : Blo 417772 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B626699 : Blo 417772 626699 := bstep (se 1 (by rfl) ⟨470024, by rfl⟩ : syracuseStep 626699 = 940049) B940049
theorem B2691089 : Blo 417772 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B626711 : Blo 417772 626711 := bstep (se 1 (by rfl) ⟨470033, by rfl⟩ : syracuseStep 626711 = 940067) B940067
theorem B626777 : Blo 417772 626777 := bstep (se 2 (by rfl) ⟨235041, by rfl⟩ : syracuseStep 626777 = 470083) B470083
theorem B3575987 : Blo 417772 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B626891 : Blo 417772 626891 := bstep (se 1 (by rfl) ⟨470168, by rfl⟩ : syracuseStep 626891 = 940337) B940337
theorem B626903 : Blo 417772 626903 := bstep (se 1 (by rfl) ⟨470177, by rfl⟩ : syracuseStep 626903 = 940355) B940355
theorem B1413341 : Blo 417772 1413341 := bstep (se 3 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 1413341 = 530003) B530003
theorem B626969 : Blo 417772 626969 := bstep (se 2 (by rfl) ⟨235113, by rfl⟩ : syracuseStep 626969 = 470227) B470227
theorem B758081 : Blo 417772 758081 := bstep (se 2 (by rfl) ⟨284280, by rfl⟩ : syracuseStep 758081 = 568561) B568561
theorem B627083 : Blo 417772 627083 := bstep (se 1 (by rfl) ⟨470312, by rfl⟩ : syracuseStep 627083 = 940625) B940625
theorem B627095 : Blo 417772 627095 := bstep (se 1 (by rfl) ⟨470321, by rfl⟩ : syracuseStep 627095 = 940643) B940643
theorem B627161 : Blo 417772 627161 := bstep (se 2 (by rfl) ⟨235185, by rfl⟩ : syracuseStep 627161 = 470371) B470371
theorem B2691629 : Blo 417772 2691629 := bstep (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) B1009361
theorem B627275 : Blo 417772 627275 := bstep (se 1 (by rfl) ⟨470456, by rfl⟩ : syracuseStep 627275 = 940913) B940913
theorem B627287 : Blo 417772 627287 := bstep (se 1 (by rfl) ⟨470465, by rfl⟩ : syracuseStep 627287 = 940931) B940931
theorem B627353 : Blo 417772 627353 := bstep (se 2 (by rfl) ⟨235257, by rfl⟩ : syracuseStep 627353 = 470515) B470515
theorem B627467 : Blo 417772 627467 := bstep (se 1 (by rfl) ⟨470600, by rfl⟩ : syracuseStep 627467 = 941201) B941201
theorem B627479 : Blo 417772 627479 := bstep (se 1 (by rfl) ⟨470609, by rfl⟩ : syracuseStep 627479 = 941219) B941219
theorem B627545 : Blo 417772 627545 := bstep (se 2 (by rfl) ⟨235329, by rfl⟩ : syracuseStep 627545 = 470659) B470659
theorem B529355 : Blo 417772 529355 := bstep (se 1 (by rfl) ⟨397016, by rfl⟩ : syracuseStep 529355 = 794033) B794033
theorem B627659 : Blo 417772 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B627671 : Blo 417772 627671 := bstep (se 1 (by rfl) ⟨470753, by rfl⟩ : syracuseStep 627671 = 941507) B941507
theorem B594955 : Blo 417772 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B594967 : Blo 417772 594967 := bstep (se 1 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 594967 = 892451) B892451
theorem B627737 : Blo 417772 627737 := bstep (se 2 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 627737 = 470803) B470803
theorem B922711 : Blo 417772 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B627851 : Blo 417772 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B627863 : Blo 417772 627863 := bstep (se 1 (by rfl) ⟨470897, by rfl⟩ : syracuseStep 627863 = 941795) B941795
theorem B1348787 : Blo 417772 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B627929 : Blo 417772 627929 := bstep (se 2 (by rfl) ⟨235473, by rfl⟩ : syracuseStep 627929 = 470947) B470947
theorem B1348825 : Blo 417772 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B4035905 : Blo 417772 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B628043 : Blo 417772 628043 := bstep (se 1 (by rfl) ⟨471032, by rfl⟩ : syracuseStep 628043 = 942065) B942065
theorem B1414475 : Blo 417772 1414475 := bstep (se 1 (by rfl) ⟨1060856, by rfl⟩ : syracuseStep 1414475 = 2121713) B2121713
theorem B628055 : Blo 417772 628055 := bstep (se 1 (by rfl) ⟨471041, by rfl⟩ : syracuseStep 628055 = 942083) B942083
theorem B628121 : Blo 417772 628121 := bstep (se 2 (by rfl) ⟨235545, by rfl⟩ : syracuseStep 628121 = 471091) B471091
theorem B628235 : Blo 417772 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B628247 : Blo 417772 628247 := bstep (se 1 (by rfl) ⟨471185, by rfl⟩ : syracuseStep 628247 = 942371) B942371
theorem B628313 : Blo 417772 628313 := bstep (se 2 (by rfl) ⟨235617, by rfl⟩ : syracuseStep 628313 = 471235) B471235
theorem B1414745 : Blo 417772 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B759385 : Blo 417772 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B530059 : Blo 417772 530059 := bstep (se 1 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 530059 = 795089) B795089
theorem B628427 : Blo 417772 628427 := bstep (se 1 (by rfl) ⟨471320, by rfl⟩ : syracuseStep 628427 = 942641) B942641
theorem B628439 : Blo 417772 628439 := bstep (se 1 (by rfl) ⟨471329, by rfl⟩ : syracuseStep 628439 = 942659) B942659
theorem B628505 : Blo 417772 628505 := bstep (se 2 (by rfl) ⟨235689, by rfl⟩ : syracuseStep 628505 = 471379) B471379
theorem B2398045 : Blo 417772 2398045 := bstep (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) B899267
theorem B628619 : Blo 417772 628619 := bstep (se 1 (by rfl) ⟨471464, by rfl⟩ : syracuseStep 628619 = 942929) B942929
theorem B530327 : Blo 417772 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B628631 : Blo 417772 628631 := bstep (se 1 (by rfl) ⟨471473, by rfl⟩ : syracuseStep 628631 = 942947) B942947
theorem B1841075 : Blo 417772 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B628697 : Blo 417772 628697 := bstep (se 2 (by rfl) ⟨235761, by rfl⟩ : syracuseStep 628697 = 471523) B471523
theorem B628811 : Blo 417772 628811 := bstep (se 1 (by rfl) ⟨471608, by rfl⟩ : syracuseStep 628811 = 943217) B943217
theorem B628823 : Blo 417772 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B628889 : Blo 417772 628889 := bstep (se 2 (by rfl) ⟨235833, by rfl⟩ : syracuseStep 628889 = 471667) B471667
theorem B629003 : Blo 417772 629003 := bstep (se 1 (by rfl) ⟨471752, by rfl⟩ : syracuseStep 629003 = 943505) B943505
theorem B629015 : Blo 417772 629015 := bstep (se 1 (by rfl) ⟨471761, by rfl⟩ : syracuseStep 629015 = 943523) B943523
theorem B1415447 : Blo 417772 1415447 := bstep (se 1 (by rfl) ⟨1061585, by rfl⟩ : syracuseStep 1415447 = 2123171) B2123171
theorem B3676481 : Blo 417772 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B629081 : Blo 417772 629081 := bstep (se 2 (by rfl) ⟨235905, by rfl⟩ : syracuseStep 629081 = 471811) B471811
theorem B629195 : Blo 417772 629195 := bstep (se 1 (by rfl) ⟨471896, by rfl⟩ : syracuseStep 629195 = 943793) B943793
theorem B629207 : Blo 417772 629207 := bstep (se 1 (by rfl) ⟨471905, by rfl⟩ : syracuseStep 629207 = 943811) B943811
theorem B2431505 : Blo 417772 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B629273 : Blo 417772 629273 := bstep (se 2 (by rfl) ⟨235977, by rfl⟩ : syracuseStep 629273 = 471955) B471955
theorem B531031 : Blo 417772 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B629387 : Blo 417772 629387 := bstep (se 1 (by rfl) ⟨472040, by rfl⟩ : syracuseStep 629387 = 944081) B944081
theorem B629399 : Blo 417772 629399 := bstep (se 1 (by rfl) ⟨472049, by rfl⟩ : syracuseStep 629399 = 944099) B944099
theorem B629465 : Blo 417772 629465 := bstep (se 2 (by rfl) ⟨236049, by rfl⟩ : syracuseStep 629465 = 472099) B472099
theorem B1514285 : Blo 417772 1514285 := bstep (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) B567857
theorem B1415987 : Blo 417772 1415987 := bstep (se 1 (by rfl) ⟨1061990, by rfl⟩ : syracuseStep 1415987 = 2123981) B2123981
theorem B629579 : Blo 417772 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B1514315 : Blo 417772 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B629591 : Blo 417772 629591 := bstep (se 1 (by rfl) ⟨472193, by rfl⟩ : syracuseStep 629591 = 944387) B944387
theorem B629657 : Blo 417772 629657 := bstep (se 2 (by rfl) ⟨236121, by rfl⟩ : syracuseStep 629657 = 472243) B472243
theorem B12098483 : Blo 417772 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B793547 : Blo 417772 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B629771 : Blo 417772 629771 := bstep (se 1 (by rfl) ⟨472328, by rfl⟩ : syracuseStep 629771 = 944657) B944657
theorem B629783 : Blo 417772 629783 := bstep (se 1 (by rfl) ⟨472337, by rfl⟩ : syracuseStep 629783 = 944675) B944675
theorem B597017 : Blo 417772 597017 := bstep (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) B447763
theorem B3185729 : Blo 417772 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B1416257 : Blo 417772 1416257 := bstep (se 2 (by rfl) ⟨531096, by rfl⟩ : syracuseStep 1416257 = 1062193) B1062193
theorem B2432065 : Blo 417772 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B629849 : Blo 417772 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B793729 : Blo 417772 793729 := bstep (se 2 (by rfl) ⟨297648, by rfl⟩ : syracuseStep 793729 = 595297) B595297
theorem B629963 : Blo 417772 629963 := bstep (se 1 (by rfl) ⟨472472, by rfl⟩ : syracuseStep 629963 = 944945) B944945
theorem B629975 : Blo 417772 629975 := bstep (se 1 (by rfl) ⟨472481, by rfl⟩ : syracuseStep 629975 = 944963) B944963
theorem B18455813 : Blo 417772 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B630041 : Blo 417772 630041 := bstep (se 2 (by rfl) ⟨236265, by rfl⟩ : syracuseStep 630041 = 472531) B472531
theorem B892289 : Blo 417772 892289 := bstep (se 2 (by rfl) ⟨334608, by rfl⟩ : syracuseStep 892289 = 669217) B669217
theorem B630155 : Blo 417772 630155 := bstep (se 1 (by rfl) ⟨472616, by rfl⟩ : syracuseStep 630155 = 945233) B945233
theorem B630167 : Blo 417772 630167 := bstep (se 1 (by rfl) ⟨472625, by rfl⟩ : syracuseStep 630167 = 945251) B945251
theorem B630233 : Blo 417772 630233 := bstep (se 2 (by rfl) ⟨236337, by rfl⟩ : syracuseStep 630233 = 472675) B472675
theorem B1089089 : Blo 417772 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B630347 : Blo 417772 630347 := bstep (se 1 (by rfl) ⟨472760, by rfl⟩ : syracuseStep 630347 = 945521) B945521
theorem B630359 : Blo 417772 630359 := bstep (se 1 (by rfl) ⟨472769, by rfl⟩ : syracuseStep 630359 = 945539) B945539
theorem B1416797 : Blo 417772 1416797 := bstep (se 3 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 1416797 = 531299) B531299
theorem B597655 : Blo 417772 597655 := bstep (se 1 (by rfl) ⟨448241, by rfl⟩ : syracuseStep 597655 = 896483) B896483
theorem B630425 : Blo 417772 630425 := bstep (se 2 (by rfl) ⟨236409, by rfl⟩ : syracuseStep 630425 = 472819) B472819
theorem B630539 : Blo 417772 630539 := bstep (se 1 (by rfl) ⟨472904, by rfl⟩ : syracuseStep 630539 = 945809) B945809
theorem B630551 : Blo 417772 630551 := bstep (se 1 (by rfl) ⟨472913, by rfl⟩ : syracuseStep 630551 = 945827) B945827
theorem B794443 : Blo 417772 794443 := bstep (se 1 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 794443 = 1191665) B1191665
theorem B2727755 : Blo 417772 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B1154891 : Blo 417772 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B630617 : Blo 417772 630617 := bstep (se 2 (by rfl) ⟨236481, by rfl⟩ : syracuseStep 630617 = 472963) B472963
theorem B794519 : Blo 417772 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B630731 : Blo 417772 630731 := bstep (se 1 (by rfl) ⟨473048, by rfl⟩ : syracuseStep 630731 = 946097) B946097
theorem B630743 : Blo 417772 630743 := bstep (se 1 (by rfl) ⟨473057, by rfl⟩ : syracuseStep 630743 = 946115) B946115
theorem B630809 : Blo 417772 630809 := bstep (se 2 (by rfl) ⟨236553, by rfl⟩ : syracuseStep 630809 = 473107) B473107
theorem B630923 : Blo 417772 630923 := bstep (se 1 (by rfl) ⟨473192, by rfl⟩ : syracuseStep 630923 = 946385) B946385
theorem B630935 : Blo 417772 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B631001 : Blo 417772 631001 := bstep (se 2 (by rfl) ⟨236625, by rfl⟩ : syracuseStep 631001 = 473251) B473251
theorem B532747 : Blo 417772 532747 := bstep (se 1 (by rfl) ⟨399560, by rfl⟩ : syracuseStep 532747 = 799121) B799121
theorem B631115 : Blo 417772 631115 := bstep (se 1 (by rfl) ⟨473336, by rfl⟩ : syracuseStep 631115 = 946673) B946673
theorem B631127 : Blo 417772 631127 := bstep (se 1 (by rfl) ⟨473345, by rfl⟩ : syracuseStep 631127 = 946691) B946691
theorem B631193 : Blo 417772 631193 := bstep (se 2 (by rfl) ⟨236697, by rfl⟩ : syracuseStep 631193 = 473395) B473395
theorem B598475 : Blo 417772 598475 := bstep (se 1 (by rfl) ⟨448856, by rfl⟩ : syracuseStep 598475 = 897713) B897713
theorem B631307 : Blo 417772 631307 := bstep (se 1 (by rfl) ⟨473480, by rfl⟩ : syracuseStep 631307 = 946961) B946961
theorem B631319 : Blo 417772 631319 := bstep (se 1 (by rfl) ⟨473489, by rfl⟩ : syracuseStep 631319 = 946979) B946979
theorem B795187 : Blo 417772 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B565835 : Blo 417772 565835 := bstep (se 1 (by rfl) ⟨424376, by rfl⟩ : syracuseStep 565835 = 848753) B848753
theorem B631385 : Blo 417772 631385 := bstep (se 2 (by rfl) ⟨236769, by rfl⟩ : syracuseStep 631385 = 473539) B473539
theorem B1417931 : Blo 417772 1417931 := bstep (se 1 (by rfl) ⟨1063448, by rfl⟩ : syracuseStep 1417931 = 2126897) B2126897
theorem B631499 : Blo 417772 631499 := bstep (se 1 (by rfl) ⟨473624, by rfl⟩ : syracuseStep 631499 = 947249) B947249
theorem B631511 : Blo 417772 631511 := bstep (se 1 (by rfl) ⟨473633, by rfl⟩ : syracuseStep 631511 = 947267) B947267
theorem B795415 : Blo 417772 795415 := bstep (se 1 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 795415 = 1193123) B1193123
theorem B631577 : Blo 417772 631577 := bstep (se 2 (by rfl) ⟨236841, by rfl⟩ : syracuseStep 631577 = 473683) B473683
theorem B2270045 : Blo 417772 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B795521 : Blo 417772 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B631691 : Blo 417772 631691 := bstep (se 1 (by rfl) ⟨473768, by rfl⟩ : syracuseStep 631691 = 947537) B947537
theorem B631703 : Blo 417772 631703 := bstep (se 1 (by rfl) ⟨473777, by rfl⟩ : syracuseStep 631703 = 947555) B947555
theorem B4301747 : Blo 417772 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B3187673 : Blo 417772 3187673 := bstep (se 2 (by rfl) ⟨1195377, by rfl⟩ : syracuseStep 3187673 = 2390755) B2390755
theorem B1418201 : Blo 417772 1418201 := bstep (se 2 (by rfl) ⟨531825, by rfl⟩ : syracuseStep 1418201 = 1063651) B1063651
theorem B631769 : Blo 417772 631769 := bstep (se 2 (by rfl) ⟨236913, by rfl⟩ : syracuseStep 631769 = 473827) B473827
theorem B795673 : Blo 417772 795673 := bstep (se 2 (by rfl) ⟨298377, by rfl⟩ : syracuseStep 795673 = 596755) B596755
theorem B959539 : Blo 417772 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B631883 : Blo 417772 631883 := bstep (se 1 (by rfl) ⟨473912, by rfl⟩ : syracuseStep 631883 = 947825) B947825
theorem B631895 : Blo 417772 631895 := bstep (se 1 (by rfl) ⟨473921, by rfl⟩ : syracuseStep 631895 = 947843) B947843
theorem B3646565 : Blo 417772 3646565 := bstep (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) B683731
theorem B894091 : Blo 417772 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B631961 : Blo 417772 631961 := bstep (se 2 (by rfl) ⟨236985, by rfl⟩ : syracuseStep 631961 = 473971) B473971
theorem B533719 : Blo 417772 533719 := bstep (se 1 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 533719 = 800579) B800579
theorem B1516765 : Blo 417772 1516765 := bstep (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) B568787
theorem B632075 : Blo 417772 632075 := bstep (se 1 (by rfl) ⟨474056, by rfl⟩ : syracuseStep 632075 = 948113) B948113
theorem B632087 : Blo 417772 632087 := bstep (se 1 (by rfl) ⟨474065, by rfl⟩ : syracuseStep 632087 = 948131) B948131
theorem B1058123 : Blo 417772 1058123 := bstep (se 1 (by rfl) ⟨793592, by rfl⟩ : syracuseStep 1058123 = 1587185) B1587185
theorem B632153 : Blo 417772 632153 := bstep (se 2 (by rfl) ⟨237057, by rfl⟩ : syracuseStep 632153 = 474115) B474115
theorem B632267 : Blo 417772 632267 := bstep (se 1 (by rfl) ⟨474200, by rfl⟩ : syracuseStep 632267 = 948401) B948401
theorem B632279 : Blo 417772 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B632345 : Blo 417772 632345 := bstep (se 2 (by rfl) ⟨237129, by rfl⟩ : syracuseStep 632345 = 474259) B474259
theorem B632459 : Blo 417772 632459 := bstep (se 1 (by rfl) ⟨474344, by rfl⟩ : syracuseStep 632459 = 948689) B948689
theorem B1418903 : Blo 417772 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B632471 : Blo 417772 632471 := bstep (se 1 (by rfl) ⟨474353, by rfl⟩ : syracuseStep 632471 = 948707) B948707
theorem B632537 : Blo 417772 632537 := bstep (se 2 (by rfl) ⟨237201, by rfl⟩ : syracuseStep 632537 = 474403) B474403
theorem B632651 : Blo 417772 632651 := bstep (se 1 (by rfl) ⟨474488, by rfl⟩ : syracuseStep 632651 = 948977) B948977
theorem B1419443 : Blo 417772 1419443 := bstep (se 1 (by rfl) ⟨1064582, by rfl⟩ : syracuseStep 1419443 = 2129165) B2129165
theorem B1059095 : Blo 417772 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B5122349 : Blo 417772 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B796979 : Blo 417772 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B1419713 : Blo 417772 1419713 := bstep (se 2 (by rfl) ⟨532392, by rfl⟩ : syracuseStep 1419713 = 1064785) B1064785
theorem B797131 : Blo 417772 797131 := bstep (se 1 (by rfl) ⟨597848, by rfl⟩ : syracuseStep 797131 = 1195697) B1195697
theorem B895475 : Blo 417772 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B3058181 : Blo 417772 3058181 := bstep (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) B573409
theorem B7547543 : Blo 417772 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B797465 : Blo 417772 797465 := bstep (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) B598099
theorem B764723 : Blo 417772 764723 := bstep (se 1 (by rfl) ⟨573542, by rfl⟩ : syracuseStep 764723 = 1147085) B1147085
theorem B3812275 : Blo 417772 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B1059763 : Blo 417772 1059763 := bstep (se 1 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 1059763 = 1589645) B1589645
theorem B1420253 : Blo 417772 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B1059905 : Blo 417772 1059905 := bstep (se 2 (by rfl) ⟨397464, by rfl⟩ : syracuseStep 1059905 = 794929) B794929
theorem B470155 : Blo 417772 470155 := bstep (se 1 (by rfl) ⟨352616, by rfl⟩ : syracuseStep 470155 = 705233) B705233
theorem B470263 : Blo 417772 470263 := bstep (se 1 (by rfl) ⟨352697, by rfl⟩ : syracuseStep 470263 = 705395) B705395
theorem B896321 : Blo 417772 896321 := bstep (se 2 (by rfl) ⟨336120, by rfl⟩ : syracuseStep 896321 = 672241) B672241
theorem B798103 : Blo 417772 798103 := bstep (se 1 (by rfl) ⟨598577, by rfl⟩ : syracuseStep 798103 = 1197155) B1197155
theorem B470443 : Blo 417772 470443 := bstep (se 1 (by rfl) ⟨352832, by rfl⟩ : syracuseStep 470443 = 705665) B705665
theorem B470551 : Blo 417772 470551 := bstep (se 1 (by rfl) ⟨352913, by rfl⟩ : syracuseStep 470551 = 705827) B705827
theorem B896663 : Blo 417772 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B470731 : Blo 417772 470731 := bstep (se 1 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 470731 = 706097) B706097
theorem B470839 : Blo 417772 470839 := bstep (se 1 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 470839 = 706259) B706259
theorem B1519505 : Blo 417772 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B471019 : Blo 417772 471019 := bstep (se 1 (by rfl) ⟨353264, by rfl⟩ : syracuseStep 471019 = 706529) B706529
theorem B1421387 : Blo 417772 1421387 := bstep (se 1 (by rfl) ⟨1066040, by rfl⟩ : syracuseStep 1421387 = 2132081) B2132081
theorem B471127 : Blo 417772 471127 := bstep (se 1 (by rfl) ⟨353345, by rfl⟩ : syracuseStep 471127 = 706691) B706691
theorem B7155863 : Blo 417772 7155863 := bstep (se 1 (by rfl) ⟨5366897, by rfl⟩ : syracuseStep 7155863 = 10733795) B10733795
theorem B798923 : Blo 417772 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B798977 : Blo 417772 798977 := bstep (se 2 (by rfl) ⟨299616, by rfl⟩ : syracuseStep 798977 = 599233) B599233
theorem B6041861 : Blo 417772 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B6828293 : Blo 417772 6828293 := bstep (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) B1280305
theorem B471307 : Blo 417772 471307 := bstep (se 1 (by rfl) ⟨353480, by rfl⟩ : syracuseStep 471307 = 706961) B706961
theorem B3191075 : Blo 417772 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B1061171 : Blo 417772 1061171 := bstep (se 1 (by rfl) ⟨795878, by rfl⟩ : syracuseStep 1061171 = 1591757) B1591757
theorem B1421657 : Blo 417772 1421657 := bstep (se 2 (by rfl) ⟨533121, by rfl⟩ : syracuseStep 1421657 = 1066243) B1066243
theorem B3584357 : Blo 417772 3584357 := bstep (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) B672067
theorem B471415 : Blo 417772 471415 := bstep (se 1 (by rfl) ⟨353561, by rfl⟩ : syracuseStep 471415 = 707123) B707123
theorem B1913305 : Blo 417772 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B471595 : Blo 417772 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B471703 : Blo 417772 471703 := bstep (se 1 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 471703 = 707555) B707555
theorem B635671 : Blo 417772 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B1061707 : Blo 417772 1061707 := bstep (se 1 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 1061707 = 1592561) B1592561
theorem B471883 : Blo 417772 471883 := bstep (se 1 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 471883 = 707825) B707825
theorem B471991 : Blo 417772 471991 := bstep (se 1 (by rfl) ⟨353993, by rfl⟩ : syracuseStep 471991 = 707987) B707987
theorem B1192907 : Blo 417772 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1061849 : Blo 417772 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B1422359 : Blo 417772 1422359 := bstep (se 1 (by rfl) ⟨1066769, by rfl⟩ : syracuseStep 1422359 = 2133539) B2133539
theorem B898123 : Blo 417772 898123 := bstep (se 1 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 898123 = 1347185) B1347185
theorem B472171 : Blo 417772 472171 := bstep (se 1 (by rfl) ⟨354128, by rfl⟩ : syracuseStep 472171 = 708257) B708257
theorem B799895 : Blo 417772 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B472279 : Blo 417772 472279 := bstep (se 1 (by rfl) ⟨354209, by rfl⟩ : syracuseStep 472279 = 708419) B708419
theorem B3814721 : Blo 417772 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B898379 : Blo 417772 898379 := bstep (se 1 (by rfl) ⟨673784, by rfl⟩ : syracuseStep 898379 = 1347569) B1347569
theorem B1193305 : Blo 417772 1193305 := bstep (se 2 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 1193305 = 894979) B894979
theorem B472459 : Blo 417772 472459 := bstep (se 1 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 472459 = 708689) B708689
theorem B472567 : Blo 417772 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B1422899 : Blo 417772 1422899 := bstep (se 1 (by rfl) ⟨1067174, by rfl⟩ : syracuseStep 1422899 = 2134349) B2134349
theorem B472747 : Blo 417772 472747 := bstep (se 1 (by rfl) ⟨354560, by rfl⟩ : syracuseStep 472747 = 709121) B709121
theorem B800435 : Blo 417772 800435 := bstep (se 1 (by rfl) ⟨600326, by rfl⟩ : syracuseStep 800435 = 1200653) B1200653
theorem B1062679 : Blo 417772 1062679 := bstep (se 1 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 1062679 = 1594019) B1594019
theorem B472855 : Blo 417772 472855 := bstep (se 1 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 472855 = 709283) B709283
theorem B1423169 : Blo 417772 1423169 := bstep (se 2 (by rfl) ⟨533688, by rfl⟩ : syracuseStep 1423169 = 1067377) B1067377
theorem B2701187 : Blo 417772 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B604055 : Blo 417772 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B3094451 : Blo 417772 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B2144179 : Blo 417772 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B473035 : Blo 417772 473035 := bstep (se 1 (by rfl) ⟨354776, by rfl⟩ : syracuseStep 473035 = 709553) B709553
theorem B473143 : Blo 417772 473143 := bstep (se 1 (by rfl) ⟨354857, by rfl⟩ : syracuseStep 473143 = 709715) B709715
theorem B1063115 : Blo 417772 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B473323 : Blo 417772 473323 := bstep (se 1 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 473323 = 709985) B709985
theorem B899353 : Blo 417772 899353 := bstep (se 2 (by rfl) ⟨337257, by rfl⟩ : syracuseStep 899353 = 674515) B674515
theorem B473431 : Blo 417772 473431 := bstep (se 1 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 473431 = 710147) B710147
theorem B899507 : Blo 417772 899507 := bstep (se 1 (by rfl) ⟨674630, by rfl⟩ : syracuseStep 899507 = 1349261) B1349261
theorem B473611 : Blo 417772 473611 := bstep (se 1 (by rfl) ⟨355208, by rfl⟩ : syracuseStep 473611 = 710417) B710417
theorem B3389987 : Blo 417772 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B1194547 : Blo 417772 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1063489 : Blo 417772 1063489 := bstep (se 2 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 1063489 = 797617) B797617
theorem B473719 : Blo 417772 473719 := bstep (se 1 (by rfl) ⟨355289, by rfl⟩ : syracuseStep 473719 = 710579) B710579
theorem B473899 : Blo 417772 473899 := bstep (se 1 (by rfl) ⟨355424, by rfl⟩ : syracuseStep 473899 = 710849) B710849
theorem B474007 : Blo 417772 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B900019 : Blo 417772 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B4045859 : Blo 417772 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B474187 : Blo 417772 474187 := bstep (se 1 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 474187 = 711281) B711281
theorem B1588355 : Blo 417772 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B1588369 : Blo 417772 1588369 := bstep (se 2 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 1588369 = 1191277) B1191277
theorem B5717143 : Blo 417772 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B1064087 : Blo 417772 1064087 := bstep (se 1 (by rfl) ⟨798065, by rfl⟩ : syracuseStep 1064087 = 1596131) B1596131
theorem B474295 : Blo 417772 474295 := bstep (se 1 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 474295 = 711443) B711443
theorem B474475 : Blo 417772 474475 := bstep (se 1 (by rfl) ⟨355856, by rfl⟩ : syracuseStep 474475 = 711713) B711713
theorem B1588673 : Blo 417772 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B900695 : Blo 417772 900695 := bstep (se 1 (by rfl) ⟨675521, by rfl⟩ : syracuseStep 900695 = 1351043) B1351043
theorem B900737 : Blo 417772 900737 := bstep (se 2 (by rfl) ⟨337776, by rfl⟩ : syracuseStep 900737 = 675553) B675553
theorem B1130201 : Blo 417772 1130201 := bstep (se 2 (by rfl) ⟨423825, by rfl⟩ : syracuseStep 1130201 = 847651) B847651
theorem B3063703 : Blo 417772 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B1064897 : Blo 417772 1064897 := bstep (se 2 (by rfl) ⟨399336, by rfl⟩ : syracuseStep 1064897 = 798673) B798673
theorem B22986827 : Blo 417772 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B671831 : Blo 417772 671831 := bstep (se 1 (by rfl) ⟨503873, by rfl⟩ : syracuseStep 671831 = 1007747) B1007747
theorem B1818713 : Blo 417772 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1589341 : Blo 417772 1589341 := bstep (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) B596003
theorem B1917101 : Blo 417772 1917101 := bstep (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) B718913
theorem B1065433 : Blo 417772 1065433 := bstep (se 2 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 1065433 = 799075) B799075
theorem B3031627 : Blo 417772 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B3621763 : Blo 417772 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B705611 : Blo 417772 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B705739 : Blo 417772 705739 := bstep (se 1 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 705739 = 1058609) B1058609
theorem B9684269 : Blo 417772 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B705881 : Blo 417772 705881 := bstep (se 2 (by rfl) ⟨264705, by rfl⟩ : syracuseStep 705881 = 529411) B529411
theorem B1590617 : Blo 417772 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B1197463 : Blo 417772 1197463 := bstep (se 1 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 1197463 = 1796195) B1796195
theorem B706009 : Blo 417772 706009 := bstep (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) B529507
theorem B3196421 : Blo 417772 3196421 := bstep (se 4 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 3196421 = 599329) B599329
theorem B1066547 : Blo 417772 1066547 := bstep (se 1 (by rfl) ⟨799910, by rfl⟩ : syracuseStep 1066547 = 1599821) B1599821
theorem B1066841 : Blo 417772 1066841 := bstep (se 2 (by rfl) ⟨400065, by rfl⟩ : syracuseStep 1066841 = 800131) B800131
theorem B2279299 : Blo 417772 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1132505 : Blo 417772 1132505 := bstep (se 2 (by rfl) ⟨424689, by rfl⟩ : syracuseStep 1132505 = 849379) B849379
theorem B1558493 : Blo 417772 1558493 := bstep (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) B584435
theorem B706583 : Blo 417772 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B706711 : Blo 417772 706711 := bstep (se 1 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 706711 = 1060067) B1060067
theorem B10799405 : Blo 417772 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B1788419 : Blo 417772 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B3066443 : Blo 417772 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B7195229 : Blo 417772 7195229 := bstep (se 3 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 7195229 = 2698211) B2698211
theorem B1198795 : Blo 417772 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B2018009 : Blo 417772 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B707339 : Blo 417772 707339 := bstep (se 1 (by rfl) ⟨530504, by rfl⟩ : syracuseStep 707339 = 1061009) B1061009
theorem B2018123 : Blo 417772 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B1919875 : Blo 417772 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B707467 : Blo 417772 707467 := bstep (se 1 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 707467 = 1061201) B1061201
theorem B1592243 : Blo 417772 1592243 := bstep (se 1 (by rfl) ⟨1194182, by rfl⟩ : syracuseStep 1592243 = 2388365) B2388365
theorem B1592257 : Blo 417772 1592257 := bstep (se 2 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 1592257 = 1194193) B1194193
theorem B1199069 : Blo 417772 1199069 := bstep (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) B449651
theorem B707609 : Blo 417772 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B707737 : Blo 417772 707737 := bstep (se 2 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 707737 = 530803) B530803
theorem B1133747 : Blo 417772 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B1199411 : Blo 417772 1199411 := bstep (se 1 (by rfl) ⟨899558, by rfl⟩ : syracuseStep 1199411 = 1799117) B1799117
theorem B2117015 : Blo 417772 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B2379365 : Blo 417772 2379365 := bstep (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) B446131
theorem B708311 : Blo 417772 708311 := bstep (se 1 (by rfl) ⟨531233, by rfl⟩ : syracuseStep 708311 = 1062467) B1062467
theorem B708439 : Blo 417772 708439 := bstep (se 1 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 708439 = 1062659) B1062659
theorem B446315 : Blo 417772 446315 := bstep (se 1 (by rfl) ⟨334736, by rfl⟩ : syracuseStep 446315 = 669473) B669473
theorem B3198851 : Blo 417772 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B806807 : Blo 417772 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B1790045 : Blo 417772 1790045 := bstep (se 3 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 1790045 = 671267) B671267
theorem B2380049 : Blo 417772 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B709067 : Blo 417772 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B3035693 : Blo 417772 3035693 := bstep (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) B1138385
theorem B709195 : Blo 417772 709195 := bstep (se 1 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 709195 = 1063793) B1063793
theorem B807641 : Blo 417772 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B709337 : Blo 417772 709337 := bstep (se 2 (by rfl) ⟨266001, by rfl⟩ : syracuseStep 709337 = 532003) B532003
theorem B1790743 : Blo 417772 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B1594187 : Blo 417772 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B447319 : Blo 417772 447319 := bstep (se 1 (by rfl) ⟨335489, by rfl⟩ : syracuseStep 447319 = 670979) B670979
theorem B1594201 : Blo 417772 1594201 := bstep (se 2 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 1594201 = 1195651) B1195651
theorem B709465 : Blo 417772 709465 := bstep (se 2 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 709465 = 532099) B532099
theorem B710039 : Blo 417772 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B3823109 : Blo 417772 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B710167 : Blo 417772 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B448139 : Blo 417772 448139 := bstep (se 1 (by rfl) ⟨336104, by rfl⟩ : syracuseStep 448139 = 672209) B672209
theorem B906967 : Blo 417772 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B1595159 : Blo 417772 1595159 := bstep (se 1 (by rfl) ⟨1196369, by rfl⟩ : syracuseStep 1595159 = 2392739) B2392739
theorem B940121 : Blo 417772 940121 := bstep (se 2 (by rfl) ⟨352545, by rfl⟩ : syracuseStep 940121 = 705091) B705091
theorem B2021507 : Blo 417772 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B546955 : Blo 417772 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B710795 : Blo 417772 710795 := bstep (se 1 (by rfl) ⟨533096, by rfl⟩ : syracuseStep 710795 = 1066193) B1066193
theorem B1792145 : Blo 417772 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B940211 : Blo 417772 940211 := bstep (se 1 (by rfl) ⟨705158, by rfl⟩ : syracuseStep 940211 = 1410317) B1410317
theorem B940247 : Blo 417772 940247 := bstep (se 1 (by rfl) ⟨705185, by rfl⟩ : syracuseStep 940247 = 1410371) B1410371
theorem B710923 : Blo 417772 710923 := bstep (se 1 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 710923 = 1066385) B1066385
theorem B2578781 : Blo 417772 2578781 := bstep (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) B967043
theorem B940427 : Blo 417772 940427 := bstep (se 1 (by rfl) ⟨705320, by rfl⟩ : syracuseStep 940427 = 1410641) B1410641
theorem B711065 : Blo 417772 711065 := bstep (se 2 (by rfl) ⟨266649, by rfl⟩ : syracuseStep 711065 = 533299) B533299
theorem B940481 : Blo 417772 940481 := bstep (se 2 (by rfl) ⟨352680, by rfl⟩ : syracuseStep 940481 = 705361) B705361
theorem B711193 : Blo 417772 711193 := bstep (se 2 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 711193 = 533395) B533395
theorem B3824279 : Blo 417772 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B940697 : Blo 417772 940697 := bstep (se 2 (by rfl) ⟨352761, by rfl⟩ : syracuseStep 940697 = 705523) B705523
theorem B940787 : Blo 417772 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B940823 : Blo 417772 940823 := bstep (se 1 (by rfl) ⟨705617, by rfl⟩ : syracuseStep 940823 = 1411235) B1411235
theorem B449335 : Blo 417772 449335 := bstep (se 1 (by rfl) ⟨337001, by rfl⟩ : syracuseStep 449335 = 674003) B674003
theorem B6970211 : Blo 417772 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B2120579 : Blo 417772 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B1727411 : Blo 417772 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B941003 : Blo 417772 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B941057 : Blo 417772 941057 := bstep (se 2 (by rfl) ⟨352896, by rfl⟩ : syracuseStep 941057 = 705793) B705793
theorem B1596419 : Blo 417772 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B7625933 : Blo 417772 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B3202253 : Blo 417772 3202253 := bstep (se 3 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 3202253 = 1200845) B1200845
theorem B941273 : Blo 417772 941273 := bstep (se 2 (by rfl) ⟨352977, by rfl⟩ : syracuseStep 941273 = 705955) B705955
theorem B941363 : Blo 417772 941363 := bstep (se 1 (by rfl) ⟨706022, by rfl⟩ : syracuseStep 941363 = 1412045) B1412045
theorem B941399 : Blo 417772 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B2383283 : Blo 417772 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B941579 : Blo 417772 941579 := bstep (se 1 (by rfl) ⟨706184, by rfl⟩ : syracuseStep 941579 = 1412369) B1412369
theorem B941633 : Blo 417772 941633 := bstep (se 2 (by rfl) ⟨353112, by rfl⟩ : syracuseStep 941633 = 706225) B706225
theorem B450155 : Blo 417772 450155 := bstep (se 1 (by rfl) ⟨337616, by rfl⟩ : syracuseStep 450155 = 675233) B675233
theorem B3202739 : Blo 417772 3202739 := bstep (se 1 (by rfl) ⟨2402054, by rfl⟩ : syracuseStep 3202739 = 4804109) B4804109
theorem B3464909 : Blo 417772 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B450283 : Blo 417772 450283 := bstep (se 1 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 450283 = 675425) B675425
theorem B941849 : Blo 417772 941849 := bstep (se 2 (by rfl) ⟨353193, by rfl⟩ : syracuseStep 941849 = 706387) B706387
theorem B3825443 : Blo 417772 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B941939 : Blo 417772 941939 := bstep (se 1 (by rfl) ⟨706454, by rfl⟩ : syracuseStep 941939 = 1412909) B1412909
theorem B941975 : Blo 417772 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B417783 : Blo 417772 417783 := bstep (se 1 (by rfl) ⟨313337, by rfl⟩ : syracuseStep 417783 = 626675) B626675
theorem B417803 : Blo 417772 417803 := bstep (se 1 (by rfl) ⟨313352, by rfl⟩ : syracuseStep 417803 = 626705) B626705
theorem B417815 : Blo 417772 417815 := bstep (se 1 (by rfl) ⟨313361, by rfl⟩ : syracuseStep 417815 = 626723) B626723
theorem B417835 : Blo 417772 417835 := bstep (se 1 (by rfl) ⟨313376, by rfl⟩ : syracuseStep 417835 = 626753) B626753
theorem B417847 : Blo 417772 417847 := bstep (se 1 (by rfl) ⟨313385, by rfl⟩ : syracuseStep 417847 = 626771) B626771
theorem B417867 : Blo 417772 417867 := bstep (se 1 (by rfl) ⟨313400, by rfl⟩ : syracuseStep 417867 = 626801) B626801
theorem B942155 : Blo 417772 942155 := bstep (se 1 (by rfl) ⟨706616, by rfl⟩ : syracuseStep 942155 = 1413233) B1413233
theorem B417879 : Blo 417772 417879 := bstep (se 1 (by rfl) ⟨313409, by rfl⟩ : syracuseStep 417879 = 626819) B626819
theorem B417899 : Blo 417772 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B417911 : Blo 417772 417911 := bstep (se 1 (by rfl) ⟨313433, by rfl⟩ : syracuseStep 417911 = 626867) B626867
theorem B942209 : Blo 417772 942209 := bstep (se 2 (by rfl) ⟨353328, by rfl⟩ : syracuseStep 942209 = 706657) B706657
theorem B417931 : Blo 417772 417931 := bstep (se 1 (by rfl) ⟨313448, by rfl⟩ : syracuseStep 417931 = 626897) B626897
theorem B417943 : Blo 417772 417943 := bstep (se 1 (by rfl) ⟨313457, by rfl⟩ : syracuseStep 417943 = 626915) B626915
theorem B3039383 : Blo 417772 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B417963 : Blo 417772 417963 := bstep (se 1 (by rfl) ⟨313472, by rfl⟩ : syracuseStep 417963 = 626945) B626945
theorem B1695917 : Blo 417772 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B417975 : Blo 417772 417975 := bstep (se 1 (by rfl) ⟨313481, by rfl⟩ : syracuseStep 417975 = 626963) B626963
theorem B417995 : Blo 417772 417995 := bstep (se 1 (by rfl) ⟨313496, by rfl⟩ : syracuseStep 417995 = 626993) B626993
theorem B418007 : Blo 417772 418007 := bstep (se 1 (by rfl) ⟨313505, by rfl⟩ : syracuseStep 418007 = 627011) B627011
theorem B418027 : Blo 417772 418027 := bstep (se 1 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 418027 = 627041) B627041
theorem B418039 : Blo 417772 418039 := bstep (se 1 (by rfl) ⟨313529, by rfl⟩ : syracuseStep 418039 = 627059) B627059
theorem B418059 : Blo 417772 418059 := bstep (se 1 (by rfl) ⟨313544, by rfl⟩ : syracuseStep 418059 = 627089) B627089
theorem B418071 : Blo 417772 418071 := bstep (se 1 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 418071 = 627107) B627107
theorem B418091 : Blo 417772 418091 := bstep (se 1 (by rfl) ⟨313568, by rfl⟩ : syracuseStep 418091 = 627137) B627137
theorem B418103 : Blo 417772 418103 := bstep (se 1 (by rfl) ⟨313577, by rfl⟩ : syracuseStep 418103 = 627155) B627155
theorem B418123 : Blo 417772 418123 := bstep (se 1 (by rfl) ⟨313592, by rfl⟩ : syracuseStep 418123 = 627185) B627185
theorem B418135 : Blo 417772 418135 := bstep (se 1 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 418135 = 627203) B627203
theorem B942425 : Blo 417772 942425 := bstep (se 2 (by rfl) ⟨353409, by rfl⟩ : syracuseStep 942425 = 706819) B706819
theorem B418155 : Blo 417772 418155 := bstep (se 1 (by rfl) ⟨313616, by rfl⟩ : syracuseStep 418155 = 627233) B627233
theorem B418167 : Blo 417772 418167 := bstep (se 1 (by rfl) ⟨313625, by rfl⟩ : syracuseStep 418167 = 627251) B627251
theorem B418187 : Blo 417772 418187 := bstep (se 1 (by rfl) ⟨313640, by rfl⟩ : syracuseStep 418187 = 627281) B627281
theorem B418199 : Blo 417772 418199 := bstep (se 1 (by rfl) ⟨313649, by rfl⟩ : syracuseStep 418199 = 627299) B627299
theorem B418219 : Blo 417772 418219 := bstep (se 1 (by rfl) ⟨313664, by rfl⟩ : syracuseStep 418219 = 627329) B627329
theorem B942515 : Blo 417772 942515 := bstep (se 1 (by rfl) ⟨706886, by rfl⟩ : syracuseStep 942515 = 1413773) B1413773
theorem B418231 : Blo 417772 418231 := bstep (se 1 (by rfl) ⟨313673, by rfl⟩ : syracuseStep 418231 = 627347) B627347
theorem B418251 : Blo 417772 418251 := bstep (se 1 (by rfl) ⟨313688, by rfl⟩ : syracuseStep 418251 = 627377) B627377
theorem B418263 : Blo 417772 418263 := bstep (se 1 (by rfl) ⟨313697, by rfl⟩ : syracuseStep 418263 = 627395) B627395
theorem B942551 : Blo 417772 942551 := bstep (se 1 (by rfl) ⟨706913, by rfl⟩ : syracuseStep 942551 = 1413827) B1413827
theorem B418283 : Blo 417772 418283 := bstep (se 1 (by rfl) ⟨313712, by rfl⟩ : syracuseStep 418283 = 627425) B627425
theorem B418295 : Blo 417772 418295 := bstep (se 1 (by rfl) ⟨313721, by rfl⟩ : syracuseStep 418295 = 627443) B627443
theorem B418315 : Blo 417772 418315 := bstep (se 1 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 418315 = 627473) B627473
theorem B418327 : Blo 417772 418327 := bstep (se 1 (by rfl) ⟨313745, by rfl⟩ : syracuseStep 418327 = 627491) B627491
theorem B418347 : Blo 417772 418347 := bstep (se 1 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 418347 = 627521) B627521
theorem B418359 : Blo 417772 418359 := bstep (se 1 (by rfl) ⟨313769, by rfl⟩ : syracuseStep 418359 = 627539) B627539
theorem B418379 : Blo 417772 418379 := bstep (se 1 (by rfl) ⟨313784, by rfl⟩ : syracuseStep 418379 = 627569) B627569
theorem B418391 : Blo 417772 418391 := bstep (se 1 (by rfl) ⟨313793, by rfl⟩ : syracuseStep 418391 = 627587) B627587
theorem B418411 : Blo 417772 418411 := bstep (se 1 (by rfl) ⟨313808, by rfl⟩ : syracuseStep 418411 = 627617) B627617
theorem B418423 : Blo 417772 418423 := bstep (se 1 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 418423 = 627635) B627635
theorem B418443 : Blo 417772 418443 := bstep (se 1 (by rfl) ⟨313832, by rfl⟩ : syracuseStep 418443 = 627665) B627665
theorem B942731 : Blo 417772 942731 := bstep (se 1 (by rfl) ⟨707048, by rfl⟩ : syracuseStep 942731 = 1414097) B1414097
theorem B418455 : Blo 417772 418455 := bstep (se 1 (by rfl) ⟨313841, by rfl⟩ : syracuseStep 418455 = 627683) B627683
theorem B418475 : Blo 417772 418475 := bstep (se 1 (by rfl) ⟨313856, by rfl⟩ : syracuseStep 418475 = 627713) B627713
theorem B418487 : Blo 417772 418487 := bstep (se 1 (by rfl) ⟨313865, by rfl⟩ : syracuseStep 418487 = 627731) B627731
theorem B942785 : Blo 417772 942785 := bstep (se 2 (by rfl) ⟨353544, by rfl⟩ : syracuseStep 942785 = 707089) B707089
theorem B418507 : Blo 417772 418507 := bstep (se 1 (by rfl) ⟨313880, by rfl⟩ : syracuseStep 418507 = 627761) B627761
theorem B418519 : Blo 417772 418519 := bstep (se 1 (by rfl) ⟨313889, by rfl⟩ : syracuseStep 418519 = 627779) B627779
theorem B418539 : Blo 417772 418539 := bstep (se 1 (by rfl) ⟨313904, by rfl⟩ : syracuseStep 418539 = 627809) B627809
theorem B418551 : Blo 417772 418551 := bstep (se 1 (by rfl) ⟨313913, by rfl⟩ : syracuseStep 418551 = 627827) B627827
theorem B418571 : Blo 417772 418571 := bstep (se 1 (by rfl) ⟨313928, by rfl⟩ : syracuseStep 418571 = 627857) B627857
theorem B418583 : Blo 417772 418583 := bstep (se 1 (by rfl) ⟨313937, by rfl⟩ : syracuseStep 418583 = 627875) B627875
theorem B418603 : Blo 417772 418603 := bstep (se 1 (by rfl) ⟨313952, by rfl⟩ : syracuseStep 418603 = 627905) B627905
theorem B418615 : Blo 417772 418615 := bstep (se 1 (by rfl) ⟨313961, by rfl⟩ : syracuseStep 418615 = 627923) B627923
theorem B1434433 : Blo 417772 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B418635 : Blo 417772 418635 := bstep (se 1 (by rfl) ⟨313976, by rfl⟩ : syracuseStep 418635 = 627953) B627953
theorem B418647 : Blo 417772 418647 := bstep (se 1 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 418647 = 627971) B627971
theorem B2384741 : Blo 417772 2384741 := bstep (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) B447139
theorem B418667 : Blo 417772 418667 := bstep (se 1 (by rfl) ⟨314000, by rfl⟩ : syracuseStep 418667 = 628001) B628001
theorem B418679 : Blo 417772 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B418699 : Blo 417772 418699 := bstep (se 1 (by rfl) ⟨314024, by rfl⟩ : syracuseStep 418699 = 628049) B628049
theorem B418711 : Blo 417772 418711 := bstep (se 1 (by rfl) ⟨314033, by rfl⟩ : syracuseStep 418711 = 628067) B628067
theorem B943001 : Blo 417772 943001 := bstep (se 2 (by rfl) ⟨353625, by rfl⟩ : syracuseStep 943001 = 707251) B707251
theorem B418731 : Blo 417772 418731 := bstep (se 1 (by rfl) ⟨314048, by rfl⟩ : syracuseStep 418731 = 628097) B628097
theorem B418743 : Blo 417772 418743 := bstep (se 1 (by rfl) ⟨314057, by rfl⟩ : syracuseStep 418743 = 628115) B628115
theorem B418763 : Blo 417772 418763 := bstep (se 1 (by rfl) ⟨314072, by rfl⟩ : syracuseStep 418763 = 628145) B628145
theorem B418775 : Blo 417772 418775 := bstep (se 1 (by rfl) ⟨314081, by rfl⟩ : syracuseStep 418775 = 628163) B628163
theorem B7168985 : Blo 417772 7168985 := bstep (se 2 (by rfl) ⟨2688369, by rfl⟩ : syracuseStep 7168985 = 5376739) B5376739
theorem B418795 : Blo 417772 418795 := bstep (se 1 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 418795 = 628193) B628193
theorem B943091 : Blo 417772 943091 := bstep (se 1 (by rfl) ⟨707318, by rfl⟩ : syracuseStep 943091 = 1414637) B1414637
theorem B418807 : Blo 417772 418807 := bstep (se 1 (by rfl) ⟨314105, by rfl⟩ : syracuseStep 418807 = 628211) B628211
theorem B418827 : Blo 417772 418827 := bstep (se 1 (by rfl) ⟨314120, by rfl⟩ : syracuseStep 418827 = 628241) B628241
theorem B418839 : Blo 417772 418839 := bstep (se 1 (by rfl) ⟨314129, by rfl⟩ : syracuseStep 418839 = 628259) B628259
theorem B943127 : Blo 417772 943127 := bstep (se 1 (by rfl) ⟨707345, by rfl⟩ : syracuseStep 943127 = 1414691) B1414691
theorem B418859 : Blo 417772 418859 := bstep (se 1 (by rfl) ⟨314144, by rfl⟩ : syracuseStep 418859 = 628289) B628289
theorem B1795117 : Blo 417772 1795117 := bstep (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) B673169
theorem B418871 : Blo 417772 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B418891 : Blo 417772 418891 := bstep (se 1 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 418891 = 628337) B628337
theorem B418903 : Blo 417772 418903 := bstep (se 1 (by rfl) ⟨314177, by rfl⟩ : syracuseStep 418903 = 628355) B628355
theorem B418923 : Blo 417772 418923 := bstep (se 1 (by rfl) ⟨314192, by rfl⟩ : syracuseStep 418923 = 628385) B628385
theorem B418935 : Blo 417772 418935 := bstep (se 1 (by rfl) ⟨314201, by rfl⟩ : syracuseStep 418935 = 628403) B628403
theorem B418955 : Blo 417772 418955 := bstep (se 1 (by rfl) ⟨314216, by rfl⟩ : syracuseStep 418955 = 628433) B628433
theorem B418967 : Blo 417772 418967 := bstep (se 1 (by rfl) ⟨314225, by rfl⟩ : syracuseStep 418967 = 628451) B628451
theorem B418987 : Blo 417772 418987 := bstep (se 1 (by rfl) ⟨314240, by rfl⟩ : syracuseStep 418987 = 628481) B628481
theorem B418999 : Blo 417772 418999 := bstep (se 1 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 418999 = 628499) B628499
theorem B419019 : Blo 417772 419019 := bstep (se 1 (by rfl) ⟨314264, by rfl⟩ : syracuseStep 419019 = 628529) B628529
theorem B943307 : Blo 417772 943307 := bstep (se 1 (by rfl) ⟨707480, by rfl⟩ : syracuseStep 943307 = 1414961) B1414961
theorem B419031 : Blo 417772 419031 := bstep (se 1 (by rfl) ⟨314273, by rfl⟩ : syracuseStep 419031 = 628547) B628547
theorem B419051 : Blo 417772 419051 := bstep (se 1 (by rfl) ⟨314288, by rfl⟩ : syracuseStep 419051 = 628577) B628577
theorem B419063 : Blo 417772 419063 := bstep (se 1 (by rfl) ⟨314297, by rfl⟩ : syracuseStep 419063 = 628595) B628595
theorem B943361 : Blo 417772 943361 := bstep (se 2 (by rfl) ⟨353760, by rfl⟩ : syracuseStep 943361 = 707521) B707521
theorem B419083 : Blo 417772 419083 := bstep (se 1 (by rfl) ⟨314312, by rfl⟩ : syracuseStep 419083 = 628625) B628625
theorem B419095 : Blo 417772 419095 := bstep (se 1 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 419095 = 628643) B628643
theorem B419115 : Blo 417772 419115 := bstep (se 1 (by rfl) ⟨314336, by rfl⟩ : syracuseStep 419115 = 628673) B628673
theorem B2385197 : Blo 417772 2385197 := bstep (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) B894449
theorem B419127 : Blo 417772 419127 := bstep (se 1 (by rfl) ⟨314345, by rfl⟩ : syracuseStep 419127 = 628691) B628691
theorem B419147 : Blo 417772 419147 := bstep (se 1 (by rfl) ⟨314360, by rfl⟩ : syracuseStep 419147 = 628721) B628721
theorem B419159 : Blo 417772 419159 := bstep (se 1 (by rfl) ⟨314369, by rfl⟩ : syracuseStep 419159 = 628739) B628739
theorem B419179 : Blo 417772 419179 := bstep (se 1 (by rfl) ⟨314384, by rfl⟩ : syracuseStep 419179 = 628769) B628769
theorem B419191 : Blo 417772 419191 := bstep (se 1 (by rfl) ⟨314393, by rfl⟩ : syracuseStep 419191 = 628787) B628787
theorem B1795459 : Blo 417772 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B419211 : Blo 417772 419211 := bstep (se 1 (by rfl) ⟨314408, by rfl⟩ : syracuseStep 419211 = 628817) B628817
theorem B419223 : Blo 417772 419223 := bstep (se 1 (by rfl) ⟨314417, by rfl⟩ : syracuseStep 419223 = 628835) B628835
theorem B419243 : Blo 417772 419243 := bstep (se 1 (by rfl) ⟨314432, by rfl⟩ : syracuseStep 419243 = 628865) B628865
theorem B419255 : Blo 417772 419255 := bstep (se 1 (by rfl) ⟨314441, by rfl⟩ : syracuseStep 419255 = 628883) B628883
theorem B419275 : Blo 417772 419275 := bstep (se 1 (by rfl) ⟨314456, by rfl⟩ : syracuseStep 419275 = 628913) B628913
theorem B419287 : Blo 417772 419287 := bstep (se 1 (by rfl) ⟨314465, by rfl⟩ : syracuseStep 419287 = 628931) B628931
theorem B943577 : Blo 417772 943577 := bstep (se 2 (by rfl) ⟨353841, by rfl⟩ : syracuseStep 943577 = 707683) B707683
theorem B419307 : Blo 417772 419307 := bstep (se 1 (by rfl) ⟨314480, by rfl⟩ : syracuseStep 419307 = 628961) B628961
theorem B419319 : Blo 417772 419319 := bstep (se 1 (by rfl) ⟨314489, by rfl⟩ : syracuseStep 419319 = 628979) B628979
theorem B419339 : Blo 417772 419339 := bstep (se 1 (by rfl) ⟨314504, by rfl⟩ : syracuseStep 419339 = 629009) B629009
theorem B419351 : Blo 417772 419351 := bstep (se 1 (by rfl) ⟨314513, by rfl⟩ : syracuseStep 419351 = 629027) B629027
theorem B419371 : Blo 417772 419371 := bstep (se 1 (by rfl) ⟨314528, by rfl⟩ : syracuseStep 419371 = 629057) B629057
theorem B943667 : Blo 417772 943667 := bstep (se 1 (by rfl) ⟨707750, by rfl⟩ : syracuseStep 943667 = 1415501) B1415501
theorem B419383 : Blo 417772 419383 := bstep (se 1 (by rfl) ⟨314537, by rfl⟩ : syracuseStep 419383 = 629075) B629075
theorem B1697345 : Blo 417772 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B419403 : Blo 417772 419403 := bstep (se 1 (by rfl) ⟨314552, by rfl⟩ : syracuseStep 419403 = 629105) B629105
theorem B419415 : Blo 417772 419415 := bstep (se 1 (by rfl) ⟨314561, by rfl⟩ : syracuseStep 419415 = 629123) B629123
theorem B943703 : Blo 417772 943703 := bstep (se 1 (by rfl) ⟨707777, by rfl⟩ : syracuseStep 943703 = 1415555) B1415555
theorem B419435 : Blo 417772 419435 := bstep (se 1 (by rfl) ⟨314576, by rfl⟩ : syracuseStep 419435 = 629153) B629153
theorem B419447 : Blo 417772 419447 := bstep (se 1 (by rfl) ⟨314585, by rfl⟩ : syracuseStep 419447 = 629171) B629171
theorem B419467 : Blo 417772 419467 := bstep (se 1 (by rfl) ⟨314600, by rfl⟩ : syracuseStep 419467 = 629201) B629201
theorem B779915 : Blo 417772 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B419479 : Blo 417772 419479 := bstep (se 1 (by rfl) ⟨314609, by rfl⟩ : syracuseStep 419479 = 629219) B629219
theorem B1402519 : Blo 417772 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B419499 : Blo 417772 419499 := bstep (se 1 (by rfl) ⟨314624, by rfl⟩ : syracuseStep 419499 = 629249) B629249
theorem B419511 : Blo 417772 419511 := bstep (se 1 (by rfl) ⟨314633, by rfl⟩ : syracuseStep 419511 = 629267) B629267
theorem B419531 : Blo 417772 419531 := bstep (se 1 (by rfl) ⟨314648, by rfl⟩ : syracuseStep 419531 = 629297) B629297
theorem B419543 : Blo 417772 419543 := bstep (se 1 (by rfl) ⟨314657, by rfl⟩ : syracuseStep 419543 = 629315) B629315
theorem B1009369 : Blo 417772 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B419563 : Blo 417772 419563 := bstep (se 1 (by rfl) ⟨314672, by rfl⟩ : syracuseStep 419563 = 629345) B629345
theorem B419575 : Blo 417772 419575 := bstep (se 1 (by rfl) ⟨314681, by rfl⟩ : syracuseStep 419575 = 629363) B629363
theorem B943883 : Blo 417772 943883 := bstep (se 1 (by rfl) ⟨707912, by rfl⟩ : syracuseStep 943883 = 1415825) B1415825
theorem B419595 : Blo 417772 419595 := bstep (se 1 (by rfl) ⟨314696, by rfl⟩ : syracuseStep 419595 = 629393) B629393
theorem B419607 : Blo 417772 419607 := bstep (se 1 (by rfl) ⟨314705, by rfl⟩ : syracuseStep 419607 = 629411) B629411
theorem B419627 : Blo 417772 419627 := bstep (se 1 (by rfl) ⟨314720, by rfl⟩ : syracuseStep 419627 = 629441) B629441
theorem B419639 : Blo 417772 419639 := bstep (se 1 (by rfl) ⟨314729, by rfl⟩ : syracuseStep 419639 = 629459) B629459
theorem B943937 : Blo 417772 943937 := bstep (se 2 (by rfl) ⟨353976, by rfl⟩ : syracuseStep 943937 = 707953) B707953
theorem B419659 : Blo 417772 419659 := bstep (se 1 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 419659 = 629489) B629489
theorem B419671 : Blo 417772 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B419691 : Blo 417772 419691 := bstep (se 1 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 419691 = 629537) B629537
theorem B419703 : Blo 417772 419703 := bstep (se 1 (by rfl) ⟨314777, by rfl⟩ : syracuseStep 419703 = 629555) B629555
theorem B419723 : Blo 417772 419723 := bstep (se 1 (by rfl) ⟨314792, by rfl⟩ : syracuseStep 419723 = 629585) B629585
theorem B419735 : Blo 417772 419735 := bstep (se 1 (by rfl) ⟨314801, by rfl⟩ : syracuseStep 419735 = 629603) B629603
theorem B419755 : Blo 417772 419755 := bstep (se 1 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 419755 = 629633) B629633
theorem B21718961 : Blo 417772 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B419767 : Blo 417772 419767 := bstep (se 1 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 419767 = 629651) B629651
theorem B419787 : Blo 417772 419787 := bstep (se 1 (by rfl) ⟨314840, by rfl⟩ : syracuseStep 419787 = 629681) B629681
theorem B419799 : Blo 417772 419799 := bstep (se 1 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 419799 = 629699) B629699
theorem B2385881 : Blo 417772 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B419819 : Blo 417772 419819 := bstep (se 1 (by rfl) ⟨314864, by rfl⟩ : syracuseStep 419819 = 629729) B629729
theorem B419831 : Blo 417772 419831 := bstep (se 1 (by rfl) ⟨314873, by rfl⟩ : syracuseStep 419831 = 629747) B629747
theorem B419851 : Blo 417772 419851 := bstep (se 1 (by rfl) ⟨314888, by rfl⟩ : syracuseStep 419851 = 629777) B629777
theorem B419863 : Blo 417772 419863 := bstep (se 1 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 419863 = 629795) B629795
theorem B944153 : Blo 417772 944153 := bstep (se 2 (by rfl) ⟨354057, by rfl⟩ : syracuseStep 944153 = 708115) B708115
theorem B419883 : Blo 417772 419883 := bstep (se 1 (by rfl) ⟨314912, by rfl⟩ : syracuseStep 419883 = 629825) B629825
theorem B1599533 : Blo 417772 1599533 := bstep (se 3 (by rfl) ⟨299912, by rfl⟩ : syracuseStep 1599533 = 599825) B599825
theorem B419895 : Blo 417772 419895 := bstep (se 1 (by rfl) ⟨314921, by rfl⟩ : syracuseStep 419895 = 629843) B629843
theorem B419915 : Blo 417772 419915 := bstep (se 1 (by rfl) ⟨314936, by rfl⟩ : syracuseStep 419915 = 629873) B629873
theorem B419927 : Blo 417772 419927 := bstep (se 1 (by rfl) ⟨314945, by rfl⟩ : syracuseStep 419927 = 629891) B629891
theorem B419947 : Blo 417772 419947 := bstep (se 1 (by rfl) ⟨314960, by rfl⟩ : syracuseStep 419947 = 629921) B629921
theorem B944243 : Blo 417772 944243 := bstep (se 1 (by rfl) ⟨708182, by rfl⟩ : syracuseStep 944243 = 1416365) B1416365
theorem B419959 : Blo 417772 419959 := bstep (se 1 (by rfl) ⟨314969, by rfl⟩ : syracuseStep 419959 = 629939) B629939
theorem B419979 : Blo 417772 419979 := bstep (se 1 (by rfl) ⟨314984, by rfl⟩ : syracuseStep 419979 = 629969) B629969
theorem B944279 : Blo 417772 944279 := bstep (se 1 (by rfl) ⟨708209, by rfl⟩ : syracuseStep 944279 = 1416419) B1416419
theorem B419991 : Blo 417772 419991 := bstep (se 1 (by rfl) ⟨314993, by rfl⟩ : syracuseStep 419991 = 629987) B629987
theorem B420011 : Blo 417772 420011 := bstep (se 1 (by rfl) ⟨315008, by rfl⟩ : syracuseStep 420011 = 630017) B630017
theorem B1271987 : Blo 417772 1271987 := bstep (se 1 (by rfl) ⟨953990, by rfl⟩ : syracuseStep 1271987 = 1907981) B1907981
theorem B420023 : Blo 417772 420023 := bstep (se 1 (by rfl) ⟨315017, by rfl⟩ : syracuseStep 420023 = 630035) B630035
theorem B420043 : Blo 417772 420043 := bstep (se 1 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 420043 = 630065) B630065
theorem B420055 : Blo 417772 420055 := bstep (se 1 (by rfl) ⟨315041, by rfl⟩ : syracuseStep 420055 = 630083) B630083
theorem B420075 : Blo 417772 420075 := bstep (se 1 (by rfl) ⟨315056, by rfl⟩ : syracuseStep 420075 = 630113) B630113
theorem B420087 : Blo 417772 420087 := bstep (se 1 (by rfl) ⟨315065, by rfl⟩ : syracuseStep 420087 = 630131) B630131
theorem B420107 : Blo 417772 420107 := bstep (se 1 (by rfl) ⟨315080, by rfl⟩ : syracuseStep 420107 = 630161) B630161
theorem B420119 : Blo 417772 420119 := bstep (se 1 (by rfl) ⟨315089, by rfl⟩ : syracuseStep 420119 = 630179) B630179
theorem B420139 : Blo 417772 420139 := bstep (se 1 (by rfl) ⟨315104, by rfl⟩ : syracuseStep 420139 = 630209) B630209
theorem B420151 : Blo 417772 420151 := bstep (se 1 (by rfl) ⟨315113, by rfl⟩ : syracuseStep 420151 = 630227) B630227
theorem B1796417 : Blo 417772 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B944459 : Blo 417772 944459 := bstep (se 1 (by rfl) ⟨708344, by rfl⟩ : syracuseStep 944459 = 1416689) B1416689
theorem B420171 : Blo 417772 420171 := bstep (se 1 (by rfl) ⟨315128, by rfl⟩ : syracuseStep 420171 = 630257) B630257
theorem B420183 : Blo 417772 420183 := bstep (se 1 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 420183 = 630275) B630275
theorem B420203 : Blo 417772 420203 := bstep (se 1 (by rfl) ⟨315152, by rfl⟩ : syracuseStep 420203 = 630305) B630305
theorem B420215 : Blo 417772 420215 := bstep (se 1 (by rfl) ⟨315161, by rfl⟩ : syracuseStep 420215 = 630323) B630323
theorem B944513 : Blo 417772 944513 := bstep (se 2 (by rfl) ⟨354192, by rfl⟩ : syracuseStep 944513 = 708385) B708385
theorem B420235 : Blo 417772 420235 := bstep (se 1 (by rfl) ⟨315176, by rfl⟩ : syracuseStep 420235 = 630353) B630353
theorem B420247 : Blo 417772 420247 := bstep (se 1 (by rfl) ⟨315185, by rfl⟩ : syracuseStep 420247 = 630371) B630371
theorem B420267 : Blo 417772 420267 := bstep (se 1 (by rfl) ⟨315200, by rfl⟩ : syracuseStep 420267 = 630401) B630401
theorem B420279 : Blo 417772 420279 := bstep (se 1 (by rfl) ⟨315209, by rfl⟩ : syracuseStep 420279 = 630419) B630419
theorem B1698251 : Blo 417772 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B420299 : Blo 417772 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B420311 : Blo 417772 420311 := bstep (se 1 (by rfl) ⟨315233, by rfl⟩ : syracuseStep 420311 = 630467) B630467
theorem B4549081 : Blo 417772 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B420331 : Blo 417772 420331 := bstep (se 1 (by rfl) ⟨315248, by rfl⟩ : syracuseStep 420331 = 630497) B630497
theorem B420343 : Blo 417772 420343 := bstep (se 1 (by rfl) ⟨315257, by rfl⟩ : syracuseStep 420343 = 630515) B630515
theorem B420363 : Blo 417772 420363 := bstep (se 1 (by rfl) ⟨315272, by rfl⟩ : syracuseStep 420363 = 630545) B630545
theorem B2124305 : Blo 417772 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B420375 : Blo 417772 420375 := bstep (se 1 (by rfl) ⟨315281, by rfl⟩ : syracuseStep 420375 = 630563) B630563
theorem B420395 : Blo 417772 420395 := bstep (se 1 (by rfl) ⟨315296, by rfl⟩ : syracuseStep 420395 = 630593) B630593
theorem B420407 : Blo 417772 420407 := bstep (se 1 (by rfl) ⟨315305, by rfl⟩ : syracuseStep 420407 = 630611) B630611
theorem B420427 : Blo 417772 420427 := bstep (se 1 (by rfl) ⟨315320, by rfl⟩ : syracuseStep 420427 = 630641) B630641
theorem B715351 : Blo 417772 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B420439 : Blo 417772 420439 := bstep (se 1 (by rfl) ⟨315329, by rfl⟩ : syracuseStep 420439 = 630659) B630659
theorem B944729 : Blo 417772 944729 := bstep (se 2 (by rfl) ⟨354273, by rfl⟩ : syracuseStep 944729 = 708547) B708547
theorem B420459 : Blo 417772 420459 := bstep (se 1 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 420459 = 630689) B630689
theorem B420471 : Blo 417772 420471 := bstep (se 1 (by rfl) ⟨315353, by rfl⟩ : syracuseStep 420471 = 630707) B630707
theorem B420491 : Blo 417772 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B420503 : Blo 417772 420503 := bstep (se 1 (by rfl) ⟨315377, by rfl⟩ : syracuseStep 420503 = 630755) B630755
theorem B420523 : Blo 417772 420523 := bstep (se 1 (by rfl) ⟨315392, by rfl⟩ : syracuseStep 420523 = 630785) B630785
theorem B2124467 : Blo 417772 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B944819 : Blo 417772 944819 := bstep (se 1 (by rfl) ⟨708614, by rfl⟩ : syracuseStep 944819 = 1417229) B1417229
theorem B420535 : Blo 417772 420535 := bstep (se 1 (by rfl) ⟨315401, by rfl⟩ : syracuseStep 420535 = 630803) B630803
theorem B1010369 : Blo 417772 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B420555 : Blo 417772 420555 := bstep (se 1 (by rfl) ⟨315416, by rfl⟩ : syracuseStep 420555 = 630833) B630833
theorem B944855 : Blo 417772 944855 := bstep (se 1 (by rfl) ⟨708641, by rfl⟩ : syracuseStep 944855 = 1417283) B1417283
theorem B420567 : Blo 417772 420567 := bstep (se 1 (by rfl) ⟨315425, by rfl⟩ : syracuseStep 420567 = 630851) B630851
theorem B420587 : Blo 417772 420587 := bstep (se 1 (by rfl) ⟨315440, by rfl⟩ : syracuseStep 420587 = 630881) B630881
theorem B420599 : Blo 417772 420599 := bstep (se 1 (by rfl) ⟨315449, by rfl⟩ : syracuseStep 420599 = 630899) B630899
theorem B420619 : Blo 417772 420619 := bstep (se 1 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 420619 = 630929) B630929
theorem B420631 : Blo 417772 420631 := bstep (se 1 (by rfl) ⟨315473, by rfl⟩ : syracuseStep 420631 = 630947) B630947
theorem B420651 : Blo 417772 420651 := bstep (se 1 (by rfl) ⟨315488, by rfl⟩ : syracuseStep 420651 = 630977) B630977
theorem B1600307 : Blo 417772 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B420663 : Blo 417772 420663 := bstep (se 1 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 420663 = 630995) B630995
theorem B420683 : Blo 417772 420683 := bstep (se 1 (by rfl) ⟨315512, by rfl⟩ : syracuseStep 420683 = 631025) B631025
theorem B420695 : Blo 417772 420695 := bstep (se 1 (by rfl) ⟨315521, by rfl⟩ : syracuseStep 420695 = 631043) B631043
theorem B420715 : Blo 417772 420715 := bstep (se 1 (by rfl) ⟨315536, by rfl⟩ : syracuseStep 420715 = 631073) B631073
theorem B420727 : Blo 417772 420727 := bstep (se 1 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 420727 = 631091) B631091
theorem B945035 : Blo 417772 945035 := bstep (se 1 (by rfl) ⟨708776, by rfl⟩ : syracuseStep 945035 = 1417553) B1417553
theorem B420747 : Blo 417772 420747 := bstep (se 1 (by rfl) ⟨315560, by rfl⟩ : syracuseStep 420747 = 631121) B631121
theorem B420759 : Blo 417772 420759 := bstep (se 1 (by rfl) ⟨315569, by rfl⟩ : syracuseStep 420759 = 631139) B631139
theorem B3599255 : Blo 417772 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B420779 : Blo 417772 420779 := bstep (se 1 (by rfl) ⟨315584, by rfl⟩ : syracuseStep 420779 = 631169) B631169
theorem B420791 : Blo 417772 420791 := bstep (se 1 (by rfl) ⟨315593, by rfl⟩ : syracuseStep 420791 = 631187) B631187
theorem B945089 : Blo 417772 945089 := bstep (se 2 (by rfl) ⟨354408, by rfl⟩ : syracuseStep 945089 = 708817) B708817
theorem B420811 : Blo 417772 420811 := bstep (se 1 (by rfl) ⟨315608, by rfl⟩ : syracuseStep 420811 = 631217) B631217
theorem B420823 : Blo 417772 420823 := bstep (se 1 (by rfl) ⟨315617, by rfl⟩ : syracuseStep 420823 = 631235) B631235
theorem B420843 : Blo 417772 420843 := bstep (se 1 (by rfl) ⟨315632, by rfl⟩ : syracuseStep 420843 = 631265) B631265
theorem B420855 : Blo 417772 420855 := bstep (se 1 (by rfl) ⟨315641, by rfl⟩ : syracuseStep 420855 = 631283) B631283
theorem B420875 : Blo 417772 420875 := bstep (se 1 (by rfl) ⟨315656, by rfl⟩ : syracuseStep 420875 = 631313) B631313
theorem B420887 : Blo 417772 420887 := bstep (se 1 (by rfl) ⟨315665, by rfl⟩ : syracuseStep 420887 = 631331) B631331
theorem B420907 : Blo 417772 420907 := bstep (se 1 (by rfl) ⟨315680, by rfl⟩ : syracuseStep 420907 = 631361) B631361
theorem B420919 : Blo 417772 420919 := bstep (se 1 (by rfl) ⟨315689, by rfl⟩ : syracuseStep 420919 = 631379) B631379
theorem B420939 : Blo 417772 420939 := bstep (se 1 (by rfl) ⟨315704, by rfl⟩ : syracuseStep 420939 = 631409) B631409
theorem B420951 : Blo 417772 420951 := bstep (se 1 (by rfl) ⟨315713, by rfl⟩ : syracuseStep 420951 = 631427) B631427
theorem B420971 : Blo 417772 420971 := bstep (se 1 (by rfl) ⟨315728, by rfl⟩ : syracuseStep 420971 = 631457) B631457
theorem B420983 : Blo 417772 420983 := bstep (se 1 (by rfl) ⟨315737, by rfl⟩ : syracuseStep 420983 = 631475) B631475
theorem B421003 : Blo 417772 421003 := bstep (se 1 (by rfl) ⟨315752, by rfl⟩ : syracuseStep 421003 = 631505) B631505
theorem B421015 : Blo 417772 421015 := bstep (se 1 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 421015 = 631523) B631523
theorem B945305 : Blo 417772 945305 := bstep (se 2 (by rfl) ⟨354489, by rfl⟩ : syracuseStep 945305 = 708979) B708979
theorem B421035 : Blo 417772 421035 := bstep (se 1 (by rfl) ⟨315776, by rfl⟩ : syracuseStep 421035 = 631553) B631553
theorem B1338547 : Blo 417772 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B421047 : Blo 417772 421047 := bstep (se 1 (by rfl) ⟨315785, by rfl⟩ : syracuseStep 421047 = 631571) B631571
theorem B421067 : Blo 417772 421067 := bstep (se 1 (by rfl) ⟨315800, by rfl⟩ : syracuseStep 421067 = 631601) B631601
theorem B421079 : Blo 417772 421079 := bstep (se 1 (by rfl) ⟨315809, by rfl⟩ : syracuseStep 421079 = 631619) B631619
theorem B421099 : Blo 417772 421099 := bstep (se 1 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 421099 = 631649) B631649
theorem B945395 : Blo 417772 945395 := bstep (se 1 (by rfl) ⟨709046, by rfl⟩ : syracuseStep 945395 = 1418093) B1418093
theorem B421111 : Blo 417772 421111 := bstep (se 1 (by rfl) ⟨315833, by rfl⟩ : syracuseStep 421111 = 631667) B631667
theorem B421131 : Blo 417772 421131 := bstep (se 1 (by rfl) ⟨315848, by rfl⟩ : syracuseStep 421131 = 631697) B631697
theorem B945431 : Blo 417772 945431 := bstep (se 1 (by rfl) ⟨709073, by rfl⟩ : syracuseStep 945431 = 1418147) B1418147
theorem B421143 : Blo 417772 421143 := bstep (se 1 (by rfl) ⟨315857, by rfl⟩ : syracuseStep 421143 = 631715) B631715
theorem B421163 : Blo 417772 421163 := bstep (se 1 (by rfl) ⟨315872, by rfl⟩ : syracuseStep 421163 = 631745) B631745
theorem B421175 : Blo 417772 421175 := bstep (se 1 (by rfl) ⟨315881, by rfl⟩ : syracuseStep 421175 = 631763) B631763
theorem B421195 : Blo 417772 421195 := bstep (se 1 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 421195 = 631793) B631793
theorem B421207 : Blo 417772 421207 := bstep (se 1 (by rfl) ⟨315905, by rfl⟩ : syracuseStep 421207 = 631811) B631811
theorem B421227 : Blo 417772 421227 := bstep (se 1 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 421227 = 631841) B631841
theorem B421239 : Blo 417772 421239 := bstep (se 1 (by rfl) ⟨315929, by rfl⟩ : syracuseStep 421239 = 631859) B631859
theorem B421259 : Blo 417772 421259 := bstep (se 1 (by rfl) ⟨315944, by rfl⟩ : syracuseStep 421259 = 631889) B631889
theorem B421271 : Blo 417772 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B421291 : Blo 417772 421291 := bstep (se 1 (by rfl) ⟨315968, by rfl⟩ : syracuseStep 421291 = 631937) B631937
theorem B421303 : Blo 417772 421303 := bstep (se 1 (by rfl) ⟨315977, by rfl⟩ : syracuseStep 421303 = 631955) B631955
theorem B945611 : Blo 417772 945611 := bstep (se 1 (by rfl) ⟨709208, by rfl⟩ : syracuseStep 945611 = 1418417) B1418417
theorem B421323 : Blo 417772 421323 := bstep (se 1 (by rfl) ⟨315992, by rfl⟩ : syracuseStep 421323 = 631985) B631985
theorem B421335 : Blo 417772 421335 := bstep (se 1 (by rfl) ⟨316001, by rfl⟩ : syracuseStep 421335 = 632003) B632003
theorem B421355 : Blo 417772 421355 := bstep (se 1 (by rfl) ⟨316016, by rfl⟩ : syracuseStep 421355 = 632033) B632033
theorem B421367 : Blo 417772 421367 := bstep (se 1 (by rfl) ⟨316025, by rfl⟩ : syracuseStep 421367 = 632051) B632051
theorem B945665 : Blo 417772 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B421387 : Blo 417772 421387 := bstep (se 1 (by rfl) ⟨316040, by rfl⟩ : syracuseStep 421387 = 632081) B632081
theorem B421399 : Blo 417772 421399 := bstep (se 1 (by rfl) ⟨316049, by rfl⟩ : syracuseStep 421399 = 632099) B632099
theorem B421419 : Blo 417772 421419 := bstep (se 1 (by rfl) ⟨316064, by rfl⟩ : syracuseStep 421419 = 632129) B632129
theorem B421431 : Blo 417772 421431 := bstep (se 1 (by rfl) ⟨316073, by rfl⟩ : syracuseStep 421431 = 632147) B632147
theorem B421451 : Blo 417772 421451 := bstep (se 1 (by rfl) ⟨316088, by rfl⟩ : syracuseStep 421451 = 632177) B632177
theorem B421463 : Blo 417772 421463 := bstep (se 1 (by rfl) ⟨316097, by rfl⟩ : syracuseStep 421463 = 632195) B632195
theorem B421483 : Blo 417772 421483 := bstep (se 1 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 421483 = 632225) B632225
theorem B421495 : Blo 417772 421495 := bstep (se 1 (by rfl) ⟨316121, by rfl⟩ : syracuseStep 421495 = 632243) B632243
theorem B421515 : Blo 417772 421515 := bstep (se 1 (by rfl) ⟨316136, by rfl⟩ : syracuseStep 421515 = 632273) B632273
theorem B1273495 : Blo 417772 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B421527 : Blo 417772 421527 := bstep (se 1 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 421527 = 632291) B632291
theorem B421547 : Blo 417772 421547 := bstep (se 1 (by rfl) ⟨316160, by rfl⟩ : syracuseStep 421547 = 632321) B632321
theorem B3174065 : Blo 417772 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B2879155 : Blo 417772 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B421559 : Blo 417772 421559 := bstep (se 1 (by rfl) ⟨316169, by rfl⟩ : syracuseStep 421559 = 632339) B632339
theorem B1797835 : Blo 417772 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B421579 : Blo 417772 421579 := bstep (se 1 (by rfl) ⟨316184, by rfl⟩ : syracuseStep 421579 = 632369) B632369
theorem B421591 : Blo 417772 421591 := bstep (se 1 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 421591 = 632387) B632387
theorem B945881 : Blo 417772 945881 := bstep (se 2 (by rfl) ⟨354705, by rfl⟩ : syracuseStep 945881 = 709411) B709411
theorem B421611 : Blo 417772 421611 := bstep (se 1 (by rfl) ⟨316208, by rfl⟩ : syracuseStep 421611 = 632417) B632417
theorem B421623 : Blo 417772 421623 := bstep (se 1 (by rfl) ⟨316217, by rfl⟩ : syracuseStep 421623 = 632435) B632435
theorem B421643 : Blo 417772 421643 := bstep (se 1 (by rfl) ⟨316232, by rfl⟩ : syracuseStep 421643 = 632465) B632465
theorem B421655 : Blo 417772 421655 := bstep (se 1 (by rfl) ⟨316241, by rfl⟩ : syracuseStep 421655 = 632483) B632483
theorem B421675 : Blo 417772 421675 := bstep (se 1 (by rfl) ⟨316256, by rfl⟩ : syracuseStep 421675 = 632513) B632513
theorem B945971 : Blo 417772 945971 := bstep (se 1 (by rfl) ⟨709478, by rfl⟩ : syracuseStep 945971 = 1418957) B1418957
theorem B421687 : Blo 417772 421687 := bstep (se 1 (by rfl) ⟨316265, by rfl⟩ : syracuseStep 421687 = 632531) B632531
theorem B421707 : Blo 417772 421707 := bstep (se 1 (by rfl) ⟨316280, by rfl⟩ : syracuseStep 421707 = 632561) B632561
theorem B946007 : Blo 417772 946007 := bstep (se 1 (by rfl) ⟨709505, by rfl⟩ : syracuseStep 946007 = 1419011) B1419011
theorem B421719 : Blo 417772 421719 := bstep (se 1 (by rfl) ⟨316289, by rfl⟩ : syracuseStep 421719 = 632579) B632579
theorem B421739 : Blo 417772 421739 := bstep (se 1 (by rfl) ⟨316304, by rfl⟩ : syracuseStep 421739 = 632609) B632609
theorem B421751 : Blo 417772 421751 := bstep (se 1 (by rfl) ⟨316313, by rfl⟩ : syracuseStep 421751 = 632627) B632627
theorem B421771 : Blo 417772 421771 := bstep (se 1 (by rfl) ⟨316328, by rfl⟩ : syracuseStep 421771 = 632657) B632657
theorem B1798109 : Blo 417772 1798109 := bstep (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) B674291
theorem B946187 : Blo 417772 946187 := bstep (se 1 (by rfl) ⟨709640, by rfl⟩ : syracuseStep 946187 = 1419281) B1419281
theorem B946241 : Blo 417772 946241 := bstep (se 2 (by rfl) ⟨354840, by rfl⟩ : syracuseStep 946241 = 709681) B709681
theorem B17789003 : Blo 417772 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B3174551 : Blo 417772 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B946457 : Blo 417772 946457 := bstep (se 2 (by rfl) ⟨354921, by rfl⟩ : syracuseStep 946457 = 709843) B709843
theorem B1536349 : Blo 417772 1536349 := bstep (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) B576131
theorem B946547 : Blo 417772 946547 := bstep (se 1 (by rfl) ⟨709910, by rfl⟩ : syracuseStep 946547 = 1419821) B1419821
theorem B946583 : Blo 417772 946583 := bstep (se 1 (by rfl) ⟨709937, by rfl⟩ : syracuseStep 946583 = 1419875) B1419875
theorem B2126411 : Blo 417772 2126411 := bstep (se 1 (by rfl) ⟨1594808, by rfl⟩ : syracuseStep 2126411 = 3189617) B3189617
theorem B946763 : Blo 417772 946763 := bstep (se 1 (by rfl) ⟨710072, by rfl⟩ : syracuseStep 946763 = 1420145) B1420145
theorem B946817 : Blo 417772 946817 := bstep (se 2 (by rfl) ⟨355056, by rfl⟩ : syracuseStep 946817 = 710113) B710113
theorem B3601169 : Blo 417772 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B947033 : Blo 417772 947033 := bstep (se 2 (by rfl) ⟨355137, by rfl⟩ : syracuseStep 947033 = 710275) B710275
theorem B947123 : Blo 417772 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B1307585 : Blo 417772 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B947159 : Blo 417772 947159 := bstep (se 1 (by rfl) ⟨710369, by rfl⟩ : syracuseStep 947159 = 1420739) B1420739
theorem B1340381 : Blo 417772 1340381 := bstep (se 3 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 1340381 = 502643) B502643
theorem B947339 : Blo 417772 947339 := bstep (se 1 (by rfl) ⟨710504, by rfl⟩ : syracuseStep 947339 = 1421009) B1421009
theorem B947393 : Blo 417772 947393 := bstep (se 2 (by rfl) ⟨355272, by rfl⟩ : syracuseStep 947393 = 710545) B710545
theorem B947609 : Blo 417772 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B947699 : Blo 417772 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B947735 : Blo 417772 947735 := bstep (se 1 (by rfl) ⟨710801, by rfl⟩ : syracuseStep 947735 = 1421603) B1421603
theorem B849547 : Blo 417772 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B947915 : Blo 417772 947915 := bstep (se 1 (by rfl) ⟨710936, by rfl⟩ : syracuseStep 947915 = 1421873) B1421873
theorem B947969 : Blo 417772 947969 := bstep (se 2 (by rfl) ⟨355488, by rfl⟩ : syracuseStep 947969 = 710977) B710977
theorem B1079191 : Blo 417772 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B948185 : Blo 417772 948185 := bstep (se 2 (by rfl) ⟨355569, by rfl⟩ : syracuseStep 948185 = 711139) B711139
theorem B3012653 : Blo 417772 3012653 := bstep (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) B1129745
theorem B948275 : Blo 417772 948275 := bstep (se 1 (by rfl) ⟨711206, by rfl⟩ : syracuseStep 948275 = 1422413) B1422413
theorem B948311 : Blo 417772 948311 := bstep (se 1 (by rfl) ⟨711233, by rfl⟩ : syracuseStep 948311 = 1422467) B1422467
theorem B948491 : Blo 417772 948491 := bstep (se 1 (by rfl) ⟨711368, by rfl⟩ : syracuseStep 948491 = 1422737) B1422737
theorem B2128193 : Blo 417772 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B948545 : Blo 417772 948545 := bstep (se 2 (by rfl) ⟨355704, by rfl⟩ : syracuseStep 948545 = 711409) B711409
theorem B1800721 : Blo 417772 1800721 := bstep (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) B1350541
theorem B948761 : Blo 417772 948761 := bstep (se 2 (by rfl) ⟨355785, by rfl⟩ : syracuseStep 948761 = 711571) B711571
theorem B2390573 : Blo 417772 2390573 := bstep (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) B896465
theorem B719435 : Blo 417772 719435 := bstep (se 1 (by rfl) ⟨539576, by rfl⟩ : syracuseStep 719435 = 1079153) B1079153
theorem B3570277 : Blo 417772 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B948851 : Blo 417772 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B948887 : Blo 417772 948887 := bstep (se 1 (by rfl) ⟨711665, by rfl⟩ : syracuseStep 948887 = 1423331) B1423331
theorem B424855 : Blo 417772 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B3571235 : Blo 417772 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B7241309 : Blo 417772 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B851609 : Blo 417772 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B753625 : Blo 417772 753625 := bstep (se 2 (by rfl) ⟨282609, by rfl⟩ : syracuseStep 753625 = 565219) B565219
theorem B720857 : Blo 417772 720857 := bstep (se 2 (by rfl) ⟨270321, by rfl⟩ : syracuseStep 720857 = 540643) B540643
theorem B34930763 : Blo 417772 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B1278067 : Blo 417772 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B4849901 : Blo 417772 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B2130461 : Blo 417772 2130461 := bstep (se 3 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 2130461 = 798923) B798923
theorem B2917093 : Blo 417772 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B852751 : Blo 417772 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B3015539 : Blo 417772 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B6456179 : Blo 417772 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B1639283 : Blo 417772 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B2130947 : Blo 417772 2130947 := bstep (se 1 (by rfl) ⟨1598210, by rfl⟩ : syracuseStep 2130947 = 3196421) B3196421
theorem B755003 : Blo 417772 755003 := bstep (se 1 (by rfl) ⟨566252, by rfl⟩ : syracuseStep 755003 = 1132505) B1132505
theorem B2393489 : Blo 417772 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B1279385 : Blo 417772 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B3409451 : Blo 417772 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B22808141 : Blo 417772 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B1345339 : Blo 417772 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B2393945 : Blo 417772 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B1345415 : Blo 417772 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B755831 : Blo 417772 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B1870025 : Blo 417772 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B1411343 : Blo 417772 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B1345825 : Blo 417772 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B1411613 : Blo 417772 1411613 := bstep (se 3 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 1411613 = 529355) B529355
theorem B2132567 : Blo 417772 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B2133053 : Blo 417772 2133053 := bstep (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) B799895
theorem B6065441 : Blo 417772 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B953801 : Blo 417772 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B2690603 : Blo 417772 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B1969921 : Blo 417772 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B2559833 : Blo 417772 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B5083033 : Blo 417772 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B1413017 : Blo 417772 1413017 := bstep (se 2 (by rfl) ⟨529881, by rfl⟩ : syracuseStep 1413017 = 1059763) B1059763
theorem B626747 : Blo 417772 626747 := bstep (se 1 (by rfl) ⟨470060, by rfl⟩ : syracuseStep 626747 = 940121) B940121
theorem B1347671 : Blo 417772 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B626807 : Blo 417772 626807 := bstep (se 1 (by rfl) ⟨470105, by rfl⟩ : syracuseStep 626807 = 940211) B940211
theorem B626831 : Blo 417772 626831 := bstep (se 1 (by rfl) ⟨470123, by rfl⟩ : syracuseStep 626831 = 940247) B940247
theorem B626873 : Blo 417772 626873 := bstep (se 2 (by rfl) ⟨235077, by rfl⟩ : syracuseStep 626873 = 470155) B470155
theorem B626951 : Blo 417772 626951 := bstep (se 1 (by rfl) ⟨470213, by rfl⟩ : syracuseStep 626951 = 940427) B940427
theorem B626987 : Blo 417772 626987 := bstep (se 1 (by rfl) ⟨470240, by rfl⟩ : syracuseStep 626987 = 940481) B940481
theorem B627017 : Blo 417772 627017 := bstep (se 2 (by rfl) ⟨235131, by rfl⟩ : syracuseStep 627017 = 470263) B470263
theorem B627131 : Blo 417772 627131 := bstep (se 1 (by rfl) ⟨470348, by rfl⟩ : syracuseStep 627131 = 940697) B940697
theorem B627191 : Blo 417772 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B627215 : Blo 417772 627215 := bstep (se 1 (by rfl) ⟨470411, by rfl⟩ : syracuseStep 627215 = 940823) B940823
theorem B627257 : Blo 417772 627257 := bstep (se 2 (by rfl) ⟨235221, by rfl⟩ : syracuseStep 627257 = 470443) B470443
theorem B1413719 : Blo 417772 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B8065655 : Blo 417772 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B529031 : Blo 417772 529031 := bstep (se 1 (by rfl) ⟨396773, by rfl⟩ : syracuseStep 529031 = 793547) B793547
theorem B627335 : Blo 417772 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B627371 : Blo 417772 627371 := bstep (se 1 (by rfl) ⟨470528, by rfl⟩ : syracuseStep 627371 = 941057) B941057
theorem B627401 : Blo 417772 627401 := bstep (se 2 (by rfl) ⟨235275, by rfl⟩ : syracuseStep 627401 = 470551) B470551
theorem B2265893 : Blo 417772 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B5083955 : Blo 417772 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B2134835 : Blo 417772 2134835 := bstep (se 1 (by rfl) ⟨1601126, by rfl⟩ : syracuseStep 2134835 = 3202253) B3202253
theorem B627515 : Blo 417772 627515 := bstep (se 1 (by rfl) ⟨470636, by rfl⟩ : syracuseStep 627515 = 941273) B941273
theorem B627575 : Blo 417772 627575 := bstep (se 1 (by rfl) ⟨470681, by rfl⟩ : syracuseStep 627575 = 941363) B941363
theorem B627599 : Blo 417772 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B3838873 : Blo 417772 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B594859 : Blo 417772 594859 := bstep (se 1 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 594859 = 892289) B892289
theorem B627641 : Blo 417772 627641 := bstep (se 2 (by rfl) ⟨235365, by rfl⟩ : syracuseStep 627641 = 470731) B470731
theorem B2397113 : Blo 417772 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B627719 : Blo 417772 627719 := bstep (se 1 (by rfl) ⟨470789, by rfl⟩ : syracuseStep 627719 = 941579) B941579
theorem B627755 : Blo 417772 627755 := bstep (se 1 (by rfl) ⟨470816, by rfl⟩ : syracuseStep 627755 = 941633) B941633
theorem B726059 : Blo 417772 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B1610813 : Blo 417772 1610813 := bstep (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) B604055
theorem B1414205 : Blo 417772 1414205 := bstep (se 3 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 1414205 = 530327) B530327
theorem B627785 : Blo 417772 627785 := bstep (se 2 (by rfl) ⟨235419, by rfl⟩ : syracuseStep 627785 = 470839) B470839
theorem B2135159 : Blo 417772 2135159 := bstep (se 1 (by rfl) ⟨1601369, by rfl⟩ : syracuseStep 2135159 = 3202739) B3202739
theorem B627899 : Blo 417772 627899 := bstep (se 1 (by rfl) ⟨470924, by rfl⟩ : syracuseStep 627899 = 941849) B941849
theorem B627959 : Blo 417772 627959 := bstep (se 1 (by rfl) ⟨470969, by rfl⟩ : syracuseStep 627959 = 941939) B941939
theorem B529679 : Blo 417772 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B627983 : Blo 417772 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B628025 : Blo 417772 628025 := bstep (se 2 (by rfl) ⟨235509, by rfl⟩ : syracuseStep 628025 = 471019) B471019
theorem B628103 : Blo 417772 628103 := bstep (se 1 (by rfl) ⟨471077, by rfl⟩ : syracuseStep 628103 = 942155) B942155
theorem B628139 : Blo 417772 628139 := bstep (se 1 (by rfl) ⟨471104, by rfl⟩ : syracuseStep 628139 = 942209) B942209
theorem B628169 : Blo 417772 628169 := bstep (se 2 (by rfl) ⟨235563, by rfl⟩ : syracuseStep 628169 = 471127) B471127
theorem B8033741 : Blo 417772 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B628283 : Blo 417772 628283 := bstep (se 1 (by rfl) ⟨471212, by rfl⟩ : syracuseStep 628283 = 942425) B942425
theorem B628343 : Blo 417772 628343 := bstep (se 1 (by rfl) ⟨471257, by rfl⟩ : syracuseStep 628343 = 942515) B942515
theorem B628367 : Blo 417772 628367 := bstep (se 1 (by rfl) ⟨471275, by rfl⟩ : syracuseStep 628367 = 942551) B942551
theorem B628409 : Blo 417772 628409 := bstep (se 2 (by rfl) ⟨235653, by rfl⟩ : syracuseStep 628409 = 471307) B471307
theorem B628487 : Blo 417772 628487 := bstep (se 1 (by rfl) ⟨471365, by rfl⟩ : syracuseStep 628487 = 942731) B942731
theorem B628523 : Blo 417772 628523 := bstep (se 1 (by rfl) ⟨471392, by rfl⟩ : syracuseStep 628523 = 942785) B942785
theorem B628553 : Blo 417772 628553 := bstep (se 2 (by rfl) ⟨235707, by rfl⟩ : syracuseStep 628553 = 471415) B471415
theorem B1513363 : Blo 417772 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B628667 : Blo 417772 628667 := bstep (se 1 (by rfl) ⟨471500, by rfl⟩ : syracuseStep 628667 = 943001) B943001
theorem B628727 : Blo 417772 628727 := bstep (se 1 (by rfl) ⟨471545, by rfl⟩ : syracuseStep 628727 = 943091) B943091
theorem B628751 : Blo 417772 628751 := bstep (se 1 (by rfl) ⟨471563, by rfl⟩ : syracuseStep 628751 = 943127) B943127
theorem B628793 : Blo 417772 628793 := bstep (se 2 (by rfl) ⟨235797, by rfl⟩ : syracuseStep 628793 = 471595) B471595
theorem B2431043 : Blo 417772 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B6035573 : Blo 417772 6035573 := bstep (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) B565835
theorem B628871 : Blo 417772 628871 := bstep (se 1 (by rfl) ⟨471653, by rfl⟩ : syracuseStep 628871 = 943307) B943307
theorem B628907 : Blo 417772 628907 := bstep (se 1 (by rfl) ⟨471680, by rfl⟩ : syracuseStep 628907 = 943361) B943361
theorem B628937 : Blo 417772 628937 := bstep (se 2 (by rfl) ⟨235851, by rfl⟩ : syracuseStep 628937 = 471703) B471703
theorem B629051 : Blo 417772 629051 := bstep (se 1 (by rfl) ⟨471788, by rfl⟩ : syracuseStep 629051 = 943577) B943577
theorem B629111 : Blo 417772 629111 := bstep (se 1 (by rfl) ⟨471833, by rfl⟩ : syracuseStep 629111 = 943667) B943667
theorem B629135 : Blo 417772 629135 := bstep (se 1 (by rfl) ⟨471851, by rfl⟩ : syracuseStep 629135 = 943703) B943703
theorem B1415609 : Blo 417772 1415609 := bstep (se 2 (by rfl) ⟨530853, by rfl⟩ : syracuseStep 1415609 = 1061707) B1061707
theorem B629177 : Blo 417772 629177 := bstep (se 2 (by rfl) ⟨235941, by rfl⟩ : syracuseStep 629177 = 471883) B471883
theorem B596425 : Blo 417772 596425 := bstep (se 2 (by rfl) ⟨223659, by rfl⟩ : syracuseStep 596425 = 447319) B447319
theorem B629255 : Blo 417772 629255 := bstep (se 1 (by rfl) ⟨471941, by rfl⟩ : syracuseStep 629255 = 943883) B943883
theorem B4528669 : Blo 417772 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B629291 : Blo 417772 629291 := bstep (se 1 (by rfl) ⟨471968, by rfl⟩ : syracuseStep 629291 = 943937) B943937
theorem B629321 : Blo 417772 629321 := bstep (se 2 (by rfl) ⟨235995, by rfl⟩ : syracuseStep 629321 = 471991) B471991
theorem B629435 : Blo 417772 629435 := bstep (se 1 (by rfl) ⟨472076, by rfl⟩ : syracuseStep 629435 = 944153) B944153
theorem B793289 : Blo 417772 793289 := bstep (se 2 (by rfl) ⟨297483, by rfl⟩ : syracuseStep 793289 = 594967) B594967
theorem B629495 : Blo 417772 629495 := bstep (se 1 (by rfl) ⟨472121, by rfl⟩ : syracuseStep 629495 = 944243) B944243
theorem B629519 : Blo 417772 629519 := bstep (se 1 (by rfl) ⟨472139, by rfl⟩ : syracuseStep 629519 = 944279) B944279
theorem B629561 : Blo 417772 629561 := bstep (se 2 (by rfl) ⟨236085, by rfl⟩ : syracuseStep 629561 = 472171) B472171
theorem B3414899 : Blo 417772 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B629639 : Blo 417772 629639 := bstep (se 1 (by rfl) ⟨472229, by rfl⟩ : syracuseStep 629639 = 944459) B944459
theorem B629675 : Blo 417772 629675 := bstep (se 1 (by rfl) ⟨472256, by rfl⟩ : syracuseStep 629675 = 944513) B944513
theorem B629705 : Blo 417772 629705 := bstep (se 2 (by rfl) ⟨236139, by rfl⟩ : syracuseStep 629705 = 472279) B472279
theorem B596983 : Blo 417772 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B2038787 : Blo 417772 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B1416203 : Blo 417772 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B629819 : Blo 417772 629819 := bstep (se 1 (by rfl) ⟨472364, by rfl⟩ : syracuseStep 629819 = 944729) B944729
theorem B1416311 : Blo 417772 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B629879 : Blo 417772 629879 := bstep (se 1 (by rfl) ⟨472409, by rfl⟩ : syracuseStep 629879 = 944819) B944819
theorem B629903 : Blo 417772 629903 := bstep (se 1 (by rfl) ⟨472427, by rfl⟩ : syracuseStep 629903 = 944855) B944855
theorem B629945 : Blo 417772 629945 := bstep (se 2 (by rfl) ⟨236229, by rfl⟩ : syracuseStep 629945 = 472459) B472459
theorem B630023 : Blo 417772 630023 := bstep (se 1 (by rfl) ⟨472517, by rfl⟩ : syracuseStep 630023 = 945035) B945035
theorem B2399503 : Blo 417772 2399503 := bstep (se 1 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 2399503 = 3599255) B3599255
theorem B630059 : Blo 417772 630059 := bstep (se 1 (by rfl) ⟨472544, by rfl⟩ : syracuseStep 630059 = 945089) B945089
theorem B630089 : Blo 417772 630089 := bstep (se 2 (by rfl) ⟨236283, by rfl⟩ : syracuseStep 630089 = 472567) B472567
theorem B630203 : Blo 417772 630203 := bstep (se 1 (by rfl) ⟨472652, by rfl⟩ : syracuseStep 630203 = 945305) B945305
theorem B630263 : Blo 417772 630263 := bstep (se 1 (by rfl) ⟨472697, by rfl⟩ : syracuseStep 630263 = 945395) B945395
theorem B630287 : Blo 417772 630287 := bstep (se 1 (by rfl) ⟨472715, by rfl⟩ : syracuseStep 630287 = 945431) B945431
theorem B4038173 : Blo 417772 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B597547 : Blo 417772 597547 := bstep (se 1 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 597547 = 896321) B896321
theorem B630329 : Blo 417772 630329 := bstep (se 2 (by rfl) ⟨236373, by rfl⟩ : syracuseStep 630329 = 472747) B472747
theorem B630407 : Blo 417772 630407 := bstep (se 1 (by rfl) ⟨472805, by rfl⟩ : syracuseStep 630407 = 945611) B945611
theorem B630443 : Blo 417772 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B1416905 : Blo 417772 1416905 := bstep (se 2 (by rfl) ⟨531339, by rfl⟩ : syracuseStep 1416905 = 1062679) B1062679
theorem B630473 : Blo 417772 630473 := bstep (se 2 (by rfl) ⟨236427, by rfl⟩ : syracuseStep 630473 = 472855) B472855
theorem B597775 : Blo 417772 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B630587 : Blo 417772 630587 := bstep (se 1 (by rfl) ⟨472940, by rfl⟩ : syracuseStep 630587 = 945881) B945881
theorem B630647 : Blo 417772 630647 := bstep (se 1 (by rfl) ⟨472985, by rfl⟩ : syracuseStep 630647 = 945971) B945971
theorem B630671 : Blo 417772 630671 := bstep (se 1 (by rfl) ⟨473003, by rfl⟩ : syracuseStep 630671 = 946007) B946007
theorem B2858905 : Blo 417772 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B630713 : Blo 417772 630713 := bstep (se 2 (by rfl) ⟨236517, by rfl⟩ : syracuseStep 630713 = 473035) B473035
theorem B630791 : Blo 417772 630791 := bstep (se 1 (by rfl) ⟨473093, by rfl⟩ : syracuseStep 630791 = 946187) B946187
theorem B630827 : Blo 417772 630827 := bstep (se 1 (by rfl) ⟨473120, by rfl⟩ : syracuseStep 630827 = 946241) B946241
theorem B630857 : Blo 417772 630857 := bstep (se 2 (by rfl) ⟨236571, by rfl⟩ : syracuseStep 630857 = 473143) B473143
theorem B532651 : Blo 417772 532651 := bstep (se 1 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 532651 = 798977) B798977
theorem B630971 : Blo 417772 630971 := bstep (se 1 (by rfl) ⟨473228, by rfl⟩ : syracuseStep 630971 = 946457) B946457
theorem B631031 : Blo 417772 631031 := bstep (se 1 (by rfl) ⟨473273, by rfl⟩ : syracuseStep 631031 = 946547) B946547
theorem B631055 : Blo 417772 631055 := bstep (se 1 (by rfl) ⟨473291, by rfl⟩ : syracuseStep 631055 = 946583) B946583
theorem B631097 : Blo 417772 631097 := bstep (se 2 (by rfl) ⟨236661, by rfl⟩ : syracuseStep 631097 = 473323) B473323
theorem B1417607 : Blo 417772 1417607 := bstep (se 1 (by rfl) ⟨1063205, by rfl⟩ : syracuseStep 1417607 = 2126411) B2126411
theorem B631175 : Blo 417772 631175 := bstep (se 1 (by rfl) ⟨473381, by rfl⟩ : syracuseStep 631175 = 946763) B946763
theorem B631211 : Blo 417772 631211 := bstep (se 1 (by rfl) ⟨473408, by rfl⟩ : syracuseStep 631211 = 946817) B946817
theorem B631241 : Blo 417772 631241 := bstep (se 2 (by rfl) ⟨236715, by rfl⟩ : syracuseStep 631241 = 473431) B473431
theorem B2400779 : Blo 417772 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B631355 : Blo 417772 631355 := bstep (se 1 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 631355 = 947033) B947033
theorem B631415 : Blo 417772 631415 := bstep (se 1 (by rfl) ⟨473561, by rfl⟩ : syracuseStep 631415 = 947123) B947123
theorem B795271 : Blo 417772 795271 := bstep (se 1 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 795271 = 1192907) B1192907
theorem B631439 : Blo 417772 631439 := bstep (se 1 (by rfl) ⟨473579, by rfl⟩ : syracuseStep 631439 = 947159) B947159
theorem B893587 : Blo 417772 893587 := bstep (se 1 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 893587 = 1340381) B1340381
theorem B631481 : Blo 417772 631481 := bstep (se 2 (by rfl) ⟨236805, by rfl⟩ : syracuseStep 631481 = 473611) B473611
theorem B2400961 : Blo 417772 2400961 := bstep (se 2 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 2400961 = 1800721) B1800721
theorem B4530917 : Blo 417772 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B1417985 : Blo 417772 1417985 := bstep (se 2 (by rfl) ⟨531744, by rfl⟩ : syracuseStep 1417985 = 1063489) B1063489
theorem B631559 : Blo 417772 631559 := bstep (se 1 (by rfl) ⟨473669, by rfl⟩ : syracuseStep 631559 = 947339) B947339
theorem B631595 : Blo 417772 631595 := bstep (se 1 (by rfl) ⟨473696, by rfl⟩ : syracuseStep 631595 = 947393) B947393
theorem B4760369 : Blo 417772 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B631625 : Blo 417772 631625 := bstep (se 2 (by rfl) ⟨236859, by rfl⟩ : syracuseStep 631625 = 473719) B473719
theorem B598919 : Blo 417772 598919 := bstep (se 1 (by rfl) ⟨449189, by rfl⟩ : syracuseStep 598919 = 898379) B898379
theorem B631739 : Blo 417772 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B631799 : Blo 417772 631799 := bstep (se 1 (by rfl) ⟨473849, by rfl⟩ : syracuseStep 631799 = 947699) B947699
theorem B631823 : Blo 417772 631823 := bstep (se 1 (by rfl) ⟨473867, by rfl⟩ : syracuseStep 631823 = 947735) B947735
theorem B631865 : Blo 417772 631865 := bstep (se 2 (by rfl) ⟨236949, by rfl⟩ : syracuseStep 631865 = 473899) B473899
theorem B599113 : Blo 417772 599113 := bstep (se 2 (by rfl) ⟨224667, by rfl⟩ : syracuseStep 599113 = 449335) B449335
theorem B533623 : Blo 417772 533623 := bstep (se 1 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 533623 = 800435) B800435
theorem B631943 : Blo 417772 631943 := bstep (se 1 (by rfl) ⟨473957, by rfl⟩ : syracuseStep 631943 = 947915) B947915
theorem B631979 : Blo 417772 631979 := bstep (se 1 (by rfl) ⟨473984, by rfl⟩ : syracuseStep 631979 = 947969) B947969
theorem B632009 : Blo 417772 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B632123 : Blo 417772 632123 := bstep (se 1 (by rfl) ⟨474092, by rfl⟩ : syracuseStep 632123 = 948185) B948185
theorem B632183 : Blo 417772 632183 := bstep (se 1 (by rfl) ⟨474137, by rfl⟩ : syracuseStep 632183 = 948275) B948275
theorem B632207 : Blo 417772 632207 := bstep (se 1 (by rfl) ⟨474155, by rfl⟩ : syracuseStep 632207 = 948311) B948311
theorem B632249 : Blo 417772 632249 := bstep (se 2 (by rfl) ⟨237093, by rfl⟩ : syracuseStep 632249 = 474187) B474187
theorem B1058305 : Blo 417772 1058305 := bstep (se 2 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 1058305 = 793729) B793729
theorem B632327 : Blo 417772 632327 := bstep (se 1 (by rfl) ⟨474245, by rfl⟩ : syracuseStep 632327 = 948491) B948491
theorem B1418795 : Blo 417772 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B632363 : Blo 417772 632363 := bstep (se 1 (by rfl) ⟨474272, by rfl⟩ : syracuseStep 632363 = 948545) B948545
theorem B632393 : Blo 417772 632393 := bstep (se 2 (by rfl) ⟨237147, by rfl⟩ : syracuseStep 632393 = 474295) B474295
theorem B599671 : Blo 417772 599671 := bstep (se 1 (by rfl) ⟨449753, by rfl⟩ : syracuseStep 599671 = 899507) B899507
theorem B632507 : Blo 417772 632507 := bstep (se 1 (by rfl) ⟨474380, by rfl⟩ : syracuseStep 632507 = 948761) B948761
theorem B632567 : Blo 417772 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B632591 : Blo 417772 632591 := bstep (se 1 (by rfl) ⟨474443, by rfl⟩ : syracuseStep 632591 = 948887) B948887
theorem B632633 : Blo 417772 632633 := bstep (se 2 (by rfl) ⟨237237, by rfl⟩ : syracuseStep 632633 = 474475) B474475
theorem B18425717 : Blo 417772 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B2697239 : Blo 417772 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B1058903 : Blo 417772 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B796873 : Blo 417772 796873 := bstep (se 2 (by rfl) ⟨298827, by rfl⟩ : syracuseStep 796873 = 597655) B597655
theorem B1190173 : Blo 417772 1190173 := bstep (se 3 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 1190173 = 446315) B446315
theorem B1059115 : Blo 417772 1059115 := bstep (se 1 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 1059115 = 1588673) B1588673
theorem B600377 : Blo 417772 600377 := bstep (se 2 (by rfl) ⟨225141, by rfl⟩ : syracuseStep 600377 = 450283) B450283
theorem B600463 : Blo 417772 600463 := bstep (se 1 (by rfl) ⟨450347, by rfl⟩ : syracuseStep 600463 = 900695) B900695
theorem B4827539 : Blo 417772 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B600491 : Blo 417772 600491 := bstep (se 1 (by rfl) ⟨450368, by rfl⟩ : syracuseStep 600491 = 900737) B900737
theorem B1059257 : Blo 417772 1059257 := bstep (se 2 (by rfl) ⟨397221, by rfl⟩ : syracuseStep 1059257 = 794443) B794443
theorem B567739 : Blo 417772 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B1420091 : Blo 417772 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B1616755 : Blo 417772 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B8105021 : Blo 417772 8105021 := bstep (se 3 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 8105021 = 3039383) B3039383
theorem B18656407 : Blo 417772 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B1420577 : Blo 417772 1420577 := bstep (se 2 (by rfl) ⟨532716, by rfl⟩ : syracuseStep 1420577 = 1065433) B1065433
theorem B470407 : Blo 417772 470407 := bstep (se 1 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 470407 = 705611) B705611
theorem B1060249 : Blo 417772 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B4042169 : Blo 417772 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B503339 : Blo 417772 503339 := bstep (se 1 (by rfl) ⟨377504, by rfl⟩ : syracuseStep 503339 = 755009) B755009
theorem B470587 : Blo 417772 470587 := bstep (se 1 (by rfl) ⟨352940, by rfl⟩ : syracuseStep 470587 = 705881) B705881
theorem B1060411 : Blo 417772 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B1060553 : Blo 417772 1060553 := bstep (se 2 (by rfl) ⟨397707, by rfl⟩ : syracuseStep 1060553 = 795415) B795415
theorem B1912577 : Blo 417772 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B4829017 : Blo 417772 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B1421171 : Blo 417772 1421171 := bstep (se 1 (by rfl) ⟨1065878, by rfl⟩ : syracuseStep 1421171 = 2131757) B2131757
theorem B471055 : Blo 417772 471055 := bstep (se 1 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 471055 = 706583) B706583
theorem B1060897 : Blo 417772 1060897 := bstep (se 2 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 1060897 = 795673) B795673
theorem B569479 : Blo 417772 569479 := bstep (se 1 (by rfl) ⟨427109, by rfl⟩ : syracuseStep 569479 = 854219) B854219
theorem B1192121 : Blo 417772 1192121 := bstep (se 2 (by rfl) ⟨447045, by rfl⟩ : syracuseStep 1192121 = 894091) B894091
theorem B2044295 : Blo 417772 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B4796819 : Blo 417772 4796819 := bstep (se 1 (by rfl) ⟨3597614, by rfl⟩ : syracuseStep 4796819 = 7195229) B7195229
theorem B471559 : Blo 417772 471559 := bstep (se 1 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 471559 = 707339) B707339
theorem B897551 : Blo 417772 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B1061495 : Blo 417772 1061495 := bstep (se 1 (by rfl) ⟨796121, by rfl⟩ : syracuseStep 1061495 = 1592243) B1592243
theorem B799379 : Blo 417772 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B471739 : Blo 417772 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B799607 : Blo 417772 799607 := bstep (se 1 (by rfl) ⟨599705, by rfl⟩ : syracuseStep 799607 = 1199411) B1199411
theorem B1586243 : Blo 417772 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B472207 : Blo 417772 472207 := bstep (se 1 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 472207 = 708311) B708311
theorem B537871 : Blo 417772 537871 := bstep (se 1 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 537871 = 806807) B806807
theorem B1193363 : Blo 417772 1193363 := bstep (se 1 (by rfl) ⟨895022, by rfl⟩ : syracuseStep 1193363 = 1790045) B1790045
theorem B1586699 : Blo 417772 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B505387 : Blo 417772 505387 := bstep (se 1 (by rfl) ⟨379040, by rfl⟩ : syracuseStep 505387 = 758081) B758081
theorem B472711 : Blo 417772 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B538427 : Blo 417772 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B472891 : Blo 417772 472891 := bstep (se 1 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 472891 = 709337) B709337
theorem B1062791 : Blo 417772 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B1062841 : Blo 417772 1062841 := bstep (se 2 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 1062841 = 797131) B797131
theorem B899191 : Blo 417772 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B473359 : Blo 417772 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B1063439 : Blo 417772 1063439 := bstep (se 1 (by rfl) ⟨797579, by rfl⟩ : syracuseStep 1063439 = 1595159) B1595159
theorem B1227383 : Blo 417772 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B473863 : Blo 417772 473863 := bstep (se 1 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 473863 = 710795) B710795
theorem B1194763 : Blo 417772 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B3390245 : Blo 417772 3390245 := bstep (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) B635671
theorem B1719187 : Blo 417772 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B1784729 : Blo 417772 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B474043 : Blo 417772 474043 := bstep (se 1 (by rfl) ⟨355532, by rfl⟩ : syracuseStep 474043 = 711065) B711065
theorem B1621003 : Blo 417772 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B1195037 : Blo 417772 1195037 := bstep (se 3 (by rfl) ⟨224069, by rfl⟩ : syracuseStep 1195037 = 448139) B448139
theorem B1064137 : Blo 417772 1064137 := bstep (se 2 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 1064137 = 798103) B798103
theorem B1064279 : Blo 417772 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B12303875 : Blo 417772 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B1588855 : Blo 417772 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B2309939 : Blo 417772 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B1818503 : Blo 417772 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B769927 : Blo 417772 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B1130611 : Blo 417772 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B2048465 : Blo 417772 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B1589827 : Blo 417772 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B2867831 : Blo 417772 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B1590131 : Blo 417772 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B705415 : Blo 417772 705415 := bstep (se 1 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 705415 = 1058123) B1058123
theorem B1131563 : Blo 417772 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B1590587 : Blo 417772 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B4769117 : Blo 417772 4769117 := bstep (se 3 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 4769117 = 1788419) B1788419
theorem B1066355 : Blo 417772 1066355 := bstep (se 1 (by rfl) ⟨799766, by rfl⟩ : syracuseStep 1066355 = 1599533) B1599533
theorem B1197497 : Blo 417772 1197497 := bstep (se 2 (by rfl) ⟨449061, by rfl⟩ : syracuseStep 1197497 = 898123) B898123
theorem B1230281 : Blo 417772 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B706063 : Blo 417772 706063 := bstep (se 1 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 706063 = 1059095) B1059095
theorem B1197611 : Blo 417772 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B5031695 : Blo 417772 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1591073 : Blo 417772 1591073 := bstep (se 2 (by rfl) ⟨596652, by rfl⟩ : syracuseStep 1591073 = 1193305) B1193305
theorem B673579 : Blo 417772 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B509815 : Blo 417772 509815 := bstep (se 1 (by rfl) ⟨382361, by rfl⟩ : syracuseStep 509815 = 764723) B764723
theorem B1066871 : Blo 417772 1066871 := bstep (se 1 (by rfl) ⟨800153, by rfl⟩ : syracuseStep 1066871 = 1600307) B1600307
theorem B706603 : Blo 417772 706603 := bstep (se 1 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 706603 = 1059905) B1059905
theorem B706745 : Blo 417772 706745 := bstep (se 2 (by rfl) ⟨265029, by rfl⟩ : syracuseStep 706745 = 530059) B530059
theorem B2116043 : Blo 417772 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B3197393 : Blo 417772 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B1198739 : Blo 417772 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B1592045 : Blo 417772 1592045 := bstep (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) B597017
theorem B2116367 : Blo 417772 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B4770575 : Blo 417772 4770575 := bstep (se 1 (by rfl) ⟨3577931, by rfl⟩ : syracuseStep 4770575 = 7155863) B7155863
theorem B707447 : Blo 417772 707447 := bstep (se 1 (by rfl) ⟨530585, by rfl⟩ : syracuseStep 707447 = 1061171) B1061171
theorem B1199137 : Blo 417772 1199137 := bstep (se 2 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 1199137 = 899353) B899353
theorem B871723 : Blo 417772 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B707899 : Blo 417772 707899 := bstep (se 1 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 707899 = 1061849) B1061849
theorem B1592729 : Blo 417772 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B708041 : Blo 417772 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B2543147 : Blo 417772 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B46157525 : Blo 417772 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B1200025 : Blo 417772 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B708743 : Blo 417772 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B2117825 : Blo 417772 2117825 := bstep (se 2 (by rfl) ⟨794184, by rfl⟩ : syracuseStep 2117825 = 1588369) B1588369
theorem B7622857 : Blo 417772 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B1200413 : Blo 417772 1200413 := bstep (se 3 (by rfl) ⟨225077, by rfl⟩ : syracuseStep 1200413 = 450155) B450155
theorem B1593715 : Blo 417772 1593715 := bstep (se 1 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 1593715 = 2390573) B2390573
theorem B479623 : Blo 417772 479623 := bstep (se 1 (by rfl) ⟨359717, by rfl⟩ : syracuseStep 479623 = 719435) B719435
theorem B709391 : Blo 417772 709391 := bstep (se 1 (by rfl) ⟨532043, by rfl⟩ : syracuseStep 709391 = 1064087) B1064087
theorem B2380823 : Blo 417772 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B4084937 : Blo 417772 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1922285 : Blo 417772 1922285 := bstep (se 3 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 1922285 = 720857) B720857
theorem B1004833 : Blo 417772 1004833 := bstep (se 2 (by rfl) ⟨376812, by rfl⟩ : syracuseStep 1004833 = 753625) B753625
theorem B709931 : Blo 417772 709931 := bstep (se 1 (by rfl) ⟨532448, by rfl⟩ : syracuseStep 709931 = 1064897) B1064897
theorem B15324551 : Blo 417772 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B447887 : Blo 417772 447887 := bstep (se 1 (by rfl) ⟨335915, by rfl⟩ : syracuseStep 447887 = 671831) B671831
theorem B2119121 : Blo 417772 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B710329 : Blo 417772 710329 := bstep (se 2 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 710329 = 532747) B532747
theorem B1136537 : Blo 417772 1136537 := bstep (se 2 (by rfl) ⟨426201, by rfl⟩ : syracuseStep 1136537 = 852403) B852403
theorem B1792043 : Blo 417772 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B711031 : Blo 417772 711031 := bstep (se 1 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 711031 = 1066547) B1066547
theorem B1595933 : Blo 417772 1595933 := bstep (se 3 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 1595933 = 598475) B598475
theorem B711227 : Blo 417772 711227 := bstep (se 1 (by rfl) ⟨533420, by rfl⟩ : syracuseStep 711227 = 1066841) B1066841
theorem B940679 : Blo 417772 940679 := bstep (se 1 (by rfl) ⟨705509, by rfl⟩ : syracuseStep 940679 = 1411019) B1411019
theorem B1038995 : Blo 417772 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B940859 : Blo 417772 940859 := bstep (se 1 (by rfl) ⟨705644, by rfl⟩ : syracuseStep 940859 = 1411289) B1411289
theorem B7199603 : Blo 417772 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B940985 : Blo 417772 940985 := bstep (se 2 (by rfl) ⟨352869, by rfl⟩ : syracuseStep 940985 = 705739) B705739
theorem B711625 : Blo 417772 711625 := bstep (se 2 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 711625 = 533719) B533719
theorem B2022353 : Blo 417772 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B1596617 : Blo 417772 1596617 := bstep (se 2 (by rfl) ⟨598731, by rfl⟩ : syracuseStep 1596617 = 1197463) B1197463
theorem B941327 : Blo 417772 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B941345 : Blo 417772 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B2121227 : Blo 417772 2121227 := bstep (se 1 (by rfl) ⟨1590920, by rfl⟩ : syracuseStep 2121227 = 3181841) B3181841
theorem B679439 : Blo 417772 679439 := bstep (se 1 (by rfl) ⟨509579, by rfl⟩ : syracuseStep 679439 = 1019159) B1019159
theorem B941687 : Blo 417772 941687 := bstep (se 1 (by rfl) ⟨706265, by rfl⟩ : syracuseStep 941687 = 1412531) B1412531
theorem B2121389 : Blo 417772 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B941867 : Blo 417772 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B3039065 : Blo 417772 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B417799 : Blo 417772 417799 := bstep (se 1 (by rfl) ⟨313349, by rfl⟩ : syracuseStep 417799 = 626699) B626699
theorem B1794059 : Blo 417772 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B417807 : Blo 417772 417807 := bstep (se 1 (by rfl) ⟨313355, by rfl⟩ : syracuseStep 417807 = 626711) B626711
theorem B417851 : Blo 417772 417851 := bstep (se 1 (by rfl) ⟨313388, by rfl⟩ : syracuseStep 417851 = 626777) B626777
theorem B2383991 : Blo 417772 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B417927 : Blo 417772 417927 := bstep (se 1 (by rfl) ⟨313445, by rfl⟩ : syracuseStep 417927 = 626891) B626891
theorem B417935 : Blo 417772 417935 := bstep (se 1 (by rfl) ⟨313451, by rfl⟩ : syracuseStep 417935 = 626903) B626903
theorem B942227 : Blo 417772 942227 := bstep (se 1 (by rfl) ⟨706670, by rfl⟩ : syracuseStep 942227 = 1413341) B1413341
theorem B1138873 : Blo 417772 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B417979 : Blo 417772 417979 := bstep (se 1 (by rfl) ⟨313484, by rfl⟩ : syracuseStep 417979 = 626969) B626969
theorem B942281 : Blo 417772 942281 := bstep (se 2 (by rfl) ⟨353355, by rfl⟩ : syracuseStep 942281 = 706711) B706711
theorem B418055 : Blo 417772 418055 := bstep (se 1 (by rfl) ⟨313541, by rfl⟩ : syracuseStep 418055 = 627083) B627083
theorem B418063 : Blo 417772 418063 := bstep (se 1 (by rfl) ⟨313547, by rfl⟩ : syracuseStep 418063 = 627095) B627095
theorem B4022561 : Blo 417772 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B418107 : Blo 417772 418107 := bstep (se 1 (by rfl) ⟨313580, by rfl⟩ : syracuseStep 418107 = 627161) B627161
theorem B1794419 : Blo 417772 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B2023795 : Blo 417772 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B418183 : Blo 417772 418183 := bstep (se 1 (by rfl) ⟨313637, by rfl⟩ : syracuseStep 418183 = 627275) B627275
theorem B418191 : Blo 417772 418191 := bstep (se 1 (by rfl) ⟨313643, by rfl⟩ : syracuseStep 418191 = 627287) B627287
theorem B4022713 : Blo 417772 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B418235 : Blo 417772 418235 := bstep (se 1 (by rfl) ⟨313676, by rfl⟩ : syracuseStep 418235 = 627353) B627353
theorem B418311 : Blo 417772 418311 := bstep (se 1 (by rfl) ⟨313733, by rfl⟩ : syracuseStep 418311 = 627467) B627467
theorem B418319 : Blo 417772 418319 := bstep (se 1 (by rfl) ⟨313739, by rfl⟩ : syracuseStep 418319 = 627479) B627479
theorem B418363 : Blo 417772 418363 := bstep (se 1 (by rfl) ⟨313772, by rfl⟩ : syracuseStep 418363 = 627545) B627545
theorem B418439 : Blo 417772 418439 := bstep (se 1 (by rfl) ⟨313829, by rfl⟩ : syracuseStep 418439 = 627659) B627659
theorem B418447 : Blo 417772 418447 := bstep (se 1 (by rfl) ⟨313835, by rfl⟩ : syracuseStep 418447 = 627671) B627671
theorem B418491 : Blo 417772 418491 := bstep (se 1 (by rfl) ⟨313868, by rfl⟩ : syracuseStep 418491 = 627737) B627737
theorem B418567 : Blo 417772 418567 := bstep (se 1 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 418567 = 627851) B627851
theorem B418575 : Blo 417772 418575 := bstep (se 1 (by rfl) ⟨313931, by rfl⟩ : syracuseStep 418575 = 627863) B627863
theorem B3629873 : Blo 417772 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B418619 : Blo 417772 418619 := bstep (se 1 (by rfl) ⟨313964, by rfl⟩ : syracuseStep 418619 = 627929) B627929
theorem B418695 : Blo 417772 418695 := bstep (se 1 (by rfl) ⟨314021, by rfl⟩ : syracuseStep 418695 = 628043) B628043
theorem B942983 : Blo 417772 942983 := bstep (se 1 (by rfl) ⟨707237, by rfl⟩ : syracuseStep 942983 = 1414475) B1414475
theorem B418703 : Blo 417772 418703 := bstep (se 1 (by rfl) ⟨314027, by rfl⟩ : syracuseStep 418703 = 628055) B628055
theorem B1598393 : Blo 417772 1598393 := bstep (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) B1198795
theorem B418747 : Blo 417772 418747 := bstep (se 1 (by rfl) ⟨314060, by rfl⟩ : syracuseStep 418747 = 628121) B628121
theorem B2548739 : Blo 417772 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B418823 : Blo 417772 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B418831 : Blo 417772 418831 := bstep (se 1 (by rfl) ⟨314123, by rfl⟩ : syracuseStep 418831 = 628247) B628247
theorem B615481 : Blo 417772 615481 := bstep (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) B461611
theorem B418875 : Blo 417772 418875 := bstep (se 1 (by rfl) ⟨314156, by rfl⟩ : syracuseStep 418875 = 628313) B628313
theorem B943163 : Blo 417772 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B418951 : Blo 417772 418951 := bstep (se 1 (by rfl) ⟨314213, by rfl⟩ : syracuseStep 418951 = 628427) B628427
theorem B418959 : Blo 417772 418959 := bstep (se 1 (by rfl) ⟨314219, by rfl⟩ : syracuseStep 418959 = 628439) B628439
theorem B943289 : Blo 417772 943289 := bstep (se 2 (by rfl) ⟨353733, by rfl⟩ : syracuseStep 943289 = 707467) B707467
theorem B419003 : Blo 417772 419003 := bstep (se 1 (by rfl) ⟨314252, by rfl⟩ : syracuseStep 419003 = 628505) B628505
theorem B2123009 : Blo 417772 2123009 := bstep (se 2 (by rfl) ⟨796128, by rfl⟩ : syracuseStep 2123009 = 1592257) B1592257
theorem B419079 : Blo 417772 419079 := bstep (se 1 (by rfl) ⟨314309, by rfl⟩ : syracuseStep 419079 = 628619) B628619
theorem B419087 : Blo 417772 419087 := bstep (se 1 (by rfl) ⟨314315, by rfl⟩ : syracuseStep 419087 = 628631) B628631
theorem B1008929 : Blo 417772 1008929 := bstep (se 2 (by rfl) ⟨378348, by rfl⟩ : syracuseStep 1008929 = 756697) B756697
theorem B419131 : Blo 417772 419131 := bstep (se 1 (by rfl) ⟨314348, by rfl⟩ : syracuseStep 419131 = 628697) B628697
theorem B419207 : Blo 417772 419207 := bstep (se 1 (by rfl) ⟨314405, by rfl⟩ : syracuseStep 419207 = 628811) B628811
theorem B419215 : Blo 417772 419215 := bstep (se 1 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 419215 = 628823) B628823
theorem B419259 : Blo 417772 419259 := bstep (se 1 (by rfl) ⟨314444, by rfl⟩ : syracuseStep 419259 = 628889) B628889
theorem B419335 : Blo 417772 419335 := bstep (se 1 (by rfl) ⟨314501, by rfl⟩ : syracuseStep 419335 = 629003) B629003
theorem B419343 : Blo 417772 419343 := bstep (se 1 (by rfl) ⟨314507, by rfl⟩ : syracuseStep 419343 = 629015) B629015
theorem B943631 : Blo 417772 943631 := bstep (se 1 (by rfl) ⟨707723, by rfl⟩ : syracuseStep 943631 = 1415447) B1415447
theorem B943649 : Blo 417772 943649 := bstep (se 2 (by rfl) ⟨353868, by rfl⟩ : syracuseStep 943649 = 707737) B707737
theorem B2450987 : Blo 417772 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B419387 : Blo 417772 419387 := bstep (se 1 (by rfl) ⟨314540, by rfl⟩ : syracuseStep 419387 = 629081) B629081
theorem B419463 : Blo 417772 419463 := bstep (se 1 (by rfl) ⟨314597, by rfl⟩ : syracuseStep 419463 = 629195) B629195
theorem B419471 : Blo 417772 419471 := bstep (se 1 (by rfl) ⟨314603, by rfl⟩ : syracuseStep 419471 = 629207) B629207
theorem B419515 : Blo 417772 419515 := bstep (se 1 (by rfl) ⟨314636, by rfl⟩ : syracuseStep 419515 = 629273) B629273
theorem B419591 : Blo 417772 419591 := bstep (se 1 (by rfl) ⟨314693, by rfl⟩ : syracuseStep 419591 = 629387) B629387
theorem B2549519 : Blo 417772 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B419599 : Blo 417772 419599 := bstep (se 1 (by rfl) ⟨314699, by rfl⟩ : syracuseStep 419599 = 629399) B629399
theorem B419643 : Blo 417772 419643 := bstep (se 1 (by rfl) ⟨314732, by rfl⟩ : syracuseStep 419643 = 629465) B629465
theorem B1009523 : Blo 417772 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B943991 : Blo 417772 943991 := bstep (se 1 (by rfl) ⟨707993, by rfl⟩ : syracuseStep 943991 = 1415987) B1415987
theorem B419719 : Blo 417772 419719 := bstep (se 1 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 419719 = 629579) B629579
theorem B419727 : Blo 417772 419727 := bstep (se 1 (by rfl) ⟨314795, by rfl⟩ : syracuseStep 419727 = 629591) B629591
theorem B4646807 : Blo 417772 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B419771 : Blo 417772 419771 := bstep (se 1 (by rfl) ⟨314828, by rfl⟩ : syracuseStep 419771 = 629657) B629657
theorem B419847 : Blo 417772 419847 := bstep (se 1 (by rfl) ⟨314885, by rfl⟩ : syracuseStep 419847 = 629771) B629771
theorem B419855 : Blo 417772 419855 := bstep (se 1 (by rfl) ⟨314891, by rfl⟩ : syracuseStep 419855 = 629783) B629783
theorem B2123819 : Blo 417772 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B944171 : Blo 417772 944171 := bstep (se 1 (by rfl) ⟨708128, by rfl⟩ : syracuseStep 944171 = 1416257) B1416257
theorem B419899 : Blo 417772 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B419975 : Blo 417772 419975 := bstep (se 1 (by rfl) ⟨314981, by rfl⟩ : syracuseStep 419975 = 629963) B629963
theorem B419983 : Blo 417772 419983 := bstep (se 1 (by rfl) ⟨314987, by rfl⟩ : syracuseStep 419983 = 629975) B629975
theorem B420027 : Blo 417772 420027 := bstep (se 1 (by rfl) ⟨315020, by rfl⟩ : syracuseStep 420027 = 630041) B630041
theorem B1697993 : Blo 417772 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B420103 : Blo 417772 420103 := bstep (se 1 (by rfl) ⟨315077, by rfl⟩ : syracuseStep 420103 = 630155) B630155
theorem B420111 : Blo 417772 420111 := bstep (se 1 (by rfl) ⟨315083, by rfl⟩ : syracuseStep 420111 = 630167) B630167
theorem B420155 : Blo 417772 420155 := bstep (se 1 (by rfl) ⟨315116, by rfl⟩ : syracuseStep 420155 = 630233) B630233
theorem B420231 : Blo 417772 420231 := bstep (se 1 (by rfl) ⟨315173, by rfl⟩ : syracuseStep 420231 = 630347) B630347
theorem B420239 : Blo 417772 420239 := bstep (se 1 (by rfl) ⟨315179, by rfl⟩ : syracuseStep 420239 = 630359) B630359
theorem B944531 : Blo 417772 944531 := bstep (se 1 (by rfl) ⟨708398, by rfl⟩ : syracuseStep 944531 = 1416797) B1416797
theorem B420283 : Blo 417772 420283 := bstep (se 1 (by rfl) ⟨315212, by rfl⟩ : syracuseStep 420283 = 630425) B630425
theorem B944585 : Blo 417772 944585 := bstep (se 2 (by rfl) ⟨354219, by rfl⟩ : syracuseStep 944585 = 708439) B708439
theorem B420359 : Blo 417772 420359 := bstep (se 1 (by rfl) ⟨315269, by rfl⟩ : syracuseStep 420359 = 630539) B630539
theorem B420367 : Blo 417772 420367 := bstep (se 1 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 420367 = 630551) B630551
theorem B2550295 : Blo 417772 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B2714141 : Blo 417772 2714141 := bstep (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) B1017803
theorem B420411 : Blo 417772 420411 := bstep (se 1 (by rfl) ⟨315308, by rfl⟩ : syracuseStep 420411 = 630617) B630617
theorem B420487 : Blo 417772 420487 := bstep (se 1 (by rfl) ⟨315365, by rfl⟩ : syracuseStep 420487 = 630731) B630731
theorem B420495 : Blo 417772 420495 := bstep (se 1 (by rfl) ⟨315371, by rfl⟩ : syracuseStep 420495 = 630743) B630743
theorem B420539 : Blo 417772 420539 := bstep (se 1 (by rfl) ⟨315404, by rfl⟩ : syracuseStep 420539 = 630809) B630809
theorem B3173093 : Blo 417772 3173093 := bstep (se 4 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 3173093 = 594955) B594955
theorem B420615 : Blo 417772 420615 := bstep (se 1 (by rfl) ⟨315461, by rfl⟩ : syracuseStep 420615 = 630923) B630923
theorem B420623 : Blo 417772 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B420667 : Blo 417772 420667 := bstep (se 1 (by rfl) ⟨315500, by rfl⟩ : syracuseStep 420667 = 631001) B631001
theorem B420743 : Blo 417772 420743 := bstep (se 1 (by rfl) ⟨315557, by rfl⟩ : syracuseStep 420743 = 631115) B631115
theorem B420751 : Blo 417772 420751 := bstep (se 1 (by rfl) ⟨315563, by rfl⟩ : syracuseStep 420751 = 631127) B631127
theorem B420795 : Blo 417772 420795 := bstep (se 1 (by rfl) ⟨315596, by rfl⟩ : syracuseStep 420795 = 631193) B631193
theorem B420871 : Blo 417772 420871 := bstep (se 1 (by rfl) ⟨315653, by rfl⟩ : syracuseStep 420871 = 631307) B631307
theorem B420879 : Blo 417772 420879 := bstep (se 1 (by rfl) ⟨315659, by rfl⟩ : syracuseStep 420879 = 631319) B631319
theorem B420923 : Blo 417772 420923 := bstep (se 1 (by rfl) ⟨315692, by rfl⟩ : syracuseStep 420923 = 631385) B631385
theorem B945287 : Blo 417772 945287 := bstep (se 1 (by rfl) ⟨708965, by rfl⟩ : syracuseStep 945287 = 1417931) B1417931
theorem B420999 : Blo 417772 420999 := bstep (se 1 (by rfl) ⟨315749, by rfl⟩ : syracuseStep 420999 = 631499) B631499
theorem B421007 : Blo 417772 421007 := bstep (se 1 (by rfl) ⟨315755, by rfl⟩ : syracuseStep 421007 = 631511) B631511
theorem B421051 : Blo 417772 421051 := bstep (se 1 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 421051 = 631577) B631577
theorem B421127 : Blo 417772 421127 := bstep (se 1 (by rfl) ⟨315845, by rfl⟩ : syracuseStep 421127 = 631691) B631691
theorem B421135 : Blo 417772 421135 := bstep (se 1 (by rfl) ⟨315851, by rfl⟩ : syracuseStep 421135 = 631703) B631703
theorem B2551073 : Blo 417772 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B4779323 : Blo 417772 4779323 := bstep (se 1 (by rfl) ⟨3584492, by rfl⟩ : syracuseStep 4779323 = 7168985) B7168985
theorem B2125115 : Blo 417772 2125115 := bstep (se 1 (by rfl) ⟨1593836, by rfl⟩ : syracuseStep 2125115 = 3187673) B3187673
theorem B945467 : Blo 417772 945467 := bstep (se 1 (by rfl) ⟨709100, by rfl⟩ : syracuseStep 945467 = 1418201) B1418201
theorem B421179 : Blo 417772 421179 := bstep (se 1 (by rfl) ⟨315884, by rfl⟩ : syracuseStep 421179 = 631769) B631769
theorem B421255 : Blo 417772 421255 := bstep (se 1 (by rfl) ⟨315941, by rfl⟩ : syracuseStep 421255 = 631883) B631883
theorem B421263 : Blo 417772 421263 := bstep (se 1 (by rfl) ⟨315947, by rfl⟩ : syracuseStep 421263 = 631895) B631895
theorem B945593 : Blo 417772 945593 := bstep (se 2 (by rfl) ⟨354597, by rfl⟩ : syracuseStep 945593 = 709195) B709195
theorem B421307 : Blo 417772 421307 := bstep (se 1 (by rfl) ⟨315980, by rfl⟩ : syracuseStep 421307 = 631961) B631961
theorem B2125277 : Blo 417772 2125277 := bstep (se 3 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 2125277 = 796979) B796979
theorem B421383 : Blo 417772 421383 := bstep (se 1 (by rfl) ⟨316037, by rfl⟩ : syracuseStep 421383 = 632075) B632075
theorem B421391 : Blo 417772 421391 := bstep (se 1 (by rfl) ⟨316043, by rfl⟩ : syracuseStep 421391 = 632087) B632087
theorem B421435 : Blo 417772 421435 := bstep (se 1 (by rfl) ⟨316076, by rfl⟩ : syracuseStep 421435 = 632153) B632153
theorem B421511 : Blo 417772 421511 := bstep (se 1 (by rfl) ⟨316133, by rfl⟩ : syracuseStep 421511 = 632267) B632267
theorem B421519 : Blo 417772 421519 := bstep (se 1 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 421519 = 632279) B632279
theorem B421563 : Blo 417772 421563 := bstep (se 1 (by rfl) ⟨316172, by rfl⟩ : syracuseStep 421563 = 632345) B632345
theorem B2387657 : Blo 417772 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B519943 : Blo 417772 519943 := bstep (se 1 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 519943 = 779915) B779915
theorem B421639 : Blo 417772 421639 := bstep (se 1 (by rfl) ⟨316229, by rfl⟩ : syracuseStep 421639 = 632459) B632459
theorem B945935 : Blo 417772 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B421647 : Blo 417772 421647 := bstep (se 1 (by rfl) ⟨316235, by rfl⟩ : syracuseStep 421647 = 632471) B632471
theorem B2125601 : Blo 417772 2125601 := bstep (se 2 (by rfl) ⟨797100, by rfl⟩ : syracuseStep 2125601 = 1594201) B1594201
theorem B945953 : Blo 417772 945953 := bstep (se 2 (by rfl) ⟨354732, by rfl⟩ : syracuseStep 945953 = 709465) B709465
theorem B421691 : Blo 417772 421691 := bstep (se 1 (by rfl) ⟨316268, by rfl⟩ : syracuseStep 421691 = 632537) B632537
theorem B421767 : Blo 417772 421767 := bstep (se 1 (by rfl) ⟨316325, by rfl⟩ : syracuseStep 421767 = 632651) B632651
theorem B14479307 : Blo 417772 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B847991 : Blo 417772 847991 := bstep (se 1 (by rfl) ⟨635993, by rfl⟩ : syracuseStep 847991 = 1271987) B1271987
theorem B946295 : Blo 417772 946295 := bstep (se 1 (by rfl) ⟨709721, by rfl⟩ : syracuseStep 946295 = 1419443) B1419443
theorem B1798433 : Blo 417772 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B946475 : Blo 417772 946475 := bstep (se 1 (by rfl) ⟨709856, by rfl⟩ : syracuseStep 946475 = 1419713) B1419713
theorem B946835 : Blo 417772 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B946889 : Blo 417772 946889 := bstep (se 2 (by rfl) ⟨355083, by rfl⟩ : syracuseStep 946889 = 710167) B710167
theorem B2126573 : Blo 417772 2126573 := bstep (se 3 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 2126573 = 797465) B797465
theorem B1012513 : Blo 417772 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B1209289 : Blo 417772 1209289 := bstep (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) B906967
theorem B1438921 : Blo 417772 1438921 := bstep (se 2 (by rfl) ⟨539595, by rfl⟩ : syracuseStep 1438921 = 1079191) B1079191
theorem B1013003 : Blo 417772 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B947591 : Blo 417772 947591 := bstep (se 1 (by rfl) ⟨710693, by rfl⟩ : syracuseStep 947591 = 1421387) B1421387
theorem B11859335 : Blo 417772 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B4027907 : Blo 417772 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B4552195 : Blo 417772 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B2127383 : Blo 417772 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B947771 : Blo 417772 947771 := bstep (se 1 (by rfl) ⟨710828, by rfl⟩ : syracuseStep 947771 = 1421657) B1421657
theorem B2389571 : Blo 417772 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B947897 : Blo 417772 947897 := bstep (se 2 (by rfl) ⟨355461, by rfl⟩ : syracuseStep 947897 = 710923) B710923
theorem B948239 : Blo 417772 948239 := bstep (se 1 (by rfl) ⟨711179, by rfl⟩ : syracuseStep 948239 = 1422359) B1422359
theorem B948257 : Blo 417772 948257 := bstep (se 2 (by rfl) ⟨355596, by rfl⟩ : syracuseStep 948257 = 711193) B711193
theorem B948599 : Blo 417772 948599 := bstep (se 1 (by rfl) ⟨711449, by rfl⟩ : syracuseStep 948599 = 1422899) B1422899
theorem B948779 : Blo 417772 948779 := bstep (se 1 (by rfl) ⟨711584, by rfl⟩ : syracuseStep 948779 = 1423169) B1423169
theorem B1800791 : Blo 417772 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B2062967 : Blo 417772 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B3242753 : Blo 417772 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B2259991 : Blo 417772 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B753467 : Blo 417772 753467 := bstep (se 1 (by rfl) ⟨565100, by rfl⟩ : syracuseStep 753467 = 1130201) B1130201
theorem B1507481 : Blo 417772 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B1704089 : Blo 417772 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B754375 : Blo 417772 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B3179411 : Blo 417772 3179411 := bstep (se 1 (by rfl) ⟨2384558, by rfl⟩ : syracuseStep 3179411 = 4769117) B4769117
theorem B852923 : Blo 417772 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B820187 : Blo 417772 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B15205427 : Blo 417772 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B7177733 : Blo 417772 7177733 := bstep (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) B1345825
theorem B1410695 : Blo 417772 1410695 := bstep (se 1 (by rfl) ⟨1058021, by rfl⟩ : syracuseStep 1410695 = 2116043) B2116043
theorem B2131595 : Blo 417772 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B1410749 : Blo 417772 1410749 := bstep (se 3 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 1410749 = 529031) B529031
theorem B1410911 : Blo 417772 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B3180383 : Blo 417772 3180383 := bstep (se 1 (by rfl) ⟨2385287, by rfl⟩ : syracuseStep 3180383 = 4770575) B4770575
theorem B1411073 : Blo 417772 1411073 := bstep (se 2 (by rfl) ⟨529152, by rfl⟩ : syracuseStep 1411073 = 1058305) B1058305
theorem B30771683 : Blo 417772 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B1706555 : Blo 417772 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B1411883 : Blo 417772 1411883 := bstep (se 1 (by rfl) ⟨1058912, by rfl⟩ : syracuseStep 1411883 = 2117825) B2117825
theorem B4295501 : Blo 417772 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B1412153 : Blo 417772 1412153 := bstep (se 2 (by rfl) ⟨529557, by rfl⟩ : syracuseStep 1412153 = 1059115) B1059115
theorem B5377103 : Blo 417772 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B1510595 : Blo 417772 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B756985 : Blo 417772 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B1412477 : Blo 417772 1412477 := bstep (se 3 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 1412477 = 529679) B529679
theorem B2723291 : Blo 417772 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B1281523 : Blo 417772 1281523 := bstep (se 1 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 1281523 = 1922285) B1922285
theorem B1412747 : Blo 417772 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B757691 : Blo 417772 757691 := bstep (se 1 (by rfl) ⟨568268, by rfl⟩ : syracuseStep 757691 = 1136537) B1136537
theorem B24875209 : Blo 417772 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B627119 : Blo 417772 627119 := bstep (se 1 (by rfl) ⟨470339, by rfl⟩ : syracuseStep 627119 = 940679) B940679
theorem B528859 : Blo 417772 528859 := bstep (se 1 (by rfl) ⟨396644, by rfl⟩ : syracuseStep 528859 = 793289) B793289
theorem B627209 : Blo 417772 627209 := bstep (se 2 (by rfl) ⟨235203, by rfl⟩ : syracuseStep 627209 = 470407) B470407
theorem B1413665 : Blo 417772 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B627239 : Blo 417772 627239 := bstep (se 1 (by rfl) ⟨470429, by rfl⟩ : syracuseStep 627239 = 940859) B940859
theorem B627323 : Blo 417772 627323 := bstep (se 1 (by rfl) ⟨470492, by rfl⟩ : syracuseStep 627323 = 940985) B940985
theorem B1348235 : Blo 417772 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B627449 : Blo 417772 627449 := bstep (se 2 (by rfl) ⟨235293, by rfl⟩ : syracuseStep 627449 = 470587) B470587
theorem B1413881 : Blo 417772 1413881 := bstep (se 2 (by rfl) ⟨530205, by rfl⟩ : syracuseStep 1413881 = 1060411) B1060411
theorem B627551 : Blo 417772 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B627563 : Blo 417772 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B2692061 : Blo 417772 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B2626561 : Blo 417772 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B1414151 : Blo 417772 1414151 := bstep (se 1 (by rfl) ⟨1060613, by rfl⟩ : syracuseStep 1414151 = 2121227) B2121227
theorem B693257 : Blo 417772 693257 := bstep (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) B519943
theorem B2692115 : Blo 417772 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B627791 : Blo 417772 627791 := bstep (se 1 (by rfl) ⟨470843, by rfl⟩ : syracuseStep 627791 = 941687) B941687
theorem B1414259 : Blo 417772 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B627911 : Blo 417772 627911 := bstep (se 1 (by rfl) ⟨470933, by rfl⟩ : syracuseStep 627911 = 941867) B941867
theorem B628073 : Blo 417772 628073 := bstep (se 2 (by rfl) ⟨235527, by rfl⟩ : syracuseStep 628073 = 471055) B471055
theorem B1414529 : Blo 417772 1414529 := bstep (se 2 (by rfl) ⟨530448, by rfl⟩ : syracuseStep 1414529 = 1060897) B1060897
theorem B628151 : Blo 417772 628151 := bstep (se 1 (by rfl) ⟨471113, by rfl⟩ : syracuseStep 628151 = 942227) B942227
theorem B628187 : Blo 417772 628187 := bstep (se 1 (by rfl) ⟨471140, by rfl⟩ : syracuseStep 628187 = 942281) B942281
theorem B759305 : Blo 417772 759305 := bstep (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) B569479
theorem B10163809 : Blo 417772 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B3282565 : Blo 417772 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B628655 : Blo 417772 628655 := bstep (se 1 (by rfl) ⟨471491, by rfl⟩ : syracuseStep 628655 = 942983) B942983
theorem B628745 : Blo 417772 628745 := bstep (se 2 (by rfl) ⟨235779, by rfl⟩ : syracuseStep 628745 = 471559) B471559
theorem B628775 : Blo 417772 628775 := bstep (se 1 (by rfl) ⟨471581, by rfl⟩ : syracuseStep 628775 = 943163) B943163
theorem B628859 : Blo 417772 628859 := bstep (se 1 (by rfl) ⟨471644, by rfl⟩ : syracuseStep 628859 = 943289) B943289
theorem B1415339 : Blo 417772 1415339 := bstep (se 1 (by rfl) ⟨1061504, by rfl⟩ : syracuseStep 1415339 = 2123009) B2123009
theorem B628985 : Blo 417772 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B629087 : Blo 417772 629087 := bstep (se 1 (by rfl) ⟨471815, by rfl⟩ : syracuseStep 629087 = 943631) B943631
theorem B629099 : Blo 417772 629099 := bstep (se 1 (by rfl) ⟨471824, by rfl⟩ : syracuseStep 629099 = 943649) B943649
theorem B1350017 : Blo 417772 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B5118497 : Blo 417772 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B793145 : Blo 417772 793145 := bstep (se 2 (by rfl) ⟨297429, by rfl⟩ : syracuseStep 793145 = 594859) B594859
theorem B629327 : Blo 417772 629327 := bstep (se 1 (by rfl) ⟨471995, by rfl⟩ : syracuseStep 629327 = 943991) B943991
theorem B1612385 : Blo 417772 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B1415879 : Blo 417772 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B629447 : Blo 417772 629447 := bstep (se 1 (by rfl) ⟨472085, by rfl⟩ : syracuseStep 629447 = 944171) B944171
theorem B629609 : Blo 417772 629609 := bstep (se 2 (by rfl) ⟨236103, by rfl⟩ : syracuseStep 629609 = 472207) B472207
theorem B3218359 : Blo 417772 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B629687 : Blo 417772 629687 := bstep (se 1 (by rfl) ⟨472265, by rfl⟩ : syracuseStep 629687 = 944531) B944531
theorem B629723 : Blo 417772 629723 := bstep (se 1 (by rfl) ⟨472292, by rfl⟩ : syracuseStep 629723 = 944585) B944585
theorem B1809427 : Blo 417772 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B6069593 : Blo 417772 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B630191 : Blo 417772 630191 := bstep (se 1 (by rfl) ⟨472643, by rfl⟩ : syracuseStep 630191 = 945287) B945287
theorem B630281 : Blo 417772 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B3186215 : Blo 417772 3186215 := bstep (se 1 (by rfl) ⟨2389661, by rfl⟩ : syracuseStep 3186215 = 4779323) B4779323
theorem B1416743 : Blo 417772 1416743 := bstep (se 1 (by rfl) ⟨1062557, by rfl⟩ : syracuseStep 1416743 = 2125115) B2125115
theorem B630311 : Blo 417772 630311 := bstep (se 1 (by rfl) ⟨472733, by rfl⟩ : syracuseStep 630311 = 945467) B945467
theorem B630395 : Blo 417772 630395 := bstep (se 1 (by rfl) ⟨472796, by rfl⟩ : syracuseStep 630395 = 945593) B945593
theorem B2694779 : Blo 417772 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B1416851 : Blo 417772 1416851 := bstep (se 1 (by rfl) ⟨1062638, by rfl⟩ : syracuseStep 1416851 = 2125277) B2125277
theorem B630521 : Blo 417772 630521 := bstep (se 2 (by rfl) ⟨236445, by rfl⟩ : syracuseStep 630521 = 472891) B472891
theorem B630623 : Blo 417772 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B1417067 : Blo 417772 1417067 := bstep (se 1 (by rfl) ⟨1062800, by rfl⟩ : syracuseStep 1417067 = 2125601) B2125601
theorem B630635 : Blo 417772 630635 := bstep (se 1 (by rfl) ⟨472976, by rfl⟩ : syracuseStep 630635 = 945953) B945953
theorem B1417121 : Blo 417772 1417121 := bstep (se 2 (by rfl) ⟨531420, by rfl⟩ : syracuseStep 1417121 = 1062841) B1062841
theorem B565327 : Blo 417772 565327 := bstep (se 1 (by rfl) ⟨423995, by rfl⟩ : syracuseStep 565327 = 847991) B847991
theorem B630863 : Blo 417772 630863 := bstep (se 1 (by rfl) ⟨473147, by rfl⟩ : syracuseStep 630863 = 946295) B946295
theorem B794747 : Blo 417772 794747 := bstep (se 1 (by rfl) ⟨596060, by rfl⟩ : syracuseStep 794747 = 1192121) B1192121
theorem B16425109 : Blo 417772 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B630983 : Blo 417772 630983 := bstep (se 1 (by rfl) ⟨473237, by rfl⟩ : syracuseStep 630983 = 946475) B946475
theorem B598367 : Blo 417772 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B631145 : Blo 417772 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B631223 : Blo 417772 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B532919 : Blo 417772 532919 := bstep (se 1 (by rfl) ⟨399689, by rfl⟩ : syracuseStep 532919 = 799379) B799379
theorem B631259 : Blo 417772 631259 := bstep (se 1 (by rfl) ⟨473444, by rfl⟩ : syracuseStep 631259 = 946889) B946889
theorem B1417715 : Blo 417772 1417715 := bstep (se 1 (by rfl) ⟨1063286, by rfl⟩ : syracuseStep 1417715 = 2126573) B2126573
theorem B533071 : Blo 417772 533071 := bstep (se 1 (by rfl) ⟨399803, by rfl⟩ : syracuseStep 533071 = 799607) B799607
theorem B795233 : Blo 417772 795233 := bstep (se 2 (by rfl) ⟨298212, by rfl⟩ : syracuseStep 795233 = 596425) B596425
theorem B6038225 : Blo 417772 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B1057495 : Blo 417772 1057495 := bstep (se 1 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 1057495 = 1586243) B1586243
theorem B631727 : Blo 417772 631727 := bstep (se 1 (by rfl) ⟨473795, by rfl⟩ : syracuseStep 631727 = 947591) B947591
theorem B7906223 : Blo 417772 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B795575 : Blo 417772 795575 := bstep (se 1 (by rfl) ⟨596681, by rfl⟩ : syracuseStep 795575 = 1193363) B1193363
theorem B1057799 : Blo 417772 1057799 := bstep (se 1 (by rfl) ⟨793349, by rfl⟩ : syracuseStep 1057799 = 1586699) B1586699
theorem B631817 : Blo 417772 631817 := bstep (se 2 (by rfl) ⟨236931, by rfl⟩ : syracuseStep 631817 = 473863) B473863
theorem B1418255 : Blo 417772 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B631847 : Blo 417772 631847 := bstep (se 1 (by rfl) ⟨473885, by rfl⟩ : syracuseStep 631847 = 947771) B947771
theorem B631931 : Blo 417772 631931 := bstep (se 1 (by rfl) ⟨473948, by rfl⟩ : syracuseStep 631931 = 947897) B947897
theorem B632057 : Blo 417772 632057 := bstep (se 2 (by rfl) ⟨237021, by rfl⟩ : syracuseStep 632057 = 474043) B474043
theorem B795977 : Blo 417772 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B632159 : Blo 417772 632159 := bstep (se 1 (by rfl) ⟨474119, by rfl⟩ : syracuseStep 632159 = 948239) B948239
theorem B632171 : Blo 417772 632171 := bstep (se 1 (by rfl) ⟨474128, by rfl⟩ : syracuseStep 632171 = 948257) B948257
theorem B632399 : Blo 417772 632399 := bstep (se 1 (by rfl) ⟨474299, by rfl⟩ : syracuseStep 632399 = 948599) B948599
theorem B1418849 : Blo 417772 1418849 := bstep (se 2 (by rfl) ⟨532068, by rfl⟩ : syracuseStep 1418849 = 1064137) B1064137
theorem B632519 : Blo 417772 632519 := bstep (se 1 (by rfl) ⟨474389, by rfl⟩ : syracuseStep 632519 = 948779) B948779
theorem B1189819 : Blo 417772 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B796691 : Blo 417772 796691 := bstep (se 1 (by rfl) ⟨597518, by rfl⟩ : syracuseStep 796691 = 1195037) B1195037
theorem B796729 : Blo 417772 796729 := bstep (se 2 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 796729 = 597547) B597547
theorem B2009245 : Blo 417772 2009245 := bstep (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) B753467
theorem B8202583 : Blo 417772 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B797033 : Blo 417772 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B3811873 : Blo 417772 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B1518497 : Blo 417772 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B1420307 : Blo 417772 1420307 := bstep (se 1 (by rfl) ⟨1065230, by rfl⟩ : syracuseStep 1420307 = 2130461) B2130461
theorem B1911887 : Blo 417772 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B2698393 : Blo 417772 2698393 := bstep (se 2 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 2698393 = 2023795) B2023795
theorem B2010359 : Blo 417772 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B1060087 : Blo 417772 1060087 := bstep (se 1 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 1060087 = 1590131) B1590131
theorem B4304119 : Blo 417772 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B1420631 : Blo 417772 1420631 := bstep (se 1 (by rfl) ⟨1065473, by rfl⟩ : syracuseStep 1420631 = 2130947) B2130947
theorem B1060361 : Blo 417772 1060361 := bstep (se 2 (by rfl) ⟨397635, by rfl⟩ : syracuseStep 1060361 = 795271) B795271
theorem B1191449 : Blo 417772 1191449 := bstep (se 2 (by rfl) ⟨446793, by rfl⟩ : syracuseStep 1191449 = 893587) B893587
theorem B1060391 : Blo 417772 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B503335 : Blo 417772 503335 := bstep (se 1 (by rfl) ⟨377501, by rfl⟩ : syracuseStep 503335 = 755003) B755003
theorem B798331 : Blo 417772 798331 := bstep (se 1 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 798331 = 1197497) B1197497
theorem B2272967 : Blo 417772 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B798407 : Blo 417772 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B3354463 : Blo 417772 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B1060715 : Blo 417772 1060715 := bstep (se 1 (by rfl) ⟨795536, by rfl⟩ : syracuseStep 1060715 = 1591073) B1591073
theorem B798817 : Blo 417772 798817 := bstep (se 2 (by rfl) ⟨299556, by rfl⟩ : syracuseStep 798817 = 599113) B599113
theorem B471163 : Blo 417772 471163 := bstep (se 1 (by rfl) ⟨353372, by rfl⟩ : syracuseStep 471163 = 706745) B706745
theorem B1421711 : Blo 417772 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B799159 : Blo 417772 799159 := bstep (se 1 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 799159 = 1198739) B1198739
theorem B1061363 : Blo 417772 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B471631 : Blo 417772 471631 := bstep (se 1 (by rfl) ⟨353723, by rfl⟩ : syracuseStep 471631 = 707447) B707447
theorem B1422035 : Blo 417772 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B9679661 : Blo 417772 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B799561 : Blo 417772 799561 := bstep (se 2 (by rfl) ⟨299835, by rfl⟩ : syracuseStep 799561 = 599671) B599671
theorem B4043627 : Blo 417772 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B1061819 : Blo 417772 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B635867 : Blo 417772 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B472027 : Blo 417772 472027 := bstep (se 1 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 472027 = 708041) B708041
theorem B4371421 : Blo 417772 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B898447 : Blo 417772 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B472495 : Blo 417772 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B800275 : Blo 417772 800275 := bstep (se 1 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 800275 = 1200413) B1200413
theorem B1062497 : Blo 417772 1062497 := bstep (se 2 (by rfl) ⟨398436, by rfl⟩ : syracuseStep 1062497 = 796873) B796873
theorem B1586897 : Blo 417772 1586897 := bstep (se 2 (by rfl) ⟨595086, by rfl⟩ : syracuseStep 1586897 = 1190173) B1190173
theorem B472927 : Blo 417772 472927 := bstep (se 1 (by rfl) ⟨354695, by rfl⟩ : syracuseStep 472927 = 709391) B709391
theorem B800617 : Blo 417772 800617 := bstep (se 2 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 800617 = 600463) B600463
theorem B3389303 : Blo 417772 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B1423223 : Blo 417772 1423223 := bstep (se 1 (by rfl) ⟨1067417, by rfl⟩ : syracuseStep 1423223 = 2134835) B2134835
theorem B1587215 : Blo 417772 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B1423439 : Blo 417772 1423439 := bstep (se 1 (by rfl) ⟨1067579, by rfl⟩ : syracuseStep 1423439 = 2135159) B2135159
theorem B473287 : Blo 417772 473287 := bstep (se 1 (by rfl) ⟨354965, by rfl⟩ : syracuseStep 473287 = 709931) B709931
theorem B5355827 : Blo 417772 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B1194365 : Blo 417772 1194365 := bstep (se 3 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 1194365 = 447887) B447887
theorem B1194695 : Blo 417772 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B1620695 : Blo 417772 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B1063955 : Blo 417772 1063955 := bstep (se 1 (by rfl) ⟨797966, by rfl⟩ : syracuseStep 1063955 = 1595933) B1595933
theorem B474151 : Blo 417772 474151 := bstep (se 1 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 474151 = 711227) B711227
theorem B1162297 : Blo 417772 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B2276599 : Blo 417772 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B4799735 : Blo 417772 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B1359191 : Blo 417772 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B1064411 : Blo 417772 1064411 := bstep (se 1 (by rfl) ⟨798308, by rfl⟩ : syracuseStep 1064411 = 1596617) B1596617
theorem B3587773 : Blo 417772 3587773 := bstep (se 3 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 3587773 = 1345415) B1345415
theorem B6438689 : Blo 417772 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B1196039 : Blo 417772 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B1589327 : Blo 417772 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B1196279 : Blo 417772 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B2015549 : Blo 417772 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B639497 : Blo 417772 639497 := bstep (se 2 (by rfl) ⟨239811, by rfl⟩ : syracuseStep 639497 = 479623) B479623
theorem B1065595 : Blo 417772 1065595 := bstep (se 1 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 1065595 = 1598393) B1598393
theorem B672619 : Blo 417772 672619 := bstep (se 1 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 672619 = 1008929) B1008929
theorem B3097871 : Blo 417772 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B705935 : Blo 417772 705935 := bstep (se 1 (by rfl) ⟨529451, by rfl⟩ : syracuseStep 705935 = 1058903) B1058903
theorem B1131995 : Blo 417772 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1918561 : Blo 417772 1918561 := bstep (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) B1438921
theorem B706171 : Blo 417772 706171 := bstep (se 1 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 706171 = 1059257) B1059257
theorem B2115395 : Blo 417772 2115395 := bstep (se 1 (by rfl) ⟨1586546, by rfl⟩ : syracuseStep 2115395 = 3173093) B3173093
theorem B673849 : Blo 417772 673849 := bstep (se 2 (by rfl) ⟨252693, by rfl⟩ : syracuseStep 673849 = 505387) B505387
theorem B707035 : Blo 417772 707035 := bstep (se 1 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 707035 = 1060553) B1060553
theorem B1591771 : Blo 417772 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B2017817 : Blo 417772 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B9652871 : Blo 417772 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B1198921 : Blo 417772 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1198955 : Blo 417772 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B1362863 : Blo 417772 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B3197879 : Blo 417772 3197879 := bstep (se 1 (by rfl) ⟨2398409, by rfl⟩ : syracuseStep 3197879 = 4796819) B4796819
theorem B707663 : Blo 417772 707663 := bstep (se 1 (by rfl) ⟨530747, by rfl⟩ : syracuseStep 707663 = 1061495) B1061495
theorem B6802861 : Blo 417772 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B675335 : Blo 417772 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B1593017 : Blo 417772 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B1593047 : Blo 417772 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B708527 : Blo 417772 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B3592421 : Blo 417772 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B708959 : Blo 417772 708959 := bstep (se 1 (by rfl) ⟨531719, by rfl⟩ : syracuseStep 708959 = 1063439) B1063439
theorem B3199337 : Blo 417772 3199337 := bstep (se 2 (by rfl) ⟨1199751, by rfl⟩ : syracuseStep 3199337 = 2399503) B2399503
theorem B1200527 : Blo 417772 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B5100205 : Blo 417772 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B2118473 : Blo 417772 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B709519 : Blo 417772 709519 := bstep (se 1 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 709519 = 1064279) B1064279
theorem B23287175 : Blo 417772 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B3233267 : Blo 417772 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B710201 : Blo 417772 710201 := bstep (se 2 (by rfl) ⟨266325, by rfl⟩ : syracuseStep 710201 = 532651) B532651
theorem B1365643 : Blo 417772 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B5363617 : Blo 417772 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B2119769 : Blo 417772 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B710903 : Blo 417772 710903 := bstep (se 1 (by rfl) ⟨533177, by rfl⟩ : syracuseStep 710903 = 1066355) B1066355
theorem B3201281 : Blo 417772 3201281 := bstep (se 2 (by rfl) ⟨1200480, by rfl⟩ : syracuseStep 3201281 = 2400961) B2400961
theorem B1595659 : Blo 417772 1595659 := bstep (se 1 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 1595659 = 2393489) B2393489
theorem B3889457 : Blo 417772 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1137001 : Blo 417772 1137001 := bstep (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) B852751
theorem B940553 : Blo 417772 940553 := bstep (se 2 (by rfl) ⟨352707, by rfl⟩ : syracuseStep 940553 = 705415) B705415
theorem B1595963 : Blo 417772 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B711247 : Blo 417772 711247 := bstep (se 1 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 711247 = 1066871) B1066871
theorem B711497 : Blo 417772 711497 := bstep (se 2 (by rfl) ⟨266811, by rfl⟩ : syracuseStep 711497 = 533623) B533623
theorem B940895 : Blo 417772 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B941075 : Blo 417772 941075 := bstep (se 1 (by rfl) ⟨705806, by rfl⟩ : syracuseStep 941075 = 1411613) B1411613
theorem B12082445 : Blo 417772 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B941417 : Blo 417772 941417 := bstep (se 2 (by rfl) ⟨353031, by rfl⟩ : syracuseStep 941417 = 706063) B706063
theorem B19946933 : Blo 417772 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B98557397 : Blo 417772 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B1597117 : Blo 417772 1597117 := bstep (se 3 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 1597117 = 598919) B598919
theorem B1695431 : Blo 417772 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B1793735 : Blo 417772 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B1793785 : Blo 417772 1793785 := bstep (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) B1345339
theorem B679753 : Blo 417772 679753 := bstep (se 2 (by rfl) ⟨254907, by rfl⟩ : syracuseStep 679753 = 509815) B509815
theorem B942011 : Blo 417772 942011 := bstep (se 1 (by rfl) ⟨706508, by rfl⟩ : syracuseStep 942011 = 1413017) B1413017
theorem B417831 : Blo 417772 417831 := bstep (se 1 (by rfl) ⟨313373, by rfl⟩ : syracuseStep 417831 = 626747) B626747
theorem B942137 : Blo 417772 942137 := bstep (se 2 (by rfl) ⟨353301, by rfl⟩ : syracuseStep 942137 = 706603) B706603
theorem B417871 : Blo 417772 417871 := bstep (se 1 (by rfl) ⟨313403, by rfl⟩ : syracuseStep 417871 = 626807) B626807
theorem B417887 : Blo 417772 417887 := bstep (se 1 (by rfl) ⟨313415, by rfl⟩ : syracuseStep 417887 = 626831) B626831
theorem B417915 : Blo 417772 417915 := bstep (se 1 (by rfl) ⟨313436, by rfl⟩ : syracuseStep 417915 = 626873) B626873
theorem B417967 : Blo 417772 417967 := bstep (se 1 (by rfl) ⟨313475, by rfl⟩ : syracuseStep 417967 = 626951) B626951
theorem B417991 : Blo 417772 417991 := bstep (se 1 (by rfl) ⟨313493, by rfl⟩ : syracuseStep 417991 = 626987) B626987
theorem B418011 : Blo 417772 418011 := bstep (se 1 (by rfl) ⟨313508, by rfl⟩ : syracuseStep 418011 = 627017) B627017
theorem B418087 : Blo 417772 418087 := bstep (se 1 (by rfl) ⟨313565, by rfl⟩ : syracuseStep 418087 = 627131) B627131
theorem B418127 : Blo 417772 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B418143 : Blo 417772 418143 := bstep (se 1 (by rfl) ⟨313607, by rfl⟩ : syracuseStep 418143 = 627215) B627215
theorem B418171 : Blo 417772 418171 := bstep (se 1 (by rfl) ⟨313628, by rfl⟩ : syracuseStep 418171 = 627257) B627257
theorem B942479 : Blo 417772 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B418223 : Blo 417772 418223 := bstep (se 1 (by rfl) ⟨313667, by rfl⟩ : syracuseStep 418223 = 627335) B627335
theorem B418247 : Blo 417772 418247 := bstep (se 1 (by rfl) ⟨313685, by rfl⟩ : syracuseStep 418247 = 627371) B627371
theorem B418267 : Blo 417772 418267 := bstep (se 1 (by rfl) ⟨313700, by rfl⟩ : syracuseStep 418267 = 627401) B627401
theorem B418343 : Blo 417772 418343 := bstep (se 1 (by rfl) ⟨313757, by rfl⟩ : syracuseStep 418343 = 627515) B627515
theorem B418383 : Blo 417772 418383 := bstep (se 1 (by rfl) ⟨313787, by rfl⟩ : syracuseStep 418383 = 627575) B627575
theorem B418399 : Blo 417772 418399 := bstep (se 1 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 418399 = 627599) B627599
theorem B418427 : Blo 417772 418427 := bstep (se 1 (by rfl) ⟨313820, by rfl⟩ : syracuseStep 418427 = 627641) B627641
theorem B1598075 : Blo 417772 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B418479 : Blo 417772 418479 := bstep (se 1 (by rfl) ⟨313859, by rfl⟩ : syracuseStep 418479 = 627719) B627719
theorem B418503 : Blo 417772 418503 := bstep (se 1 (by rfl) ⟨313877, by rfl⟩ : syracuseStep 418503 = 627755) B627755
theorem B484039 : Blo 417772 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B3400393 : Blo 417772 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B942803 : Blo 417772 942803 := bstep (se 1 (by rfl) ⟨707102, by rfl⟩ : syracuseStep 942803 = 1414205) B1414205
theorem B418523 : Blo 417772 418523 := bstep (se 1 (by rfl) ⟨313892, by rfl⟩ : syracuseStep 418523 = 627785) B627785
theorem B418599 : Blo 417772 418599 := bstep (se 1 (by rfl) ⟨313949, by rfl⟩ : syracuseStep 418599 = 627899) B627899
theorem B418639 : Blo 417772 418639 := bstep (se 1 (by rfl) ⟨313979, by rfl⟩ : syracuseStep 418639 = 627959) B627959
theorem B418655 : Blo 417772 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B418683 : Blo 417772 418683 := bstep (se 1 (by rfl) ⟨314012, by rfl⟩ : syracuseStep 418683 = 628025) B628025
theorem B418735 : Blo 417772 418735 := bstep (se 1 (by rfl) ⟨314051, by rfl⟩ : syracuseStep 418735 = 628103) B628103
theorem B10216367 : Blo 417772 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B418759 : Blo 417772 418759 := bstep (se 1 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 418759 = 628139) B628139
theorem B418779 : Blo 417772 418779 := bstep (se 1 (by rfl) ⟨314084, by rfl⟩ : syracuseStep 418779 = 628169) B628169
theorem B418855 : Blo 417772 418855 := bstep (se 1 (by rfl) ⟨314141, by rfl⟩ : syracuseStep 418855 = 628283) B628283
theorem B418895 : Blo 417772 418895 := bstep (se 1 (by rfl) ⟨314171, by rfl⟩ : syracuseStep 418895 = 628343) B628343
theorem B418911 : Blo 417772 418911 := bstep (se 1 (by rfl) ⟨314183, by rfl⟩ : syracuseStep 418911 = 628367) B628367
theorem B418939 : Blo 417772 418939 := bstep (se 1 (by rfl) ⟨314204, by rfl⟩ : syracuseStep 418939 = 628409) B628409
theorem B2155673 : Blo 417772 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B418991 : Blo 417772 418991 := bstep (se 1 (by rfl) ⟨314243, by rfl⟩ : syracuseStep 418991 = 628487) B628487
theorem B419015 : Blo 417772 419015 := bstep (se 1 (by rfl) ⟨314261, by rfl⟩ : syracuseStep 419015 = 628523) B628523
theorem B419035 : Blo 417772 419035 := bstep (se 1 (by rfl) ⟨314276, by rfl⟩ : syracuseStep 419035 = 628553) B628553
theorem B419111 : Blo 417772 419111 := bstep (se 1 (by rfl) ⟨314333, by rfl⟩ : syracuseStep 419111 = 628667) B628667
theorem B419151 : Blo 417772 419151 := bstep (se 1 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 419151 = 628727) B628727
theorem B419167 : Blo 417772 419167 := bstep (se 1 (by rfl) ⟨314375, by rfl⟩ : syracuseStep 419167 = 628751) B628751
theorem B419195 : Blo 417772 419195 := bstep (se 1 (by rfl) ⟨314396, by rfl⟩ : syracuseStep 419195 = 628793) B628793
theorem B1598849 : Blo 417772 1598849 := bstep (se 2 (by rfl) ⟨599568, by rfl⟩ : syracuseStep 1598849 = 1199137) B1199137
theorem B4023715 : Blo 417772 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B419247 : Blo 417772 419247 := bstep (se 1 (by rfl) ⟨314435, by rfl⟩ : syracuseStep 419247 = 628871) B628871
theorem B419271 : Blo 417772 419271 := bstep (se 1 (by rfl) ⟨314453, by rfl⟩ : syracuseStep 419271 = 628907) B628907
theorem B419291 : Blo 417772 419291 := bstep (se 1 (by rfl) ⟨314468, by rfl⟩ : syracuseStep 419291 = 628937) B628937
theorem B419367 : Blo 417772 419367 := bstep (se 1 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 419367 = 629051) B629051
theorem B419407 : Blo 417772 419407 := bstep (se 1 (by rfl) ⟨314555, by rfl⟩ : syracuseStep 419407 = 629111) B629111
theorem B419423 : Blo 417772 419423 := bstep (se 1 (by rfl) ⟨314567, by rfl⟩ : syracuseStep 419423 = 629135) B629135
theorem B943739 : Blo 417772 943739 := bstep (se 1 (by rfl) ⟨707804, by rfl⟩ : syracuseStep 943739 = 1415609) B1415609
theorem B419451 : Blo 417772 419451 := bstep (se 1 (by rfl) ⟨314588, by rfl⟩ : syracuseStep 419451 = 629177) B629177
theorem B419503 : Blo 417772 419503 := bstep (se 1 (by rfl) ⟨314627, by rfl⟩ : syracuseStep 419503 = 629255) B629255
theorem B419527 : Blo 417772 419527 := bstep (se 1 (by rfl) ⟨314645, by rfl⟩ : syracuseStep 419527 = 629291) B629291
theorem B419547 : Blo 417772 419547 := bstep (se 1 (by rfl) ⟨314660, by rfl⟩ : syracuseStep 419547 = 629321) B629321
theorem B943865 : Blo 417772 943865 := bstep (se 2 (by rfl) ⟨353949, by rfl⟩ : syracuseStep 943865 = 707899) B707899
theorem B419623 : Blo 417772 419623 := bstep (se 1 (by rfl) ⟨314717, by rfl⟩ : syracuseStep 419623 = 629435) B629435
theorem B419663 : Blo 417772 419663 := bstep (se 1 (by rfl) ⟨314747, by rfl⟩ : syracuseStep 419663 = 629495) B629495
theorem B419679 : Blo 417772 419679 := bstep (se 1 (by rfl) ⟨314759, by rfl⟩ : syracuseStep 419679 = 629519) B629519
theorem B419707 : Blo 417772 419707 := bstep (se 1 (by rfl) ⟨314780, by rfl⟩ : syracuseStep 419707 = 629561) B629561
theorem B419759 : Blo 417772 419759 := bstep (se 1 (by rfl) ⟨314819, by rfl⟩ : syracuseStep 419759 = 629639) B629639
theorem B419783 : Blo 417772 419783 := bstep (se 1 (by rfl) ⟨314837, by rfl⟩ : syracuseStep 419783 = 629675) B629675
theorem B419803 : Blo 417772 419803 := bstep (se 1 (by rfl) ⟨314852, by rfl⟩ : syracuseStep 419803 = 629705) B629705
theorem B944135 : Blo 417772 944135 := bstep (se 1 (by rfl) ⟨708101, by rfl⟩ : syracuseStep 944135 = 1416203) B1416203
theorem B419879 : Blo 417772 419879 := bstep (se 1 (by rfl) ⟨314909, by rfl⟩ : syracuseStep 419879 = 629819) B629819
theorem B944207 : Blo 417772 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B419919 : Blo 417772 419919 := bstep (se 1 (by rfl) ⟨314939, by rfl⟩ : syracuseStep 419919 = 629879) B629879
theorem B419935 : Blo 417772 419935 := bstep (se 1 (by rfl) ⟨314951, by rfl⟩ : syracuseStep 419935 = 629903) B629903
theorem B9168997 : Blo 417772 9168997 := bstep (se 4 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 9168997 = 1719187) B1719187
theorem B419963 : Blo 417772 419963 := bstep (se 1 (by rfl) ⟨314972, by rfl⟩ : syracuseStep 419963 = 629945) B629945
theorem B1435805 : Blo 417772 1435805 := bstep (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) B538427
theorem B420015 : Blo 417772 420015 := bstep (se 1 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 420015 = 630023) B630023
theorem B420039 : Blo 417772 420039 := bstep (se 1 (by rfl) ⟨315029, by rfl⟩ : syracuseStep 420039 = 630059) B630059
theorem B420059 : Blo 417772 420059 := bstep (se 1 (by rfl) ⟨315044, by rfl⟩ : syracuseStep 420059 = 630089) B630089
theorem B420135 : Blo 417772 420135 := bstep (se 1 (by rfl) ⟨315101, by rfl⟩ : syracuseStep 420135 = 630203) B630203
theorem B420175 : Blo 417772 420175 := bstep (se 1 (by rfl) ⟨315131, by rfl⟩ : syracuseStep 420175 = 630263) B630263
theorem B452959 : Blo 417772 452959 := bstep (se 1 (by rfl) ⟨339719, by rfl⟩ : syracuseStep 452959 = 679439) B679439
theorem B420191 : Blo 417772 420191 := bstep (se 1 (by rfl) ⟨315143, by rfl⟩ : syracuseStep 420191 = 630287) B630287
theorem B420219 : Blo 417772 420219 := bstep (se 1 (by rfl) ⟨315164, by rfl⟩ : syracuseStep 420219 = 630329) B630329
theorem B420271 : Blo 417772 420271 := bstep (se 1 (by rfl) ⟨315203, by rfl⟩ : syracuseStep 420271 = 630407) B630407
theorem B420295 : Blo 417772 420295 := bstep (se 1 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 420295 = 630443) B630443
theorem B944603 : Blo 417772 944603 := bstep (se 1 (by rfl) ⟨708452, by rfl⟩ : syracuseStep 944603 = 1416905) B1416905
theorem B420315 : Blo 417772 420315 := bstep (se 1 (by rfl) ⟨315236, by rfl⟩ : syracuseStep 420315 = 630473) B630473
theorem B6777377 : Blo 417772 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B1600033 : Blo 417772 1600033 := bstep (se 2 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 1600033 = 1200025) B1200025
theorem B420391 : Blo 417772 420391 := bstep (se 1 (by rfl) ⟨315293, by rfl⟩ : syracuseStep 420391 = 630587) B630587
theorem B2026043 : Blo 417772 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B420431 : Blo 417772 420431 := bstep (se 1 (by rfl) ⟨315323, by rfl⟩ : syracuseStep 420431 = 630647) B630647
theorem B420447 : Blo 417772 420447 := bstep (se 1 (by rfl) ⟨315335, by rfl⟩ : syracuseStep 420447 = 630671) B630671
theorem B420475 : Blo 417772 420475 := bstep (se 1 (by rfl) ⟨315356, by rfl⟩ : syracuseStep 420475 = 630713) B630713
theorem B420527 : Blo 417772 420527 := bstep (se 1 (by rfl) ⟨315395, by rfl⟩ : syracuseStep 420527 = 630791) B630791
theorem B420551 : Blo 417772 420551 := bstep (se 1 (by rfl) ⟨315413, by rfl⟩ : syracuseStep 420551 = 630827) B630827
theorem B420571 : Blo 417772 420571 := bstep (se 1 (by rfl) ⟨315428, by rfl⟩ : syracuseStep 420571 = 630857) B630857
theorem B420647 : Blo 417772 420647 := bstep (se 1 (by rfl) ⟨315485, by rfl⟩ : syracuseStep 420647 = 630971) B630971
theorem B420687 : Blo 417772 420687 := bstep (se 1 (by rfl) ⟨315515, by rfl⟩ : syracuseStep 420687 = 631031) B631031
theorem B420703 : Blo 417772 420703 := bstep (se 1 (by rfl) ⟨315527, by rfl⟩ : syracuseStep 420703 = 631055) B631055
theorem B2681707 : Blo 417772 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B420731 : Blo 417772 420731 := bstep (se 1 (by rfl) ⟨315548, by rfl⟩ : syracuseStep 420731 = 631097) B631097
theorem B945071 : Blo 417772 945071 := bstep (se 1 (by rfl) ⟨708803, by rfl⟩ : syracuseStep 945071 = 1417607) B1417607
theorem B420783 : Blo 417772 420783 := bstep (se 1 (by rfl) ⟨315587, by rfl⟩ : syracuseStep 420783 = 631175) B631175
theorem B420807 : Blo 417772 420807 := bstep (se 1 (by rfl) ⟨315605, by rfl⟩ : syracuseStep 420807 = 631211) B631211
theorem B420827 : Blo 417772 420827 := bstep (se 1 (by rfl) ⟨315620, by rfl⟩ : syracuseStep 420827 = 631241) B631241
theorem B1600519 : Blo 417772 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B420903 : Blo 417772 420903 := bstep (se 1 (by rfl) ⟨315677, by rfl⟩ : syracuseStep 420903 = 631355) B631355
theorem B420943 : Blo 417772 420943 := bstep (se 1 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 420943 = 631415) B631415
theorem B420959 : Blo 417772 420959 := bstep (se 1 (by rfl) ⟨315719, by rfl⟩ : syracuseStep 420959 = 631439) B631439
theorem B5368949 : Blo 417772 5368949 := bstep (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) B503339
theorem B420987 : Blo 417772 420987 := bstep (se 1 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 420987 = 631481) B631481
theorem B2124953 : Blo 417772 2124953 := bstep (se 2 (by rfl) ⟨796857, by rfl⟩ : syracuseStep 2124953 = 1593715) B1593715
theorem B945323 : Blo 417772 945323 := bstep (se 1 (by rfl) ⟨708992, by rfl⟩ : syracuseStep 945323 = 1417985) B1417985
theorem B421039 : Blo 417772 421039 := bstep (se 1 (by rfl) ⟨315779, by rfl⟩ : syracuseStep 421039 = 631559) B631559
theorem B421063 : Blo 417772 421063 := bstep (se 1 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 421063 = 631595) B631595
theorem B3173579 : Blo 417772 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B421083 : Blo 417772 421083 := bstep (se 1 (by rfl) ⟨315812, by rfl⟩ : syracuseStep 421083 = 631625) B631625
theorem B421159 : Blo 417772 421159 := bstep (se 1 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 421159 = 631739) B631739
theorem B421199 : Blo 417772 421199 := bstep (se 1 (by rfl) ⟨315899, by rfl⟩ : syracuseStep 421199 = 631799) B631799
theorem B1699159 : Blo 417772 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B421215 : Blo 417772 421215 := bstep (se 1 (by rfl) ⟨315911, by rfl⟩ : syracuseStep 421215 = 631823) B631823
theorem B421243 : Blo 417772 421243 := bstep (se 1 (by rfl) ⟨315932, by rfl⟩ : syracuseStep 421243 = 631865) B631865
theorem B421295 : Blo 417772 421295 := bstep (se 1 (by rfl) ⟨315971, by rfl⟩ : syracuseStep 421295 = 631943) B631943
theorem B421319 : Blo 417772 421319 := bstep (se 1 (by rfl) ⟨315989, by rfl⟩ : syracuseStep 421319 = 631979) B631979
theorem B44330453 : Blo 417772 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B421339 : Blo 417772 421339 := bstep (se 1 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 421339 = 632009) B632009
theorem B1601005 : Blo 417772 1601005 := bstep (se 3 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 1601005 = 600377) B600377
theorem B421415 : Blo 417772 421415 := bstep (se 1 (by rfl) ⟨316061, by rfl⟩ : syracuseStep 421415 = 632123) B632123
theorem B421455 : Blo 417772 421455 := bstep (se 1 (by rfl) ⟨316091, by rfl⟩ : syracuseStep 421455 = 632183) B632183
theorem B421471 : Blo 417772 421471 := bstep (se 1 (by rfl) ⟨316103, by rfl⟩ : syracuseStep 421471 = 632207) B632207
theorem B421499 : Blo 417772 421499 := bstep (se 1 (by rfl) ⟨316124, by rfl⟩ : syracuseStep 421499 = 632249) B632249
theorem B421551 : Blo 417772 421551 := bstep (se 1 (by rfl) ⟨316163, by rfl⟩ : syracuseStep 421551 = 632327) B632327
theorem B1633991 : Blo 417772 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B945863 : Blo 417772 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B421575 : Blo 417772 421575 := bstep (se 1 (by rfl) ⟨316181, by rfl⟩ : syracuseStep 421575 = 632363) B632363
theorem B421595 : Blo 417772 421595 := bstep (se 1 (by rfl) ⟨316196, by rfl⟩ : syracuseStep 421595 = 632393) B632393
theorem B1601309 : Blo 417772 1601309 := bstep (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) B600491
theorem B421671 : Blo 417772 421671 := bstep (se 1 (by rfl) ⟨316253, by rfl⟩ : syracuseStep 421671 = 632507) B632507
theorem B421711 : Blo 417772 421711 := bstep (se 1 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 421711 = 632567) B632567
theorem B1699679 : Blo 417772 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B421727 : Blo 417772 421727 := bstep (se 1 (by rfl) ⟨316295, by rfl⟩ : syracuseStep 421727 = 632591) B632591
theorem B421755 : Blo 417772 421755 := bstep (se 1 (by rfl) ⟨316316, by rfl⟩ : syracuseStep 421755 = 632633) B632633
theorem B12283811 : Blo 417772 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B1798159 : Blo 417772 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B5501245 : Blo 417772 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B717161 : Blo 417772 717161 := bstep (se 2 (by rfl) ⟨268935, by rfl⟩ : syracuseStep 717161 = 537871) B537871
theorem B1339777 : Blo 417772 1339777 := bstep (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) B1004833
theorem B946727 : Blo 417772 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B5403347 : Blo 417772 5403347 := bstep (se 1 (by rfl) ⟨4052510, by rfl⟩ : syracuseStep 5403347 = 8105021) B8105021
theorem B947051 : Blo 417772 947051 := bstep (se 1 (by rfl) ⟨710288, by rfl⟩ : syracuseStep 947051 = 1420577) B1420577
theorem B947105 : Blo 417772 947105 := bstep (se 2 (by rfl) ⟨355164, by rfl⟩ : syracuseStep 947105 = 710329) B710329
theorem B947447 : Blo 417772 947447 := bstep (se 1 (by rfl) ⟨710585, by rfl⟩ : syracuseStep 947447 = 1421171) B1421171
theorem B948041 : Blo 417772 948041 := bstep (se 2 (by rfl) ⟨355515, by rfl⟩ : syracuseStep 948041 = 711031) B711031
theorem B2685271 : Blo 417772 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B948833 : Blo 417772 948833 := bstep (se 2 (by rfl) ⟨355812, by rfl⟩ : syracuseStep 948833 = 711625) B711625
theorem B2161337 : Blo 417772 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B3013321 : Blo 417772 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B818255 : Blo 417772 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B2161835 : Blo 417772 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B2260163 : Blo 417772 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1212335 : Blo 417772 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B753769 : Blo 417772 753769 := bstep (se 2 (by rfl) ⟨282663, by rfl⟩ : syracuseStep 753769 = 565327) B565327
theorem B1343699 : Blo 417772 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B426331 : Blo 417772 426331 := bstep (se 1 (by rfl) ⟨319748, by rfl⟩ : syracuseStep 426331 = 639497) B639497
theorem B2065247 : Blo 417772 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1409993 : Blo 417772 1409993 := bstep (se 2 (by rfl) ⟨528747, by rfl⟩ : syracuseStep 1409993 = 1057495) B1057495
theorem B4785155 : Blo 417772 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B1410263 : Blo 417772 1410263 := bstep (se 1 (by rfl) ⟨1057697, by rfl⟩ : syracuseStep 1410263 = 2115395) B2115395
theorem B20514455 : Blo 417772 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B1345211 : Blo 417772 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B2131919 : Blo 417772 2131919 := bstep (se 1 (by rfl) ⟨1598939, by rfl⟩ : syracuseStep 2131919 = 3197879) B3197879
theorem B2558081 : Blo 417772 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B12225329 : Blo 417772 12225329 := bstep (se 2 (by rfl) ⟨4584498, by rfl⟩ : syracuseStep 12225329 = 9168997) B9168997
theorem B2394947 : Blo 417772 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B2132891 : Blo 417772 2132891 := bstep (se 1 (by rfl) ⟨1599668, by rfl⟩ : syracuseStep 2132891 = 3199337) B3199337
theorem B1412315 : Blo 417772 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B5082497 : Blo 417772 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B2133377 : Blo 417772 2133377 := bstep (se 2 (by rfl) ⟨800016, by rfl⟩ : syracuseStep 2133377 = 1600033) B1600033
theorem B3575609 : Blo 417772 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B3018653 : Blo 417772 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B2134025 : Blo 417772 2134025 := bstep (se 2 (by rfl) ⟨800259, by rfl⟩ : syracuseStep 2134025 = 1600519) B1600519
theorem B1413179 : Blo 417772 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B2134187 : Blo 417772 2134187 := bstep (se 1 (by rfl) ⟨1600640, by rfl⟩ : syracuseStep 2134187 = 3201281) B3201281
theorem B2592971 : Blo 417772 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1413449 : Blo 417772 1413449 := bstep (se 2 (by rfl) ⟨530043, by rfl⟩ : syracuseStep 1413449 = 1060087) B1060087
theorem B5738825 : Blo 417772 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B627035 : Blo 417772 627035 := bstep (se 1 (by rfl) ⟨470276, by rfl⟩ : syracuseStep 627035 = 940553) B940553
theorem B3412331 : Blo 417772 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B528763 : Blo 417772 528763 := bstep (se 1 (by rfl) ⟨396572, by rfl⟩ : syracuseStep 528763 = 793145) B793145
theorem B2265545 : Blo 417772 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B627263 : Blo 417772 627263 := bstep (se 1 (by rfl) ⟨470447, by rfl⟩ : syracuseStep 627263 = 940895) B940895
theorem B2134673 : Blo 417772 2134673 := bstep (se 2 (by rfl) ⟨800502, by rfl⟩ : syracuseStep 2134673 = 1601005) B1601005
theorem B1708697 : Blo 417772 1708697 := bstep (se 2 (by rfl) ⟨640761, by rfl⟩ : syracuseStep 1708697 = 1281523) B1281523
theorem B627383 : Blo 417772 627383 := bstep (se 1 (by rfl) ⟨470537, by rfl⟩ : syracuseStep 627383 = 941075) B941075
theorem B627611 : Blo 417772 627611 := bstep (se 1 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 627611 = 941417) B941417
theorem B65704931 : Blo 417772 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B628007 : Blo 417772 628007 := bstep (se 1 (by rfl) ⟨471005, by rfl⟩ : syracuseStep 628007 = 942011) B942011
theorem B2397545 : Blo 417772 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B628091 : Blo 417772 628091 := bstep (se 1 (by rfl) ⟨471068, by rfl⟩ : syracuseStep 628091 = 942137) B942137
theorem B529831 : Blo 417772 529831 := bstep (se 1 (by rfl) ⟨397373, by rfl⟩ : syracuseStep 529831 = 794747) B794747
theorem B628217 : Blo 417772 628217 := bstep (se 2 (by rfl) ⟨235581, by rfl⟩ : syracuseStep 628217 = 471163) B471163
theorem B628319 : Blo 417772 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B33166945 : Blo 417772 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B530155 : Blo 417772 530155 := bstep (se 1 (by rfl) ⟨397616, by rfl⟩ : syracuseStep 530155 = 795233) B795233
theorem B628535 : Blo 417772 628535 := bstep (se 1 (by rfl) ⟨471401, by rfl⟩ : syracuseStep 628535 = 942803) B942803
theorem B530383 : Blo 417772 530383 := bstep (se 1 (by rfl) ⟨397787, by rfl⟩ : syracuseStep 530383 = 795575) B795575
theorem B628841 : Blo 417772 628841 := bstep (se 2 (by rfl) ⟨235815, by rfl⟩ : syracuseStep 628841 = 471631) B471631
theorem B530651 : Blo 417772 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B629159 : Blo 417772 629159 := bstep (se 1 (by rfl) ⟨471869, by rfl⟩ : syracuseStep 629159 = 943739) B943739
theorem B629243 : Blo 417772 629243 := bstep (se 1 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 629243 = 943865) B943865
theorem B629369 : Blo 417772 629369 := bstep (se 2 (by rfl) ⟨236013, by rfl⟩ : syracuseStep 629369 = 472027) B472027
theorem B629423 : Blo 417772 629423 := bstep (se 1 (by rfl) ⟨472067, by rfl⟩ : syracuseStep 629423 = 944135) B944135
theorem B531127 : Blo 417772 531127 := bstep (se 1 (by rfl) ⟨398345, by rfl⟩ : syracuseStep 531127 = 796691) B796691
theorem B629471 : Blo 417772 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B957203 : Blo 417772 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B531355 : Blo 417772 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B629735 : Blo 417772 629735 := bstep (se 1 (by rfl) ⟨472301, by rfl⟩ : syracuseStep 629735 = 944603) B944603
theorem B1350695 : Blo 417772 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B629993 : Blo 417772 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B630047 : Blo 417772 630047 := bstep (se 1 (by rfl) ⟨472535, by rfl⟩ : syracuseStep 630047 = 945071) B945071
theorem B3579299 : Blo 417772 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B1416635 : Blo 417772 1416635 := bstep (se 1 (by rfl) ⟨1062476, by rfl⟩ : syracuseStep 1416635 = 2124953) B2124953
theorem B630215 : Blo 417772 630215 := bstep (se 1 (by rfl) ⟨472661, by rfl⟩ : syracuseStep 630215 = 945323) B945323
theorem B794299 : Blo 417772 794299 := bstep (se 1 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 794299 = 1191449) B1191449
theorem B630569 : Blo 417772 630569 := bstep (se 2 (by rfl) ⟨236463, by rfl⟩ : syracuseStep 630569 = 472927) B472927
theorem B630575 : Blo 417772 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B1515311 : Blo 417772 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B532271 : Blo 417772 532271 := bstep (se 1 (by rfl) ⟨399203, by rfl⟩ : syracuseStep 532271 = 798407) B798407
theorem B7151489 : Blo 417772 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B631049 : Blo 417772 631049 := bstep (se 2 (by rfl) ⟨236643, by rfl⟩ : syracuseStep 631049 = 473287) B473287
theorem B631151 : Blo 417772 631151 := bstep (se 1 (by rfl) ⟨473363, by rfl⟩ : syracuseStep 631151 = 946727) B946727
theorem B3580361 : Blo 417772 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B1516001 : Blo 417772 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B54206981 : Blo 417772 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B2695751 : Blo 417772 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B631367 : Blo 417772 631367 := bstep (se 1 (by rfl) ⟨473525, by rfl⟩ : syracuseStep 631367 = 947051) B947051
theorem B631403 : Blo 417772 631403 := bstep (se 1 (by rfl) ⟨473552, by rfl⟩ : syracuseStep 631403 = 947105) B947105
theorem B7283429 : Blo 417772 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B631631 : Blo 417772 631631 := bstep (se 1 (by rfl) ⟨473723, by rfl⟩ : syracuseStep 631631 = 947447) B947447
theorem B1057931 : Blo 417772 1057931 := bstep (se 1 (by rfl) ⟨793448, by rfl⟩ : syracuseStep 1057931 = 1586897) B1586897
theorem B632027 : Blo 417772 632027 := bstep (se 1 (by rfl) ⟨474020, by rfl⟩ : syracuseStep 632027 = 948041) B948041
theorem B1058143 : Blo 417772 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B632201 : Blo 417772 632201 := bstep (se 2 (by rfl) ⟨237075, by rfl⟩ : syracuseStep 632201 = 474151) B474151
theorem B1549729 : Blo 417772 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B796243 : Blo 417772 796243 := bstep (se 1 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 796243 = 1194365) B1194365
theorem B632555 : Blo 417772 632555 := bstep (se 1 (by rfl) ⟨474416, by rfl⟩ : syracuseStep 632555 = 948833) B948833
theorem B796463 : Blo 417772 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B797359 : Blo 417772 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B1059551 : Blo 417772 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B797519 : Blo 417772 797519 := bstep (se 1 (by rfl) ⟨598139, by rfl⟩ : syracuseStep 797519 = 1196279) B1196279
theorem B21900145 : Blo 417772 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B568615 : Blo 417772 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B10136951 : Blo 417772 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B1420793 : Blo 417772 1420793 := bstep (se 2 (by rfl) ⟨532797, by rfl⟩ : syracuseStep 1420793 = 1065595) B1065595
theorem B470623 : Blo 417772 470623 := bstep (se 1 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 470623 = 705935) B705935
theorem B4533857 : Blo 417772 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B1912429 : Blo 417772 1912429 := bstep (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) B717161
theorem B1421063 : Blo 417772 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B896825 : Blo 417772 896825 := bstep (se 2 (by rfl) ⟨336309, by rfl⟩ : syracuseStep 896825 = 672619) B672619
theorem B1421117 : Blo 417772 1421117 := bstep (se 3 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 1421117 = 532919) B532919
theorem B2863667 : Blo 417772 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B799303 : Blo 417772 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B471775 : Blo 417772 471775 := bstep (se 1 (by rfl) ⟨353831, by rfl⟩ : syracuseStep 471775 = 707663) B707663
theorem B3584735 : Blo 417772 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B1815527 : Blo 417772 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B1062011 : Blo 417772 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B21083261 : Blo 417772 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B1062031 : Blo 417772 1062031 := bstep (se 1 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 1062031 = 1593047) B1593047
theorem B1586425 : Blo 417772 1586425 := bstep (se 2 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 1586425 = 1189819) B1189819
theorem B472351 : Blo 417772 472351 := bstep (se 1 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 472351 = 708527) B708527
theorem B505127 : Blo 417772 505127 := bstep (se 1 (by rfl) ⟨378845, by rfl⟩ : syracuseStep 505127 = 757691) B757691
theorem B1848685 : Blo 417772 1848685 := bstep (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) B693257
theorem B1062305 : Blo 417772 1062305 := bstep (se 2 (by rfl) ⟨398364, by rfl⟩ : syracuseStep 1062305 = 796729) B796729
theorem B898465 : Blo 417772 898465 := bstep (se 2 (by rfl) ⟨336924, by rfl⟩ : syracuseStep 898465 = 673849) B673849
theorem B472639 : Blo 417772 472639 := bstep (se 1 (by rfl) ⟨354479, by rfl⟩ : syracuseStep 472639 = 708959) B708959
theorem B800351 : Blo 417772 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B898823 : Blo 417772 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B473467 : Blo 417772 473467 := bstep (se 1 (by rfl) ⟨355100, by rfl⟩ : syracuseStep 473467 = 710201) B710201
theorem B473935 : Blo 417772 473935 := bstep (se 1 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 473935 = 710903) B710903
theorem B900011 : Blo 417772 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B1063975 : Blo 417772 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B474331 : Blo 417772 474331 := bstep (se 1 (by rfl) ⟨355748, by rfl⟩ : syracuseStep 474331 = 711497) B711497
theorem B671113 : Blo 417772 671113 := bstep (se 2 (by rfl) ⟨251667, by rfl⟩ : syracuseStep 671113 = 503335) B503335
theorem B1064441 : Blo 417772 1064441 := bstep (se 2 (by rfl) ⟨399165, by rfl⟩ : syracuseStep 1064441 = 798331) B798331
theorem B472858165 : Blo 417772 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B4046395 : Blo 417772 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B4472617 : Blo 417772 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B1130287 : Blo 417772 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1195823 : Blo 417772 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B1065089 : Blo 417772 1065089 := bstep (se 2 (by rfl) ⟨399408, by rfl⟩ : syracuseStep 1065089 = 798817) B798817
theorem B1065383 : Blo 417772 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B1786369 : Blo 417772 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B1065545 : Blo 417772 1065545 := bstep (se 2 (by rfl) ⟨399579, by rfl⟩ : syracuseStep 1065545 = 799159) B799159
theorem B705145 : Blo 417772 705145 := bstep (se 2 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 705145 = 528859) B528859
theorem B705199 : Blo 417772 705199 := bstep (se 1 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 705199 = 1057799) B1057799
theorem B6800273 : Blo 417772 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B1065899 : Blo 417772 1065899 := bstep (se 1 (by rfl) ⟨799424, by rfl⟩ : syracuseStep 1065899 = 1598849) B1598849
theorem B1066081 : Blo 417772 1066081 := bstep (se 2 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 1066081 = 799561) B799561
theorem B25740989 : Blo 417772 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B1197929 : Blo 417772 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B1067033 : Blo 417772 1067033 := bstep (se 2 (by rfl) ⟨400137, by rfl⟩ : syracuseStep 1067033 = 800275) B800275
theorem B2115719 : Blo 417772 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B4376753 : Blo 417772 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B706907 : Blo 417772 706907 := bstep (se 1 (by rfl) ⟨530180, by rfl⟩ : syracuseStep 706907 = 1060361) B1060361
theorem B706927 : Blo 417772 706927 := bstep (se 1 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 706927 = 1060391) B1060391
theorem B1067489 : Blo 417772 1067489 := bstep (se 2 (by rfl) ⟨400308, by rfl⟩ : syracuseStep 1067489 = 800617) B800617
theorem B1067539 : Blo 417772 1067539 := bstep (se 1 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 1067539 = 1601309) B1601309
theorem B1133119 : Blo 417772 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B707143 : Blo 417772 707143 := bstep (se 1 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 707143 = 1060715) B1060715
theorem B707575 : Blo 417772 707575 := bstep (se 1 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 707575 = 1061363) B1061363
theorem B707879 : Blo 417772 707879 := bstep (se 1 (by rfl) ⟨530909, by rfl⟩ : syracuseStep 707879 = 1061819) B1061819
theorem B3624509 : Blo 417772 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B4017761 : Blo 417772 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B708331 : Blo 417772 708331 := bstep (se 1 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 708331 = 1062497) B1062497
theorem B2412569 : Blo 417772 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B3035465 : Blo 417772 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B709303 : Blo 417772 709303 := bstep (se 1 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 709303 = 1063955) B1063955
theorem B545503 : Blo 417772 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B3199823 : Blo 417772 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B709607 : Blo 417772 709607 := bstep (se 1 (by rfl) ⟨532205, by rfl⟩ : syracuseStep 709607 = 1064411) B1064411
theorem B906337 : Blo 417772 906337 := bstep (se 2 (by rfl) ⟨339876, by rfl⟩ : syracuseStep 906337 = 679753) B679753
theorem B808223 : Blo 417772 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B1004987 : Blo 417772 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B4544237 : Blo 417772 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B2119607 : Blo 417772 2119607 := bstep (se 1 (by rfl) ⟨1589705, by rfl⟩ : syracuseStep 2119607 = 3179411) B3179411
theorem B546791 : Blo 417772 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B710761 : Blo 417772 710761 := bstep (se 2 (by rfl) ⟨266535, by rfl⟩ : syracuseStep 710761 = 533071) B533071
theorem B1595645 : Blo 417772 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B1005833 : Blo 417772 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B645385 : Blo 417772 645385 := bstep (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) B484039
theorem B940463 : Blo 417772 940463 := bstep (se 1 (by rfl) ⟨705347, by rfl⟩ : syracuseStep 940463 = 1410695) B1410695
theorem B940499 : Blo 417772 940499 := bstep (se 1 (by rfl) ⟨705374, by rfl⟩ : syracuseStep 940499 = 1410749) B1410749
theorem B940607 : Blo 417772 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B2120255 : Blo 417772 2120255 := bstep (se 1 (by rfl) ⟨1590191, by rfl⟩ : syracuseStep 2120255 = 3180383) B3180383
theorem B940715 : Blo 417772 940715 := bstep (se 1 (by rfl) ⟨705536, by rfl⟩ : syracuseStep 940715 = 1411073) B1411073
theorem B2415781 : Blo 417772 2415781 := bstep (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) B452959
theorem B941255 : Blo 417772 941255 := bstep (se 1 (by rfl) ⟨705941, by rfl⟩ : syracuseStep 941255 = 1411883) B1411883
theorem B5364953 : Blo 417772 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B941435 : Blo 417772 941435 := bstep (se 1 (by rfl) ⟨706076, by rfl⟩ : syracuseStep 941435 = 1412153) B1412153
theorem B1007063 : Blo 417772 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B941561 : Blo 417772 941561 := bstep (se 2 (by rfl) ⟨353085, by rfl⟩ : syracuseStep 941561 = 706171) B706171
theorem B941651 : Blo 417772 941651 := bstep (se 1 (by rfl) ⟨706238, by rfl⟩ : syracuseStep 941651 = 1412477) B1412477
theorem B941831 : Blo 417772 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B2678993 : Blo 417772 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B418079 : Blo 417772 418079 := bstep (se 1 (by rfl) ⟨313559, by rfl⟩ : syracuseStep 418079 = 627119) B627119
theorem B418139 : Blo 417772 418139 := bstep (se 1 (by rfl) ⟨313604, by rfl⟩ : syracuseStep 418139 = 627209) B627209
theorem B942443 : Blo 417772 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B418159 : Blo 417772 418159 := bstep (se 1 (by rfl) ⟨313619, by rfl⟩ : syracuseStep 418159 = 627239) B627239
theorem B418215 : Blo 417772 418215 := bstep (se 1 (by rfl) ⟨313661, by rfl⟩ : syracuseStep 418215 = 627323) B627323
theorem B10936777 : Blo 417772 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B418299 : Blo 417772 418299 := bstep (se 1 (by rfl) ⟨313724, by rfl⟩ : syracuseStep 418299 = 627449) B627449
theorem B942587 : Blo 417772 942587 := bstep (se 1 (by rfl) ⟨706940, by rfl⟩ : syracuseStep 942587 = 1413881) B1413881
theorem B418367 : Blo 417772 418367 := bstep (se 1 (by rfl) ⟨313775, by rfl⟩ : syracuseStep 418367 = 627551) B627551
theorem B418375 : Blo 417772 418375 := bstep (se 1 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 418375 = 627563) B627563
theorem B942713 : Blo 417772 942713 := bstep (se 2 (by rfl) ⟨353517, by rfl⟩ : syracuseStep 942713 = 707035) B707035
theorem B2122361 : Blo 417772 2122361 := bstep (se 2 (by rfl) ⟨795885, by rfl⟩ : syracuseStep 2122361 = 1591771) B1591771
theorem B1794707 : Blo 417772 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B942767 : Blo 417772 942767 := bstep (se 1 (by rfl) ⟨707075, by rfl⟩ : syracuseStep 942767 = 1414151) B1414151
theorem B1794743 : Blo 417772 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B418527 : Blo 417772 418527 := bstep (se 1 (by rfl) ⟨313895, by rfl⟩ : syracuseStep 418527 = 627791) B627791
theorem B942839 : Blo 417772 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B418607 : Blo 417772 418607 := bstep (se 1 (by rfl) ⟨313955, by rfl⟩ : syracuseStep 418607 = 627911) B627911
theorem B418715 : Blo 417772 418715 := bstep (se 1 (by rfl) ⟨314036, by rfl⟩ : syracuseStep 418715 = 628073) B628073
theorem B943019 : Blo 417772 943019 := bstep (se 1 (by rfl) ⟨707264, by rfl⟩ : syracuseStep 943019 = 1414529) B1414529
theorem B15524783 : Blo 417772 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B418767 : Blo 417772 418767 := bstep (se 1 (by rfl) ⟨314075, by rfl⟩ : syracuseStep 418767 = 628151) B628151
theorem B418791 : Blo 417772 418791 := bstep (se 1 (by rfl) ⟨314093, by rfl⟩ : syracuseStep 418791 = 628187) B628187
theorem B2155511 : Blo 417772 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B1598561 : Blo 417772 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B419103 : Blo 417772 419103 := bstep (se 1 (by rfl) ⟨314327, by rfl⟩ : syracuseStep 419103 = 628655) B628655
theorem B419163 : Blo 417772 419163 := bstep (se 1 (by rfl) ⟨314372, by rfl⟩ : syracuseStep 419163 = 628745) B628745
theorem B2024813 : Blo 417772 2024813 := bstep (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) B759305
theorem B419183 : Blo 417772 419183 := bstep (se 1 (by rfl) ⟨314387, by rfl⟩ : syracuseStep 419183 = 628775) B628775
theorem B419239 : Blo 417772 419239 := bstep (se 1 (by rfl) ⟨314429, by rfl⟩ : syracuseStep 419239 = 628859) B628859
theorem B943559 : Blo 417772 943559 := bstep (se 1 (by rfl) ⟨707669, by rfl⟩ : syracuseStep 943559 = 1415339) B1415339
theorem B419323 : Blo 417772 419323 := bstep (se 1 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 419323 = 628985) B628985
theorem B3597857 : Blo 417772 3597857 := bstep (se 2 (by rfl) ⟨1349196, by rfl⟩ : syracuseStep 3597857 = 2698393) B2698393
theorem B419391 : Blo 417772 419391 := bstep (se 1 (by rfl) ⟨314543, by rfl⟩ : syracuseStep 419391 = 629087) B629087
theorem B419399 : Blo 417772 419399 := bstep (se 1 (by rfl) ⟨314549, by rfl⟩ : syracuseStep 419399 = 629099) B629099
theorem B1009313 : Blo 417772 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B419551 : Blo 417772 419551 := bstep (se 1 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 419551 = 629327) B629327
theorem B1074923 : Blo 417772 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B943919 : Blo 417772 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B419631 : Blo 417772 419631 := bstep (se 1 (by rfl) ⟨314723, by rfl⟩ : syracuseStep 419631 = 629447) B629447
theorem B9070481 : Blo 417772 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B419739 : Blo 417772 419739 := bstep (se 1 (by rfl) ⟨314804, by rfl⟩ : syracuseStep 419739 = 629609) B629609
theorem B419791 : Blo 417772 419791 := bstep (se 1 (by rfl) ⟨314843, by rfl⟩ : syracuseStep 419791 = 629687) B629687
theorem B419815 : Blo 417772 419815 := bstep (se 1 (by rfl) ⟨314861, by rfl⟩ : syracuseStep 419815 = 629723) B629723
theorem B8054963 : Blo 417772 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B420127 : Blo 417772 420127 := bstep (se 1 (by rfl) ⟨315095, by rfl⟩ : syracuseStep 420127 = 630191) B630191
theorem B13297955 : Blo 417772 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B9038141 : Blo 417772 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B420187 : Blo 417772 420187 := bstep (se 1 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 420187 = 630281) B630281
theorem B2124143 : Blo 417772 2124143 := bstep (se 1 (by rfl) ⟨1593107, by rfl⟩ : syracuseStep 2124143 = 3186215) B3186215
theorem B944495 : Blo 417772 944495 := bstep (se 1 (by rfl) ⟨708371, by rfl⟩ : syracuseStep 944495 = 1416743) B1416743
theorem B420207 : Blo 417772 420207 := bstep (se 1 (by rfl) ⟨315155, by rfl⟩ : syracuseStep 420207 = 630311) B630311
theorem B420263 : Blo 417772 420263 := bstep (se 1 (by rfl) ⟨315197, by rfl⟩ : syracuseStep 420263 = 630395) B630395
theorem B1796519 : Blo 417772 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B944567 : Blo 417772 944567 := bstep (se 1 (by rfl) ⟨708425, by rfl⟩ : syracuseStep 944567 = 1416851) B1416851
theorem B420347 : Blo 417772 420347 := bstep (se 1 (by rfl) ⟨315260, by rfl⟩ : syracuseStep 420347 = 630521) B630521
theorem B420415 : Blo 417772 420415 := bstep (se 1 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 420415 = 630623) B630623
theorem B944711 : Blo 417772 944711 := bstep (se 1 (by rfl) ⟨708533, by rfl⟩ : syracuseStep 944711 = 1417067) B1417067
theorem B420423 : Blo 417772 420423 := bstep (se 1 (by rfl) ⟨315317, by rfl⟩ : syracuseStep 420423 = 630635) B630635
theorem B944747 : Blo 417772 944747 := bstep (se 1 (by rfl) ⟨708560, by rfl⟩ : syracuseStep 944747 = 1417121) B1417121
theorem B420575 : Blo 417772 420575 := bstep (se 1 (by rfl) ⟨315431, by rfl⟩ : syracuseStep 420575 = 630863) B630863
theorem B420655 : Blo 417772 420655 := bstep (se 1 (by rfl) ⟨315491, by rfl⟩ : syracuseStep 420655 = 630983) B630983
theorem B420763 : Blo 417772 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B420815 : Blo 417772 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B420839 : Blo 417772 420839 := bstep (se 1 (by rfl) ⟨315629, by rfl⟩ : syracuseStep 420839 = 631259) B631259
theorem B945143 : Blo 417772 945143 := bstep (se 1 (by rfl) ⟨708857, by rfl⟩ : syracuseStep 945143 = 1417715) B1417715
theorem B7334993 : Blo 417772 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B4025483 : Blo 417772 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B6810911 : Blo 417772 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B421151 : Blo 417772 421151 := bstep (se 1 (by rfl) ⟨315863, by rfl⟩ : syracuseStep 421151 = 631727) B631727
theorem B421211 : Blo 417772 421211 := bstep (se 1 (by rfl) ⟨315908, by rfl⟩ : syracuseStep 421211 = 631817) B631817
theorem B945503 : Blo 417772 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B421231 : Blo 417772 421231 := bstep (se 1 (by rfl) ⟨315923, by rfl⟩ : syracuseStep 421231 = 631847) B631847
theorem B421287 : Blo 417772 421287 := bstep (se 1 (by rfl) ⟨315965, by rfl⟩ : syracuseStep 421287 = 631931) B631931
theorem B1437115 : Blo 417772 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B421371 : Blo 417772 421371 := bstep (se 1 (by rfl) ⟨316028, by rfl⟩ : syracuseStep 421371 = 632057) B632057
theorem B421439 : Blo 417772 421439 := bstep (se 1 (by rfl) ⟨316079, by rfl⟩ : syracuseStep 421439 = 632159) B632159
theorem B421447 : Blo 417772 421447 := bstep (se 1 (by rfl) ⟨316085, by rfl⟩ : syracuseStep 421447 = 632171) B632171
theorem B421599 : Blo 417772 421599 := bstep (se 1 (by rfl) ⟨316199, by rfl⟩ : syracuseStep 421599 = 632399) B632399
theorem B945899 : Blo 417772 945899 := bstep (se 1 (by rfl) ⟨709424, by rfl⟩ : syracuseStep 945899 = 1418849) B1418849
theorem B421679 : Blo 417772 421679 := bstep (se 1 (by rfl) ⟨316259, by rfl⟩ : syracuseStep 421679 = 632519) B632519
theorem B946025 : Blo 417772 946025 := bstep (se 2 (by rfl) ⟨354759, by rfl⟩ : syracuseStep 946025 = 709519) B709519
theorem B5828561 : Blo 417772 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B3502081 : Blo 417772 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B4550813 : Blo 417772 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B4518251 : Blo 417772 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B5763565 : Blo 417772 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B1012331 : Blo 417772 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B946871 : Blo 417772 946871 := bstep (se 1 (by rfl) ⟨710153, by rfl⟩ : syracuseStep 946871 = 1420307) B1420307
theorem B1274591 : Blo 417772 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B1340239 : Blo 417772 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B947087 : Blo 417772 947087 := bstep (se 1 (by rfl) ⟨710315, by rfl⟩ : syracuseStep 947087 = 1420631) B1420631
theorem B3634301 : Blo 417772 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B8189207 : Blo 417772 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B947807 : Blo 417772 947807 := bstep (se 1 (by rfl) ⟨710855, by rfl⟩ : syracuseStep 947807 = 1421711) B1421711
theorem B2127545 : Blo 417772 2127545 := bstep (se 2 (by rfl) ⟨797829, by rfl⟩ : syracuseStep 2127545 = 1595659) B1595659
theorem B948023 : Blo 417772 948023 := bstep (se 1 (by rfl) ⟨711017, by rfl⟩ : syracuseStep 948023 = 1422035) B1422035
theorem B3602231 : Blo 417772 3602231 := bstep (se 1 (by rfl) ⟨2701673, by rfl⟩ : syracuseStep 3602231 = 5403347) B5403347
theorem B6453107 : Blo 417772 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B423911 : Blo 417772 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B948329 : Blo 417772 948329 := bstep (se 2 (by rfl) ⟨355623, by rfl⟩ : syracuseStep 948329 = 711247) B711247
theorem B4291145 : Blo 417772 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B948815 : Blo 417772 948815 := bstep (se 1 (by rfl) ⟨711611, by rfl⟩ : syracuseStep 948815 = 1423223) B1423223
theorem B1800893 : Blo 417772 1800893 := bstep (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) B675335
theorem B948959 : Blo 417772 948959 := bstep (se 1 (by rfl) ⟨711719, by rfl⟩ : syracuseStep 948959 = 1423439) B1423439
theorem B3570551 : Blo 417772 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B1080463 : Blo 417772 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B4357309 : Blo 417772 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B1441223 : Blo 417772 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B1506775 : Blo 417772 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B4783697 : Blo 417772 4783697 := bstep (se 2 (by rfl) ⟨1793886, by rfl⟩ : syracuseStep 4783697 = 3587773) B3587773
theorem B2129489 : Blo 417772 2129489 := bstep (se 2 (by rfl) ⟨798558, by rfl⟩ : syracuseStep 2129489 = 1597117) B1597117
theorem B2391713 : Blo 417772 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B4292459 : Blo 417772 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B18677765 : Blo 417772 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B1376831 : Blo 417772 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B14582369 : Blo 417772 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B1705387 : Blo 417772 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B1410479 : Blo 417772 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B2917835 : Blo 417772 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1410857 : Blo 417772 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B2066305 : Blo 417772 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B1608379 : Blo 417772 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B1510363 : Blo 417772 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B2133215 : Blo 417772 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B1510825 : Blo 417772 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B1347005 : Blo 417772 1347005 := bstep (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) B505127
theorem B29200193 : Blo 417772 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B1413071 : Blo 417772 1413071 := bstep (se 1 (by rfl) ⟨1059803, by rfl⟩ : syracuseStep 1413071 = 2119607) B2119607
theorem B626975 : Blo 417772 626975 := bstep (se 1 (by rfl) ⟨470231, by rfl⟩ : syracuseStep 626975 = 940463) B940463
theorem B626999 : Blo 417772 626999 := bstep (se 1 (by rfl) ⟨470249, by rfl⟩ : syracuseStep 626999 = 940499) B940499
theorem B627071 : Blo 417772 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B1413503 : Blo 417772 1413503 := bstep (se 1 (by rfl) ⟨1060127, by rfl⟩ : syracuseStep 1413503 = 2120255) B2120255
theorem B758153 : Blo 417772 758153 := bstep (se 2 (by rfl) ⟨284307, by rfl⟩ : syracuseStep 758153 = 568615) B568615
theorem B627143 : Blo 417772 627143 := bstep (se 1 (by rfl) ⟨470357, by rfl⟩ : syracuseStep 627143 = 940715) B940715
theorem B2396861 : Blo 417772 2396861 := bstep (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) B898823
theorem B627497 : Blo 417772 627497 := bstep (se 2 (by rfl) ⟨235311, by rfl⟩ : syracuseStep 627497 = 470623) B470623
theorem B627503 : Blo 417772 627503 := bstep (se 1 (by rfl) ⟨470627, by rfl⟩ : syracuseStep 627503 = 941255) B941255
theorem B3576635 : Blo 417772 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B627623 : Blo 417772 627623 := bstep (se 1 (by rfl) ⟨470717, by rfl⟩ : syracuseStep 627623 = 941435) B941435
theorem B627707 : Blo 417772 627707 := bstep (se 1 (by rfl) ⟨470780, by rfl⟩ : syracuseStep 627707 = 941561) B941561
theorem B627767 : Blo 417772 627767 := bstep (se 1 (by rfl) ⟨470825, by rfl⟩ : syracuseStep 627767 = 941651) B941651
theorem B627887 : Blo 417772 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B628295 : Blo 417772 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B628391 : Blo 417772 628391 := bstep (se 1 (by rfl) ⟨471293, by rfl⟩ : syracuseStep 628391 = 942587) B942587
theorem B628475 : Blo 417772 628475 := bstep (se 1 (by rfl) ⟨471356, by rfl⟩ : syracuseStep 628475 = 942713) B942713
theorem B1414907 : Blo 417772 1414907 := bstep (se 1 (by rfl) ⟨1061180, by rfl⟩ : syracuseStep 1414907 = 2122361) B2122361
theorem B628511 : Blo 417772 628511 := bstep (se 1 (by rfl) ⟨471383, by rfl⟩ : syracuseStep 628511 = 942767) B942767
theorem B4855619 : Blo 417772 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B628559 : Blo 417772 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B1415069 : Blo 417772 1415069 := bstep (se 3 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 1415069 = 530651) B530651
theorem B628679 : Blo 417772 628679 := bstep (se 1 (by rfl) ⟨471509, by rfl⟩ : syracuseStep 628679 = 943019) B943019
theorem B1349875 : Blo 417772 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B629033 : Blo 417772 629033 := bstep (se 2 (by rfl) ⟨235887, by rfl⟩ : syracuseStep 629033 = 471775) B471775
theorem B727337 : Blo 417772 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B629039 : Blo 417772 629039 := bstep (se 1 (by rfl) ⟨471779, by rfl⟩ : syracuseStep 629039 = 943559) B943559
theorem B2398571 : Blo 417772 2398571 := bstep (se 1 (by rfl) ⟨1798928, by rfl⟩ : syracuseStep 2398571 = 3597857) B3597857
theorem B629279 : Blo 417772 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B530975 : Blo 417772 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B1416041 : Blo 417772 1416041 := bstep (se 2 (by rfl) ⟨531015, by rfl⟩ : syracuseStep 1416041 = 1062031) B1062031
theorem B1416095 : Blo 417772 1416095 := bstep (se 1 (by rfl) ⟨1062071, by rfl⟩ : syracuseStep 1416095 = 2124143) B2124143
theorem B629663 : Blo 417772 629663 := bstep (se 1 (by rfl) ⟨472247, by rfl⟩ : syracuseStep 629663 = 944495) B944495
theorem B629711 : Blo 417772 629711 := bstep (se 1 (by rfl) ⟨472283, by rfl⟩ : syracuseStep 629711 = 944567) B944567
theorem B629801 : Blo 417772 629801 := bstep (se 2 (by rfl) ⟨236175, by rfl⟩ : syracuseStep 629801 = 472351) B472351
theorem B629807 : Blo 417772 629807 := bstep (se 1 (by rfl) ⟨472355, by rfl⟩ : syracuseStep 629807 = 944711) B944711
theorem B629831 : Blo 417772 629831 := bstep (se 1 (by rfl) ⟨472373, by rfl⟩ : syracuseStep 629831 = 944747) B944747
theorem B2464913 : Blo 417772 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B531679 : Blo 417772 531679 := bstep (se 1 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 531679 = 797519) B797519
theorem B630095 : Blo 417772 630095 := bstep (se 1 (by rfl) ⟨472571, by rfl⟩ : syracuseStep 630095 = 945143) B945143
theorem B630185 : Blo 417772 630185 := bstep (se 2 (by rfl) ⟨236319, by rfl⟩ : syracuseStep 630185 = 472639) B472639
theorem B630335 : Blo 417772 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B6757967 : Blo 417772 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B3022571 : Blo 417772 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B2400029 : Blo 417772 2400029 := bstep (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) B900011
theorem B630599 : Blo 417772 630599 := bstep (se 1 (by rfl) ⟨472949, by rfl⟩ : syracuseStep 630599 = 945899) B945899
theorem B597883 : Blo 417772 597883 := bstep (se 1 (by rfl) ⟨448412, by rfl⟩ : syracuseStep 597883 = 896825) B896825
theorem B630683 : Blo 417772 630683 := bstep (se 1 (by rfl) ⟨473012, by rfl⟩ : syracuseStep 630683 = 946025) B946025
theorem B860513 : Blo 417772 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1909111 : Blo 417772 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B631247 : Blo 417772 631247 := bstep (se 1 (by rfl) ⟨473435, by rfl⟩ : syracuseStep 631247 = 946871) B946871
theorem B631289 : Blo 417772 631289 := bstep (se 2 (by rfl) ⟨236733, by rfl⟩ : syracuseStep 631289 = 473467) B473467
theorem B10199621 : Blo 417772 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B631391 : Blo 417772 631391 := bstep (se 1 (by rfl) ⟨473543, by rfl⟩ : syracuseStep 631391 = 947087) B947087
theorem B631871 : Blo 417772 631871 := bstep (se 1 (by rfl) ⟨473903, by rfl⟩ : syracuseStep 631871 = 947807) B947807
theorem B533567 : Blo 417772 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B631913 : Blo 417772 631913 := bstep (se 2 (by rfl) ⟨236967, by rfl⟩ : syracuseStep 631913 = 473935) B473935
theorem B1418363 : Blo 417772 1418363 := bstep (se 1 (by rfl) ⟨1063772, by rfl⟩ : syracuseStep 1418363 = 2127545) B2127545
theorem B632015 : Blo 417772 632015 := bstep (se 1 (by rfl) ⟨474011, by rfl⟩ : syracuseStep 632015 = 948023) B948023
theorem B2401487 : Blo 417772 2401487 := bstep (se 1 (by rfl) ⟨1801115, by rfl⟩ : syracuseStep 2401487 = 3602231) B3602231
theorem B4302071 : Blo 417772 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B1418633 : Blo 417772 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B632219 : Blo 417772 632219 := bstep (se 1 (by rfl) ⟨474164, by rfl⟩ : syracuseStep 632219 = 948329) B948329
theorem B3221041 : Blo 417772 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B5809745 : Blo 417772 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B632441 : Blo 417772 632441 := bstep (se 2 (by rfl) ⟨237165, by rfl⟩ : syracuseStep 632441 = 474331) B474331
theorem B2860763 : Blo 417772 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B632543 : Blo 417772 632543 := bstep (se 1 (by rfl) ⟨474407, by rfl⟩ : syracuseStep 632543 = 948815) B948815
theorem B632639 : Blo 417772 632639 := bstep (se 1 (by rfl) ⟨474479, by rfl⟩ : syracuseStep 632639 = 948959) B948959
theorem B894817 : Blo 417772 894817 := bstep (se 2 (by rfl) ⟨335556, by rfl⟩ : syracuseStep 894817 = 671113) B671113
theorem B2009033 : Blo 417772 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1419389 : Blo 417772 1419389 := bstep (se 3 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 1419389 = 532271) B532271
theorem B1059065 : Blo 417772 1059065 := bstep (se 2 (by rfl) ⟨397149, by rfl⟩ : syracuseStep 1059065 = 794299) B794299
theorem B960815 : Blo 417772 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B3189131 : Blo 417772 3189131 := bstep (se 1 (by rfl) ⟨2391848, by rfl⟩ : syracuseStep 3189131 = 4783697) B4783697
theorem B1419659 : Blo 417772 1419659 := bstep (se 1 (by rfl) ⟨1064744, by rfl⟩ : syracuseStep 1419659 = 2129489) B2129489
theorem B797215 : Blo 417772 797215 := bstep (se 1 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 797215 = 1195823) B1195823
theorem B2861639 : Blo 417772 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B895799 : Blo 417772 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B568441 : Blo 417772 568441 := bstep (se 2 (by rfl) ⟨213165, by rfl⟩ : syracuseStep 568441 = 426331) B426331
theorem B4533515 : Blo 417772 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3190103 : Blo 417772 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B13676303 : Blo 417772 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B896807 : Blo 417772 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B4042669 : Blo 417772 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B1421279 : Blo 417772 1421279 := bstep (se 1 (by rfl) ⟨1065959, by rfl⟩ : syracuseStep 1421279 = 2131919) B2131919
theorem B1421441 : Blo 417772 1421441 := bstep (se 2 (by rfl) ⟨533040, by rfl⟩ : syracuseStep 1421441 = 1066081) B1066081
theorem B471271 : Blo 417772 471271 := bstep (se 1 (by rfl) ⟨353453, by rfl⟩ : syracuseStep 471271 = 706907) B706907
theorem B1421927 : Blo 417772 1421927 := bstep (se 1 (by rfl) ⟨1066445, by rfl⟩ : syracuseStep 1421927 = 2132891) B2132891
theorem B1061657 : Blo 417772 1061657 := bstep (se 2 (by rfl) ⟨398121, by rfl⟩ : syracuseStep 1061657 = 796243) B796243
theorem B471919 : Blo 417772 471919 := bstep (se 1 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 471919 = 707879) B707879
theorem B3388331 : Blo 417772 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B1422251 : Blo 417772 1422251 := bstep (se 1 (by rfl) ⟨1066688, by rfl⟩ : syracuseStep 1422251 = 2133377) B2133377
theorem B2012435 : Blo 417772 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B5748029 : Blo 417772 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B1422683 : Blo 417772 1422683 := bstep (se 1 (by rfl) ⟨1067012, by rfl⟩ : syracuseStep 1422683 = 2134025) B2134025
theorem B1422791 : Blo 417772 1422791 := bstep (se 1 (by rfl) ⟨1067093, by rfl⟩ : syracuseStep 1422791 = 2134187) B2134187
theorem B2274887 : Blo 417772 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B1423115 : Blo 417772 1423115 := bstep (se 1 (by rfl) ⟨1067336, by rfl⟩ : syracuseStep 1423115 = 2134673) B2134673
theorem B473071 : Blo 417772 473071 := bstep (se 1 (by rfl) ⟨354803, by rfl⟩ : syracuseStep 473071 = 709607) B709607
theorem B1423385 : Blo 417772 1423385 := bstep (se 2 (by rfl) ⟨533769, by rfl⟩ : syracuseStep 1423385 = 1067539) B1067539
theorem B1063145 : Blo 417772 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B3029491 : Blo 417772 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B1063763 : Blo 417772 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B670555 : Blo 417772 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B638135 : Blo 417772 638135 := bstep (se 1 (by rfl) ⟨478601, by rfl⟩ : syracuseStep 638135 = 957203) B957203
theorem B1916153 : Blo 417772 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B3194477 : Blo 417772 3194477 := bstep (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) B1197929
theorem B671375 : Blo 417772 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B4767659 : Blo 417772 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B1130429 : Blo 417772 1130429 := bstep (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) B423911
theorem B1458109 : Blo 417772 1458109 := bstep (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) B546791
theorem B1785995 : Blo 417772 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B1196471 : Blo 417772 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B1196495 : Blo 417772 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B705017 : Blo 417772 705017 := bstep (se 2 (by rfl) ⟨264381, by rfl⟩ : syracuseStep 705017 = 528763) B528763
theorem B7684753 : Blo 417772 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B1065707 : Blo 417772 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B705287 : Blo 417772 705287 := bstep (se 1 (by rfl) ⟨528965, by rfl⟩ : syracuseStep 705287 = 1057931) B1057931
theorem B1065737 : Blo 417772 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B1786985 : Blo 417772 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B672875 : Blo 417772 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B6046987 : Blo 417772 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B1197679 : Blo 417772 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B2115233 : Blo 417772 2115233 := bstep (se 2 (by rfl) ⟨793212, by rfl⟩ : syracuseStep 2115233 = 1586425) B1586425
theorem B706367 : Blo 417772 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B1197953 : Blo 417772 1197953 := bstep (se 2 (by rfl) ⟨449232, by rfl⟩ : syracuseStep 1197953 = 898465) B898465
theorem B706441 : Blo 417772 706441 := bstep (se 2 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 706441 = 529831) B529831
theorem B44222593 : Blo 417772 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B4540607 : Blo 417772 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B706873 : Blo 417772 706873 := bstep (se 2 (by rfl) ⟨265077, by rfl⟩ : syracuseStep 706873 = 530155) B530155
theorem B707177 : Blo 417772 707177 := bstep (se 2 (by rfl) ⟨265191, by rfl⟩ : syracuseStep 707177 = 530383) B530383
theorem B3885707 : Blo 417772 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B3033875 : Blo 417772 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B674887 : Blo 417772 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B708007 : Blo 417772 708007 := bstep (se 1 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 708007 = 1062011) B1062011
theorem B5459471 : Blo 417772 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B708169 : Blo 417772 708169 := bstep (se 2 (by rfl) ⟨265563, by rfl⟩ : syracuseStep 708169 = 531127) B531127
theorem B708203 : Blo 417772 708203 := bstep (se 1 (by rfl) ⟨531152, by rfl⟩ : syracuseStep 708203 = 1062305) B1062305
theorem B708473 : Blo 417772 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B1200595 : Blo 417772 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B2380367 : Blo 417772 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B630477553 : Blo 417772 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B5395193 : Blo 417772 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B709627 : Blo 417772 709627 := bstep (se 1 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 709627 = 1064441) B1064441
theorem B1594475 : Blo 417772 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B710059 : Blo 417772 710059 := bstep (se 1 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 710059 = 1065089) B1065089
theorem B710255 : Blo 417772 710255 := bstep (se 1 (by rfl) ⟨532691, by rfl⟩ : syracuseStep 710255 = 1065383) B1065383
theorem B710363 : Blo 417772 710363 := bstep (se 1 (by rfl) ⟨532772, by rfl⟩ : syracuseStep 710363 = 1065545) B1065545
theorem B4020101 : Blo 417772 4020101 := bstep (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) B753769
theorem B710599 : Blo 417772 710599 := bstep (se 1 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 710599 = 1065899) B1065899
theorem B939995 : Blo 417772 939995 := bstep (se 1 (by rfl) ⟨704996, by rfl⟩ : syracuseStep 939995 = 1409993) B1409993
theorem B2381825 : Blo 417772 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B940175 : Blo 417772 940175 := bstep (se 1 (by rfl) ⟨705131, by rfl⟩ : syracuseStep 940175 = 1410263) B1410263
theorem B940193 : Blo 417772 940193 := bstep (se 2 (by rfl) ⟨352572, by rfl⟩ : syracuseStep 940193 = 705145) B705145
theorem B940265 : Blo 417772 940265 := bstep (se 2 (by rfl) ⟨352599, by rfl⟩ : syracuseStep 940265 = 705199) B705199
theorem B17160659 : Blo 417772 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B711355 : Blo 417772 711355 := bstep (se 1 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 711355 = 1067033) B1067033
theorem B711659 : Blo 417772 711659 := bstep (se 1 (by rfl) ⟨533744, by rfl⟩ : syracuseStep 711659 = 1067489) B1067489
theorem B8150219 : Blo 417772 8150219 := bstep (se 1 (by rfl) ⟨6112664, by rfl⟩ : syracuseStep 8150219 = 12225329) B12225329
theorem B1596631 : Blo 417772 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B941543 : Blo 417772 941543 := bstep (se 1 (by rfl) ⟨706157, by rfl⟩ : syracuseStep 941543 = 1412315) B1412315
theorem B2416339 : Blo 417772 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B2678507 : Blo 417772 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B2383739 : Blo 417772 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B942119 : Blo 417772 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B1728647 : Blo 417772 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B942299 : Blo 417772 942299 := bstep (se 1 (by rfl) ⟨706724, by rfl⟩ : syracuseStep 942299 = 1413449) B1413449
theorem B3825883 : Blo 417772 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B2023643 : Blo 417772 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B418023 : Blo 417772 418023 := bstep (se 1 (by rfl) ⟨313517, by rfl⟩ : syracuseStep 418023 = 627035) B627035
theorem B9691469 : Blo 417772 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B56222029 : Blo 417772 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B141844853 : Blo 417772 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B418175 : Blo 417772 418175 := bstep (se 1 (by rfl) ⟨313631, by rfl⟩ : syracuseStep 418175 = 627263) B627263
theorem B1139131 : Blo 417772 1139131 := bstep (se 1 (by rfl) ⟨854348, by rfl⟩ : syracuseStep 1139131 = 1708697) B1708697
theorem B418255 : Blo 417772 418255 := bstep (se 1 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 418255 = 627383) B627383
theorem B942569 : Blo 417772 942569 := bstep (se 2 (by rfl) ⟨353463, by rfl⟩ : syracuseStep 942569 = 706927) B706927
theorem B418407 : Blo 417772 418407 := bstep (se 1 (by rfl) ⟨313805, by rfl⟩ : syracuseStep 418407 = 627611) B627611
theorem B43803287 : Blo 417772 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B2155261 : Blo 417772 2155261 := bstep (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) B808223
theorem B942857 : Blo 417772 942857 := bstep (se 2 (by rfl) ⟨353571, by rfl⟩ : syracuseStep 942857 = 707143) B707143
theorem B418671 : Blo 417772 418671 := bstep (se 1 (by rfl) ⟨314003, by rfl⟩ : syracuseStep 418671 = 628007) B628007
theorem B1598363 : Blo 417772 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B418727 : Blo 417772 418727 := bstep (se 1 (by rfl) ⟨314045, by rfl⟩ : syracuseStep 418727 = 628091) B628091
theorem B418811 : Blo 417772 418811 := bstep (se 1 (by rfl) ⟨314108, by rfl⟩ : syracuseStep 418811 = 628217) B628217
theorem B418879 : Blo 417772 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B2679965 : Blo 417772 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B419023 : Blo 417772 419023 := bstep (se 1 (by rfl) ⟨314267, by rfl⟩ : syracuseStep 419023 = 628535) B628535
theorem B943433 : Blo 417772 943433 := bstep (se 2 (by rfl) ⟨353787, by rfl⟩ : syracuseStep 943433 = 707575) B707575
theorem B419227 : Blo 417772 419227 := bstep (se 1 (by rfl) ⟨314420, by rfl⟩ : syracuseStep 419227 = 628841) B628841
theorem B419439 : Blo 417772 419439 := bstep (se 1 (by rfl) ⟨314579, by rfl⟩ : syracuseStep 419439 = 629159) B629159
theorem B419495 : Blo 417772 419495 := bstep (se 1 (by rfl) ⟨314621, by rfl⟩ : syracuseStep 419495 = 629243) B629243
theorem B419579 : Blo 417772 419579 := bstep (se 1 (by rfl) ⟨314684, by rfl⟩ : syracuseStep 419579 = 629369) B629369
theorem B419615 : Blo 417772 419615 := bstep (se 1 (by rfl) ⟨314711, by rfl⟩ : syracuseStep 419615 = 629423) B629423
theorem B419647 : Blo 417772 419647 := bstep (se 1 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 419647 = 629471) B629471
theorem B419823 : Blo 417772 419823 := bstep (se 1 (by rfl) ⟨314867, by rfl⟩ : syracuseStep 419823 = 629735) B629735
theorem B419995 : Blo 417772 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B420031 : Blo 417772 420031 := bstep (se 1 (by rfl) ⟨315023, by rfl⟩ : syracuseStep 420031 = 630047) B630047
theorem B2386199 : Blo 417772 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B944423 : Blo 417772 944423 := bstep (se 1 (by rfl) ⟨708317, by rfl⟩ : syracuseStep 944423 = 1416635) B1416635
theorem B420143 : Blo 417772 420143 := bstep (se 1 (by rfl) ⟨315107, by rfl⟩ : syracuseStep 420143 = 630215) B630215
theorem B944441 : Blo 417772 944441 := bstep (se 2 (by rfl) ⟨354165, by rfl⟩ : syracuseStep 944441 = 708331) B708331
theorem B420379 : Blo 417772 420379 := bstep (se 1 (by rfl) ⟨315284, by rfl⟩ : syracuseStep 420379 = 630569) B630569
theorem B420383 : Blo 417772 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B1010207 : Blo 417772 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B420699 : Blo 417772 420699 := bstep (se 1 (by rfl) ⟨315524, by rfl⟩ : syracuseStep 420699 = 631049) B631049
theorem B420767 : Blo 417772 420767 := bstep (se 1 (by rfl) ⟨315575, by rfl⟩ : syracuseStep 420767 = 631151) B631151
theorem B2386907 : Blo 417772 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B36137987 : Blo 417772 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B1797167 : Blo 417772 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B420911 : Blo 417772 420911 := bstep (se 1 (by rfl) ⟨315683, by rfl⟩ : syracuseStep 420911 = 631367) B631367
theorem B420935 : Blo 417772 420935 := bstep (se 1 (by rfl) ⟨315701, by rfl⟩ : syracuseStep 420935 = 631403) B631403
theorem B421087 : Blo 417772 421087 := bstep (se 1 (by rfl) ⟨315815, by rfl⟩ : syracuseStep 421087 = 631631) B631631
theorem B10349855 : Blo 417772 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B421351 : Blo 417772 421351 := bstep (se 1 (by rfl) ⟨316013, by rfl⟩ : syracuseStep 421351 = 632027) B632027
theorem B945737 : Blo 417772 945737 := bstep (se 2 (by rfl) ⟨354651, by rfl⟩ : syracuseStep 945737 = 709303) B709303
theorem B421467 : Blo 417772 421467 := bstep (se 1 (by rfl) ⟨316100, by rfl⟩ : syracuseStep 421467 = 632201) B632201
theorem B716615 : Blo 417772 716615 := bstep (se 1 (by rfl) ⟨537461, by rfl⟩ : syracuseStep 716615 = 1074923) B1074923
theorem B421703 : Blo 417772 421703 := bstep (se 1 (by rfl) ⟨316277, by rfl⟩ : syracuseStep 421703 = 632555) B632555
theorem B5369975 : Blo 417772 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B1208449 : Blo 417772 1208449 := bstep (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) B906337
theorem B6025427 : Blo 417772 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B2683655 : Blo 417772 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B947195 : Blo 417772 947195 := bstep (se 1 (by rfl) ⟨710396, by rfl⟩ : syracuseStep 947195 = 1420793) B1420793
theorem B947375 : Blo 417772 947375 := bstep (se 1 (by rfl) ⟨710531, by rfl⟩ : syracuseStep 947375 = 1421063) B1421063
theorem B947411 : Blo 417772 947411 := bstep (se 1 (by rfl) ⟨710558, by rfl⟩ : syracuseStep 947411 = 1421117) B1421117
theorem B3601853 : Blo 417772 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B947681 : Blo 417772 947681 := bstep (se 2 (by rfl) ⟨355380, by rfl⟩ : syracuseStep 947681 = 710761) B710761
theorem B19559981 : Blo 417772 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B3012167 : Blo 417772 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B849727 : Blo 417772 849727 := bstep (se 1 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 849727 = 1274591) B1274591
theorem B2389823 : Blo 417772 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B1210351 : Blo 417772 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1440617 : Blo 417772 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B5963489 : Blo 417772 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B1507049 : Blo 417772 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B12451843 : Blo 417772 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B917887 : Blo 417772 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B2294701 : Blo 417772 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B1410155 : Blo 417772 1410155 := bstep (se 1 (by rfl) ⟨1057616, by rfl⟩ : syracuseStep 1410155 = 2115233) B2115233
theorem B27198989 : Blo 417772 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B8062649 : Blo 417772 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B2590471 : Blo 417772 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B4294721 : Blo 417772 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B3639647 : Blo 417772 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B2755073 : Blo 417772 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B19466795 : Blo 417772 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B34312085 : Blo 417772 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B626663 : Blo 417772 626663 := bstep (se 1 (by rfl) ⟨469997, by rfl⟩ : syracuseStep 626663 = 939995) B939995
theorem B626783 : Blo 417772 626783 := bstep (se 1 (by rfl) ⟨470087, by rfl⟩ : syracuseStep 626783 = 940175) B940175
theorem B626795 : Blo 417772 626795 := bstep (se 1 (by rfl) ⟨470096, by rfl⟩ : syracuseStep 626795 = 940193) B940193
theorem B626843 : Blo 417772 626843 := bstep (se 1 (by rfl) ⟨470132, by rfl⟩ : syracuseStep 626843 = 940265) B940265
theorem B757921 : Blo 417772 757921 := bstep (se 2 (by rfl) ⟨284220, by rfl⟩ : syracuseStep 757921 = 568441) B568441
theorem B11440439 : Blo 417772 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B1643275 : Blo 417772 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B627695 : Blo 417772 627695 := bstep (se 1 (by rfl) ⟨470771, by rfl⟩ : syracuseStep 627695 = 941543) B941543
theorem B628079 : Blo 417772 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B1152431 : Blo 417772 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B628199 : Blo 417772 628199 := bstep (se 1 (by rfl) ⟨471149, by rfl⟩ : syracuseStep 628199 = 942299) B942299
theorem B1349095 : Blo 417772 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B1611265 : Blo 417772 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B6460979 : Blo 417772 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B628361 : Blo 417772 628361 := bstep (se 2 (by rfl) ⟨235635, by rfl⟩ : syracuseStep 628361 = 471271) B471271
theorem B628379 : Blo 417772 628379 := bstep (se 1 (by rfl) ⟨471284, by rfl⟩ : syracuseStep 628379 = 942569) B942569
theorem B29202191 : Blo 417772 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B628571 : Blo 417772 628571 := bstep (se 1 (by rfl) ⟨471428, by rfl⟩ : syracuseStep 628571 = 942857) B942857
theorem B1939565 : Blo 417772 1939565 := bstep (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) B727337
theorem B628955 : Blo 417772 628955 := bstep (se 1 (by rfl) ⟨471716, by rfl⟩ : syracuseStep 628955 = 943433) B943433
theorem B840636737 : Blo 417772 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B629225 : Blo 417772 629225 := bstep (se 2 (by rfl) ⟨235959, by rfl⟩ : syracuseStep 629225 = 471919) B471919
theorem B1415933 : Blo 417772 1415933 := bstep (se 3 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 1415933 = 530975) B530975
theorem B629615 : Blo 417772 629615 := bstep (se 1 (by rfl) ⟨472211, by rfl⟩ : syracuseStep 629615 = 944423) B944423
theorem B629627 : Blo 417772 629627 := bstep (se 1 (by rfl) ⟨472220, by rfl⟩ : syracuseStep 629627 = 944441) B944441
theorem B1907759 : Blo 417772 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B24091991 : Blo 417772 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B3022343 : Blo 417772 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B630491 : Blo 417772 630491 := bstep (se 1 (by rfl) ⟨472868, by rfl⟩ : syracuseStep 630491 = 945737) B945737
theorem B9117535 : Blo 417772 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B597871 : Blo 417772 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B1613801 : Blo 417772 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B630761 : Blo 417772 630761 := bstep (se 2 (by rfl) ⟨236535, by rfl⟩ : syracuseStep 630761 = 473071) B473071
theorem B3579983 : Blo 417772 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B4792445 : Blo 417772 4792445 := bstep (se 3 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 4792445 = 1797167) B1797167
theorem B4039321 : Blo 417772 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B631463 : Blo 417772 631463 := bstep (se 1 (by rfl) ⟨473597, by rfl⟩ : syracuseStep 631463 = 947195) B947195
theorem B631583 : Blo 417772 631583 := bstep (se 1 (by rfl) ⟨473687, by rfl⟩ : syracuseStep 631583 = 947375) B947375
theorem B631607 : Blo 417772 631607 := bstep (se 1 (by rfl) ⟨473705, by rfl⟩ : syracuseStep 631607 = 947411) B947411
theorem B2401235 : Blo 417772 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B631787 : Blo 417772 631787 := bstep (se 1 (by rfl) ⟨473840, by rfl⟩ : syracuseStep 631787 = 947681) B947681
theorem B2008111 : Blo 417772 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1516591 : Blo 417772 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B894073 : Blo 417772 894073 := bstep (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) B670555
theorem B3221785 : Blo 417772 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B3975659 : Blo 417772 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B797177 : Blo 417772 797177 := bstep (se 2 (by rfl) ⟨298941, by rfl⟩ : syracuseStep 797177 = 597883) B597883
theorem B1944145 : Blo 417772 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B1190663 : Blo 417772 1190663 := bstep (se 1 (by rfl) ⟨892997, by rfl⟩ : syracuseStep 1190663 = 1785995) B1785995
theorem B797663 : Blo 417772 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B470011 : Blo 417772 470011 := bstep (se 1 (by rfl) ⟨352508, by rfl⟩ : syracuseStep 470011 = 705017) B705017
theorem B470191 : Blo 417772 470191 := bstep (se 1 (by rfl) ⟨352643, by rfl⟩ : syracuseStep 470191 = 705287) B705287
theorem B1518841 : Blo 417772 1518841 := bstep (se 2 (by rfl) ⟨569565, by rfl⟩ : syracuseStep 1518841 = 1139131) B1139131
theorem B1191323 : Blo 417772 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B1945223 : Blo 417772 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B3190589 : Blo 417772 3190589 := bstep (se 3 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 3190589 = 1196471) B1196471
theorem B470911 : Blo 417772 470911 := bstep (se 1 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 470911 = 706367) B706367
theorem B798635 : Blo 417772 798635 := bstep (se 1 (by rfl) ⟨598976, by rfl⟩ : syracuseStep 798635 = 1197953) B1197953
theorem B3027071 : Blo 417772 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B471451 : Blo 417772 471451 := bstep (se 1 (by rfl) ⟨353588, by rfl⟩ : syracuseStep 471451 = 707177) B707177
theorem B2273849 : Blo 417772 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B1422143 : Blo 417772 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B898003 : Blo 417772 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B472135 : Blo 417772 472135 := bstep (se 1 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 472135 = 708203) B708203
theorem B1193089 : Blo 417772 1193089 := bstep (se 2 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 1193089 = 894817) B894817
theorem B472315 : Blo 417772 472315 := bstep (se 1 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 472315 = 708473) B708473
theorem B1422845 : Blo 417772 1422845 := bstep (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) B533567
theorem B58963457 : Blo 417772 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B505435 : Blo 417772 505435 := bstep (se 1 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 505435 = 758153) B758153
theorem B1586911 : Blo 417772 1586911 := bstep (se 1 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 1586911 = 2380367) B2380367
theorem B1062953 : Blo 417772 1062953 := bstep (se 2 (by rfl) ⟨398607, by rfl⟩ : syracuseStep 1062953 = 797215) B797215
theorem B1062983 : Blo 417772 1062983 := bstep (se 1 (by rfl) ⟨797237, by rfl⟩ : syracuseStep 1062983 = 1594475) B1594475
theorem B473503 : Blo 417772 473503 := bstep (se 1 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 473503 = 710255) B710255
theorem B473575 : Blo 417772 473575 := bstep (se 1 (by rfl) ⟨355181, by rfl⟩ : syracuseStep 473575 = 710363) B710363
theorem B2013817 : Blo 417772 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1587883 : Blo 417772 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B899849 : Blo 417772 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B2014433 : Blo 417772 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B474439 : Blo 417772 474439 := bstep (se 1 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 474439 = 711659) B711659
theorem B4505311 : Blo 417772 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1785671 : Blo 417772 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B2015047 : Blo 417772 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B5390225 : Blo 417772 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B1589159 : Blo 417772 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B1065575 : Blo 417772 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B1786643 : Blo 417772 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B2868047 : Blo 417772 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B706043 : Blo 417772 706043 := bstep (se 1 (by rfl) ⟨529532, by rfl⟩ : syracuseStep 706043 = 1059065) B1059065
theorem B1590799 : Blo 417772 1590799 := bstep (se 1 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 1590799 = 2386199) B2386199
theorem B640543 : Blo 417772 640543 := bstep (se 1 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 640543 = 960815) B960815
theorem B673471 : Blo 417772 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B1591271 : Blo 417772 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B6899903 : Blo 417772 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B1132969 : Blo 417772 1132969 := bstep (se 2 (by rfl) ⟨424863, by rfl⟩ : syracuseStep 1132969 = 849727) B849727
theorem B477743 : Blo 417772 477743 := bstep (se 1 (by rfl) ⟨358307, by rfl⟩ : syracuseStep 477743 = 716615) B716615
theorem B4016951 : Blo 417772 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B1789103 : Blo 417772 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B707771 : Blo 417772 707771 := bstep (se 1 (by rfl) ⟨530828, by rfl⟩ : syracuseStep 707771 = 1061657) B1061657
theorem B1593215 : Blo 417772 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B708763 : Blo 417772 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B708905 : Blo 417772 708905 := bstep (se 2 (by rfl) ⟨265839, by rfl⟩ : syracuseStep 708905 = 531679) B531679
theorem B1790333 : Blo 417772 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B709175 : Blo 417772 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B1004699 : Blo 417772 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B9721579 : Blo 417772 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B710471 : Blo 417772 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B2545481 : Blo 417772 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B710491 : Blo 417772 710491 := bstep (se 1 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 710491 = 1065737) B1065737
theorem B448583 : Blo 417772 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B10246337 : Blo 417772 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B940319 : Blo 417772 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B2873681 : Blo 417772 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B20404709 : Blo 417772 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B940571 : Blo 417772 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B299850821 : Blo 417772 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B2022583 : Blo 417772 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B1596905 : Blo 417772 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B941921 : Blo 417772 941921 := bstep (se 2 (by rfl) ⟨353220, by rfl⟩ : syracuseStep 941921 = 706441) B706441
theorem B942047 : Blo 417772 942047 := bstep (se 1 (by rfl) ⟨706535, by rfl⟩ : syracuseStep 942047 = 1413071) B1413071
theorem B417983 : Blo 417772 417983 := bstep (se 1 (by rfl) ⟨313487, by rfl⟩ : syracuseStep 417983 = 626975) B626975
theorem B417999 : Blo 417772 417999 := bstep (se 1 (by rfl) ⟨313499, by rfl⟩ : syracuseStep 417999 = 626999) B626999
theorem B418047 : Blo 417772 418047 := bstep (se 1 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 418047 = 627071) B627071
theorem B942335 : Blo 417772 942335 := bstep (se 1 (by rfl) ⟨706751, by rfl⟩ : syracuseStep 942335 = 1413503) B1413503
theorem B418095 : Blo 417772 418095 := bstep (se 1 (by rfl) ⟨313571, by rfl⟩ : syracuseStep 418095 = 627143) B627143
theorem B942497 : Blo 417772 942497 := bstep (se 2 (by rfl) ⟨353436, by rfl⟩ : syracuseStep 942497 = 706873) B706873
theorem B1597907 : Blo 417772 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B3596795 : Blo 417772 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B418331 : Blo 417772 418331 := bstep (se 1 (by rfl) ⟨313748, by rfl⟩ : syracuseStep 418331 = 627497) B627497
theorem B418335 : Blo 417772 418335 := bstep (se 1 (by rfl) ⟨313751, by rfl⟩ : syracuseStep 418335 = 627503) B627503
theorem B2384423 : Blo 417772 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B418415 : Blo 417772 418415 := bstep (se 1 (by rfl) ⟨313811, by rfl⟩ : syracuseStep 418415 = 627623) B627623
theorem B418471 : Blo 417772 418471 := bstep (se 1 (by rfl) ⟨313853, by rfl⟩ : syracuseStep 418471 = 627707) B627707
theorem B418511 : Blo 417772 418511 := bstep (se 1 (by rfl) ⟨313883, by rfl⟩ : syracuseStep 418511 = 627767) B627767
theorem B418591 : Blo 417772 418591 := bstep (se 1 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 418591 = 627887) B627887
theorem B418863 : Blo 417772 418863 := bstep (se 1 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 418863 = 628295) B628295
theorem B418927 : Blo 417772 418927 := bstep (se 1 (by rfl) ⟨314195, by rfl⟩ : syracuseStep 418927 = 628391) B628391
theorem B418983 : Blo 417772 418983 := bstep (se 1 (by rfl) ⟨314237, by rfl⟩ : syracuseStep 418983 = 628475) B628475
theorem B943271 : Blo 417772 943271 := bstep (se 1 (by rfl) ⟨707453, by rfl⟩ : syracuseStep 943271 = 1414907) B1414907
theorem B419007 : Blo 417772 419007 := bstep (se 1 (by rfl) ⟨314255, by rfl⟩ : syracuseStep 419007 = 628511) B628511
theorem B3237079 : Blo 417772 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B419039 : Blo 417772 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B2680067 : Blo 417772 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B943379 : Blo 417772 943379 := bstep (se 1 (by rfl) ⟨707534, by rfl⟩ : syracuseStep 943379 = 1415069) B1415069
theorem B419119 : Blo 417772 419119 := bstep (se 1 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 419119 = 628679) B628679
theorem B52159949 : Blo 417772 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B419355 : Blo 417772 419355 := bstep (se 1 (by rfl) ⟨314516, by rfl⟩ : syracuseStep 419355 = 629033) B629033
theorem B419359 : Blo 417772 419359 := bstep (se 1 (by rfl) ⟨314519, by rfl⟩ : syracuseStep 419359 = 629039) B629039
theorem B15492653 : Blo 417772 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B1599047 : Blo 417772 1599047 := bstep (se 1 (by rfl) ⟨1199285, by rfl⟩ : syracuseStep 1599047 = 2398571) B2398571
theorem B419519 : Blo 417772 419519 := bstep (se 1 (by rfl) ⟨314639, by rfl⟩ : syracuseStep 419519 = 629279) B629279
theorem B944009 : Blo 417772 944009 := bstep (se 2 (by rfl) ⟨354003, by rfl⟩ : syracuseStep 944009 = 708007) B708007
theorem B944027 : Blo 417772 944027 := bstep (se 1 (by rfl) ⟨708020, by rfl⟩ : syracuseStep 944027 = 1416041) B1416041
theorem B7628701 : Blo 417772 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B944063 : Blo 417772 944063 := bstep (se 1 (by rfl) ⟨708047, by rfl⟩ : syracuseStep 944063 = 1416095) B1416095
theorem B419775 : Blo 417772 419775 := bstep (se 1 (by rfl) ⟨314831, by rfl⟩ : syracuseStep 419775 = 629663) B629663
theorem B419807 : Blo 417772 419807 := bstep (se 1 (by rfl) ⟨314855, by rfl⟩ : syracuseStep 419807 = 629711) B629711
theorem B419867 : Blo 417772 419867 := bstep (se 1 (by rfl) ⟨314900, by rfl⟩ : syracuseStep 419867 = 629801) B629801
theorem B419871 : Blo 417772 419871 := bstep (se 1 (by rfl) ⟨314903, by rfl⟩ : syracuseStep 419871 = 629807) B629807
theorem B419887 : Blo 417772 419887 := bstep (se 1 (by rfl) ⟨314915, by rfl⟩ : syracuseStep 419887 = 629831) B629831
theorem B944225 : Blo 417772 944225 := bstep (se 2 (by rfl) ⟨354084, by rfl⟩ : syracuseStep 944225 = 708169) B708169
theorem B5433479 : Blo 417772 5433479 := bstep (se 1 (by rfl) ⟨4075109, by rfl⟩ : syracuseStep 5433479 = 8150219) B8150219
theorem B420063 : Blo 417772 420063 := bstep (se 1 (by rfl) ⟨315047, by rfl⟩ : syracuseStep 420063 = 630095) B630095
theorem B420123 : Blo 417772 420123 := bstep (se 1 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 420123 = 630185) B630185
theorem B420223 : Blo 417772 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B1600019 : Blo 417772 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B420399 : Blo 417772 420399 := bstep (se 1 (by rfl) ⟨315299, by rfl⟩ : syracuseStep 420399 = 630599) B630599
theorem B420455 : Blo 417772 420455 := bstep (se 1 (by rfl) ⟨315341, by rfl⟩ : syracuseStep 420455 = 630683) B630683
theorem B94563235 : Blo 417772 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B420831 : Blo 417772 420831 := bstep (se 1 (by rfl) ⟨315623, by rfl⟩ : syracuseStep 420831 = 631247) B631247
theorem B420859 : Blo 417772 420859 := bstep (se 1 (by rfl) ⟨315644, by rfl⟩ : syracuseStep 420859 = 631289) B631289
theorem B420927 : Blo 417772 420927 := bstep (se 1 (by rfl) ⟨315695, by rfl⟩ : syracuseStep 420927 = 631391) B631391
theorem B1600793 : Blo 417772 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B421247 : Blo 417772 421247 := bstep (se 1 (by rfl) ⟨315935, by rfl⟩ : syracuseStep 421247 = 631871) B631871
theorem B421275 : Blo 417772 421275 := bstep (se 1 (by rfl) ⟨315956, by rfl⟩ : syracuseStep 421275 = 631913) B631913
theorem B945575 : Blo 417772 945575 := bstep (se 1 (by rfl) ⟨709181, by rfl⟩ : syracuseStep 945575 = 1418363) B1418363
theorem B421343 : Blo 417772 421343 := bstep (se 1 (by rfl) ⟨316007, by rfl⟩ : syracuseStep 421343 = 632015) B632015
theorem B1600991 : Blo 417772 1600991 := bstep (se 1 (by rfl) ⟨1200743, by rfl⟩ : syracuseStep 1600991 = 2401487) B2401487
theorem B945755 : Blo 417772 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B421479 : Blo 417772 421479 := bstep (se 1 (by rfl) ⟨316109, by rfl⟩ : syracuseStep 421479 = 632219) B632219
theorem B421627 : Blo 417772 421627 := bstep (se 1 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 421627 = 632441) B632441
theorem B421695 : Blo 417772 421695 := bstep (se 1 (by rfl) ⟨316271, by rfl⟩ : syracuseStep 421695 = 632543) B632543
theorem B421759 : Blo 417772 421759 := bstep (se 1 (by rfl) ⟨316319, by rfl⟩ : syracuseStep 421759 = 632639) B632639
theorem B1339355 : Blo 417772 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B946169 : Blo 417772 946169 := bstep (se 2 (by rfl) ⟨354813, by rfl⟩ : syracuseStep 946169 = 709627) B709627
theorem B946259 : Blo 417772 946259 := bstep (se 1 (by rfl) ⟨709694, by rfl⟩ : syracuseStep 946259 = 1419389) B1419389
theorem B2126087 : Blo 417772 2126087 := bstep (se 1 (by rfl) ⟨1594565, by rfl⟩ : syracuseStep 2126087 = 3189131) B3189131
theorem B946439 : Blo 417772 946439 := bstep (se 1 (by rfl) ⟨709829, by rfl⟩ : syracuseStep 946439 = 1419659) B1419659
theorem B946745 : Blo 417772 946745 := bstep (se 2 (by rfl) ⟨355029, by rfl⟩ : syracuseStep 946745 = 710059) B710059
theorem B2388797 : Blo 417772 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B2126735 : Blo 417772 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B947465 : Blo 417772 947465 := bstep (se 2 (by rfl) ⟨355299, by rfl⟩ : syracuseStep 947465 = 710599) B710599
theorem B947519 : Blo 417772 947519 := bstep (se 1 (by rfl) ⟨710639, by rfl⟩ : syracuseStep 947519 = 1421279) B1421279
theorem B947627 : Blo 417772 947627 := bstep (se 1 (by rfl) ⟨710720, by rfl⟩ : syracuseStep 947627 = 1421441) B1421441
theorem B1799833 : Blo 417772 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B947951 : Blo 417772 947951 := bstep (se 1 (by rfl) ⟨710963, by rfl⟩ : syracuseStep 947951 = 1421927) B1421927
theorem B2258887 : Blo 417772 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B948167 : Blo 417772 948167 := bstep (se 1 (by rfl) ⟨711125, by rfl⟩ : syracuseStep 948167 = 1422251) B1422251
theorem B1341623 : Blo 417772 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3832019 : Blo 417772 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B948455 : Blo 417772 948455 := bstep (se 1 (by rfl) ⟨711341, by rfl⟩ : syracuseStep 948455 = 1422683) B1422683
theorem B948473 : Blo 417772 948473 := bstep (se 2 (by rfl) ⟨355677, by rfl⟩ : syracuseStep 948473 = 711355) B711355
theorem B948527 : Blo 417772 948527 := bstep (se 1 (by rfl) ⟨711395, by rfl⟩ : syracuseStep 948527 = 1422791) B1422791
theorem B15366581 : Blo 417772 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B948743 : Blo 417772 948743 := bstep (se 1 (by rfl) ⟨711557, by rfl⟩ : syracuseStep 948743 = 1423115) B1423115
theorem B948923 : Blo 417772 948923 := bstep (se 1 (by rfl) ⟨711692, by rfl⟩ : syracuseStep 948923 = 1423385) B1423385
theorem B2128841 : Blo 417772 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B425423 : Blo 417772 425423 := bstep (se 1 (by rfl) ⟨319067, by rfl⟩ : syracuseStep 425423 = 638135) B638135
theorem B1277435 : Blo 417772 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B2129651 : Blo 417772 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B3178439 : Blo 417772 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B753619 : Blo 417772 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B5375099 : Blo 417772 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B2426431 : Blo 417772 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B1836715 : Blo 417772 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B12977863 : Blo 417772 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B854057 : Blo 417772 854057 := bstep (se 2 (by rfl) ⟨320271, by rfl⟩ : syracuseStep 854057 = 640543) B640543
theorem B22874723 : Blo 417772 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B4295713 : Blo 417772 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B1510625 : Blo 417772 1510625 := bstep (se 2 (by rfl) ⟨566484, by rfl⟩ : syracuseStep 1510625 = 1132969) B1132969
theorem B19468127 : Blo 417772 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B626681 : Blo 417772 626681 := bstep (se 2 (by rfl) ⟨235005, by rfl⟩ : syracuseStep 626681 = 470011) B470011
theorem B626879 : Blo 417772 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B626921 : Blo 417772 626921 := bstep (se 2 (by rfl) ⟨235095, by rfl⟩ : syracuseStep 626921 = 470191) B470191
theorem B13603139 : Blo 417772 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B627047 : Blo 417772 627047 := bstep (se 1 (by rfl) ⟨470285, by rfl⟩ : syracuseStep 627047 = 940571) B940571
theorem B16061327 : Blo 417772 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B627881 : Blo 417772 627881 := bstep (se 2 (by rfl) ⟨235455, by rfl⟩ : syracuseStep 627881 = 470911) B470911
theorem B627947 : Blo 417772 627947 := bstep (se 1 (by rfl) ⟨470960, by rfl⟩ : syracuseStep 627947 = 941921) B941921
theorem B628031 : Blo 417772 628031 := bstep (se 1 (by rfl) ⟨471023, by rfl⟩ : syracuseStep 628031 = 942047) B942047
theorem B628223 : Blo 417772 628223 := bstep (se 1 (by rfl) ⟨471167, by rfl⟩ : syracuseStep 628223 = 942335) B942335
theorem B628331 : Blo 417772 628331 := bstep (se 1 (by rfl) ⟨471248, by rfl⟩ : syracuseStep 628331 = 942497) B942497
theorem B2397863 : Blo 417772 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B628601 : Blo 417772 628601 := bstep (se 2 (by rfl) ⟨235725, by rfl⟩ : syracuseStep 628601 = 471451) B471451
theorem B628847 : Blo 417772 628847 := bstep (se 1 (by rfl) ⟨471635, by rfl⟩ : syracuseStep 628847 = 943271) B943271
theorem B628919 : Blo 417772 628919 := bstep (se 1 (by rfl) ⟨471689, by rfl⟩ : syracuseStep 628919 = 943379) B943379
theorem B34773299 : Blo 417772 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B10328435 : Blo 417772 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B629339 : Blo 417772 629339 := bstep (se 1 (by rfl) ⟨472004, by rfl⟩ : syracuseStep 629339 = 944009) B944009
theorem B629351 : Blo 417772 629351 := bstep (se 1 (by rfl) ⟨472013, by rfl⟩ : syracuseStep 629351 = 944027) B944027
theorem B629375 : Blo 417772 629375 := bstep (se 1 (by rfl) ⟨472031, by rfl⟩ : syracuseStep 629375 = 944063) B944063
theorem B629483 : Blo 417772 629483 := bstep (se 1 (by rfl) ⟨472112, by rfl⟩ : syracuseStep 629483 = 944225) B944225
theorem B629513 : Blo 417772 629513 := bstep (se 2 (by rfl) ⟨236067, by rfl⟩ : syracuseStep 629513 = 472135) B472135
theorem B629753 : Blo 417772 629753 := bstep (se 2 (by rfl) ⟨236157, by rfl⟩ : syracuseStep 629753 = 472315) B472315
theorem B531451 : Blo 417772 531451 := bstep (se 1 (by rfl) ⟨398588, by rfl⟩ : syracuseStep 531451 = 797177) B797177
theorem B793775 : Blo 417772 793775 := bstep (se 1 (by rfl) ⟨595331, by rfl⟩ : syracuseStep 793775 = 1190663) B1190663
theorem B531775 : Blo 417772 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B2399777 : Blo 417772 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B794215 : Blo 417772 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B630383 : Blo 417772 630383 := bstep (se 1 (by rfl) ⟨472787, by rfl⟩ : syracuseStep 630383 = 945575) B945575
theorem B630503 : Blo 417772 630503 := bstep (se 1 (by rfl) ⟨472877, by rfl⟩ : syracuseStep 630503 = 945755) B945755
theorem B532423 : Blo 417772 532423 := bstep (se 1 (by rfl) ⟨399317, by rfl⟩ : syracuseStep 532423 = 798635) B798635
theorem B630779 : Blo 417772 630779 := bstep (se 1 (by rfl) ⟨473084, by rfl⟩ : syracuseStep 630779 = 946169) B946169
theorem B630839 : Blo 417772 630839 := bstep (se 1 (by rfl) ⟨473129, by rfl⟩ : syracuseStep 630839 = 946259) B946259
theorem B5087357 : Blo 417772 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B1417391 : Blo 417772 1417391 := bstep (se 1 (by rfl) ⟨1063043, by rfl⟩ : syracuseStep 1417391 = 2126087) B2126087
theorem B630959 : Blo 417772 630959 := bstep (se 1 (by rfl) ⟨473219, by rfl⟩ : syracuseStep 630959 = 946439) B946439
theorem B1515899 : Blo 417772 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B631163 : Blo 417772 631163 := bstep (se 1 (by rfl) ⟨473372, by rfl⟩ : syracuseStep 631163 = 946745) B946745
theorem B631337 : Blo 417772 631337 := bstep (se 2 (by rfl) ⟨236751, by rfl⟩ : syracuseStep 631337 = 473503) B473503
theorem B1417823 : Blo 417772 1417823 := bstep (se 1 (by rfl) ⟨1063367, by rfl⟩ : syracuseStep 1417823 = 2126735) B2126735
theorem B631433 : Blo 417772 631433 := bstep (se 2 (by rfl) ⟨236787, by rfl⟩ : syracuseStep 631433 = 473575) B473575
theorem B631643 : Blo 417772 631643 := bstep (se 1 (by rfl) ⟨473732, by rfl⟩ : syracuseStep 631643 = 947465) B947465
theorem B631679 : Blo 417772 631679 := bstep (se 1 (by rfl) ⟨473759, by rfl⟩ : syracuseStep 631679 = 947519) B947519
theorem B631751 : Blo 417772 631751 := bstep (se 1 (by rfl) ⟨473813, by rfl⟩ : syracuseStep 631751 = 947627) B947627
theorem B631967 : Blo 417772 631967 := bstep (se 1 (by rfl) ⟨473975, by rfl⟩ : syracuseStep 631967 = 947951) B947951
theorem B632111 : Blo 417772 632111 := bstep (se 1 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 632111 = 948167) B948167
theorem B894415 : Blo 417772 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B632303 : Blo 417772 632303 := bstep (se 1 (by rfl) ⟨474227, by rfl⟩ : syracuseStep 632303 = 948455) B948455
theorem B632315 : Blo 417772 632315 := bstep (se 1 (by rfl) ⟨474236, by rfl⟩ : syracuseStep 632315 = 948473) B948473
theorem B632351 : Blo 417772 632351 := bstep (se 1 (by rfl) ⟨474263, by rfl⟩ : syracuseStep 632351 = 948527) B948527
theorem B2696777 : Blo 417772 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B632495 : Blo 417772 632495 := bstep (se 1 (by rfl) ⟨474371, by rfl⟩ : syracuseStep 632495 = 948743) B948743
theorem B632585 : Blo 417772 632585 := bstep (se 2 (by rfl) ⟨237219, by rfl⟩ : syracuseStep 632585 = 474439) B474439
theorem B632615 : Blo 417772 632615 := bstep (se 1 (by rfl) ⟨474461, by rfl⟩ : syracuseStep 632615 = 948923) B948923
theorem B599899 : Blo 417772 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B3188645 : Blo 417772 3188645 := bstep (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) B597871
theorem B1419227 : Blo 417772 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B6007081 : Blo 417772 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B1419767 : Blo 417772 1419767 := bstep (se 1 (by rfl) ⟨1064825, by rfl⟩ : syracuseStep 1419767 = 2129651) B2129651
theorem B1190447 : Blo 417772 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B4303469 : Blo 417772 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B1059439 : Blo 417772 1059439 := bstep (se 1 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 1059439 = 1589159) B1589159
theorem B1223849 : Blo 417772 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B1191095 : Blo 417772 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B1912031 : Blo 417772 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B5385761 : Blo 417772 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B470695 : Blo 417772 470695 := bstep (se 1 (by rfl) ⟨353021, by rfl⟩ : syracuseStep 470695 = 706043) B706043
theorem B18132659 : Blo 417772 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B1060847 : Blo 417772 1060847 := bstep (se 1 (by rfl) ⟨795635, by rfl⟩ : syracuseStep 1060847 = 1591271) B1591271
theorem B4599935 : Blo 417772 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B1192097 : Blo 417772 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B1192735 : Blo 417772 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B471847 : Blo 417772 471847 := bstep (se 1 (by rfl) ⟨353885, by rfl⟩ : syracuseStep 471847 = 707771) B707771
theorem B897961 : Blo 417772 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B3453961 : Blo 417772 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B10171601 : Blo 417772 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B1062143 : Blo 417772 1062143 := bstep (se 1 (by rfl) ⟨796607, by rfl⟩ : syracuseStep 1062143 = 1593215) B1593215
theorem B472603 : Blo 417772 472603 := bstep (se 1 (by rfl) ⟨354452, by rfl⟩ : syracuseStep 472603 = 708905) B708905
theorem B1193555 : Blo 417772 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B472783 : Blo 417772 472783 := bstep (se 1 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 472783 = 709175) B709175
theorem B10368773 : Blo 417772 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B669799 : Blo 417772 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B768287 : Blo 417772 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B473647 : Blo 417772 473647 := bstep (se 1 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 473647 = 710471) B710471
theorem B6830891 : Blo 417772 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B1915787 : Blo 417772 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B199900547 : Blo 417772 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B1064603 : Blo 417772 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B2014895 : Blo 417772 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B3194963 : Blo 417772 3194963 := bstep (se 1 (by rfl) ⟨2396222, by rfl⟩ : syracuseStep 3194963 = 4792445) B4792445
theorem B11452589 : Blo 417772 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B1196221 : Blo 417772 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B1065271 : Blo 417772 1065271 := bstep (se 1 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 1065271 = 1597907) B1597907
theorem B1589615 : Blo 417772 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B1786711 : Blo 417772 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B1066031 : Blo 417772 1066031 := bstep (se 1 (by rfl) ⟨799523, by rfl⟩ : syracuseStep 1066031 = 1599047) B1599047
theorem B1197337 : Blo 417772 1197337 := bstep (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) B898003
theorem B3622319 : Blo 417772 3622319 := bstep (se 1 (by rfl) ⟨2716739, by rfl⟩ : syracuseStep 3622319 = 5433479) B5433479
theorem B1590785 : Blo 417772 1590785 := bstep (se 2 (by rfl) ⟨596544, by rfl⟩ : syracuseStep 1590785 = 1193089) B1193089
theorem B1066679 : Blo 417772 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B2148353 : Blo 417772 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B673913 : Blo 417772 673913 := bstep (se 2 (by rfl) ⟨252717, by rfl⟩ : syracuseStep 673913 = 505435) B505435
theorem B1067195 : Blo 417772 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B2115881 : Blo 417772 2115881 := bstep (se 2 (by rfl) ⟨793455, by rfl⟩ : syracuseStep 2115881 = 1586911) B1586911
theorem B12962105 : Blo 417772 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B1067327 : Blo 417772 1067327 := bstep (se 1 (by rfl) ⟨800495, by rfl⟩ : syracuseStep 1067327 = 1600991) B1600991
theorem B1296815 : Blo 417772 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B2018047 : Blo 417772 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B1592531 : Blo 417772 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B2117177 : Blo 417772 2117177 := bstep (se 2 (by rfl) ⟨793941, by rfl⟩ : syracuseStep 2117177 = 1587883) B1587883
theorem B39308971 : Blo 417772 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B1134461 : Blo 417772 1134461 := bstep (se 3 (by rfl) ⟨212711, by rfl⟩ : syracuseStep 1134461 = 425423) B425423
theorem B708635 : Blo 417772 708635 := bstep (se 1 (by rfl) ⟨531476, by rfl⟩ : syracuseStep 708635 = 1062953) B1062953
theorem B708655 : Blo 417772 708655 := bstep (se 1 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 708655 = 1062983) B1062983
theorem B10244387 : Blo 417772 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B3593483 : Blo 417772 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B1004825 : Blo 417772 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B2118959 : Blo 417772 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B16602457 : Blo 417772 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B710383 : Blo 417772 710383 := bstep (se 1 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 710383 = 1065575) B1065575
theorem B940103 : Blo 417772 940103 := bstep (se 1 (by rfl) ⟨705077, by rfl⟩ : syracuseStep 940103 = 1410155) B1410155
theorem B2677481 : Blo 417772 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2022121 : Blo 417772 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B4316105 : Blo 417772 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B2677967 : Blo 417772 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B2121065 : Blo 417772 2121065 := bstep (se 2 (by rfl) ⟨795399, by rfl⟩ : syracuseStep 2121065 = 1590799) B1590799
theorem B417775 : Blo 417772 417775 := bstep (se 1 (by rfl) ⟨313331, by rfl⟩ : syracuseStep 417775 = 626663) B626663
theorem B417855 : Blo 417772 417855 := bstep (se 1 (by rfl) ⟨313391, by rfl⟩ : syracuseStep 417855 = 626783) B626783
theorem B417863 : Blo 417772 417863 := bstep (se 1 (by rfl) ⟨313397, by rfl⟩ : syracuseStep 417863 = 626795) B626795
theorem B417895 : Blo 417772 417895 := bstep (se 1 (by rfl) ⟨313421, by rfl⟩ : syracuseStep 417895 = 626843) B626843
theorem B7626959 : Blo 417772 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B418463 : Blo 417772 418463 := bstep (se 1 (by rfl) ⟨313847, by rfl⟩ : syracuseStep 418463 = 627695) B627695
theorem B418719 : Blo 417772 418719 := bstep (se 1 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 418719 = 628079) B628079
theorem B418799 : Blo 417772 418799 := bstep (se 1 (by rfl) ⟨314099, by rfl⟩ : syracuseStep 418799 = 628199) B628199
theorem B418907 : Blo 417772 418907 := bstep (se 1 (by rfl) ⟨314180, by rfl⟩ : syracuseStep 418907 = 628361) B628361
theorem B418919 : Blo 417772 418919 := bstep (se 1 (by rfl) ⟨314189, by rfl⟩ : syracuseStep 418919 = 628379) B628379
theorem B126084313 : Blo 417772 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B1696987 : Blo 417772 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B419047 : Blo 417772 419047 := bstep (se 1 (by rfl) ⟨314285, by rfl⟩ : syracuseStep 419047 = 628571) B628571
theorem B17229277 : Blo 417772 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B419303 : Blo 417772 419303 := bstep (se 1 (by rfl) ⟨314477, by rfl⟩ : syracuseStep 419303 = 628955) B628955
theorem B560424491 : Blo 417772 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B419483 : Blo 417772 419483 := bstep (se 1 (by rfl) ⟨314612, by rfl⟩ : syracuseStep 419483 = 629225) B629225
theorem B2025121 : Blo 417772 2025121 := bstep (se 2 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 2025121 = 1518841) B1518841
theorem B943955 : Blo 417772 943955 := bstep (se 1 (by rfl) ⟨707966, by rfl⟩ : syracuseStep 943955 = 1415933) B1415933
theorem B419743 : Blo 417772 419743 := bstep (se 1 (by rfl) ⟨314807, by rfl⟩ : syracuseStep 419743 = 629615) B629615
theorem B419751 : Blo 417772 419751 := bstep (se 1 (by rfl) ⟨314813, by rfl⟩ : syracuseStep 419751 = 629627) B629627
theorem B420327 : Blo 417772 420327 := bstep (se 1 (by rfl) ⟨315245, by rfl⟩ : syracuseStep 420327 = 630491) B630491
theorem B420507 : Blo 417772 420507 := bstep (se 1 (by rfl) ⟨315380, by rfl⟩ : syracuseStep 420507 = 630761) B630761
theorem B2386655 : Blo 417772 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B945017 : Blo 417772 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B1010561 : Blo 417772 1010561 := bstep (se 2 (by rfl) ⟨378960, by rfl⟩ : syracuseStep 1010561 = 757921) B757921
theorem B5172173 : Blo 417772 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B420975 : Blo 417772 420975 := bstep (se 1 (by rfl) ⟨315731, by rfl⟩ : syracuseStep 420975 = 631463) B631463
theorem B421055 : Blo 417772 421055 := bstep (se 1 (by rfl) ⟨315791, by rfl⟩ : syracuseStep 421055 = 631583) B631583
theorem B421071 : Blo 417772 421071 := bstep (se 1 (by rfl) ⟨315803, by rfl⟩ : syracuseStep 421071 = 631607) B631607
theorem B1600823 : Blo 417772 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B421191 : Blo 417772 421191 := bstep (se 1 (by rfl) ⟨315893, by rfl⟩ : syracuseStep 421191 = 631787) B631787
theorem B2191033 : Blo 417772 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B1273981 : Blo 417772 1273981 := bstep (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) B477743
theorem B2650439 : Blo 417772 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B1798793 : Blo 417772 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B947321 : Blo 417772 947321 := bstep (se 2 (by rfl) ⟨355245, by rfl⟩ : syracuseStep 947321 = 710491) B710491
theorem B2127059 : Blo 417772 2127059 := bstep (se 1 (by rfl) ⟨1595294, by rfl⟩ : syracuseStep 2127059 = 3190589) B3190589
theorem B3011849 : Blo 417772 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B948095 : Blo 417772 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B2685089 : Blo 417772 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B48953621 : Blo 417772 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B948563 : Blo 417772 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B2554679 : Blo 417772 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B10746917 : Blo 417772 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B1342955 : Blo 417772 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B851623 : Blo 417772 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B12156713 : Blo 417772 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B3571613 : Blo 417772 3571613 := bstep (se 3 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 3571613 = 1339355) B1339355
theorem B2129975 : Blo 417772 2129975 := bstep (se 1 (by rfl) ⟨1597481, by rfl⟩ : syracuseStep 2129975 = 3194963) B3194963
theorem B7635059 : Blo 417772 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B3178925 : Blo 417772 3178925 := bstep (se 3 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 3178925 = 1192097) B1192097
theorem B3572261 : Blo 417772 3572261 := bstep (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) B669799
theorem B1410587 : Blo 417772 1410587 := bstep (se 1 (by rfl) ⟨1057940, by rfl⟩ : syracuseStep 1410587 = 2115881) B2115881
theorem B2262649 : Blo 417772 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B22972369 : Blo 417772 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B1411451 : Blo 417772 1411451 := bstep (se 1 (by rfl) ⟨1058588, by rfl⟩ : syracuseStep 1411451 = 2117177) B2117177
theorem B12978751 : Blo 417772 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B756307 : Blo 417772 756307 := bstep (se 1 (by rfl) ⟨567230, by rfl⟩ : syracuseStep 756307 = 1134461) B1134461
theorem B1412585 : Blo 417772 1412585 := bstep (se 2 (by rfl) ⟨529719, by rfl⟩ : syracuseStep 1412585 = 1059439) B1059439
theorem B2395655 : Blo 417772 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B1412639 : Blo 417772 1412639 := bstep (se 1 (by rfl) ⟨1059479, by rfl⟩ : syracuseStep 1412639 = 2118959) B2118959
theorem B2690729 : Blo 417772 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B626735 : Blo 417772 626735 := bstep (se 1 (by rfl) ⟨470051, by rfl⟩ : syracuseStep 626735 = 940103) B940103
theorem B3182813 : Blo 417772 3182813 := bstep (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) B1193555
theorem B6885623 : Blo 417772 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B13832693 : Blo 417772 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B529183 : Blo 417772 529183 := bstep (se 1 (by rfl) ⟨396887, by rfl⟩ : syracuseStep 529183 = 793775) B793775
theorem B627593 : Blo 417772 627593 := bstep (se 2 (by rfl) ⟨235347, by rfl⟩ : syracuseStep 627593 = 470695) B470695
theorem B1414043 : Blo 417772 1414043 := bstep (se 1 (by rfl) ⟨1060532, by rfl⟩ : syracuseStep 1414043 = 2121065) B2121065
theorem B5084639 : Blo 417772 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B629129 : Blo 417772 629129 := bstep (se 2 (by rfl) ⟨235923, by rfl⟩ : syracuseStep 629129 = 471847) B471847
theorem B629303 : Blo 417772 629303 := bstep (se 1 (by rfl) ⟨471977, by rfl⟩ : syracuseStep 629303 = 943955) B943955
theorem B793631 : Blo 417772 793631 := bstep (se 1 (by rfl) ⟨595223, by rfl⟩ : syracuseStep 793631 = 1190447) B1190447
theorem B630011 : Blo 417772 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B3448115 : Blo 417772 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B630137 : Blo 417772 630137 := bstep (se 2 (by rfl) ⟨236301, by rfl⟩ : syracuseStep 630137 = 472603) B472603
theorem B794063 : Blo 417772 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B630377 : Blo 417772 630377 := bstep (se 2 (by rfl) ⟨236391, by rfl⟩ : syracuseStep 630377 = 472783) B472783
theorem B2694829 : Blo 417772 2694829 := bstep (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) B1010561
theorem B11509613 : Blo 417772 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B631529 : Blo 417772 631529 := bstep (se 2 (by rfl) ⟨236823, by rfl⟩ : syracuseStep 631529 = 473647) B473647
theorem B631547 : Blo 417772 631547 := bstep (se 1 (by rfl) ⟨473660, by rfl⟩ : syracuseStep 631547 = 947321) B947321
theorem B1418039 : Blo 417772 1418039 := bstep (se 1 (by rfl) ⟨1063529, by rfl⟩ : syracuseStep 1418039 = 2127059) B2127059
theorem B2007899 : Blo 417772 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B2696161 : Blo 417772 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B69215269 : Blo 417772 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B632063 : Blo 417772 632063 := bstep (se 1 (by rfl) ⟨474047, by rfl⟩ : syracuseStep 632063 = 948095) B948095
theorem B632375 : Blo 417772 632375 := bstep (se 1 (by rfl) ⟨474281, by rfl⟩ : syracuseStep 632375 = 948563) B948563
theorem B1058953 : Blo 417772 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B895303 : Blo 417772 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B8104475 : Blo 417772 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B1059743 : Blo 417772 1059743 := bstep (se 1 (by rfl) ⟨794807, by rfl⟩ : syracuseStep 1059743 = 1589615) B1589615
theorem B1420361 : Blo 417772 1420361 := bstep (se 2 (by rfl) ⟨532635, by rfl⟩ : syracuseStep 1420361 = 1065271) B1065271
theorem B3583399 : Blo 417772 3583399 := bstep (se 1 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 3583399 = 5375099) B5375099
theorem B1060523 : Blo 417772 1060523 := bstep (se 1 (by rfl) ⟨795392, by rfl⟩ : syracuseStep 1060523 = 1590785) B1590785
theorem B569371 : Blo 417772 569371 := bstep (se 1 (by rfl) ⟨427028, by rfl⟩ : syracuseStep 569371 = 854057) B854057
theorem B168112417 : Blo 417772 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B15249815 : Blo 417772 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B1192553 : Blo 417772 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1061687 : Blo 417772 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B2700161 : Blo 417772 2700161 := bstep (se 2 (by rfl) ⟨1012560, by rfl⟩ : syracuseStep 2700161 = 2025121) B2025121
theorem B799865 : Blo 417772 799865 := bstep (se 2 (by rfl) ⟨299949, by rfl⟩ : syracuseStep 799865 = 599899) B599899
theorem B472423 : Blo 417772 472423 := bstep (se 1 (by rfl) ⟨354317, by rfl⟩ : syracuseStep 472423 = 708635) B708635
theorem B6829591 : Blo 417772 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B8009441 : Blo 417772 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B669883 : Blo 417772 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B23182199 : Blo 417772 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B1784987 : Blo 417772 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B1785311 : Blo 417772 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B52411961 : Blo 417772 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B3391571 : Blo 417772 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B7160237 : Blo 417772 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B1590313 : Blo 417772 1590313 := bstep (se 2 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 1590313 = 1192735) B1192735
theorem B1197281 : Blo 417772 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B4605281 : Blo 417772 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B2868979 : Blo 417772 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B22136609 : Blo 417772 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B1591103 : Blo 417772 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B1067215 : Blo 417772 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B3590507 : Blo 417772 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B707231 : Blo 417772 707231 := bstep (se 1 (by rfl) ⟨530423, by rfl⟩ : syracuseStep 707231 = 1060847) B1060847
theorem B3066623 : Blo 417772 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B1199195 : Blo 417772 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B3263597 : Blo 417772 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B708095 : Blo 417772 708095 := bstep (se 1 (by rfl) ⟨531071, by rfl⟩ : syracuseStep 708095 = 1062143) B1062143
theorem B4541989 : Blo 417772 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B11685509 : Blo 417772 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B708601 : Blo 417772 708601 := bstep (se 2 (by rfl) ⟨265725, by rfl⟩ : syracuseStep 708601 = 531451) B531451
theorem B512191 : Blo 417772 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B709033 : Blo 417772 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B7164611 : Blo 417772 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B709735 : Blo 417772 709735 := bstep (se 1 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 709735 = 1064603) B1064603
theorem B709897 : Blo 417772 709897 := bstep (se 2 (by rfl) ⟨266211, by rfl⟩ : syracuseStep 709897 = 532423) B532423
theorem B2381075 : Blo 417772 2381075 := bstep (se 1 (by rfl) ⟨1785806, by rfl⟩ : syracuseStep 2381075 = 3571613) B3571613
theorem B1594961 : Blo 417772 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B710687 : Blo 417772 710687 := bstep (se 1 (by rfl) ⟨533015, by rfl⟩ : syracuseStep 710687 = 1066031) B1066031
theorem B7067837 : Blo 417772 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B2414879 : Blo 417772 2414879 := bstep (se 1 (by rfl) ⟨1811159, by rfl⟩ : syracuseStep 2414879 = 3622319) B3622319
theorem B2382281 : Blo 417772 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B711119 : Blo 417772 711119 := bstep (se 1 (by rfl) ⟨533339, by rfl⟩ : syracuseStep 711119 = 1066679) B1066679
theorem B1432235 : Blo 417772 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B449275 : Blo 417772 449275 := bstep (se 1 (by rfl) ⟨336956, by rfl⟩ : syracuseStep 449275 = 673913) B673913
theorem B711463 : Blo 417772 711463 := bstep (se 1 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 711463 = 1067195) B1067195
theorem B8641403 : Blo 417772 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B711551 : Blo 417772 711551 := bstep (se 1 (by rfl) ⟨533663, by rfl⟩ : syracuseStep 711551 = 1067327) B1067327
theorem B1596449 : Blo 417772 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B3235241 : Blo 417772 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B1007083 : Blo 417772 1007083 := bstep (se 1 (by rfl) ⟨755312, by rfl⟩ : syracuseStep 1007083 = 1510625) B1510625
theorem B2448953 : Blo 417772 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B417787 : Blo 417772 417787 := bstep (se 1 (by rfl) ⟨313340, by rfl⟩ : syracuseStep 417787 = 626681) B626681
theorem B417919 : Blo 417772 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B417947 : Blo 417772 417947 := bstep (se 1 (by rfl) ⟨313460, by rfl⟩ : syracuseStep 417947 = 626921) B626921
theorem B9068759 : Blo 417772 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B418031 : Blo 417772 418031 := bstep (se 1 (by rfl) ⟨313523, by rfl⟩ : syracuseStep 418031 = 627047) B627047
theorem B10707551 : Blo 417772 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B418587 : Blo 417772 418587 := bstep (se 1 (by rfl) ⟨313940, by rfl⟩ : syracuseStep 418587 = 627881) B627881
theorem B418631 : Blo 417772 418631 := bstep (se 1 (by rfl) ⟨313973, by rfl⟩ : syracuseStep 418631 = 627947) B627947
theorem B418687 : Blo 417772 418687 := bstep (se 1 (by rfl) ⟨314015, by rfl⟩ : syracuseStep 418687 = 628031) B628031
theorem B418815 : Blo 417772 418815 := bstep (se 1 (by rfl) ⟨314111, by rfl⟩ : syracuseStep 418815 = 628223) B628223
theorem B418887 : Blo 417772 418887 := bstep (se 1 (by rfl) ⟨314165, by rfl⟩ : syracuseStep 418887 = 628331) B628331
theorem B1598575 : Blo 417772 1598575 := bstep (se 1 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 1598575 = 2397863) B2397863
theorem B419067 : Blo 417772 419067 := bstep (se 1 (by rfl) ⟨314300, by rfl⟩ : syracuseStep 419067 = 628601) B628601
theorem B5727617 : Blo 417772 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B419231 : Blo 417772 419231 := bstep (se 1 (by rfl) ⟨314423, by rfl⟩ : syracuseStep 419231 = 628847) B628847
theorem B419279 : Blo 417772 419279 := bstep (se 1 (by rfl) ⟨314459, by rfl⟩ : syracuseStep 419279 = 628919) B628919
theorem B419559 : Blo 417772 419559 := bstep (se 1 (by rfl) ⟨314669, by rfl⟩ : syracuseStep 419559 = 629339) B629339
theorem B419567 : Blo 417772 419567 := bstep (se 1 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 419567 = 629351) B629351
theorem B419583 : Blo 417772 419583 := bstep (se 1 (by rfl) ⟨314687, by rfl⟩ : syracuseStep 419583 = 629375) B629375
theorem B419655 : Blo 417772 419655 := bstep (se 1 (by rfl) ⟨314741, by rfl⟩ : syracuseStep 419655 = 629483) B629483
theorem B419675 : Blo 417772 419675 := bstep (se 1 (by rfl) ⟨314756, by rfl⟩ : syracuseStep 419675 = 629513) B629513
theorem B419835 : Blo 417772 419835 := bstep (se 1 (by rfl) ⟨314876, by rfl⟩ : syracuseStep 419835 = 629753) B629753
theorem B1599851 : Blo 417772 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B420255 : Blo 417772 420255 := bstep (se 1 (by rfl) ⟨315191, by rfl⟩ : syracuseStep 420255 = 630383) B630383
theorem B420335 : Blo 417772 420335 := bstep (se 1 (by rfl) ⟨315251, by rfl⟩ : syracuseStep 420335 = 630503) B630503
theorem B420519 : Blo 417772 420519 := bstep (se 1 (by rfl) ⟨315389, by rfl⟩ : syracuseStep 420519 = 630779) B630779
theorem B420559 : Blo 417772 420559 := bstep (se 1 (by rfl) ⟨315419, by rfl⟩ : syracuseStep 420559 = 630839) B630839
theorem B944873 : Blo 417772 944873 := bstep (se 2 (by rfl) ⟨354327, by rfl⟩ : syracuseStep 944873 = 708655) B708655
theorem B944927 : Blo 417772 944927 := bstep (se 1 (by rfl) ⟨708695, by rfl⟩ : syracuseStep 944927 = 1417391) B1417391
theorem B420639 : Blo 417772 420639 := bstep (se 1 (by rfl) ⟨315479, by rfl⟩ : syracuseStep 420639 = 630959) B630959
theorem B1698641 : Blo 417772 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B1010599 : Blo 417772 1010599 := bstep (se 1 (by rfl) ⟨757949, by rfl⟩ : syracuseStep 1010599 = 1515899) B1515899
theorem B420775 : Blo 417772 420775 := bstep (se 1 (by rfl) ⟨315581, by rfl⟩ : syracuseStep 420775 = 631163) B631163
theorem B420891 : Blo 417772 420891 := bstep (se 1 (by rfl) ⟨315668, by rfl⟩ : syracuseStep 420891 = 631337) B631337
theorem B945215 : Blo 417772 945215 := bstep (se 1 (by rfl) ⟨708911, by rfl⟩ : syracuseStep 945215 = 1417823) B1417823
theorem B420955 : Blo 417772 420955 := bstep (se 1 (by rfl) ⟨315716, by rfl⟩ : syracuseStep 420955 = 631433) B631433
theorem B421095 : Blo 417772 421095 := bstep (se 1 (by rfl) ⟨315821, by rfl⟩ : syracuseStep 421095 = 631643) B631643
theorem B421119 : Blo 417772 421119 := bstep (se 1 (by rfl) ⟨315839, by rfl⟩ : syracuseStep 421119 = 631679) B631679
theorem B421167 : Blo 417772 421167 := bstep (se 1 (by rfl) ⟨315875, by rfl⟩ : syracuseStep 421167 = 631751) B631751
theorem B421311 : Blo 417772 421311 := bstep (se 1 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 421311 = 631967) B631967
theorem B421407 : Blo 417772 421407 := bstep (se 1 (by rfl) ⟨316055, by rfl⟩ : syracuseStep 421407 = 632111) B632111
theorem B421535 : Blo 417772 421535 := bstep (se 1 (by rfl) ⟨316151, by rfl⟩ : syracuseStep 421535 = 632303) B632303
theorem B421543 : Blo 417772 421543 := bstep (se 1 (by rfl) ⟨316157, by rfl⟩ : syracuseStep 421543 = 632315) B632315
theorem B421567 : Blo 417772 421567 := bstep (se 1 (by rfl) ⟨316175, by rfl⟩ : syracuseStep 421567 = 632351) B632351
theorem B373616327 : Blo 417772 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B1797851 : Blo 417772 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B421663 : Blo 417772 421663 := bstep (se 1 (by rfl) ⟨316247, by rfl⟩ : syracuseStep 421663 = 632495) B632495
theorem B421723 : Blo 417772 421723 := bstep (se 1 (by rfl) ⟨316292, by rfl⟩ : syracuseStep 421723 = 632585) B632585
theorem B421743 : Blo 417772 421743 := bstep (se 1 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 421743 = 632615) B632615
theorem B2125763 : Blo 417772 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B946151 : Blo 417772 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B946511 : Blo 417772 946511 := bstep (se 1 (by rfl) ⟨709883, by rfl⟩ : syracuseStep 946511 = 1419767) B1419767
theorem B1274687 : Blo 417772 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B947177 : Blo 417772 947177 := bstep (se 2 (by rfl) ⟨355191, by rfl⟩ : syracuseStep 947177 = 710383) B710383
theorem B12088439 : Blo 417772 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B6781067 : Blo 417772 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B6912515 : Blo 417772 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B32635747 : Blo 417772 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B4553927 : Blo 417772 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B1703119 : Blo 417772 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1277191 : Blo 417772 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B133267031 : Blo 417772 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B1343263 : Blo 417772 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B2261047 : Blo 417772 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B2131433 : Blo 417772 2131433 := bstep (se 2 (by rfl) ⟨799287, by rfl⟩ : syracuseStep 2131433 = 1598575) B1598575
theorem B2393671 : Blo 417772 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B3016865 : Blo 417772 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B4590415 : Blo 417772 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B1411937 : Blo 417772 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B17305001 : Blo 417772 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B1609919 : Blo 417772 1609919 := bstep (se 1 (by rfl) ⟨1207439, by rfl⟩ : syracuseStep 1609919 = 2414879) B2414879
theorem B954823 : Blo 417772 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B529087 : Blo 417772 529087 := bstep (se 1 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 529087 = 793631) B793631
theorem B2298743 : Blo 417772 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B7673075 : Blo 417772 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B759161 : Blo 417772 759161 := bstep (se 2 (by rfl) ⟨284685, by rfl⟩ : syracuseStep 759161 = 569371) B569371
theorem B629897 : Blo 417772 629897 := bstep (se 2 (by rfl) ⟨236211, by rfl⟩ : syracuseStep 629897 = 472423) B472423
theorem B629915 : Blo 417772 629915 := bstep (se 1 (by rfl) ⟨472436, by rfl⟩ : syracuseStep 629915 = 944873) B944873
theorem B629951 : Blo 417772 629951 := bstep (se 1 (by rfl) ⟨472463, by rfl⟩ : syracuseStep 629951 = 944927) B944927
theorem B630143 : Blo 417772 630143 := bstep (se 1 (by rfl) ⟨472607, by rfl⟩ : syracuseStep 630143 = 945215) B945215
theorem B249077551 : Blo 417772 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B1417175 : Blo 417772 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B630767 : Blo 417772 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B631007 : Blo 417772 631007 := bstep (se 1 (by rfl) ⟨473255, by rfl⟩ : syracuseStep 631007 = 946511) B946511
theorem B893177 : Blo 417772 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B10166543 : Blo 417772 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B795035 : Blo 417772 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B631451 : Blo 417772 631451 := bstep (se 1 (by rfl) ⟨473588, by rfl⟩ : syracuseStep 631451 = 947177) B947177
theorem B533243 : Blo 417772 533243 := bstep (se 1 (by rfl) ⟨399932, by rfl⟩ : syracuseStep 533243 = 799865) B799865
theorem B599033 : Blo 417772 599033 := bstep (se 2 (by rfl) ⟨224637, by rfl⟩ : syracuseStep 599033 = 449275) B449275
theorem B2270825 : Blo 417772 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B1189991 : Blo 417772 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B1190207 : Blo 417772 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B34941307 : Blo 417772 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B88844687 : Blo 417772 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B1419983 : Blo 417772 1419983 := bstep (se 1 (by rfl) ⟨1064987, by rfl⟩ : syracuseStep 1419983 = 2129975) B2129975
theorem B5090039 : Blo 417772 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B798187 : Blo 417772 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B1060735 : Blo 417772 1060735 := bstep (se 1 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 1060735 = 1591103) B1591103
theorem B92287025 : Blo 417772 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B471487 : Blo 417772 471487 := bstep (se 1 (by rfl) ⟨353615, by rfl⟩ : syracuseStep 471487 = 707231) B707231
theorem B2044415 : Blo 417772 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B799463 : Blo 417772 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B2175731 : Blo 417772 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B472063 : Blo 417772 472063 := bstep (se 1 (by rfl) ⟨354047, by rfl⟩ : syracuseStep 472063 = 708095) B708095
theorem B1422953 : Blo 417772 1422953 := bstep (se 2 (by rfl) ⟨533607, by rfl⟩ : syracuseStep 1422953 = 1067215) B1067215
theorem B9221795 : Blo 417772 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B1587383 : Blo 417772 1587383 := bstep (se 1 (by rfl) ⟨1190537, by rfl⟩ : syracuseStep 1587383 = 2381075) B2381075
theorem B3389759 : Blo 417772 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B1063307 : Blo 417772 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B473791 : Blo 417772 473791 := bstep (se 1 (by rfl) ⟨355343, by rfl⟩ : syracuseStep 473791 = 710687) B710687
theorem B1588187 : Blo 417772 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B474079 : Blo 417772 474079 := bstep (se 1 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 474079 = 711119) B711119
theorem B474367 : Blo 417772 474367 := bstep (se 1 (by rfl) ⟨355775, by rfl⟩ : syracuseStep 474367 = 711551) B711551
theorem B1064299 : Blo 417772 1064299 := bstep (se 1 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 1064299 = 1596449) B1596449
theorem B59030957 : Blo 417772 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B5389861 : Blo 417772 5389861 := bstep (se 4 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 5389861 = 1010599) B1010599
theorem B6045839 : Blo 417772 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B224149889 : Blo 417772 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B3818411 : Blo 417772 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B705577 : Blo 417772 705577 := bstep (se 2 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 705577 = 529183) B529183
theorem B1066567 : Blo 417772 1066567 := bstep (se 1 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 1066567 = 1599851) B1599851
theorem B1132427 : Blo 417772 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B706495 : Blo 417772 706495 := bstep (se 1 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 706495 = 1059743) B1059743
theorem B707015 : Blo 417772 707015 := bstep (se 1 (by rfl) ⟨530261, by rfl⟩ : syracuseStep 707015 = 1060523) B1060523
theorem B1198567 : Blo 417772 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B707791 : Blo 417772 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B2117501 : Blo 417772 2117501 := bstep (se 3 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 2117501 = 794063) B794063
theorem B4608343 : Blo 417772 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B15454799 : Blo 417772 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B3035951 : Blo 417772 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B3593105 : Blo 417772 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B1791017 : Blo 417772 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B2119283 : Blo 417772 2119283 := bstep (se 1 (by rfl) ⟨1589462, by rfl⟩ : syracuseStep 2119283 = 3178925) B3178925
theorem B4773491 : Blo 417772 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B2381507 : Blo 417772 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B3070187 : Blo 417772 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B940391 : Blo 417772 940391 := bstep (se 1 (by rfl) ⟨705293, by rfl⟩ : syracuseStep 940391 = 1410587) B1410587
theorem B3594881 : Blo 417772 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B2120417 : Blo 417772 2120417 := bstep (se 2 (by rfl) ⟨795156, by rfl⟩ : syracuseStep 2120417 = 1590313) B1590313
theorem B940967 : Blo 417772 940967 := bstep (se 1 (by rfl) ⟨705725, by rfl⟩ : syracuseStep 940967 = 1411451) B1411451
theorem B4774949 : Blo 417772 4774949 := bstep (se 4 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 4774949 = 895303) B895303
theorem B3825305 : Blo 417772 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B941723 : Blo 417772 941723 := bstep (se 1 (by rfl) ⟨706292, by rfl⟩ : syracuseStep 941723 = 1412585) B1412585
theorem B1597103 : Blo 417772 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B941759 : Blo 417772 941759 := bstep (se 1 (by rfl) ⟨706319, by rfl⟩ : syracuseStep 941759 = 1412639) B1412639
theorem B7790339 : Blo 417772 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B1793819 : Blo 417772 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B30629825 : Blo 417772 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B417823 : Blo 417772 417823 := bstep (se 1 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 417823 = 626735) B626735
theorem B2121875 : Blo 417772 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B4776407 : Blo 417772 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B418395 : Blo 417772 418395 := bstep (se 1 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 418395 = 627593) B627593
theorem B942695 : Blo 417772 942695 := bstep (se 1 (by rfl) ⟨707021, by rfl⟩ : syracuseStep 942695 = 1414043) B1414043
theorem B1008409 : Blo 417772 1008409 := bstep (se 2 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 1008409 = 756307) B756307
theorem B4711891 : Blo 417772 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B419419 : Blo 417772 419419 := bstep (se 1 (by rfl) ⟨314564, by rfl⟩ : syracuseStep 419419 = 629129) B629129
theorem B419535 : Blo 417772 419535 := bstep (se 1 (by rfl) ⟨314651, by rfl⟩ : syracuseStep 419535 = 629303) B629303
theorem B4777865 : Blo 417772 4777865 := bstep (se 2 (by rfl) ⟨1791699, by rfl⟩ : syracuseStep 4777865 = 3583399) B3583399
theorem B5760935 : Blo 417772 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B6055985 : Blo 417772 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B420007 : Blo 417772 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B420091 : Blo 417772 420091 := bstep (se 1 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 420091 = 630137) B630137
theorem B2156827 : Blo 417772 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B1632635 : Blo 417772 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B420251 : Blo 417772 420251 := bstep (se 1 (by rfl) ⟨315188, by rfl⟩ : syracuseStep 420251 = 630377) B630377
theorem B944801 : Blo 417772 944801 := bstep (se 2 (by rfl) ⟨354300, by rfl⟩ : syracuseStep 944801 = 708601) B708601
theorem B682921 : Blo 417772 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B7138367 : Blo 417772 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B421019 : Blo 417772 421019 := bstep (se 1 (by rfl) ⟨315764, by rfl⟩ : syracuseStep 421019 = 631529) B631529
theorem B421031 : Blo 417772 421031 := bstep (se 1 (by rfl) ⟨315773, by rfl⟩ : syracuseStep 421031 = 631547) B631547
theorem B945359 : Blo 417772 945359 := bstep (se 1 (by rfl) ⟨709019, by rfl⟩ : syracuseStep 945359 = 1418039) B1418039
theorem B945377 : Blo 417772 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B1338599 : Blo 417772 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B421375 : Blo 417772 421375 := bstep (se 1 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 421375 = 632063) B632063
theorem B421583 : Blo 417772 421583 := bstep (se 1 (by rfl) ⟨316187, by rfl⟩ : syracuseStep 421583 = 632375) B632375
theorem B6811685 : Blo 417772 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B946313 : Blo 417772 946313 := bstep (se 2 (by rfl) ⟨354867, by rfl⟩ : syracuseStep 946313 = 709735) B709735
theorem B946529 : Blo 417772 946529 := bstep (se 2 (by rfl) ⟨354948, by rfl⟩ : syracuseStep 946529 = 709897) B709897
theorem B5402983 : Blo 417772 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B9106121 : Blo 417772 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B946907 : Blo 417772 946907 := bstep (se 1 (by rfl) ⟨710180, by rfl⟩ : syracuseStep 946907 = 1420361) B1420361
theorem B849791 : Blo 417772 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B1800107 : Blo 417772 1800107 := bstep (se 1 (by rfl) ⟨1350080, by rfl⟩ : syracuseStep 1800107 = 2700161) B2700161
theorem B8058959 : Blo 417772 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B948617 : Blo 417772 948617 := bstep (se 2 (by rfl) ⟨355731, by rfl⟩ : syracuseStep 948617 = 711463) B711463
theorem B43514329 : Blo 417772 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B5339627 : Blo 417772 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B4520711 : Blo 417772 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B1342777 : Blo 417772 1342777 := bstep (se 2 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 1342777 = 1007083) B1007083
theorem B3014729 : Blo 417772 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B4030559 : Blo 417772 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B1344545 : Blo 417772 1344545 := bstep (se 2 (by rfl) ⟨504204, by rfl⟩ : syracuseStep 1344545 = 1008409) B1008409
theorem B754951 : Blo 417772 754951 := bstep (se 1 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 754951 = 1132427) B1132427
theorem B11536667 : Blo 417772 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B1411667 : Blo 417772 1411667 := bstep (se 1 (by rfl) ⟨1058750, by rfl⟩ : syracuseStep 1411667 = 2117501) B2117501
theorem B2395403 : Blo 417772 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B5115383 : Blo 417772 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B1412855 : Blo 417772 1412855 := bstep (se 1 (by rfl) ⟨1059641, by rfl⟩ : syracuseStep 1412855 = 2119283) B2119283
theorem B3182327 : Blo 417772 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B626927 : Blo 417772 626927 := bstep (se 1 (by rfl) ⟨470195, by rfl⟩ : syracuseStep 626927 = 940391) B940391
theorem B24482213 : Blo 417772 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B2396587 : Blo 417772 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B1413611 : Blo 417772 1413611 := bstep (se 1 (by rfl) ⟨1060208, by rfl⟩ : syracuseStep 1413611 = 2120417) B2120417
theorem B627311 : Blo 417772 627311 := bstep (se 1 (by rfl) ⟨470483, by rfl⟩ : syracuseStep 627311 = 940967) B940967
theorem B3183299 : Blo 417772 3183299 := bstep (se 1 (by rfl) ⟨2387474, by rfl⟩ : syracuseStep 3183299 = 4774949) B4774949
theorem B2266109 : Blo 417772 2266109 := bstep (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) B849791
theorem B627815 : Blo 417772 627815 := bstep (se 1 (by rfl) ⟨470861, by rfl⟩ : syracuseStep 627815 = 941723) B941723
theorem B627839 : Blo 417772 627839 := bstep (se 1 (by rfl) ⟨470879, by rfl⟩ : syracuseStep 627839 = 941759) B941759
theorem B1414313 : Blo 417772 1414313 := bstep (se 2 (by rfl) ⟨530367, by rfl⟩ : syracuseStep 1414313 = 1060735) B1060735
theorem B20419883 : Blo 417772 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B1414583 : Blo 417772 1414583 := bstep (se 1 (by rfl) ⟨1060937, by rfl⟩ : syracuseStep 1414583 = 2121875) B2121875
theorem B595451 : Blo 417772 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B3184271 : Blo 417772 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B628463 : Blo 417772 628463 := bstep (se 1 (by rfl) ⟨471347, by rfl⟩ : syracuseStep 628463 = 942695) B942695
theorem B628649 : Blo 417772 628649 := bstep (se 2 (by rfl) ⟨235743, by rfl⟩ : syracuseStep 628649 = 471487) B471487
theorem B1513883 : Blo 417772 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B3185243 : Blo 417772 3185243 := bstep (se 1 (by rfl) ⟨2388932, by rfl⟩ : syracuseStep 3185243 = 4777865) B4777865
theorem B3840623 : Blo 417772 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B629417 : Blo 417772 629417 := bstep (se 2 (by rfl) ⟨236031, by rfl⟩ : syracuseStep 629417 = 472063) B472063
theorem B4037323 : Blo 417772 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B793327 : Blo 417772 793327 := bstep (se 1 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 793327 = 1189991) B1189991
theorem B793471 : Blo 417772 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B1088423 : Blo 417772 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B629867 : Blo 417772 629867 := bstep (se 1 (by rfl) ⟨472400, by rfl⟩ : syracuseStep 629867 = 944801) B944801
theorem B4758911 : Blo 417772 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B630239 : Blo 417772 630239 := bstep (se 1 (by rfl) ⟨472679, by rfl⟩ : syracuseStep 630239 = 945359) B945359
theorem B630251 : Blo 417772 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B892399 : Blo 417772 892399 := bstep (se 1 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 892399 = 1338599) B1338599
theorem B630875 : Blo 417772 630875 := bstep (se 1 (by rfl) ⟨473156, by rfl⟩ : syracuseStep 630875 = 946313) B946313
theorem B631019 : Blo 417772 631019 := bstep (se 1 (by rfl) ⟨473264, by rfl⟩ : syracuseStep 631019 = 946529) B946529
theorem B6070747 : Blo 417772 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B631271 : Blo 417772 631271 := bstep (se 1 (by rfl) ⟨473453, by rfl⟩ : syracuseStep 631271 = 946907) B946907
theorem B532975 : Blo 417772 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B1450487 : Blo 417772 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B631721 : Blo 417772 631721 := bstep (se 2 (by rfl) ⟨236895, by rfl⟩ : syracuseStep 631721 = 473791) B473791
theorem B632105 : Blo 417772 632105 := bstep (se 2 (by rfl) ⟨237039, by rfl⟩ : syracuseStep 632105 = 474079) B474079
theorem B1058255 : Blo 417772 1058255 := bstep (se 1 (by rfl) ⟨793691, by rfl⟩ : syracuseStep 1058255 = 1587383) B1587383
theorem B632411 : Blo 417772 632411 := bstep (se 1 (by rfl) ⟨474308, by rfl⟩ : syracuseStep 632411 = 948617) B948617
theorem B632489 : Blo 417772 632489 := bstep (se 2 (by rfl) ⟨237183, by rfl⟩ : syracuseStep 632489 = 474367) B474367
theorem B1419065 : Blo 417772 1419065 := bstep (se 2 (by rfl) ⟨532149, by rfl⟩ : syracuseStep 1419065 = 1064299) B1064299
theorem B1058791 : Blo 417772 1058791 := bstep (se 1 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 1058791 = 1588187) B1588187
theorem B7186481 : Blo 417772 7186481 := bstep (se 2 (by rfl) ⟨2694930, by rfl⟩ : syracuseStep 7186481 = 5389861) B5389861
theorem B1420955 : Blo 417772 1420955 := bstep (se 1 (by rfl) ⟨1065716, by rfl⟩ : syracuseStep 1420955 = 2131433) B2131433
theorem B597733037 : Blo 417772 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B2011243 : Blo 417772 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B471343 : Blo 417772 471343 := bstep (se 1 (by rfl) ⟨353507, by rfl⟩ : syracuseStep 471343 = 707015) B707015
theorem B1421981 : Blo 417772 1421981 := bstep (se 3 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 1421981 = 533243) B533243
theorem B3191561 : Blo 417772 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B1422089 : Blo 417772 1422089 := bstep (se 2 (by rfl) ⟨533283, by rfl⟩ : syracuseStep 1422089 = 1066567) B1066567
theorem B10303199 : Blo 417772 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B1194011 : Blo 417772 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B506107 : Blo 417772 506107 := bstep (se 1 (by rfl) ⟨379580, by rfl⟩ : syracuseStep 506107 = 759161) B759161
theorem B1587671 : Blo 417772 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B2046791 : Blo 417772 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B1064249 : Blo 417772 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B1064735 : Blo 417772 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B5193559 : Blo 417772 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B1195879 : Blo 417772 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B6144457 : Blo 417772 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B705449 : Blo 417772 705449 := bstep (se 2 (by rfl) ⟨264543, by rfl⟩ : syracuseStep 705449 = 529087) B529087
theorem B59229791 : Blo 417772 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B3393359 : Blo 417772 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B4541123 : Blo 417772 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B61524683 : Blo 417772 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B1362943 : Blo 417772 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B58019105 : Blo 417772 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B6147863 : Blo 417772 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B1200071 : Blo 417772 1200071 := bstep (se 1 (by rfl) ⟨900053, by rfl⟩ : syracuseStep 1200071 = 1800107) B1800107
theorem B708871 : Blo 417772 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B3559751 : Blo 417772 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B1790369 : Blo 417772 1790369 := bstep (se 2 (by rfl) ⟨671388, by rfl⟩ : syracuseStep 1790369 = 1342777) B1342777
theorem B2545607 : Blo 417772 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B2120093 : Blo 417772 2120093 := bstep (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) B795035
theorem B940769 : Blo 417772 940769 := bstep (se 2 (by rfl) ⟨352788, by rfl⟩ : syracuseStep 940769 = 705577) B705577
theorem B941291 : Blo 417772 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B6282521 : Blo 417772 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B941993 : Blo 417772 941993 := bstep (se 2 (by rfl) ⟨353247, by rfl⟩ : syracuseStep 941993 = 706495) B706495
theorem B1597421 : Blo 417772 1597421 := bstep (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) B599033
theorem B1073279 : Blo 417772 1073279 := bstep (se 1 (by rfl) ⟨804959, by rfl⟩ : syracuseStep 1073279 = 1609919) B1609919
theorem B2875769 : Blo 417772 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B46588409 : Blo 417772 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B2023967 : Blo 417772 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B1532495 : Blo 417772 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B1598089 : Blo 417772 1598089 := bstep (se 2 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 1598089 = 1198567) B1198567
theorem B910561 : Blo 417772 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B943721 : Blo 417772 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B419931 : Blo 417772 419931 := bstep (se 1 (by rfl) ⟨314948, by rfl⟩ : syracuseStep 419931 = 629897) B629897
theorem B419943 : Blo 417772 419943 := bstep (se 1 (by rfl) ⟨314957, by rfl⟩ : syracuseStep 419943 = 629915) B629915
theorem B419967 : Blo 417772 419967 := bstep (se 1 (by rfl) ⟨314975, by rfl⟩ : syracuseStep 419967 = 629951) B629951
theorem B420095 : Blo 417772 420095 := bstep (se 1 (by rfl) ⟨315071, by rfl⟩ : syracuseStep 420095 = 630143) B630143
theorem B2550203 : Blo 417772 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B944783 : Blo 417772 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B420511 : Blo 417772 420511 := bstep (se 1 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 420511 = 630767) B630767
theorem B420671 : Blo 417772 420671 := bstep (se 1 (by rfl) ⟨315503, by rfl⟩ : syracuseStep 420671 = 631007) B631007
theorem B6777695 : Blo 417772 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B420967 : Blo 417772 420967 := bstep (se 1 (by rfl) ⟨315725, by rfl⟩ : syracuseStep 420967 = 631451) B631451
theorem B7203977 : Blo 417772 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B1273097 : Blo 417772 1273097 := bstep (se 2 (by rfl) ⟨477411, by rfl⟩ : syracuseStep 1273097 = 954823) B954823
theorem B946655 : Blo 417772 946655 := bstep (se 1 (by rfl) ⟨709991, by rfl⟩ : syracuseStep 946655 = 1419983) B1419983
theorem B948635 : Blo 417772 948635 := bstep (se 1 (by rfl) ⟨711476, by rfl⟩ : syracuseStep 948635 = 1422953) B1422953
theorem B5372639 : Blo 417772 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B2259839 : Blo 417772 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B3013807 : Blo 417772 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B39353971 : Blo 417772 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B332103401 : Blo 417772 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B2687039 : Blo 417772 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B8192609 : Blo 417772 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B8094329 : Blo 417772 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B2130785 : Blo 417772 2130785 := bstep (se 2 (by rfl) ⟨799044, by rfl⟩ : syracuseStep 2130785 = 1598089) B1598089
theorem B39486527 : Blo 417772 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B2262239 : Blo 417772 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1214081 : Blo 417772 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B3410255 : Blo 417772 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B4098575 : Blo 417772 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B1411721 : Blo 417772 1411721 := bstep (se 2 (by rfl) ⟨529395, by rfl⟩ : syracuseStep 1411721 = 1058791) B1058791
theorem B16321475 : Blo 417772 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B1510739 : Blo 417772 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B1413395 : Blo 417772 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B2560415 : Blo 417772 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B627179 : Blo 417772 627179 := bstep (se 1 (by rfl) ⟨470384, by rfl⟩ : syracuseStep 627179 = 940769) B940769
theorem B725615 : Blo 417772 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B627527 : Blo 417772 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B627995 : Blo 417772 627995 := bstep (se 1 (by rfl) ⟨470996, by rfl⟩ : syracuseStep 627995 = 941993) B941993
theorem B1349311 : Blo 417772 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B1021663 : Blo 417772 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B628457 : Blo 417772 628457 := bstep (se 2 (by rfl) ⟨235671, by rfl⟩ : syracuseStep 628457 = 471343) B471343
theorem B629147 : Blo 417772 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B4790987 : Blo 417772 4790987 := bstep (se 1 (by rfl) ⟨3593240, by rfl⟩ : syracuseStep 4790987 = 7186481) B7186481
theorem B629855 : Blo 417772 629855 := bstep (se 1 (by rfl) ⟨472391, by rfl⟩ : syracuseStep 629855 = 944783) B944783
theorem B631103 : Blo 417772 631103 := bstep (se 1 (by rfl) ⟨473327, by rfl⟩ : syracuseStep 631103 = 946655) B946655
theorem B5383097 : Blo 417772 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B1057769 : Blo 417772 1057769 := bstep (se 2 (by rfl) ⟨396663, by rfl⟩ : syracuseStep 1057769 = 793327) B793327
theorem B1057961 : Blo 417772 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B796007 : Blo 417772 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B632423 : Blo 417772 632423 := bstep (se 1 (by rfl) ⟨474317, by rfl⟩ : syracuseStep 632423 = 948635) B948635
theorem B1058447 : Blo 417772 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B3581759 : Blo 417772 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B1189865 : Blo 417772 1189865 := bstep (se 2 (by rfl) ⟨446199, by rfl⟩ : syracuseStep 1189865 = 892399) B892399
theorem B52471961 : Blo 417772 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B6924745 : Blo 417772 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B2009819 : Blo 417772 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B470299 : Blo 417772 470299 := bstep (se 1 (by rfl) ⟨352724, by rfl⟩ : syracuseStep 470299 = 705449) B705449
theorem B896363 : Blo 417772 896363 := bstep (se 1 (by rfl) ⟨672272, by rfl⟩ : syracuseStep 896363 = 1344545) B1344545
theorem B2699237 : Blo 417772 2699237 := bstep (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) B506107
theorem B38679403 : Blo 417772 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B800047 : Blo 417772 800047 := bstep (se 1 (by rfl) ⟨600035, by rfl⟩ : syracuseStep 800047 = 1200071) B1200071
theorem B2373167 : Blo 417772 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B1193579 : Blo 417772 1193579 := bstep (se 1 (by rfl) ⟨895184, by rfl⟩ : syracuseStep 1193579 = 1790369) B1790369
theorem B13613255 : Blo 417772 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1587869 : Blo 417772 1587869 := bstep (se 3 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 1587869 = 595451) B595451
theorem B1817257 : Blo 417772 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B1064947 : Blo 417772 1064947 := bstep (se 1 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 1064947 = 1597421) B1597421
theorem B1917179 : Blo 417772 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B966991 : Blo 417772 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B3195449 : Blo 417772 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B705503 : Blo 417772 705503 := bstep (se 1 (by rfl) ⟨529127, by rfl⟩ : syracuseStep 705503 = 1058255) B1058255
theorem B12109661 : Blo 417772 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B4802651 : Blo 417772 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B6868799 : Blo 417772 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B4018409 : Blo 417772 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B1364527 : Blo 417772 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B709499 : Blo 417772 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B1594505 : Blo 417772 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B221402267 : Blo 417772 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B709823 : Blo 417772 709823 := bstep (se 1 (by rfl) ⟨532367, by rfl⟩ : syracuseStep 709823 = 1064735) B1064735
theorem B710633 : Blo 417772 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B7691111 : Blo 417772 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B1006601 : Blo 417772 1006601 := bstep (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) B754951
theorem B941111 : Blo 417772 941111 := bstep (se 1 (by rfl) ⟨705833, by rfl⟩ : syracuseStep 941111 = 1411667) B1411667
theorem B41016455 : Blo 417772 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B1596935 : Blo 417772 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B941903 : Blo 417772 941903 := bstep (se 1 (by rfl) ⟨706427, by rfl⟩ : syracuseStep 941903 = 1412855) B1412855
theorem B2121551 : Blo 417772 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B417951 : Blo 417772 417951 := bstep (se 1 (by rfl) ⟨313463, by rfl⟩ : syracuseStep 417951 = 626927) B626927
theorem B942407 : Blo 417772 942407 := bstep (se 1 (by rfl) ⟨706805, by rfl⟩ : syracuseStep 942407 = 1413611) B1413611
theorem B418207 : Blo 417772 418207 := bstep (se 1 (by rfl) ⟨313655, by rfl⟩ : syracuseStep 418207 = 627311) B627311
theorem B2122199 : Blo 417772 2122199 := bstep (se 1 (by rfl) ⟨1591649, by rfl⟩ : syracuseStep 2122199 = 3183299) B3183299
theorem B418543 : Blo 417772 418543 := bstep (se 1 (by rfl) ⟨313907, by rfl⟩ : syracuseStep 418543 = 627815) B627815
theorem B418559 : Blo 417772 418559 := bstep (se 1 (by rfl) ⟨313919, by rfl⟩ : syracuseStep 418559 = 627839) B627839
theorem B942875 : Blo 417772 942875 := bstep (se 1 (by rfl) ⟨707156, by rfl⟩ : syracuseStep 942875 = 1414313) B1414313
theorem B943055 : Blo 417772 943055 := bstep (se 1 (by rfl) ⟨707291, by rfl⟩ : syracuseStep 943055 = 1414583) B1414583
theorem B2122847 : Blo 417772 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B418975 : Blo 417772 418975 := bstep (se 1 (by rfl) ⟨314231, by rfl⟩ : syracuseStep 418975 = 628463) B628463
theorem B419099 : Blo 417772 419099 := bstep (se 1 (by rfl) ⟨314324, by rfl⟩ : syracuseStep 419099 = 628649) B628649
theorem B1697071 : Blo 417772 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B1009255 : Blo 417772 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B2123495 : Blo 417772 2123495 := bstep (se 1 (by rfl) ⟨1592621, by rfl⟩ : syracuseStep 2123495 = 3185243) B3185243
theorem B419611 : Blo 417772 419611 := bstep (se 1 (by rfl) ⟨314708, by rfl⟩ : syracuseStep 419611 = 629417) B629417
theorem B419911 : Blo 417772 419911 := bstep (se 1 (by rfl) ⟨314933, by rfl⟩ : syracuseStep 419911 = 629867) B629867
theorem B4188347 : Blo 417772 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B3172607 : Blo 417772 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B420159 : Blo 417772 420159 := bstep (se 1 (by rfl) ⟨315119, by rfl⟩ : syracuseStep 420159 = 630239) B630239
theorem B420167 : Blo 417772 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420583 : Blo 417772 420583 := bstep (se 1 (by rfl) ⟨315437, by rfl⟩ : syracuseStep 420583 = 630875) B630875
theorem B715519 : Blo 417772 715519 := bstep (se 1 (by rfl) ⟨536639, by rfl⟩ : syracuseStep 715519 = 1073279) B1073279
theorem B2681657 : Blo 417772 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B420679 : Blo 417772 420679 := bstep (se 1 (by rfl) ⟨315509, by rfl⟩ : syracuseStep 420679 = 631019) B631019
theorem B420847 : Blo 417772 420847 := bstep (se 1 (by rfl) ⟨315635, by rfl⟩ : syracuseStep 420847 = 631271) B631271
theorem B31058939 : Blo 417772 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B945161 : Blo 417772 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B421147 : Blo 417772 421147 := bstep (se 1 (by rfl) ⟨315860, by rfl⟩ : syracuseStep 421147 = 631721) B631721
theorem B421403 : Blo 417772 421403 := bstep (se 1 (by rfl) ⟨316052, by rfl⟩ : syracuseStep 421403 = 632105) B632105
theorem B421607 : Blo 417772 421607 := bstep (se 1 (by rfl) ⟨316205, by rfl⟩ : syracuseStep 421607 = 632411) B632411
theorem B421659 : Blo 417772 421659 := bstep (se 1 (by rfl) ⟨316244, by rfl⟩ : syracuseStep 421659 = 632489) B632489
theorem B946043 : Blo 417772 946043 := bstep (se 1 (by rfl) ⟨709532, by rfl⟩ : syracuseStep 946043 = 1419065) B1419065
theorem B1700135 : Blo 417772 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B4518463 : Blo 417772 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B848731 : Blo 417772 848731 := bstep (se 1 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 848731 = 1273097) B1273097
theorem B947303 : Blo 417772 947303 := bstep (se 1 (by rfl) ⟨710477, by rfl⟩ : syracuseStep 947303 = 1420955) B1420955
theorem B398488691 : Blo 417772 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B947987 : Blo 417772 947987 := bstep (se 1 (by rfl) ⟨710990, by rfl⟩ : syracuseStep 947987 = 1421981) B1421981
theorem B2127707 : Blo 417772 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B948059 : Blo 417772 948059 := bstep (se 1 (by rfl) ⟨711044, by rfl⟩ : syracuseStep 948059 = 1422089) B1422089
theorem B1506559 : Blo 417772 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B1278119 : Blo 417772 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B2130299 : Blo 417772 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B1508159 : Blo 417772 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B2262761 : Blo 417772 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B10880983 : Blo 417772 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B1345673 : Blo 417772 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B1062636509 : Blo 417772 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B954025 : Blo 417772 954025 := bstep (se 2 (by rfl) ⟨357759, by rfl⟩ : syracuseStep 954025 = 715519) B715519
theorem B627065 : Blo 417772 627065 := bstep (se 2 (by rfl) ⟨235149, by rfl⟩ : syracuseStep 627065 = 470299) B470299
theorem B627407 : Blo 417772 627407 := bstep (se 1 (by rfl) ⟨470555, by rfl⟩ : syracuseStep 627407 = 941111) B941111
theorem B627935 : Blo 417772 627935 := bstep (se 1 (by rfl) ⟨470951, by rfl⟩ : syracuseStep 627935 = 941903) B941903
theorem B1414367 : Blo 417772 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B628271 : Blo 417772 628271 := bstep (se 1 (by rfl) ⟨471203, by rfl⟩ : syracuseStep 628271 = 942407) B942407
theorem B1414799 : Blo 417772 1414799 := bstep (se 1 (by rfl) ⟨1061099, by rfl⟩ : syracuseStep 1414799 = 2122199) B2122199
theorem B628583 : Blo 417772 628583 := bstep (se 1 (by rfl) ⟨471437, by rfl⟩ : syracuseStep 628583 = 942875) B942875
theorem B628703 : Blo 417772 628703 := bstep (se 1 (by rfl) ⟨471527, by rfl⟩ : syracuseStep 628703 = 943055) B943055
theorem B1415231 : Blo 417772 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B1415663 : Blo 417772 1415663 := bstep (se 1 (by rfl) ⟨1061747, by rfl⟩ : syracuseStep 1415663 = 2123495) B2123495
theorem B793243 : Blo 417772 793243 := bstep (se 1 (by rfl) ⟨594932, by rfl⟩ : syracuseStep 793243 = 1189865) B1189865
theorem B2792231 : Blo 417772 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B630107 : Blo 417772 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B597575 : Blo 417772 597575 := bstep (se 1 (by rfl) ⟨448181, by rfl⟩ : syracuseStep 597575 = 896363) B896363
theorem B630695 : Blo 417772 630695 := bstep (se 1 (by rfl) ⟨473021, by rfl⟩ : syracuseStep 630695 = 946043) B946043
theorem B631535 : Blo 417772 631535 := bstep (se 1 (by rfl) ⟨473651, by rfl⟩ : syracuseStep 631535 = 947303) B947303
theorem B1582111 : Blo 417772 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B795719 : Blo 417772 795719 := bstep (se 1 (by rfl) ⟨596789, by rfl⟩ : syracuseStep 795719 = 1193579) B1193579
theorem B631991 : Blo 417772 631991 := bstep (se 1 (by rfl) ⟨473993, by rfl⟩ : syracuseStep 631991 = 947987) B947987
theorem B1418471 : Blo 417772 1418471 := bstep (se 1 (by rfl) ⟨1063853, by rfl⟩ : syracuseStep 1418471 = 2127707) B2127707
theorem B632039 : Blo 417772 632039 := bstep (se 1 (by rfl) ⟨474029, by rfl⟩ : syracuseStep 632039 = 948059) B948059
theorem B2008745 : Blo 417772 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B1058579 : Blo 417772 1058579 := bstep (se 1 (by rfl) ⟨793934, by rfl⟩ : syracuseStep 1058579 = 1587869) B1587869
theorem B1419929 : Blo 417772 1419929 := bstep (se 2 (by rfl) ⟨532473, by rfl⟩ : syracuseStep 1419929 = 1064947) B1064947
theorem B1289321 : Blo 417772 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B1420523 : Blo 417772 1420523 := bstep (se 1 (by rfl) ⟨1065392, by rfl⟩ : syracuseStep 1420523 = 2130785) B2130785
theorem B470335 : Blo 417772 470335 := bstep (se 1 (by rfl) ⟨352751, by rfl⟩ : syracuseStep 470335 = 705503) B705503
theorem B26324351 : Blo 417772 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B6827773 : Blo 417772 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B8073107 : Blo 417772 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B2273503 : Blo 417772 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B2732383 : Blo 417772 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B472999 : Blo 417772 472999 := bstep (se 1 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 472999 = 709499) B709499
theorem B1063003 : Blo 417772 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B147601511 : Blo 417772 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B473215 : Blo 417772 473215 := bstep (se 1 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 473215 = 709823) B709823
theorem B473755 : Blo 417772 473755 := bstep (se 1 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 473755 = 710633) B710633
theorem B3193991 : Blo 417772 3193991 := bstep (se 1 (by rfl) ⟨2395493, by rfl⟩ : syracuseStep 3193991 = 4790987) B4790987
theorem B5127407 : Blo 417772 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B27344303 : Blo 417772 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B1064623 : Blo 417772 1064623 := bstep (se 1 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 1064623 = 1596935) B1596935
theorem B3588731 : Blo 417772 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B705179 : Blo 417772 705179 := bstep (se 1 (by rfl) ⟨528884, by rfl⟩ : syracuseStep 705179 = 1057769) B1057769
theorem B1819369 : Blo 417772 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B705307 : Blo 417772 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B705631 : Blo 417772 705631 := bstep (se 1 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 705631 = 1058447) B1058447
theorem B1131641 : Blo 417772 1131641 := bstep (se 2 (by rfl) ⟨424365, by rfl⟩ : syracuseStep 1131641 = 848731) B848731
theorem B34981307 : Blo 417772 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B2115071 : Blo 417772 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B1066729 : Blo 417772 1066729 := bstep (se 2 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 1066729 = 800047) B800047
theorem B1787771 : Blo 417772 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B5359517 : Blo 417772 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B1362217 : Blo 417772 1362217 := bstep (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) B1021663
theorem B1133423 : Blo 417772 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B1791359 : Blo 417772 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B5461739 : Blo 417772 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B5396219 : Blo 417772 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B809387 : Blo 417772 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B3201767 : Blo 417772 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B941147 : Blo 417772 941147 := bstep (se 1 (by rfl) ⟨705860, by rfl⟩ : syracuseStep 941147 = 1411721) B1411721
theorem B1007159 : Blo 417772 1007159 := bstep (se 1 (by rfl) ⟨755369, by rfl⟩ : syracuseStep 1007159 = 1510739) B1510739
theorem B4579199 : Blo 417772 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2678939 : Blo 417772 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B942263 : Blo 417772 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B418119 : Blo 417772 418119 := bstep (se 1 (by rfl) ⟨313589, by rfl⟩ : syracuseStep 418119 = 627179) B627179
theorem B483743 : Blo 417772 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B418351 : Blo 417772 418351 := bstep (se 1 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 418351 = 627527) B627527
theorem B9232993 : Blo 417772 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B418663 : Blo 417772 418663 := bstep (se 1 (by rfl) ⟨313997, by rfl⟩ : syracuseStep 418663 = 627995) B627995
theorem B2122685 : Blo 417772 2122685 := bstep (se 3 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 2122685 = 796007) B796007
theorem B418971 : Blo 417772 418971 := bstep (se 1 (by rfl) ⟨314228, by rfl⟩ : syracuseStep 418971 = 628457) B628457
theorem B419431 : Blo 417772 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B419903 : Blo 417772 419903 := bstep (se 1 (by rfl) ⟨314927, by rfl⟩ : syracuseStep 419903 = 629855) B629855
theorem B420735 : Blo 417772 420735 := bstep (se 1 (by rfl) ⟨315551, by rfl⟩ : syracuseStep 420735 = 631103) B631103
theorem B6024617 : Blo 417772 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B421615 : Blo 417772 421615 := bstep (se 1 (by rfl) ⟨316211, by rfl⟩ : syracuseStep 421615 = 632423) B632423
theorem B51572537 : Blo 417772 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B2387839 : Blo 417772 2387839 := bstep (se 1 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 2387839 = 3581759) B3581759
theorem B20705959 : Blo 417772 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B1799081 : Blo 417772 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B1799491 : Blo 417772 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B2684269 : Blo 417772 2684269 := bstep (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) B1006601
theorem B2423009 : Blo 417772 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B9075503 : Blo 417772 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B2392487 : Blo 417772 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B3408317 : Blo 417772 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B754427 : Blo 417772 754427 := bstep (se 1 (by rfl) ⟨565820, by rfl⟩ : syracuseStep 754427 = 1131641) B1131641
theorem B2425825 : Blo 417772 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B1410047 : Blo 417772 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B1508507 : Blo 417772 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B3573011 : Blo 417772 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B755615 : Blo 417772 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B3641159 : Blo 417772 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B627113 : Blo 417772 627113 := bstep (se 2 (by rfl) ⟨235167, by rfl⟩ : syracuseStep 627113 = 470335) B470335
theorem B2134511 : Blo 417772 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B627431 : Blo 417772 627431 := bstep (se 1 (by rfl) ⟨470573, by rfl⟩ : syracuseStep 627431 = 941147) B941147
theorem B3183785 : Blo 417772 3183785 := bstep (se 2 (by rfl) ⟨1193919, by rfl⟩ : syracuseStep 3183785 = 2387839) B2387839
theorem B3052799 : Blo 417772 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B628175 : Blo 417772 628175 := bstep (se 1 (by rfl) ⟨471131, by rfl⟩ : syracuseStep 628175 = 942263) B942263
theorem B3643177 : Blo 417772 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B1415123 : Blo 417772 1415123 := bstep (se 1 (by rfl) ⟨1061342, by rfl⟩ : syracuseStep 1415123 = 2122685) B2122685
theorem B530479 : Blo 417772 530479 := bstep (se 1 (by rfl) ⟨397859, by rfl⟩ : syracuseStep 530479 = 795719) B795719
theorem B2399321 : Blo 417772 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B3579025 : Blo 417772 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B859547 : Blo 417772 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B34381691 : Blo 417772 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B630665 : Blo 417772 630665 := bstep (se 2 (by rfl) ⟨236499, by rfl⟩ : syracuseStep 630665 = 472999) B472999
theorem B5382071 : Blo 417772 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1417337 : Blo 417772 1417337 := bstep (se 2 (by rfl) ⟨531501, by rfl⟩ : syracuseStep 1417337 = 1063003) B1063003
theorem B630953 : Blo 417772 630953 := bstep (se 2 (by rfl) ⟨236607, by rfl⟩ : syracuseStep 630953 = 473215) B473215
theorem B1057657 : Blo 417772 1057657 := bstep (se 2 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 1057657 = 793243) B793243
theorem B631673 : Blo 417772 631673 := bstep (se 2 (by rfl) ⟨236877, by rfl⟩ : syracuseStep 631673 = 473755) B473755
theorem B5088133 : Blo 417772 5088133 := bstep (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) B954025
theorem B1615339 : Blo 417772 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B3418271 : Blo 417772 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B1419497 : Blo 417772 1419497 := bstep (se 2 (by rfl) ⟨532311, by rfl⟩ : syracuseStep 1419497 = 1064623) B1064623
theorem B18229535 : Blo 417772 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1420199 : Blo 417772 1420199 := bstep (se 1 (by rfl) ⟨1065149, by rfl⟩ : syracuseStep 1420199 = 2130299) B2130299
theorem B470119 : Blo 417772 470119 := bstep (se 1 (by rfl) ⟨352589, by rfl⟩ : syracuseStep 470119 = 705179) B705179
theorem B1289981 : Blo 417772 1289981 := bstep (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) B483743
theorem B1191847 : Blo 417772 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B897115 : Blo 417772 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B1422305 : Blo 417772 1422305 := bstep (se 2 (by rfl) ⟨533364, by rfl⟩ : syracuseStep 1422305 = 1066729) B1066729
theorem B1816289 : Blo 417772 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B1194239 : Blo 417772 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B539591 : Blo 417772 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B1785959 : Blo 417772 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B8437925 : Blo 417772 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B3031337 : Blo 417772 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B27607945 : Blo 417772 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B705719 : Blo 417772 705719 := bstep (se 1 (by rfl) ⟨529289, by rfl⟩ : syracuseStep 705719 = 1058579) B1058579
theorem B17549567 : Blo 417772 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B4016411 : Blo 417772 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B2833697357 : Blo 417772 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B1199387 : Blo 417772 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B1593533 : Blo 417772 1593533 := bstep (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) B597575
theorem B6050335 : Blo 417772 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B23320871 : Blo 417772 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B940409 : Blo 417772 940409 := bstep (se 2 (by rfl) ⟨352653, by rfl⟩ : syracuseStep 940409 = 705307) B705307
theorem B940841 : Blo 417772 940841 := bstep (se 2 (by rfl) ⟨352815, by rfl⟩ : syracuseStep 940841 = 705631) B705631
theorem B4021757 : Blo 417772 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B418043 : Blo 417772 418043 := bstep (se 1 (by rfl) ⟨313532, by rfl⟩ : syracuseStep 418043 = 627065) B627065
theorem B418271 : Blo 417772 418271 := bstep (se 1 (by rfl) ⟨313703, by rfl⟩ : syracuseStep 418271 = 627407) B627407
theorem B49242629 : Blo 417772 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B418623 : Blo 417772 418623 := bstep (se 1 (by rfl) ⟨313967, by rfl⟩ : syracuseStep 418623 = 627935) B627935
theorem B942911 : Blo 417772 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B418847 : Blo 417772 418847 := bstep (se 1 (by rfl) ⟨314135, by rfl⟩ : syracuseStep 418847 = 628271) B628271
theorem B943199 : Blo 417772 943199 := bstep (se 1 (by rfl) ⟨707399, by rfl⟩ : syracuseStep 943199 = 1414799) B1414799
theorem B3597479 : Blo 417772 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B419055 : Blo 417772 419055 := bstep (se 1 (by rfl) ⟨314291, by rfl⟩ : syracuseStep 419055 = 628583) B628583
theorem B419135 : Blo 417772 419135 := bstep (se 1 (by rfl) ⟨314351, by rfl⟩ : syracuseStep 419135 = 628703) B628703
theorem B943487 : Blo 417772 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B943775 : Blo 417772 943775 := bstep (se 1 (by rfl) ⟨707831, by rfl⟩ : syracuseStep 943775 = 1415663) B1415663
theorem B1861487 : Blo 417772 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B420071 : Blo 417772 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B9103697 : Blo 417772 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B420463 : Blo 417772 420463 := bstep (se 1 (by rfl) ⟨315347, by rfl⟩ : syracuseStep 420463 = 630695) B630695
theorem B421023 : Blo 417772 421023 := bstep (se 1 (by rfl) ⟨315767, by rfl⟩ : syracuseStep 421023 = 631535) B631535
theorem B421327 : Blo 417772 421327 := bstep (se 1 (by rfl) ⟨315995, by rfl⟩ : syracuseStep 421327 = 631991) B631991
theorem B945647 : Blo 417772 945647 := bstep (se 1 (by rfl) ⟨709235, by rfl⟩ : syracuseStep 945647 = 1418471) B1418471
theorem B421359 : Blo 417772 421359 := bstep (se 1 (by rfl) ⟨316019, by rfl⟩ : syracuseStep 421359 = 632039) B632039
theorem B1339163 : Blo 417772 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B946619 : Blo 417772 946619 := bstep (se 1 (by rfl) ⟨709964, by rfl⟩ : syracuseStep 946619 = 1419929) B1419929
theorem B947015 : Blo 417772 947015 := bstep (se 1 (by rfl) ⟨710261, by rfl⟩ : syracuseStep 947015 = 1420523) B1420523
theorem B98401007 : Blo 417772 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B2685757 : Blo 417772 2685757 := bstep (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) B1007159
theorem B2129327 : Blo 417772 2129327 := bstep (se 1 (by rfl) ⟨1596995, by rfl⟩ : syracuseStep 2129327 = 3193991) B3193991
theorem B58031909 : Blo 417772 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B1410209 : Blo 417772 1410209 := bstep (se 2 (by rfl) ⟨528828, by rfl⟩ : syracuseStep 1410209 = 1057657) B1057657
theorem B6784177 : Blo 417772 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B11699711 : Blo 417772 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B2035199 : Blo 417772 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B626825 : Blo 417772 626825 := bstep (se 2 (by rfl) ⟨235059, by rfl⟩ : syracuseStep 626825 = 470119) B470119
theorem B626939 : Blo 417772 626939 := bstep (se 1 (by rfl) ⟨470204, by rfl⟩ : syracuseStep 626939 = 940409) B940409
theorem B627227 : Blo 417772 627227 := bstep (se 1 (by rfl) ⟨470420, by rfl⟩ : syracuseStep 627227 = 940841) B940841
theorem B628607 : Blo 417772 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B8067113 : Blo 417772 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B628799 : Blo 417772 628799 := bstep (se 1 (by rfl) ⟨471599, by rfl⟩ : syracuseStep 628799 = 943199) B943199
theorem B2398319 : Blo 417772 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B628991 : Blo 417772 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B629183 : Blo 417772 629183 := bstep (se 1 (by rfl) ⟨471887, by rfl⟩ : syracuseStep 629183 = 943775) B943775
theorem B6069131 : Blo 417772 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B630431 : Blo 417772 630431 := bstep (se 1 (by rfl) ⟨472823, by rfl⟩ : syracuseStep 630431 = 945647) B945647
theorem B4857569 : Blo 417772 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B892775 : Blo 417772 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B631079 : Blo 417772 631079 := bstep (se 1 (by rfl) ⟨473309, by rfl⟩ : syracuseStep 631079 = 946619) B946619
theorem B631343 : Blo 417772 631343 := bstep (se 1 (by rfl) ⟨473507, by rfl⟩ : syracuseStep 631343 = 947015) B947015
theorem B3581009 : Blo 417772 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B796159 : Blo 417772 796159 := bstep (se 1 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 796159 = 1194239) B1194239
theorem B9709757 : Blo 417772 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B1419551 : Blo 417772 1419551 := bstep (se 1 (by rfl) ⟨1064663, by rfl⟩ : syracuseStep 1419551 = 2129327) B2129327
theorem B1190639 : Blo 417772 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B2272211 : Blo 417772 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B502951 : Blo 417772 502951 := bstep (se 1 (by rfl) ⟨377213, by rfl⟩ : syracuseStep 502951 = 754427) B754427
theorem B470479 : Blo 417772 470479 := bstep (se 1 (by rfl) ⟨352859, by rfl⟩ : syracuseStep 470479 = 705719) B705719
theorem B36810593 : Blo 417772 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B503743 : Blo 417772 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B1062355 : Blo 417772 1062355 := bstep (se 1 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 1062355 = 1593533) B1593533
theorem B1423007 : Blo 417772 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B15547247 : Blo 417772 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B573031 : Blo 417772 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B1589129 : Blo 417772 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B22921127 : Blo 417772 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B3588047 : Blo 417772 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B1196153 : Blo 417772 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B2278847 : Blo 417772 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B707305 : Blo 417772 707305 := bstep (se 2 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 707305 = 530479) B530479
theorem B3198365 : Blo 417772 3198365 := bstep (se 3 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 3198365 = 1199387) B1199387
theorem B4772033 : Blo 417772 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B5755637 : Blo 417772 5755637 := bstep (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) B539591
theorem B38687939 : Blo 417772 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B5625283 : Blo 417772 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B2020891 : Blo 417772 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B1594991 : Blo 417772 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B940031 : Blo 417772 940031 := bstep (se 1 (by rfl) ⟨705023, by rfl⟩ : syracuseStep 940031 = 1410047) B1410047
theorem B1005671 : Blo 417772 1005671 := bstep (se 1 (by rfl) ⟨754253, by rfl⟩ : syracuseStep 1005671 = 1508507) B1508507
theorem B2382007 : Blo 417772 2382007 := bstep (se 1 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 2382007 = 3573011) B3573011
theorem B3234433 : Blo 417772 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B2677607 : Blo 417772 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B1889131571 : Blo 417772 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B2153785 : Blo 417772 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B418075 : Blo 417772 418075 := bstep (se 1 (by rfl) ⟨313556, by rfl⟩ : syracuseStep 418075 = 627113) B627113
theorem B418287 : Blo 417772 418287 := bstep (se 1 (by rfl) ⟨313715, by rfl⟩ : syracuseStep 418287 = 627431) B627431
theorem B2122523 : Blo 417772 2122523 := bstep (se 1 (by rfl) ⟨1591892, by rfl⟩ : syracuseStep 2122523 = 3183785) B3183785
theorem B418783 : Blo 417772 418783 := bstep (se 1 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 418783 = 628175) B628175
theorem B943415 : Blo 417772 943415 := bstep (se 1 (by rfl) ⟨707561, by rfl⟩ : syracuseStep 943415 = 1415123) B1415123
theorem B1599547 : Blo 417772 1599547 := bstep (se 1 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 1599547 = 2399321) B2399321
theorem B2681171 : Blo 417772 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B420443 : Blo 417772 420443 := bstep (se 1 (by rfl) ⟨315332, by rfl⟩ : syracuseStep 420443 = 630665) B630665
theorem B944891 : Blo 417772 944891 := bstep (se 1 (by rfl) ⟨708668, by rfl⟩ : syracuseStep 944891 = 1417337) B1417337
theorem B420635 : Blo 417772 420635 := bstep (se 1 (by rfl) ⟨315476, by rfl⟩ : syracuseStep 420635 = 630953) B630953
theorem B32828419 : Blo 417772 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B421115 : Blo 417772 421115 := bstep (se 1 (by rfl) ⟨315836, by rfl⟩ : syracuseStep 421115 = 631673) B631673
theorem B1240991 : Blo 417772 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B946331 : Blo 417772 946331 := bstep (se 1 (by rfl) ⟨709748, by rfl⟩ : syracuseStep 946331 = 1419497) B1419497
theorem B12153023 : Blo 417772 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B946799 : Blo 417772 946799 := bstep (se 1 (by rfl) ⟨710099, by rfl⟩ : syracuseStep 946799 = 1420199) B1420199
theorem B262402685 : Blo 417772 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B948203 : Blo 417772 948203 := bstep (se 1 (by rfl) ⟨711152, by rfl⟩ : syracuseStep 948203 = 1422305) B1422305
theorem B1210859 : Blo 417772 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B3439949 : Blo 417772 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B7799807 : Blo 417772 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B9045569 : Blo 417772 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B2132243 : Blo 417772 2132243 := bstep (se 1 (by rfl) ⟨1599182, by rfl⟩ : syracuseStep 2132243 = 3198365) B3198365
theorem B2132729 : Blo 417772 2132729 := bstep (se 2 (by rfl) ⟨799773, by rfl⟩ : syracuseStep 2132729 = 1599547) B1599547
theorem B3181355 : Blo 417772 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B25791959 : Blo 417772 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B626687 : Blo 417772 626687 := bstep (se 1 (by rfl) ⟨470015, by rfl⟩ : syracuseStep 626687 = 940031) B940031
theorem B5378075 : Blo 417772 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B627305 : Blo 417772 627305 := bstep (se 2 (by rfl) ⟨235239, by rfl⟩ : syracuseStep 627305 = 470479) B470479
theorem B595183 : Blo 417772 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B175084901 : Blo 417772 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B1415015 : Blo 417772 1415015 := bstep (se 1 (by rfl) ⟨1061261, by rfl⟩ : syracuseStep 1415015 = 2122523) B2122523
theorem B628943 : Blo 417772 628943 := bstep (se 1 (by rfl) ⟨471707, by rfl⟩ : syracuseStep 628943 = 943415) B943415
theorem B629927 : Blo 417772 629927 := bstep (se 1 (by rfl) ⟨472445, by rfl⟩ : syracuseStep 629927 = 944891) B944891
theorem B1416473 : Blo 417772 1416473 := bstep (se 2 (by rfl) ⟨531177, by rfl⟩ : syracuseStep 1416473 = 1062355) B1062355
theorem B1514807 : Blo 417772 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B2694521 : Blo 417772 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B827327 : Blo 417772 827327 := bstep (se 1 (by rfl) ⟨620495, by rfl⟩ : syracuseStep 827327 = 1240991) B1240991
theorem B630887 : Blo 417772 630887 := bstep (se 1 (by rfl) ⟨473165, by rfl⟩ : syracuseStep 630887 = 946331) B946331
theorem B8102015 : Blo 417772 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B631199 : Blo 417772 631199 := bstep (se 1 (by rfl) ⟨473399, by rfl⟩ : syracuseStep 631199 = 946799) B946799
theorem B632135 : Blo 417772 632135 := bstep (se 1 (by rfl) ⟨474101, by rfl⟩ : syracuseStep 632135 = 948203) B948203
theorem B10364831 : Blo 417772 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B764041 : Blo 417772 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B1059419 : Blo 417772 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B15280751 : Blo 417772 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B797435 : Blo 417772 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B1519231 : Blo 417772 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B15348365 : Blo 417772 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B1061545 : Blo 417772 1061545 := bstep (se 2 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 1061545 = 796159) B796159
theorem B1356799 : Blo 417772 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B1063327 : Blo 417772 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B1570585301 : Blo 417772 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B670447 : Blo 417772 670447 := bstep (se 1 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 670447 = 1005671) B1005671
theorem B670601 : Blo 417772 670601 := bstep (se 2 (by rfl) ⟨251475, by rfl⟩ : syracuseStep 670601 = 502951) B502951
theorem B1785071 : Blo 417772 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B4046087 : Blo 417772 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B1259421047 : Blo 417772 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B671657 : Blo 417772 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B6473171 : Blo 417772 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B1787447 : Blo 417772 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B174935123 : Blo 417772 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B4312577 : Blo 417772 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B807239 : Blo 417772 807239 := bstep (se 1 (by rfl) ⟨605429, by rfl⟩ : syracuseStep 807239 = 1210859) B1210859
theorem B2871713 : Blo 417772 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B940139 : Blo 417772 940139 := bstep (se 1 (by rfl) ⟨705104, by rfl⟩ : syracuseStep 940139 = 1410209) B1410209
theorem B417883 : Blo 417772 417883 := bstep (se 1 (by rfl) ⟨313412, by rfl⟩ : syracuseStep 417883 = 626825) B626825
theorem B417959 : Blo 417772 417959 := bstep (se 1 (by rfl) ⟨313469, by rfl⟩ : syracuseStep 417959 = 626939) B626939
theorem B418151 : Blo 417772 418151 := bstep (se 1 (by rfl) ⟨313613, by rfl⟩ : syracuseStep 418151 = 627227) B627227
theorem B943073 : Blo 417772 943073 := bstep (se 2 (by rfl) ⟨353652, by rfl⟩ : syracuseStep 943073 = 707305) B707305
theorem B419071 : Blo 417772 419071 := bstep (se 1 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 419071 = 628607) B628607
theorem B419199 : Blo 417772 419199 := bstep (se 1 (by rfl) ⟨314399, by rfl⟩ : syracuseStep 419199 = 628799) B628799
theorem B1598879 : Blo 417772 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B419327 : Blo 417772 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B419455 : Blo 417772 419455 := bstep (se 1 (by rfl) ⟨314591, by rfl⟩ : syracuseStep 419455 = 629183) B629183
theorem B420287 : Blo 417772 420287 := bstep (se 1 (by rfl) ⟨315215, by rfl⟩ : syracuseStep 420287 = 630431) B630431
theorem B3238379 : Blo 417772 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B420719 : Blo 417772 420719 := bstep (se 1 (by rfl) ⟨315539, by rfl⟩ : syracuseStep 420719 = 631079) B631079
theorem B420895 : Blo 417772 420895 := bstep (se 1 (by rfl) ⟨315671, by rfl⟩ : syracuseStep 420895 = 631343) B631343
theorem B2387339 : Blo 417772 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B946367 : Blo 417772 946367 := bstep (se 1 (by rfl) ⟨709775, by rfl⟩ : syracuseStep 946367 = 1419551) B1419551
theorem B7500377 : Blo 417772 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B3175037 : Blo 417772 3175037 := bstep (se 3 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 3175037 = 1190639) B1190639
theorem B3176009 : Blo 417772 3176009 := bstep (se 2 (by rfl) ⟨1191003, by rfl⟩ : syracuseStep 3176009 = 2382007) B2382007
theorem B9173197 : Blo 417772 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B948671 : Blo 417772 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B2392031 : Blo 417772 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6030379 : Blo 417772 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B116623415 : Blo 417772 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B1018721 : Blo 417772 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B116723267 : Blo 417772 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B626759 : Blo 417772 626759 := bstep (se 1 (by rfl) ⟨470069, by rfl⟩ : syracuseStep 626759 = 940139) B940139
theorem B628715 : Blo 417772 628715 := bstep (se 1 (by rfl) ⟨471536, by rfl⟩ : syracuseStep 628715 = 943073) B943073
theorem B1415393 : Blo 417772 1415393 := bstep (se 2 (by rfl) ⟨530772, by rfl⟩ : syracuseStep 1415393 = 1061545) B1061545
theorem B1809065 : Blo 417772 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B793577 : Blo 417772 793577 := bstep (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) B595183
theorem B531623 : Blo 417772 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B630911 : Blo 417772 630911 := bstep (se 1 (by rfl) ⟨473183, by rfl⟩ : syracuseStep 630911 = 946367) B946367
theorem B12230929 : Blo 417772 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B10232243 : Blo 417772 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B1417769 : Blo 417772 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B893929 : Blo 417772 893929 := bstep (se 2 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 893929 = 670447) B670447
theorem B632447 : Blo 417772 632447 := bstep (se 1 (by rfl) ⟨474335, by rfl⟩ : syracuseStep 632447 = 948671) B948671
theorem B1190047 : Blo 417772 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B2697391 : Blo 417772 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B2206205 : Blo 417772 2206205 := bstep (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) B827327
theorem B1191631 : Blo 417772 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B1421495 : Blo 417772 1421495 := bstep (se 1 (by rfl) ⟨1066121, by rfl⟩ : syracuseStep 1421495 = 2132243) B2132243
theorem B20001005 : Blo 417772 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B1421819 : Blo 417772 1421819 := bstep (se 1 (by rfl) ⟨1066364, by rfl⟩ : syracuseStep 1421819 = 2132729) B2132729
theorem B3585383 : Blo 417772 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B538159 : Blo 417772 538159 := bstep (se 1 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 538159 = 807239) B807239
theorem B1914475 : Blo 417772 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B1065919 : Blo 417772 1065919 := bstep (se 1 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 1065919 = 1598879) B1598879
theorem B706279 : Blo 417772 706279 := bstep (se 1 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 706279 = 1059419) B1059419
theorem B1591559 : Blo 417772 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B2116691 : Blo 417772 2116691 := bstep (se 1 (by rfl) ⟨1587518, by rfl⟩ : syracuseStep 2116691 = 3175037) B3175037
theorem B2117339 : Blo 417772 2117339 := bstep (se 1 (by rfl) ⟨1588004, by rfl⟩ : syracuseStep 2117339 = 3176009) B3176009
theorem B1047056867 : Blo 417772 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B447067 : Blo 417772 447067 := bstep (se 1 (by rfl) ⟨335300, by rfl⟩ : syracuseStep 447067 = 670601) B670601
theorem B1791085 : Blo 417772 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B1594687 : Blo 417772 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B5199871 : Blo 417772 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B4315447 : Blo 417772 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B2120903 : Blo 417772 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B17194639 : Blo 417772 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B2875051 : Blo 417772 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B417791 : Blo 417772 417791 := bstep (se 1 (by rfl) ⟨313343, by rfl⟩ : syracuseStep 417791 = 626687) B626687
theorem B418203 : Blo 417772 418203 := bstep (se 1 (by rfl) ⟨313652, by rfl⟩ : syracuseStep 418203 = 627305) B627305
theorem B943343 : Blo 417772 943343 := bstep (se 1 (by rfl) ⟨707507, by rfl⟩ : syracuseStep 943343 = 1415015) B1415015
theorem B419295 : Blo 417772 419295 := bstep (se 1 (by rfl) ⟨314471, by rfl⟩ : syracuseStep 419295 = 628943) B628943
theorem B419951 : Blo 417772 419951 := bstep (se 1 (by rfl) ⟨314963, by rfl⟩ : syracuseStep 419951 = 629927) B629927
theorem B2025641 : Blo 417772 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B944315 : Blo 417772 944315 := bstep (se 1 (by rfl) ⟨708236, by rfl⟩ : syracuseStep 944315 = 1416473) B1416473
theorem B1009871 : Blo 417772 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B1796347 : Blo 417772 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B420591 : Blo 417772 420591 := bstep (se 1 (by rfl) ⟨315443, by rfl⟩ : syracuseStep 420591 = 630887) B630887
theorem B5401343 : Blo 417772 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B420799 : Blo 417772 420799 := bstep (se 1 (by rfl) ⟨315599, by rfl⟩ : syracuseStep 420799 = 631199) B631199
theorem B421423 : Blo 417772 421423 := bstep (se 1 (by rfl) ⟨316067, by rfl⟩ : syracuseStep 421423 = 632135) B632135
theorem B6909887 : Blo 417772 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B2158919 : Blo 417772 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B10187167 : Blo 417772 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B839614031 : Blo 417772 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B1411127 : Blo 417772 1411127 := bstep (se 1 (by rfl) ⟨1058345, by rfl⟩ : syracuseStep 1411127 = 2116691) B2116691
theorem B1411559 : Blo 417772 1411559 := bstep (se 1 (by rfl) ⟨1058669, by rfl⟩ : syracuseStep 1411559 = 2117339) B2117339
theorem B2395129 : Blo 417772 2395129 := bstep (se 2 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 2395129 = 1796347) B1796347
theorem B1413935 : Blo 417772 1413935 := bstep (se 1 (by rfl) ⟨1060451, by rfl⟩ : syracuseStep 1413935 = 2120903) B2120903
theorem B6821495 : Blo 417772 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B596089 : Blo 417772 596089 := bstep (se 2 (by rfl) ⟨223533, by rfl⟩ : syracuseStep 596089 = 447067) B447067
theorem B628895 : Blo 417772 628895 := bstep (se 1 (by rfl) ⟨471671, by rfl⟩ : syracuseStep 628895 = 943343) B943343
theorem B1350427 : Blo 417772 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B629543 : Blo 417772 629543 := bstep (se 1 (by rfl) ⟨472157, by rfl⟩ : syracuseStep 629543 = 944315) B944315
theorem B4824173 : Blo 417772 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B1417661 : Blo 417772 1417661 := bstep (se 3 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 1417661 = 531623) B531623
theorem B18426365 : Blo 417772 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B1421225 : Blo 417772 1421225 := bstep (se 2 (by rfl) ⟨532959, by rfl⟩ : syracuseStep 1421225 = 1065919) B1065919
theorem B1191905 : Blo 417772 1191905 := bstep (se 2 (by rfl) ⟨446964, by rfl⟩ : syracuseStep 1191905 = 893929) B893929
theorem B8040505 : Blo 417772 8040505 := bstep (se 2 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 8040505 = 6030379) B6030379
theorem B1061039 : Blo 417772 1061039 := bstep (se 1 (by rfl) ⟨795779, by rfl⟩ : syracuseStep 1061039 = 1591559) B1591559
theorem B1586729 : Blo 417772 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B698037911 : Blo 417772 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B1588841 : Blo 417772 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B13582889 : Blo 417772 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B673247 : Blo 417772 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B2116205 : Blo 417772 2116205 := bstep (se 3 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 2116205 = 793577) B793577
theorem B6933161 : Blo 417772 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B5753929 : Blo 417772 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B22926185 : Blo 417772 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B16307905 : Blo 417772 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B77748943 : Blo 417772 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B679147 : Blo 417772 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B941705 : Blo 417772 941705 := bstep (se 2 (by rfl) ⟨353139, by rfl⟩ : syracuseStep 941705 = 706279) B706279
theorem B77815511 : Blo 417772 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B417839 : Blo 417772 417839 := bstep (se 1 (by rfl) ⟨313379, by rfl⟩ : syracuseStep 417839 = 626759) B626759
theorem B3596521 : Blo 417772 3596521 := bstep (se 2 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 3596521 = 2697391) B2697391
theorem B419143 : Blo 417772 419143 := bstep (se 1 (by rfl) ⟨314357, by rfl⟩ : syracuseStep 419143 = 628715) B628715
theorem B943595 : Blo 417772 943595 := bstep (se 1 (by rfl) ⟨707696, by rfl⟩ : syracuseStep 943595 = 1415393) B1415393
theorem B420607 : Blo 417772 420607 := bstep (se 1 (by rfl) ⟨315455, by rfl⟩ : syracuseStep 420607 = 630911) B630911
theorem B945179 : Blo 417772 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B421631 : Blo 417772 421631 := bstep (se 1 (by rfl) ⟨316223, by rfl⟩ : syracuseStep 421631 = 632447) B632447
theorem B2388113 : Blo 417772 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B1470803 : Blo 417772 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B2126249 : Blo 417772 2126249 := bstep (se 2 (by rfl) ⟨797343, by rfl⟩ : syracuseStep 2126249 = 1594687) B1594687
theorem B3600895 : Blo 417772 3600895 := bstep (se 1 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 3600895 = 5401343) B5401343
theorem B717545 : Blo 417772 717545 := bstep (se 2 (by rfl) ⟨269079, by rfl⟩ : syracuseStep 717545 = 538159) B538159
theorem B2552633 : Blo 417772 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B947663 : Blo 417772 947663 := bstep (se 1 (by rfl) ⟨710747, by rfl⟩ : syracuseStep 947663 = 1421495) B1421495
theorem B13334003 : Blo 417772 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B1439279 : Blo 417772 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B947879 : Blo 417772 947879 := bstep (se 1 (by rfl) ⟨710909, by rfl⟩ : syracuseStep 947879 = 1421819) B1421819
theorem B2390255 : Blo 417772 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B3833401 : Blo 417772 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B559742687 : Blo 417772 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B1410803 : Blo 417772 1410803 := bstep (se 1 (by rfl) ⟨1058102, by rfl⟩ : syracuseStep 1410803 = 2116205) B2116205
theorem B7671905 : Blo 417772 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B3216115 : Blo 417772 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B627803 : Blo 417772 627803 := bstep (se 1 (by rfl) ⟨470852, by rfl⟩ : syracuseStep 627803 = 941705) B941705
theorem B51877007 : Blo 417772 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B10720673 : Blo 417772 10720673 := bstep (se 2 (by rfl) ⟨4020252, by rfl⟩ : syracuseStep 10720673 = 8040505) B8040505
theorem B629063 : Blo 417772 629063 := bstep (se 1 (by rfl) ⟨471797, by rfl⟩ : syracuseStep 629063 = 943595) B943595
theorem B18488429 : Blo 417772 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B630119 : Blo 417772 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B794603 : Blo 417772 794603 := bstep (se 1 (by rfl) ⟨595952, by rfl⟩ : syracuseStep 794603 = 1191905) B1191905
theorem B794785 : Blo 417772 794785 := bstep (se 2 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 794785 = 596089) B596089
theorem B1417499 : Blo 417772 1417499 := bstep (se 1 (by rfl) ⟨1063124, by rfl⟩ : syracuseStep 1417499 = 2126249) B2126249
theorem B631775 : Blo 417772 631775 := bstep (se 1 (by rfl) ⟨473831, by rfl⟩ : syracuseStep 631775 = 947663) B947663
theorem B8889335 : Blo 417772 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B1057819 : Blo 417772 1057819 := bstep (se 1 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 1057819 = 1586729) B1586729
theorem B959519 : Blo 417772 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B631919 : Blo 417772 631919 := bstep (se 1 (by rfl) ⟨473939, by rfl⟩ : syracuseStep 631919 = 947879) B947879
theorem B1059227 : Blo 417772 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B4795361 : Blo 417772 4795361 := bstep (se 2 (by rfl) ⟨1798260, by rfl⟩ : syracuseStep 4795361 = 3596521) B3596521
theorem B9055259 : Blo 417772 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B1913453 : Blo 417772 1913453 := bstep (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) B717545
theorem B15284123 : Blo 417772 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B3193505 : Blo 417772 3193505 := bstep (se 2 (by rfl) ⟨1197564, by rfl⟩ : syracuseStep 3193505 = 2395129) B2395129
theorem B4801193 : Blo 417772 4801193 := bstep (se 2 (by rfl) ⟨1800447, by rfl⟩ : syracuseStep 4801193 = 3600895) B3600895
theorem B3622117 : Blo 417772 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B21743873 : Blo 417772 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1592075 : Blo 417772 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B707359 : Blo 417772 707359 := bstep (se 1 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 707359 = 1061039) B1061039
theorem B103665257 : Blo 417772 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B465358607 : Blo 417772 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B1593503 : Blo 417772 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B3922141 : Blo 417772 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B448831 : Blo 417772 448831 := bstep (se 1 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 448831 = 673247) B673247
theorem B940751 : Blo 417772 940751 := bstep (se 1 (by rfl) ⟨705563, by rfl⟩ : syracuseStep 940751 = 1411127) B1411127
theorem B941039 : Blo 417772 941039 := bstep (se 1 (by rfl) ⟨705779, by rfl⟩ : syracuseStep 941039 = 1411559) B1411559
theorem B942623 : Blo 417772 942623 := bstep (se 1 (by rfl) ⟨706967, by rfl⟩ : syracuseStep 942623 = 1413935) B1413935
theorem B4547663 : Blo 417772 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B419263 : Blo 417772 419263 := bstep (se 1 (by rfl) ⟨314447, by rfl⟩ : syracuseStep 419263 = 628895) B628895
theorem B419695 : Blo 417772 419695 := bstep (se 1 (by rfl) ⟨314771, by rfl⟩ : syracuseStep 419695 = 629543) B629543
theorem B945107 : Blo 417772 945107 := bstep (se 1 (by rfl) ⟨708830, by rfl⟩ : syracuseStep 945107 = 1417661) B1417661
theorem B12284243 : Blo 417772 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B947483 : Blo 417772 947483 := bstep (se 1 (by rfl) ⟨710612, by rfl⟩ : syracuseStep 947483 = 1421225) B1421225
theorem B1701755 : Blo 417772 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B1800569 : Blo 417772 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B5111201 : Blo 417772 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B373161791 : Blo 417772 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B1410425 : Blo 417772 1410425 := bstep (se 2 (by rfl) ⟨528909, by rfl⟩ : syracuseStep 1410425 = 1057819) B1057819
theorem B69110171 : Blo 417772 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B5114603 : Blo 417772 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B7147115 : Blo 417772 7147115 := bstep (se 1 (by rfl) ⟨5360336, by rfl⟩ : syracuseStep 7147115 = 10720673) B10720673
theorem B627167 : Blo 417772 627167 := bstep (se 1 (by rfl) ⟨470375, by rfl⟩ : syracuseStep 627167 = 940751) B940751
theorem B627359 : Blo 417772 627359 := bstep (se 1 (by rfl) ⟨470519, by rfl⟩ : syracuseStep 627359 = 941039) B941039
theorem B12325619 : Blo 417772 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B529735 : Blo 417772 529735 := bstep (se 1 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 529735 = 794603) B794603
theorem B628415 : Blo 417772 628415 := bstep (se 1 (by rfl) ⟨471311, by rfl⟩ : syracuseStep 628415 = 942623) B942623
theorem B630071 : Blo 417772 630071 := bstep (se 1 (by rfl) ⟨472553, by rfl⟩ : syracuseStep 630071 = 945107) B945107
theorem B6036839 : Blo 417772 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B598441 : Blo 417772 598441 := bstep (se 2 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 598441 = 448831) B448831
theorem B631655 : Blo 417772 631655 := bstep (se 1 (by rfl) ⟨473741, by rfl⟩ : syracuseStep 631655 = 947483) B947483
theorem B1059713 : Blo 417772 1059713 := bstep (se 2 (by rfl) ⟨397392, by rfl⟩ : syracuseStep 1059713 = 794785) B794785
theorem B14495915 : Blo 417772 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B4829489 : Blo 417772 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1061383 : Blo 417772 1061383 := bstep (se 1 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 1061383 = 1592075) B1592075
theorem B1062335 : Blo 417772 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B34584671 : Blo 417772 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B639679 : Blo 417772 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B3031775 : Blo 417772 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B706151 : Blo 417772 706151 := bstep (se 1 (by rfl) ⟨529613, by rfl⟩ : syracuseStep 706151 = 1059227) B1059227
theorem B3196907 : Blo 417772 3196907 := bstep (se 1 (by rfl) ⟨2397680, by rfl⟩ : syracuseStep 3196907 = 4795361) B4795361
theorem B5229521 : Blo 417772 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B1134503 : Blo 417772 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1200379 : Blo 417772 1200379 := bstep (se 1 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 1200379 = 1800569) B1800569
theorem B3200795 : Blo 417772 3200795 := bstep (se 1 (by rfl) ⟨2400596, by rfl⟩ : syracuseStep 3200795 = 4801193) B4801193
theorem B940535 : Blo 417772 940535 := bstep (se 1 (by rfl) ⟨705401, by rfl⟩ : syracuseStep 940535 = 1410803) B1410803
theorem B310239071 : Blo 417772 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B418535 : Blo 417772 418535 := bstep (se 1 (by rfl) ⟨313901, by rfl⟩ : syracuseStep 418535 = 627803) B627803
theorem B943145 : Blo 417772 943145 := bstep (se 2 (by rfl) ⟨353679, by rfl⟩ : syracuseStep 943145 = 707359) B707359
theorem B419375 : Blo 417772 419375 := bstep (se 1 (by rfl) ⟨314531, by rfl⟩ : syracuseStep 419375 = 629063) B629063
theorem B420079 : Blo 417772 420079 := bstep (se 1 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 420079 = 630119) B630119
theorem B944999 : Blo 417772 944999 := bstep (se 1 (by rfl) ⟨708749, by rfl⟩ : syracuseStep 944999 = 1417499) B1417499
theorem B421183 : Blo 417772 421183 := bstep (se 1 (by rfl) ⟨315887, by rfl⟩ : syracuseStep 421183 = 631775) B631775
theorem B5926223 : Blo 417772 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B421279 : Blo 417772 421279 := bstep (se 1 (by rfl) ⟨315959, by rfl⟩ : syracuseStep 421279 = 631919) B631919
theorem B4288153 : Blo 417772 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B8189495 : Blo 417772 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B1275635 : Blo 417772 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B10189415 : Blo 417772 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B2129003 : Blo 417772 2129003 := bstep (se 1 (by rfl) ⟨1596752, by rfl⟩ : syracuseStep 2129003 = 3193505) B3193505
theorem B3407467 : Blo 417772 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B248774527 : Blo 417772 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B852905 : Blo 417772 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B2131271 : Blo 417772 2131271 := bstep (se 1 (by rfl) ⟨1598453, by rfl⟩ : syracuseStep 2131271 = 3196907) B3196907
theorem B46073447 : Blo 417772 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B3409735 : Blo 417772 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B32868317 : Blo 417772 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B756335 : Blo 417772 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B2133863 : Blo 417772 2133863 := bstep (se 1 (by rfl) ⟨1600397, by rfl⟩ : syracuseStep 2133863 = 3200795) B3200795
theorem B627023 : Blo 417772 627023 := bstep (se 1 (by rfl) ⟨470267, by rfl⟩ : syracuseStep 627023 = 940535) B940535
theorem B1415177 : Blo 417772 1415177 := bstep (se 2 (by rfl) ⟨530691, by rfl⟩ : syracuseStep 1415177 = 1061383) B1061383
theorem B628763 : Blo 417772 628763 := bstep (se 1 (by rfl) ⟨471572, by rfl⟩ : syracuseStep 628763 = 943145) B943145
theorem B629999 : Blo 417772 629999 := bstep (se 1 (by rfl) ⟨472499, by rfl⟩ : syracuseStep 629999 = 944999) B944999
theorem B3219659 : Blo 417772 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B6792943 : Blo 417772 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B1419335 : Blo 417772 1419335 := bstep (se 1 (by rfl) ⟨1064501, by rfl⟩ : syracuseStep 1419335 = 2129003) B2129003
theorem B797921 : Blo 417772 797921 := bstep (se 2 (by rfl) ⟨299220, by rfl⟩ : syracuseStep 797921 = 598441) B598441
theorem B470767 : Blo 417772 470767 := bstep (se 1 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 470767 = 706151) B706151
theorem B3486347 : Blo 417772 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B4764743 : Blo 417772 4764743 := bstep (se 1 (by rfl) ⟨3573557, by rfl⟩ : syracuseStep 4764743 = 7147115) B7147115
theorem B5717537 : Blo 417772 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B706313 : Blo 417772 706313 := bstep (se 2 (by rfl) ⟨264867, by rfl⟩ : syracuseStep 706313 = 529735) B529735
theorem B706475 : Blo 417772 706475 := bstep (se 1 (by rfl) ⟨529856, by rfl⟩ : syracuseStep 706475 = 1059713) B1059713
theorem B3950815 : Blo 417772 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B708223 : Blo 417772 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B5459663 : Blo 417772 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B23056447 : Blo 417772 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B4543289 : Blo 417772 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B331699369 : Blo 417772 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B2021183 : Blo 417772 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B940283 : Blo 417772 940283 := bstep (se 1 (by rfl) ⟨705212, by rfl⟩ : syracuseStep 940283 = 1410425) B1410425
theorem B418111 : Blo 417772 418111 := bstep (se 1 (by rfl) ⟨313583, by rfl⟩ : syracuseStep 418111 = 627167) B627167
theorem B418239 : Blo 417772 418239 := bstep (se 1 (by rfl) ⟨313679, by rfl⟩ : syracuseStep 418239 = 627359) B627359
theorem B418943 : Blo 417772 418943 := bstep (se 1 (by rfl) ⟨314207, by rfl⟩ : syracuseStep 418943 = 628415) B628415
theorem B420047 : Blo 417772 420047 := bstep (se 1 (by rfl) ⟨315035, by rfl⟩ : syracuseStep 420047 = 630071) B630071
theorem B4024559 : Blo 417772 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B206826047 : Blo 417772 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B1600505 : Blo 417772 1600505 := bstep (se 2 (by rfl) ⟨600189, by rfl⟩ : syracuseStep 1600505 = 1200379) B1200379
theorem B421103 : Blo 417772 421103 := bstep (se 1 (by rfl) ⟨315827, by rfl⟩ : syracuseStep 421103 = 631655) B631655
theorem B9663943 : Blo 417772 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B850423 : Blo 417772 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B1347455 : Blo 417772 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B626855 : Blo 417772 626855 := bstep (se 1 (by rfl) ⟨470141, by rfl⟩ : syracuseStep 626855 = 940283) B940283
theorem B627689 : Blo 417772 627689 := bstep (se 2 (by rfl) ⟨235383, by rfl⟩ : syracuseStep 627689 = 470767) B470767
theorem B30741929 : Blo 417772 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B12885257 : Blo 417772 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B531947 : Blo 417772 531947 := bstep (se 1 (by rfl) ⟨398960, by rfl⟩ : syracuseStep 531947 = 797921) B797921
theorem B14559101 : Blo 417772 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B3811691 : Blo 417772 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B568603 : Blo 417772 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B1420847 : Blo 417772 1420847 := bstep (se 1 (by rfl) ⟨1065635, by rfl⟩ : syracuseStep 1420847 = 2131271) B2131271
theorem B30715631 : Blo 417772 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B470875 : Blo 417772 470875 := bstep (se 1 (by rfl) ⟨353156, by rfl⟩ : syracuseStep 470875 = 706313) B706313
theorem B470983 : Blo 417772 470983 := bstep (se 1 (by rfl) ⟨353237, by rfl⟩ : syracuseStep 470983 = 706475) B706475
theorem B9057257 : Blo 417772 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B1422575 : Blo 417772 1422575 := bstep (se 1 (by rfl) ⟨1066931, by rfl⟩ : syracuseStep 1422575 = 2133863) B2133863
theorem B3028859 : Blo 417772 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B2146439 : Blo 417772 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B148750805 : Blo 417772 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B2016893 : Blo 417772 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B1067003 : Blo 417772 1067003 := bstep (se 1 (by rfl) ⟨800252, by rfl⟩ : syracuseStep 1067003 = 1600505) B1600505
theorem B1133897 : Blo 417772 1133897 := bstep (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) B850423
theorem B21912211 : Blo 417772 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B4546313 : Blo 417772 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B418015 : Blo 417772 418015 := bstep (se 1 (by rfl) ⟨313511, by rfl⟩ : syracuseStep 418015 = 627023) B627023
theorem B5267753 : Blo 417772 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B943451 : Blo 417772 943451 := bstep (se 1 (by rfl) ⟨707588, by rfl⟩ : syracuseStep 943451 = 1415177) B1415177
theorem B419175 : Blo 417772 419175 := bstep (se 1 (by rfl) ⟨314381, by rfl⟩ : syracuseStep 419175 = 628763) B628763
theorem B419999 : Blo 417772 419999 := bstep (se 1 (by rfl) ⟨314999, by rfl⟩ : syracuseStep 419999 = 629999) B629999
theorem B944297 : Blo 417772 944297 := bstep (se 2 (by rfl) ⟨354111, by rfl⟩ : syracuseStep 944297 = 708223) B708223
theorem B946223 : Blo 417772 946223 := bstep (se 1 (by rfl) ⟨709667, by rfl⟩ : syracuseStep 946223 = 1419335) B1419335
theorem B2683039 : Blo 417772 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B442265825 : Blo 417772 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B137884031 : Blo 417772 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B3176495 : Blo 417772 3176495 := bstep (se 1 (by rfl) ⟨2382371, by rfl⟩ : syracuseStep 3176495 = 4764743) B4764743
theorem B1344595 : Blo 417772 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B8590171 : Blo 417772 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B627833 : Blo 417772 627833 := bstep (se 2 (by rfl) ⟨235437, by rfl⟩ : syracuseStep 627833 = 470875) B470875
theorem B627977 : Blo 417772 627977 := bstep (se 2 (by rfl) ⟨235491, by rfl⟩ : syracuseStep 627977 = 470983) B470983
theorem B3511835 : Blo 417772 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B3577385 : Blo 417772 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B628967 : Blo 417772 628967 := bstep (se 1 (by rfl) ⟨471725, by rfl⟩ : syracuseStep 628967 = 943451) B943451
theorem B9706067 : Blo 417772 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B629531 : Blo 417772 629531 := bstep (se 1 (by rfl) ⟨472148, by rfl⟩ : syracuseStep 629531 = 944297) B944297
theorem B630815 : Blo 417772 630815 := bstep (se 1 (by rfl) ⟨473111, by rfl⟩ : syracuseStep 630815 = 946223) B946223
theorem B91922687 : Blo 417772 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B6038171 : Blo 417772 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B3023725 : Blo 417772 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B1418525 : Blo 417772 1418525 := bstep (se 3 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 1418525 = 531947) B531947
theorem B99167203 : Blo 417772 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B898303 : Blo 417772 898303 := bstep (se 1 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 898303 = 1347455) B1347455
theorem B116865125 : Blo 417772 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B20494619 : Blo 417772 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B3030875 : Blo 417772 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B3032549 : Blo 417772 3032549 := bstep (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) B568603
theorem B2541127 : Blo 417772 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B2019239 : Blo 417772 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B2117663 : Blo 417772 2117663 := bstep (se 1 (by rfl) ⟨1588247, by rfl⟩ : syracuseStep 2117663 = 3176495) B3176495
theorem B1430959 : Blo 417772 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B711335 : Blo 417772 711335 := bstep (se 1 (by rfl) ⟨533501, by rfl⟩ : syracuseStep 711335 = 1067003) B1067003
theorem B417903 : Blo 417772 417903 := bstep (se 1 (by rfl) ⟨313427, by rfl⟩ : syracuseStep 417903 = 626855) B626855
theorem B418459 : Blo 417772 418459 := bstep (se 1 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 418459 = 627689) B627689
theorem B947231 : Blo 417772 947231 := bstep (se 1 (by rfl) ⟨710423, by rfl⟩ : syracuseStep 947231 = 1420847) B1420847
theorem B20477087 : Blo 417772 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B294843883 : Blo 417772 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B948383 : Blo 417772 948383 := bstep (se 1 (by rfl) ⟨711287, by rfl⟩ : syracuseStep 948383 = 1422575) B1422575
theorem B4031633 : Blo 417772 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B1346159 : Blo 417772 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B1411775 : Blo 417772 1411775 := bstep (se 1 (by rfl) ⟨1058831, by rfl⟩ : syracuseStep 1411775 = 2117663) B2117663
theorem B132222937 : Blo 417772 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B61281791 : Blo 417772 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B1907945 : Blo 417772 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B393125177 : Blo 417772 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B631487 : Blo 417772 631487 := bstep (se 1 (by rfl) ⟨473615, by rfl⟩ : syracuseStep 631487 = 947231) B947231
theorem B632255 : Blo 417772 632255 := bstep (se 1 (by rfl) ⟨474191, by rfl⟩ : syracuseStep 632255 = 948383) B948383
theorem B3388169 : Blo 417772 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B2341223 : Blo 417772 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B6470711 : Blo 417772 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B474223 : Blo 417772 474223 := bstep (se 1 (by rfl) ⟨355667, by rfl⟩ : syracuseStep 474223 = 711335) B711335
theorem B11453561 : Blo 417772 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B1197737 : Blo 417772 1197737 := bstep (se 2 (by rfl) ⟨449151, by rfl⟩ : syracuseStep 1197737 = 898303) B898303
theorem B13651391 : Blo 417772 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B77910083 : Blo 417772 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B2020583 : Blo 417772 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B2021699 : Blo 417772 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B1792793 : Blo 417772 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B418555 : Blo 417772 418555 := bstep (se 1 (by rfl) ⟨313916, by rfl⟩ : syracuseStep 418555 = 627833) B627833
theorem B418651 : Blo 417772 418651 := bstep (se 1 (by rfl) ⟨313988, by rfl⟩ : syracuseStep 418651 = 627977) B627977
theorem B2384923 : Blo 417772 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B419311 : Blo 417772 419311 := bstep (se 1 (by rfl) ⟨314483, by rfl⟩ : syracuseStep 419311 = 628967) B628967
theorem B419687 : Blo 417772 419687 := bstep (se 1 (by rfl) ⟨314765, by rfl⟩ : syracuseStep 419687 = 629531) B629531
theorem B420543 : Blo 417772 420543 := bstep (se 1 (by rfl) ⟨315407, by rfl⟩ : syracuseStep 420543 = 630815) B630815
theorem B4025447 : Blo 417772 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B945683 : Blo 417772 945683 := bstep (se 1 (by rfl) ⟨709262, by rfl⟩ : syracuseStep 945683 = 1418525) B1418525
theorem B13663079 : Blo 417772 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B7635707 : Blo 417772 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B2687755 : Blo 417772 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B3179897 : Blo 417772 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B51940055 : Blo 417772 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B262083451 : Blo 417772 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B176297249 : Blo 417772 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B630455 : Blo 417772 630455 := bstep (se 1 (by rfl) ⟨472841, by rfl⟩ : syracuseStep 630455 = 945683) B945683
theorem B632297 : Blo 417772 632297 := bstep (se 2 (by rfl) ⟨237111, by rfl⟩ : syracuseStep 632297 = 474223) B474223
theorem B798491 : Blo 417772 798491 := bstep (se 1 (by rfl) ⟨598868, by rfl⟩ : syracuseStep 798491 = 1197737) B1197737
theorem B5388221 : Blo 417772 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B5391197 : Blo 417772 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B3589757 : Blo 417772 3589757 := bstep (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) B1346159
theorem B1560815 : Blo 417772 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B4313807 : Blo 417772 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B941183 : Blo 417772 941183 := bstep (se 1 (by rfl) ⟨705887, by rfl⟩ : syracuseStep 941183 = 1411775) B1411775
theorem B9100927 : Blo 417772 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B40854527 : Blo 417772 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B1271963 : Blo 417772 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B420991 : Blo 417772 420991 := bstep (se 1 (by rfl) ⟨315743, by rfl⟩ : syracuseStep 420991 = 631487) B631487
theorem B421503 : Blo 417772 421503 := bstep (se 1 (by rfl) ⟨316127, by rfl⟩ : syracuseStep 421503 = 632255) B632255
theorem B4780781 : Blo 417772 4780781 := bstep (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) B1792793
theorem B2683631 : Blo 417772 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B2258779 : Blo 417772 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B9108719 : Blo 417772 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B2393171 : Blo 417772 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B627455 : Blo 417772 627455 := bstep (se 1 (by rfl) ⟨470591, by rfl⟩ : syracuseStep 627455 = 941183) B941183
theorem B27236351 : Blo 417772 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B349444601 : Blo 417772 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B532327 : Blo 417772 532327 := bstep (se 1 (by rfl) ⟨399245, by rfl⟩ : syracuseStep 532327 = 798491) B798491
theorem B3187187 : Blo 417772 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B6072479 : Blo 417772 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B12134569 : Blo 417772 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B5090471 : Blo 417772 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B3583673 : Blo 417772 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B3391901 : Blo 417772 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B1789087 : Blo 417772 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B3592147 : Blo 417772 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B3594131 : Blo 417772 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B2119931 : Blo 417772 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B34626703 : Blo 417772 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B1040543 : Blo 417772 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B2875871 : Blo 417772 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B117531499 : Blo 417772 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B420303 : Blo 417772 420303 := bstep (se 1 (by rfl) ⟨315227, by rfl⟩ : syracuseStep 420303 = 630455) B630455
theorem B421531 : Blo 417772 421531 := bstep (se 1 (by rfl) ⟨316148, by rfl⟩ : syracuseStep 421531 = 632297) B632297
theorem B3011705 : Blo 417772 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B2261267 : Blo 417772 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B7668989 : Blo 417772 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B2396087 : Blo 417772 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B18157567 : Blo 417772 18157567 := bstep (se 1 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 18157567 = 27236351) B27236351
theorem B1413287 : Blo 417772 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B4789529 : Blo 417772 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B693695 : Blo 417772 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B2007803 : Blo 417772 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B156708665 : Blo 417772 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B232963067 : Blo 417772 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B4048319 : Blo 417772 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B3393647 : Blo 417772 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B709769 : Blo 417772 709769 := bstep (se 2 (by rfl) ⟨266163, by rfl⟩ : syracuseStep 709769 = 532327) B532327
theorem B1595447 : Blo 417772 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B16179425 : Blo 417772 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B418303 : Blo 417772 418303 := bstep (se 1 (by rfl) ⟨313727, by rfl⟩ : syracuseStep 418303 = 627455) B627455
theorem B2385449 : Blo 417772 2385449 := bstep (se 2 (by rfl) ⟨894543, by rfl⟩ : syracuseStep 2385449 = 1789087) B1789087
theorem B2124791 : Blo 417772 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B2389115 : Blo 417772 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B46168937 : Blo 417772 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B1507511 : Blo 417772 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B5112659 : Blo 417772 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B2262431 : Blo 417772 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B10786283 : Blo 417772 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B1416527 : Blo 417772 1416527 := bstep (se 1 (by rfl) ⟨1062395, by rfl⟩ : syracuseStep 1416527 = 2124791) B2124791
theorem B104472443 : Blo 417772 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B30779291 : Blo 417772 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B2698879 : Blo 417772 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B473179 : Blo 417772 473179 := bstep (se 1 (by rfl) ⟨354884, by rfl⟩ : syracuseStep 473179 = 709769) B709769
theorem B3193019 : Blo 417772 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B1849853 : Blo 417772 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B1063631 : Blo 417772 1063631 := bstep (se 1 (by rfl) ⟨797723, by rfl⟩ : syracuseStep 1063631 = 1595447) B1595447
theorem B1590299 : Blo 417772 1590299 := bstep (se 1 (by rfl) ⟨1192724, by rfl⟩ : syracuseStep 1590299 = 2385449) B2385449
theorem B1592743 : Blo 417772 1592743 := bstep (se 1 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 1592743 = 2389115) B2389115
theorem B155308711 : Blo 417772 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B1597391 : Blo 417772 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B942191 : Blo 417772 942191 := bstep (se 1 (by rfl) ⟨706643, by rfl⟩ : syracuseStep 942191 = 1413287) B1413287
theorem B24210089 : Blo 417772 24210089 := bstep (se 2 (by rfl) ⟨9078783, by rfl⟩ : syracuseStep 24210089 = 18157567) B18157567
theorem B1338535 : Blo 417772 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B13633757 : Blo 417772 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B6033149 : Blo 417772 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B628127 : Blo 417772 628127 := bstep (se 1 (by rfl) ⟨471095, by rfl⟩ : syracuseStep 628127 = 942191) B942191
theorem B20519527 : Blo 417772 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B630905 : Blo 417772 630905 := bstep (se 2 (by rfl) ⟨236589, by rfl⟩ : syracuseStep 630905 = 473179) B473179
theorem B1060199 : Blo 417772 1060199 := bstep (se 1 (by rfl) ⟨795149, by rfl⟩ : syracuseStep 1060199 = 1590299) B1590299
theorem B7190855 : Blo 417772 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B1784713 : Blo 417772 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B1064927 : Blo 417772 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B207078281 : Blo 417772 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B16140059 : Blo 417772 16140059 := bstep (se 1 (by rfl) ⟨12105044, by rfl⟩ : syracuseStep 16140059 = 24210089) B24210089
theorem B1233235 : Blo 417772 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B709087 : Blo 417772 709087 := bstep (se 1 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 709087 = 1063631) B1063631
theorem B1005007 : Blo 417772 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B2123657 : Blo 417772 2123657 := bstep (se 2 (by rfl) ⟨796371, by rfl⟩ : syracuseStep 2123657 = 1592743) B1592743
theorem B3598505 : Blo 417772 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B944351 : Blo 417772 944351 := bstep (se 1 (by rfl) ⟨708263, by rfl⟩ : syracuseStep 944351 = 1416527) B1416527
theorem B2128679 : Blo 417772 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B278593181 : Blo 417772 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B138052187 : Blo 417772 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B1644313 : Blo 417772 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B1415771 : Blo 417772 1415771 := bstep (se 1 (by rfl) ⟨1061828, by rfl⟩ : syracuseStep 1415771 = 2123657) B2123657
theorem B2399003 : Blo 417772 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B629567 : Blo 417772 629567 := bstep (se 1 (by rfl) ⟨472175, by rfl⟩ : syracuseStep 629567 = 944351) B944351
theorem B4793903 : Blo 417772 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B1419119 : Blo 417772 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B10760039 : Blo 417772 10760039 := bstep (se 1 (by rfl) ⟨8070029, by rfl⟩ : syracuseStep 10760039 = 16140059) B16140059
theorem B9089171 : Blo 417772 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B706799 : Blo 417772 706799 := bstep (se 1 (by rfl) ⟨530099, by rfl⟩ : syracuseStep 706799 = 1060199) B1060199
theorem B2379617 : Blo 417772 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B709951 : Blo 417772 709951 := bstep (se 1 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 709951 = 1064927) B1064927
theorem B4022099 : Blo 417772 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B418751 : Blo 417772 418751 := bstep (se 1 (by rfl) ⟨314063, by rfl⟩ : syracuseStep 418751 = 628127) B628127
theorem B420603 : Blo 417772 420603 := bstep (se 1 (by rfl) ⟨315452, by rfl⟩ : syracuseStep 420603 = 630905) B630905
theorem B945449 : Blo 417772 945449 := bstep (se 2 (by rfl) ⟨354543, by rfl⟩ : syracuseStep 945449 = 709087) B709087
theorem B1340009 : Blo 417772 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B27359369 : Blo 417772 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B185728787 : Blo 417772 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B630299 : Blo 417772 630299 := bstep (se 1 (by rfl) ⟨472724, by rfl⟩ : syracuseStep 630299 = 945449) B945449
theorem B893339 : Blo 417772 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B471199 : Blo 417772 471199 := bstep (se 1 (by rfl) ⟨353399, by rfl⟩ : syracuseStep 471199 = 706799) B706799
theorem B1586411 : Blo 417772 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B3195935 : Blo 417772 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B18239579 : Blo 417772 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B123819191 : Blo 417772 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B92034791 : Blo 417772 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B943847 : Blo 417772 943847 := bstep (se 1 (by rfl) ⟨707885, by rfl⟩ : syracuseStep 943847 = 1415771) B1415771
theorem B1599335 : Blo 417772 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B419711 : Blo 417772 419711 := bstep (se 1 (by rfl) ⟨314783, by rfl⟩ : syracuseStep 419711 = 629567) B629567
theorem B2681399 : Blo 417772 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B946079 : Blo 417772 946079 := bstep (se 1 (by rfl) ⟨709559, by rfl⟩ : syracuseStep 946079 = 1419119) B1419119
theorem B946601 : Blo 417772 946601 := bstep (se 2 (by rfl) ⟨354975, by rfl⟩ : syracuseStep 946601 = 709951) B709951
theorem B2192417 : Blo 417772 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B7173359 : Blo 417772 7173359 := bstep (se 1 (by rfl) ⟨5380019, by rfl⟩ : syracuseStep 7173359 = 10760039) B10760039
theorem B6059447 : Blo 417772 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B2130623 : Blo 417772 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B12159719 : Blo 417772 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B82546127 : Blo 417772 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B628265 : Blo 417772 628265 := bstep (se 2 (by rfl) ⟨235599, by rfl⟩ : syracuseStep 628265 = 471199) B471199
theorem B595559 : Blo 417772 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B629231 : Blo 417772 629231 := bstep (se 1 (by rfl) ⟨471923, by rfl⟩ : syracuseStep 629231 = 943847) B943847
theorem B630719 : Blo 417772 630719 := bstep (se 1 (by rfl) ⟨473039, by rfl⟩ : syracuseStep 630719 = 946079) B946079
theorem B631067 : Blo 417772 631067 := bstep (se 1 (by rfl) ⟨473300, by rfl⟩ : syracuseStep 631067 = 946601) B946601
theorem B1057607 : Blo 417772 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B4039631 : Blo 417772 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B61356527 : Blo 417772 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B1066223 : Blo 417772 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B1787599 : Blo 417772 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B1461611 : Blo 417772 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B420199 : Blo 417772 420199 := bstep (se 1 (by rfl) ⟨315149, by rfl⟩ : syracuseStep 420199 = 630299) B630299
theorem B4782239 : Blo 417772 4782239 := bstep (se 1 (by rfl) ⟨3586679, by rfl⟩ : syracuseStep 4782239 = 7173359) B7173359
theorem B2693087 : Blo 417772 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B3188159 : Blo 417772 3188159 := bstep (se 1 (by rfl) ⟨2391119, by rfl⟩ : syracuseStep 3188159 = 4782239) B4782239
theorem B40904351 : Blo 417772 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B1420415 : Blo 417772 1420415 := bstep (se 1 (by rfl) ⟨1065311, by rfl⟩ : syracuseStep 1420415 = 2130623) B2130623
theorem B8106479 : Blo 417772 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B55030751 : Blo 417772 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B1588157 : Blo 417772 1588157 := bstep (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) B595559
theorem B705071 : Blo 417772 705071 := bstep (se 1 (by rfl) ⟨528803, by rfl⟩ : syracuseStep 705071 = 1057607) B1057607
theorem B710815 : Blo 417772 710815 := bstep (se 1 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 710815 = 1066223) B1066223
theorem B2383465 : Blo 417772 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B418843 : Blo 417772 418843 := bstep (se 1 (by rfl) ⟨314132, by rfl⟩ : syracuseStep 418843 = 628265) B628265
theorem B419487 : Blo 417772 419487 := bstep (se 1 (by rfl) ⟨314615, by rfl⟩ : syracuseStep 419487 = 629231) B629231
theorem B420479 : Blo 417772 420479 := bstep (se 1 (by rfl) ⟨315359, by rfl⟩ : syracuseStep 420479 = 630719) B630719
theorem B420711 : Blo 417772 420711 := bstep (se 1 (by rfl) ⟨315533, by rfl⟩ : syracuseStep 420711 = 631067) B631067
theorem B3897629 : Blo 417772 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B27269567 : Blo 417772 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B2598419 : Blo 417772 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1058771 : Blo 417772 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B470047 : Blo 417772 470047 := bstep (se 1 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 470047 = 705071) B705071
theorem B36687167 : Blo 417772 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B1795391 : Blo 417772 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B2125439 : Blo 417772 2125439 := bstep (se 1 (by rfl) ⟨1594079, by rfl⟩ : syracuseStep 2125439 = 3188159) B3188159
theorem B946943 : Blo 417772 946943 := bstep (se 1 (by rfl) ⟨710207, by rfl⟩ : syracuseStep 946943 = 1420415) B1420415
theorem B947753 : Blo 417772 947753 := bstep (se 2 (by rfl) ⟨355407, by rfl⟩ : syracuseStep 947753 = 710815) B710815
theorem B5404319 : Blo 417772 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B3177953 : Blo 417772 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B626729 : Blo 417772 626729 := bstep (se 2 (by rfl) ⟨235023, by rfl⟩ : syracuseStep 626729 = 470047) B470047
theorem B1416959 : Blo 417772 1416959 := bstep (se 1 (by rfl) ⟨1062719, by rfl⟩ : syracuseStep 1416959 = 2125439) B2125439
theorem B631295 : Blo 417772 631295 := bstep (se 1 (by rfl) ⟨473471, by rfl⟩ : syracuseStep 631295 = 946943) B946943
theorem B631835 : Blo 417772 631835 := bstep (se 1 (by rfl) ⟨473876, by rfl⟩ : syracuseStep 631835 = 947753) B947753
theorem B24458111 : Blo 417772 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B1196927 : Blo 417772 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B705847 : Blo 417772 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B2118635 : Blo 417772 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B18179711 : Blo 417772 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B1732279 : Blo 417772 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B3602879 : Blo 417772 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B1412423 : Blo 417772 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B2401919 : Blo 417772 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B797951 : Blo 417772 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B2309705 : Blo 417772 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B16305407 : Blo 417772 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B941129 : Blo 417772 941129 := bstep (se 2 (by rfl) ⟨352923, by rfl⟩ : syracuseStep 941129 = 705847) B705847
theorem B417819 : Blo 417772 417819 := bstep (se 1 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 417819 = 626729) B626729
theorem B944639 : Blo 417772 944639 := bstep (se 1 (by rfl) ⟨708479, by rfl⟩ : syracuseStep 944639 = 1416959) B1416959
theorem B420863 : Blo 417772 420863 := bstep (se 1 (by rfl) ⟨315647, by rfl⟩ : syracuseStep 420863 = 631295) B631295
theorem B421223 : Blo 417772 421223 := bstep (se 1 (by rfl) ⟨315917, by rfl⟩ : syracuseStep 421223 = 631835) B631835
theorem B12119807 : Blo 417772 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B627419 : Blo 417772 627419 := bstep (se 1 (by rfl) ⟨470564, by rfl⟩ : syracuseStep 627419 = 941129) B941129
theorem B629759 : Blo 417772 629759 := bstep (se 1 (by rfl) ⟨472319, by rfl⟩ : syracuseStep 629759 = 944639) B944639
theorem B8079871 : Blo 417772 8079871 := bstep (se 1 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 8079871 = 12119807) B12119807
theorem B10870271 : Blo 417772 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B941615 : Blo 417772 941615 := bstep (se 1 (by rfl) ⟨706211, by rfl⟩ : syracuseStep 941615 = 1412423) B1412423
theorem B1601279 : Blo 417772 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B2127869 : Blo 417772 2127869 := bstep (se 3 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 2127869 = 797951) B797951
theorem B1539803 : Blo 417772 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B7246847 : Blo 417772 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B627743 : Blo 417772 627743 := bstep (se 1 (by rfl) ⟨470807, by rfl⟩ : syracuseStep 627743 = 941615) B941615
theorem B1418579 : Blo 417772 1418579 := bstep (se 1 (by rfl) ⟨1063934, by rfl⟩ : syracuseStep 1418579 = 2127869) B2127869
theorem B1026535 : Blo 417772 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B1067519 : Blo 417772 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B418279 : Blo 417772 418279 := bstep (se 1 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 418279 = 627419) B627419
theorem B10773161 : Blo 417772 10773161 := bstep (se 2 (by rfl) ⟨4039935, by rfl⟩ : syracuseStep 10773161 = 8079871) B8079871
theorem B419839 : Blo 417772 419839 := bstep (se 1 (by rfl) ⟨314879, by rfl⟩ : syracuseStep 419839 = 629759) B629759
theorem B7182107 : Blo 417772 7182107 := bstep (se 1 (by rfl) ⟨5386580, by rfl⟩ : syracuseStep 7182107 = 10773161) B10773161
theorem B711679 : Blo 417772 711679 := bstep (se 1 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 711679 = 1067519) B1067519
theorem B19324925 : Blo 417772 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B1368713 : Blo 417772 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B418495 : Blo 417772 418495 := bstep (se 1 (by rfl) ⟨313871, by rfl⟩ : syracuseStep 418495 = 627743) B627743
theorem B945719 : Blo 417772 945719 := bstep (se 1 (by rfl) ⟨709289, by rfl⟩ : syracuseStep 945719 = 1418579) B1418579
theorem B4788071 : Blo 417772 4788071 := bstep (se 1 (by rfl) ⟨3591053, by rfl⟩ : syracuseStep 4788071 = 7182107) B7182107
theorem B12883283 : Blo 417772 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B630479 : Blo 417772 630479 := bstep (se 1 (by rfl) ⟨472859, by rfl⟩ : syracuseStep 630479 = 945719) B945719
theorem B912475 : Blo 417772 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B948905 : Blo 417772 948905 := bstep (se 2 (by rfl) ⟨355839, by rfl⟩ : syracuseStep 948905 = 711679) B711679
theorem B8588855 : Blo 417772 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B1216633 : Blo 417772 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B632603 : Blo 417772 632603 := bstep (se 1 (by rfl) ⟨474452, by rfl⟩ : syracuseStep 632603 = 948905) B948905
theorem B3192047 : Blo 417772 3192047 := bstep (se 1 (by rfl) ⟨2394035, by rfl⟩ : syracuseStep 3192047 = 4788071) B4788071
theorem B420319 : Blo 417772 420319 := bstep (se 1 (by rfl) ⟨315239, by rfl⟩ : syracuseStep 420319 = 630479) B630479
theorem B1622177 : Blo 417772 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B5725903 : Blo 417772 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B421735 : Blo 417772 421735 := bstep (se 1 (by rfl) ⟨316301, by rfl⟩ : syracuseStep 421735 = 632603) B632603
theorem B2128031 : Blo 417772 2128031 := bstep (se 1 (by rfl) ⟨1596023, by rfl⟩ : syracuseStep 2128031 = 3192047) B3192047
theorem B1081451 : Blo 417772 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B1418687 : Blo 417772 1418687 := bstep (se 1 (by rfl) ⟨1064015, by rfl⟩ : syracuseStep 1418687 = 2128031) B2128031
theorem B7634537 : Blo 417772 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B2883869 : Blo 417772 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B5089691 : Blo 417772 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B945791 : Blo 417772 945791 := bstep (se 1 (by rfl) ⟨709343, by rfl⟩ : syracuseStep 945791 = 1418687) B1418687
theorem B630527 : Blo 417772 630527 := bstep (se 1 (by rfl) ⟨472895, by rfl⟩ : syracuseStep 630527 = 945791) B945791
theorem B3393127 : Blo 417772 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B1922579 : Blo 417772 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B4524169 : Blo 417772 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B1281719 : Blo 417772 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B420351 : Blo 417772 420351 := bstep (se 1 (by rfl) ⟨315263, by rfl⟩ : syracuseStep 420351 = 630527) B630527
theorem B854479 : Blo 417772 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B6032225 : Blo 417772 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B4021483 : Blo 417772 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B1139305 : Blo 417772 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B1519073 : Blo 417772 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B5361977 : Blo 417772 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B3574651 : Blo 417772 3574651 := bstep (se 1 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 3574651 = 5361977) B5361977
theorem B1012715 : Blo 417772 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B4766201 : Blo 417772 4766201 := bstep (se 2 (by rfl) ⟨1787325, by rfl⟩ : syracuseStep 4766201 = 3574651) B3574651
theorem B675143 : Blo 417772 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B450095 : Blo 417772 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B3177467 : Blo 417772 3177467 := bstep (se 1 (by rfl) ⟨2383100, by rfl⟩ : syracuseStep 3177467 = 4766201) B4766201
theorem B1200253 : Blo 417772 1200253 := bstep (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) B450095
theorem B2118311 : Blo 417772 2118311 := bstep (se 1 (by rfl) ⟨1588733, by rfl⟩ : syracuseStep 2118311 = 3177467) B3177467
theorem B1412207 : Blo 417772 1412207 := bstep (se 1 (by rfl) ⟨1059155, by rfl⟩ : syracuseStep 1412207 = 2118311) B2118311
theorem B1600337 : Blo 417772 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B1066891 : Blo 417772 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B941471 : Blo 417772 941471 := bstep (se 1 (by rfl) ⟨706103, by rfl⟩ : syracuseStep 941471 = 1412207) B1412207
theorem B627647 : Blo 417772 627647 := bstep (se 1 (by rfl) ⟨470735, by rfl⟩ : syracuseStep 627647 = 941471) B941471
theorem B1422521 : Blo 417772 1422521 := bstep (se 2 (by rfl) ⟨533445, by rfl⟩ : syracuseStep 1422521 = 1066891) B1066891
theorem B418431 : Blo 417772 418431 := bstep (se 1 (by rfl) ⟨313823, by rfl⟩ : syracuseStep 418431 = 627647) B627647
theorem B948347 : Blo 417772 948347 := bstep (se 1 (by rfl) ⟨711260, by rfl⟩ : syracuseStep 948347 = 1422521) B1422521
theorem B632231 : Blo 417772 632231 := bstep (se 1 (by rfl) ⟨474173, by rfl⟩ : syracuseStep 632231 = 948347) B948347
theorem B421487 : Blo 417772 421487 := bstep (se 1 (by rfl) ⟨316115, by rfl⟩ : syracuseStep 421487 = 632231) B632231

theorem C0 (j : ℕ) (h1 : 104443 ≤ j) (h2 : j ≤ 105142) : Blo 417772 (4 * j + 3) := by
  interval_cases j
  · exact B417775
  · exact B417779
  · exact B417783
  · exact B417787
  · exact B417791
  · exact B417795
  · exact B417799
  · exact B417803
  · exact B417807
  · exact B417811
  · exact B417815
  · exact B417819
  · exact B417823
  · exact B417827
  · exact B417831
  · exact B417835
  · exact B417839
  · exact B417843
  · exact B417847
  · exact B417851
  · exact B417855
  · exact B417859
  · exact B417863
  · exact B417867
  · exact B417871
  · exact B417875
  · exact B417879
  · exact B417883
  · exact B417887
  · exact B417891
  · exact B417895
  · exact B417899
  · exact B417903
  · exact B417907
  · exact B417911
  · exact B417915
  · exact B417919
  · exact B417923
  · exact B417927
  · exact B417931
  · exact B417935
  · exact B417939
  · exact B417943
  · exact B417947
  · exact B417951
  · exact B417955
  · exact B417959
  · exact B417963
  · exact B417967
  · exact B417971
  · exact B417975
  · exact B417979
  · exact B417983
  · exact B417987
  · exact B417991
  · exact B417995
  · exact B417999
  · exact B418003
  · exact B418007
  · exact B418011
  · exact B418015
  · exact B418019
  · exact B418023
  · exact B418027
  · exact B418031
  · exact B418035
  · exact B418039
  · exact B418043
  · exact B418047
  · exact B418051
  · exact B418055
  · exact B418059
  · exact B418063
  · exact B418067
  · exact B418071
  · exact B418075
  · exact B418079
  · exact B418083
  · exact B418087
  · exact B418091
  · exact B418095
  · exact B418099
  · exact B418103
  · exact B418107
  · exact B418111
  · exact B418115
  · exact B418119
  · exact B418123
  · exact B418127
  · exact B418131
  · exact B418135
  · exact B418139
  · exact B418143
  · exact B418147
  · exact B418151
  · exact B418155
  · exact B418159
  · exact B418163
  · exact B418167
  · exact B418171
  · exact B418175
  · exact B418179
  · exact B418183
  · exact B418187
  · exact B418191
  · exact B418195
  · exact B418199
  · exact B418203
  · exact B418207
  · exact B418211
  · exact B418215
  · exact B418219
  · exact B418223
  · exact B418227
  · exact B418231
  · exact B418235
  · exact B418239
  · exact B418243
  · exact B418247
  · exact B418251
  · exact B418255
  · exact B418259
  · exact B418263
  · exact B418267
  · exact B418271
  · exact B418275
  · exact B418279
  · exact B418283
  · exact B418287
  · exact B418291
  · exact B418295
  · exact B418299
  · exact B418303
  · exact B418307
  · exact B418311
  · exact B418315
  · exact B418319
  · exact B418323
  · exact B418327
  · exact B418331
  · exact B418335
  · exact B418339
  · exact B418343
  · exact B418347
  · exact B418351
  · exact B418355
  · exact B418359
  · exact B418363
  · exact B418367
  · exact B418371
  · exact B418375
  · exact B418379
  · exact B418383
  · exact B418387
  · exact B418391
  · exact B418395
  · exact B418399
  · exact B418403
  · exact B418407
  · exact B418411
  · exact B418415
  · exact B418419
  · exact B418423
  · exact B418427
  · exact B418431
  · exact B418435
  · exact B418439
  · exact B418443
  · exact B418447
  · exact B418451
  · exact B418455
  · exact B418459
  · exact B418463
  · exact B418467
  · exact B418471
  · exact B418475
  · exact B418479
  · exact B418483
  · exact B418487
  · exact B418491
  · exact B418495
  · exact B418499
  · exact B418503
  · exact B418507
  · exact B418511
  · exact B418515
  · exact B418519
  · exact B418523
  · exact B418527
  · exact B418531
  · exact B418535
  · exact B418539
  · exact B418543
  · exact B418547
  · exact B418551
  · exact B418555
  · exact B418559
  · exact B418563
  · exact B418567
  · exact B418571
  · exact B418575
  · exact B418579
  · exact B418583
  · exact B418587
  · exact B418591
  · exact B418595
  · exact B418599
  · exact B418603
  · exact B418607
  · exact B418611
  · exact B418615
  · exact B418619
  · exact B418623
  · exact B418627
  · exact B418631
  · exact B418635
  · exact B418639
  · exact B418643
  · exact B418647
  · exact B418651
  · exact B418655
  · exact B418659
  · exact B418663
  · exact B418667
  · exact B418671
  · exact B418675
  · exact B418679
  · exact B418683
  · exact B418687
  · exact B418691
  · exact B418695
  · exact B418699
  · exact B418703
  · exact B418707
  · exact B418711
  · exact B418715
  · exact B418719
  · exact B418723
  · exact B418727
  · exact B418731
  · exact B418735
  · exact B418739
  · exact B418743
  · exact B418747
  · exact B418751
  · exact B418755
  · exact B418759
  · exact B418763
  · exact B418767
  · exact B418771
  · exact B418775
  · exact B418779
  · exact B418783
  · exact B418787
  · exact B418791
  · exact B418795
  · exact B418799
  · exact B418803
  · exact B418807
  · exact B418811
  · exact B418815
  · exact B418819
  · exact B418823
  · exact B418827
  · exact B418831
  · exact B418835
  · exact B418839
  · exact B418843
  · exact B418847
  · exact B418851
  · exact B418855
  · exact B418859
  · exact B418863
  · exact B418867
  · exact B418871
  · exact B418875
  · exact B418879
  · exact B418883
  · exact B418887
  · exact B418891
  · exact B418895
  · exact B418899
  · exact B418903
  · exact B418907
  · exact B418911
  · exact B418915
  · exact B418919
  · exact B418923
  · exact B418927
  · exact B418931
  · exact B418935
  · exact B418939
  · exact B418943
  · exact B418947
  · exact B418951
  · exact B418955
  · exact B418959
  · exact B418963
  · exact B418967
  · exact B418971
  · exact B418975
  · exact B418979
  · exact B418983
  · exact B418987
  · exact B418991
  · exact B418995
  · exact B418999
  · exact B419003
  · exact B419007
  · exact B419011
  · exact B419015
  · exact B419019
  · exact B419023
  · exact B419027
  · exact B419031
  · exact B419035
  · exact B419039
  · exact B419043
  · exact B419047
  · exact B419051
  · exact B419055
  · exact B419059
  · exact B419063
  · exact B419067
  · exact B419071
  · exact B419075
  · exact B419079
  · exact B419083
  · exact B419087
  · exact B419091
  · exact B419095
  · exact B419099
  · exact B419103
  · exact B419107
  · exact B419111
  · exact B419115
  · exact B419119
  · exact B419123
  · exact B419127
  · exact B419131
  · exact B419135
  · exact B419139
  · exact B419143
  · exact B419147
  · exact B419151
  · exact B419155
  · exact B419159
  · exact B419163
  · exact B419167
  · exact B419171
  · exact B419175
  · exact B419179
  · exact B419183
  · exact B419187
  · exact B419191
  · exact B419195
  · exact B419199
  · exact B419203
  · exact B419207
  · exact B419211
  · exact B419215
  · exact B419219
  · exact B419223
  · exact B419227
  · exact B419231
  · exact B419235
  · exact B419239
  · exact B419243
  · exact B419247
  · exact B419251
  · exact B419255
  · exact B419259
  · exact B419263
  · exact B419267
  · exact B419271
  · exact B419275
  · exact B419279
  · exact B419283
  · exact B419287
  · exact B419291
  · exact B419295
  · exact B419299
  · exact B419303
  · exact B419307
  · exact B419311
  · exact B419315
  · exact B419319
  · exact B419323
  · exact B419327
  · exact B419331
  · exact B419335
  · exact B419339
  · exact B419343
  · exact B419347
  · exact B419351
  · exact B419355
  · exact B419359
  · exact B419363
  · exact B419367
  · exact B419371
  · exact B419375
  · exact B419379
  · exact B419383
  · exact B419387
  · exact B419391
  · exact B419395
  · exact B419399
  · exact B419403
  · exact B419407
  · exact B419411
  · exact B419415
  · exact B419419
  · exact B419423
  · exact B419427
  · exact B419431
  · exact B419435
  · exact B419439
  · exact B419443
  · exact B419447
  · exact B419451
  · exact B419455
  · exact B419459
  · exact B419463
  · exact B419467
  · exact B419471
  · exact B419475
  · exact B419479
  · exact B419483
  · exact B419487
  · exact B419491
  · exact B419495
  · exact B419499
  · exact B419503
  · exact B419507
  · exact B419511
  · exact B419515
  · exact B419519
  · exact B419523
  · exact B419527
  · exact B419531
  · exact B419535
  · exact B419539
  · exact B419543
  · exact B419547
  · exact B419551
  · exact B419555
  · exact B419559
  · exact B419563
  · exact B419567
  · exact B419571
  · exact B419575
  · exact B419579
  · exact B419583
  · exact B419587
  · exact B419591
  · exact B419595
  · exact B419599
  · exact B419603
  · exact B419607
  · exact B419611
  · exact B419615
  · exact B419619
  · exact B419623
  · exact B419627
  · exact B419631
  · exact B419635
  · exact B419639
  · exact B419643
  · exact B419647
  · exact B419651
  · exact B419655
  · exact B419659
  · exact B419663
  · exact B419667
  · exact B419671
  · exact B419675
  · exact B419679
  · exact B419683
  · exact B419687
  · exact B419691
  · exact B419695
  · exact B419699
  · exact B419703
  · exact B419707
  · exact B419711
  · exact B419715
  · exact B419719
  · exact B419723
  · exact B419727
  · exact B419731
  · exact B419735
  · exact B419739
  · exact B419743
  · exact B419747
  · exact B419751
  · exact B419755
  · exact B419759
  · exact B419763
  · exact B419767
  · exact B419771
  · exact B419775
  · exact B419779
  · exact B419783
  · exact B419787
  · exact B419791
  · exact B419795
  · exact B419799
  · exact B419803
  · exact B419807
  · exact B419811
  · exact B419815
  · exact B419819
  · exact B419823
  · exact B419827
  · exact B419831
  · exact B419835
  · exact B419839
  · exact B419843
  · exact B419847
  · exact B419851
  · exact B419855
  · exact B419859
  · exact B419863
  · exact B419867
  · exact B419871
  · exact B419875
  · exact B419879
  · exact B419883
  · exact B419887
  · exact B419891
  · exact B419895
  · exact B419899
  · exact B419903
  · exact B419907
  · exact B419911
  · exact B419915
  · exact B419919
  · exact B419923
  · exact B419927
  · exact B419931
  · exact B419935
  · exact B419939
  · exact B419943
  · exact B419947
  · exact B419951
  · exact B419955
  · exact B419959
  · exact B419963
  · exact B419967
  · exact B419971
  · exact B419975
  · exact B419979
  · exact B419983
  · exact B419987
  · exact B419991
  · exact B419995
  · exact B419999
  · exact B420003
  · exact B420007
  · exact B420011
  · exact B420015
  · exact B420019
  · exact B420023
  · exact B420027
  · exact B420031
  · exact B420035
  · exact B420039
  · exact B420043
  · exact B420047
  · exact B420051
  · exact B420055
  · exact B420059
  · exact B420063
  · exact B420067
  · exact B420071
  · exact B420075
  · exact B420079
  · exact B420083
  · exact B420087
  · exact B420091
  · exact B420095
  · exact B420099
  · exact B420103
  · exact B420107
  · exact B420111
  · exact B420115
  · exact B420119
  · exact B420123
  · exact B420127
  · exact B420131
  · exact B420135
  · exact B420139
  · exact B420143
  · exact B420147
  · exact B420151
  · exact B420155
  · exact B420159
  · exact B420163
  · exact B420167
  · exact B420171
  · exact B420175
  · exact B420179
  · exact B420183
  · exact B420187
  · exact B420191
  · exact B420195
  · exact B420199
  · exact B420203
  · exact B420207
  · exact B420211
  · exact B420215
  · exact B420219
  · exact B420223
  · exact B420227
  · exact B420231
  · exact B420235
  · exact B420239
  · exact B420243
  · exact B420247
  · exact B420251
  · exact B420255
  · exact B420259
  · exact B420263
  · exact B420267
  · exact B420271
  · exact B420275
  · exact B420279
  · exact B420283
  · exact B420287
  · exact B420291
  · exact B420295
  · exact B420299
  · exact B420303
  · exact B420307
  · exact B420311
  · exact B420315
  · exact B420319
  · exact B420323
  · exact B420327
  · exact B420331
  · exact B420335
  · exact B420339
  · exact B420343
  · exact B420347
  · exact B420351
  · exact B420355
  · exact B420359
  · exact B420363
  · exact B420367
  · exact B420371
  · exact B420375
  · exact B420379
  · exact B420383
  · exact B420387
  · exact B420391
  · exact B420395
  · exact B420399
  · exact B420403
  · exact B420407
  · exact B420411
  · exact B420415
  · exact B420419
  · exact B420423
  · exact B420427
  · exact B420431
  · exact B420435
  · exact B420439
  · exact B420443
  · exact B420447
  · exact B420451
  · exact B420455
  · exact B420459
  · exact B420463
  · exact B420467
  · exact B420471
  · exact B420475
  · exact B420479
  · exact B420483
  · exact B420487
  · exact B420491
  · exact B420495
  · exact B420499
  · exact B420503
  · exact B420507
  · exact B420511
  · exact B420515
  · exact B420519
  · exact B420523
  · exact B420527
  · exact B420531
  · exact B420535
  · exact B420539
  · exact B420543
  · exact B420547
  · exact B420551
  · exact B420555
  · exact B420559
  · exact B420563
  · exact B420567
  · exact B420571

theorem C1 (j : ℕ) (h1 : 105143 ≤ j) (h2 : j ≤ 105442) : Blo 417772 (4 * j + 3) := by
  interval_cases j
  · exact B420575
  · exact B420579
  · exact B420583
  · exact B420587
  · exact B420591
  · exact B420595
  · exact B420599
  · exact B420603
  · exact B420607
  · exact B420611
  · exact B420615
  · exact B420619
  · exact B420623
  · exact B420627
  · exact B420631
  · exact B420635
  · exact B420639
  · exact B420643
  · exact B420647
  · exact B420651
  · exact B420655
  · exact B420659
  · exact B420663
  · exact B420667
  · exact B420671
  · exact B420675
  · exact B420679
  · exact B420683
  · exact B420687
  · exact B420691
  · exact B420695
  · exact B420699
  · exact B420703
  · exact B420707
  · exact B420711
  · exact B420715
  · exact B420719
  · exact B420723
  · exact B420727
  · exact B420731
  · exact B420735
  · exact B420739
  · exact B420743
  · exact B420747
  · exact B420751
  · exact B420755
  · exact B420759
  · exact B420763
  · exact B420767
  · exact B420771
  · exact B420775
  · exact B420779
  · exact B420783
  · exact B420787
  · exact B420791
  · exact B420795
  · exact B420799
  · exact B420803
  · exact B420807
  · exact B420811
  · exact B420815
  · exact B420819
  · exact B420823
  · exact B420827
  · exact B420831
  · exact B420835
  · exact B420839
  · exact B420843
  · exact B420847
  · exact B420851
  · exact B420855
  · exact B420859
  · exact B420863
  · exact B420867
  · exact B420871
  · exact B420875
  · exact B420879
  · exact B420883
  · exact B420887
  · exact B420891
  · exact B420895
  · exact B420899
  · exact B420903
  · exact B420907
  · exact B420911
  · exact B420915
  · exact B420919
  · exact B420923
  · exact B420927
  · exact B420931
  · exact B420935
  · exact B420939
  · exact B420943
  · exact B420947
  · exact B420951
  · exact B420955
  · exact B420959
  · exact B420963
  · exact B420967
  · exact B420971
  · exact B420975
  · exact B420979
  · exact B420983
  · exact B420987
  · exact B420991
  · exact B420995
  · exact B420999
  · exact B421003
  · exact B421007
  · exact B421011
  · exact B421015
  · exact B421019
  · exact B421023
  · exact B421027
  · exact B421031
  · exact B421035
  · exact B421039
  · exact B421043
  · exact B421047
  · exact B421051
  · exact B421055
  · exact B421059
  · exact B421063
  · exact B421067
  · exact B421071
  · exact B421075
  · exact B421079
  · exact B421083
  · exact B421087
  · exact B421091
  · exact B421095
  · exact B421099
  · exact B421103
  · exact B421107
  · exact B421111
  · exact B421115
  · exact B421119
  · exact B421123
  · exact B421127
  · exact B421131
  · exact B421135
  · exact B421139
  · exact B421143
  · exact B421147
  · exact B421151
  · exact B421155
  · exact B421159
  · exact B421163
  · exact B421167
  · exact B421171
  · exact B421175
  · exact B421179
  · exact B421183
  · exact B421187
  · exact B421191
  · exact B421195
  · exact B421199
  · exact B421203
  · exact B421207
  · exact B421211
  · exact B421215
  · exact B421219
  · exact B421223
  · exact B421227
  · exact B421231
  · exact B421235
  · exact B421239
  · exact B421243
  · exact B421247
  · exact B421251
  · exact B421255
  · exact B421259
  · exact B421263
  · exact B421267
  · exact B421271
  · exact B421275
  · exact B421279
  · exact B421283
  · exact B421287
  · exact B421291
  · exact B421295
  · exact B421299
  · exact B421303
  · exact B421307
  · exact B421311
  · exact B421315
  · exact B421319
  · exact B421323
  · exact B421327
  · exact B421331
  · exact B421335
  · exact B421339
  · exact B421343
  · exact B421347
  · exact B421351
  · exact B421355
  · exact B421359
  · exact B421363
  · exact B421367
  · exact B421371
  · exact B421375
  · exact B421379
  · exact B421383
  · exact B421387
  · exact B421391
  · exact B421395
  · exact B421399
  · exact B421403
  · exact B421407
  · exact B421411
  · exact B421415
  · exact B421419
  · exact B421423
  · exact B421427
  · exact B421431
  · exact B421435
  · exact B421439
  · exact B421443
  · exact B421447
  · exact B421451
  · exact B421455
  · exact B421459
  · exact B421463
  · exact B421467
  · exact B421471
  · exact B421475
  · exact B421479
  · exact B421483
  · exact B421487
  · exact B421491
  · exact B421495
  · exact B421499
  · exact B421503
  · exact B421507
  · exact B421511
  · exact B421515
  · exact B421519
  · exact B421523
  · exact B421527
  · exact B421531
  · exact B421535
  · exact B421539
  · exact B421543
  · exact B421547
  · exact B421551
  · exact B421555
  · exact B421559
  · exact B421563
  · exact B421567
  · exact B421571
  · exact B421575
  · exact B421579
  · exact B421583
  · exact B421587
  · exact B421591
  · exact B421595
  · exact B421599
  · exact B421603
  · exact B421607
  · exact B421611
  · exact B421615
  · exact B421619
  · exact B421623
  · exact B421627
  · exact B421631
  · exact B421635
  · exact B421639
  · exact B421643
  · exact B421647
  · exact B421651
  · exact B421655
  · exact B421659
  · exact B421663
  · exact B421667
  · exact B421671
  · exact B421675
  · exact B421679
  · exact B421683
  · exact B421687
  · exact B421691
  · exact B421695
  · exact B421699
  · exact B421703
  · exact B421707
  · exact B421711
  · exact B421715
  · exact B421719
  · exact B421723
  · exact B421727
  · exact B421731
  · exact B421735
  · exact B421739
  · exact B421743
  · exact B421747
  · exact B421751
  · exact B421755
  · exact B421759
  · exact B421763
  · exact B421767
  · exact B421771

theorem solution (m : ℕ) (hlo : 417772 ≤ m) (hhi : m ≤ 421772) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 104443 ≤ j := by omega
    have hj2 : j ≤ 105442 := by omega
    have hb : Blo 417772 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 105143 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
