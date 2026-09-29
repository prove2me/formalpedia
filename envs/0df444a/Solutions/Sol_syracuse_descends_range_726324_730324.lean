-- Prove2me | solution 1 for syracuse_descends_range_726324_730324
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:09.608835+00:00
-- url     : https://prove2.me/submissions/3d3ecd80-1e1b-4475-8e1a-ba3f557dc39c

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


theorem B1638413 : Blo 726324 1638413 := bbase (se 3 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 1638413 = 614405) (by norm_num)
theorem B819229 : Blo 726324 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B819265 : Blo 726324 819265 := bbase (se 2 (by rfl) ⟨307224, by rfl⟩ : syracuseStep 819265 = 614449) (by norm_num)
theorem B1638485 : Blo 726324 1638485 := bbase (se 8 (by rfl) ⟨9600, by rfl⟩ : syracuseStep 1638485 = 19201) (by norm_num)
theorem B2457701 : Blo 726324 2457701 := bbase (se 4 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 2457701 = 460819) (by norm_num)
theorem B819301 : Blo 726324 819301 := bbase (se 4 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 819301 = 153619) (by norm_num)
theorem B3113093 : Blo 726324 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B819337 : Blo 726324 819337 := bbase (se 2 (by rfl) ⟨307251, by rfl⟩ : syracuseStep 819337 = 614503) (by norm_num)
theorem B1638557 : Blo 726324 1638557 := bbase (se 3 (by rfl) ⟨307229, by rfl⟩ : syracuseStep 1638557 = 614459) (by norm_num)
theorem B819373 : Blo 726324 819373 := bbase (se 3 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 819373 = 307265) (by norm_num)
theorem B819409 : Blo 726324 819409 := bbase (se 2 (by rfl) ⟨307278, by rfl⟩ : syracuseStep 819409 = 614557) (by norm_num)
theorem B1638629 : Blo 726324 1638629 := bbase (se 4 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 1638629 = 307243) (by norm_num)
theorem B819445 : Blo 726324 819445 := bbase (se 5 (by rfl) ⟨38411, by rfl⟩ : syracuseStep 819445 = 76823) (by norm_num)
theorem B819481 : Blo 726324 819481 := bbase (se 2 (by rfl) ⟨307305, by rfl⟩ : syracuseStep 819481 = 614611) (by norm_num)
theorem B1638701 : Blo 726324 1638701 := bbase (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) (by norm_num)
theorem B819517 : Blo 726324 819517 := bbase (se 3 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 819517 = 307319) (by norm_num)
theorem B819553 : Blo 726324 819553 := bbase (se 2 (by rfl) ⟨307332, by rfl⟩ : syracuseStep 819553 = 614665) (by norm_num)
theorem B1638773 : Blo 726324 1638773 := bbase (se 5 (by rfl) ⟨76817, by rfl⟩ : syracuseStep 1638773 = 153635) (by norm_num)
theorem B819589 : Blo 726324 819589 := bbase (se 4 (by rfl) ⟨76836, by rfl⟩ : syracuseStep 819589 = 153673) (by norm_num)
theorem B819625 : Blo 726324 819625 := bbase (se 2 (by rfl) ⟨307359, by rfl⟩ : syracuseStep 819625 = 614719) (by norm_num)
theorem B1638845 : Blo 726324 1638845 := bbase (se 3 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 1638845 = 614567) (by norm_num)
theorem B819661 : Blo 726324 819661 := bbase (se 3 (by rfl) ⟨153686, by rfl⟩ : syracuseStep 819661 = 307373) (by norm_num)
theorem B819697 : Blo 726324 819697 := bbase (se 2 (by rfl) ⟨307386, by rfl⟩ : syracuseStep 819697 = 614773) (by norm_num)
theorem B1638917 : Blo 726324 1638917 := bbase (se 4 (by rfl) ⟨153648, by rfl⟩ : syracuseStep 1638917 = 307297) (by norm_num)
theorem B2458133 : Blo 726324 2458133 := bbase (se 6 (by rfl) ⟨57612, by rfl⟩ : syracuseStep 2458133 = 115225) (by norm_num)
theorem B819733 : Blo 726324 819733 := bbase (se 6 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 819733 = 38425) (by norm_num)
theorem B819769 : Blo 726324 819769 := bbase (se 2 (by rfl) ⟨307413, by rfl⟩ : syracuseStep 819769 = 614827) (by norm_num)
theorem B983629 : Blo 726324 983629 := bbase (se 3 (by rfl) ⟨184430, by rfl⟩ : syracuseStep 983629 = 368861) (by norm_num)
theorem B1638989 : Blo 726324 1638989 := bbase (se 3 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 1638989 = 614621) (by norm_num)
theorem B1770077 : Blo 726324 1770077 := bbase (se 3 (by rfl) ⟨331889, by rfl⟩ : syracuseStep 1770077 = 663779) (by norm_num)
theorem B819805 : Blo 726324 819805 := bbase (se 3 (by rfl) ⟨153713, by rfl⟩ : syracuseStep 819805 = 307427) (by norm_num)
theorem B819841 : Blo 726324 819841 := bbase (se 2 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 819841 = 614881) (by norm_num)
theorem B1639061 : Blo 726324 1639061 := bbase (se 6 (by rfl) ⟨38415, by rfl⟩ : syracuseStep 1639061 = 76831) (by norm_num)
theorem B819877 : Blo 726324 819877 := bbase (se 4 (by rfl) ⟨76863, by rfl⟩ : syracuseStep 819877 = 153727) (by norm_num)
theorem B819913 : Blo 726324 819913 := bbase (se 2 (by rfl) ⟨307467, by rfl⟩ : syracuseStep 819913 = 614935) (by norm_num)
theorem B1639133 : Blo 726324 1639133 := bbase (se 3 (by rfl) ⟨307337, by rfl⟩ : syracuseStep 1639133 = 614675) (by norm_num)
theorem B819949 : Blo 726324 819949 := bbase (se 3 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 819949 = 307481) (by norm_num)
theorem B2425589 : Blo 726324 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B819985 : Blo 726324 819985 := bbase (se 2 (by rfl) ⟨307494, by rfl⟩ : syracuseStep 819985 = 614989) (by norm_num)
theorem B1639205 : Blo 726324 1639205 := bbase (se 4 (by rfl) ⟨153675, by rfl⟩ : syracuseStep 1639205 = 307351) (by norm_num)
theorem B820021 : Blo 726324 820021 := bbase (se 5 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 820021 = 76877) (by norm_num)
theorem B820057 : Blo 726324 820057 := bbase (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) (by norm_num)
theorem B1639277 : Blo 726324 1639277 := bbase (se 3 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 1639277 = 614729) (by norm_num)
theorem B2327413 : Blo 726324 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B820093 : Blo 726324 820093 := bbase (se 3 (by rfl) ⟨153767, by rfl⟩ : syracuseStep 820093 = 307535) (by norm_num)
theorem B820129 : Blo 726324 820129 := bbase (se 2 (by rfl) ⟨307548, by rfl⟩ : syracuseStep 820129 = 615097) (by norm_num)
theorem B1639349 : Blo 726324 1639349 := bbase (se 5 (by rfl) ⟨76844, by rfl⟩ : syracuseStep 1639349 = 153689) (by norm_num)
theorem B2458565 : Blo 726324 2458565 := bbase (se 4 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 2458565 = 460981) (by norm_num)
theorem B820165 : Blo 726324 820165 := bbase (se 4 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 820165 = 153781) (by norm_num)
theorem B820201 : Blo 726324 820201 := bbase (se 2 (by rfl) ⟨307575, by rfl⟩ : syracuseStep 820201 = 615151) (by norm_num)
theorem B1639421 : Blo 726324 1639421 := bbase (se 3 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 1639421 = 614783) (by norm_num)
theorem B820237 : Blo 726324 820237 := bbase (se 3 (by rfl) ⟨153794, by rfl⟩ : syracuseStep 820237 = 307589) (by norm_num)
theorem B820273 : Blo 726324 820273 := bbase (se 2 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 820273 = 615205) (by norm_num)
theorem B1180741 : Blo 726324 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B1639493 : Blo 726324 1639493 := bbase (se 4 (by rfl) ⟨153702, by rfl⟩ : syracuseStep 1639493 = 307405) (by norm_num)
theorem B820309 : Blo 726324 820309 := bbase (se 8 (by rfl) ⟨4806, by rfl⟩ : syracuseStep 820309 = 9613) (by norm_num)
theorem B820345 : Blo 726324 820345 := bbase (se 2 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 820345 = 615259) (by norm_num)
theorem B1639565 : Blo 726324 1639565 := bbase (se 3 (by rfl) ⟨307418, by rfl⟩ : syracuseStep 1639565 = 614837) (by norm_num)
theorem B820381 : Blo 726324 820381 := bbase (se 3 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 820381 = 307643) (by norm_num)
theorem B820417 : Blo 726324 820417 := bbase (se 2 (by rfl) ⟨307656, by rfl⟩ : syracuseStep 820417 = 615313) (by norm_num)
theorem B1639637 : Blo 726324 1639637 := bbase (se 7 (by rfl) ⟨19214, by rfl⟩ : syracuseStep 1639637 = 38429) (by norm_num)
theorem B820453 : Blo 726324 820453 := bbase (se 4 (by rfl) ⟨76917, by rfl⟩ : syracuseStep 820453 = 153835) (by norm_num)
theorem B2622709 : Blo 726324 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B820489 : Blo 726324 820489 := bbase (se 2 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 820489 = 615367) (by norm_num)
theorem B1639709 : Blo 726324 1639709 := bbase (se 3 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 1639709 = 614891) (by norm_num)
theorem B820525 : Blo 726324 820525 := bbase (se 3 (by rfl) ⟨153848, by rfl⟩ : syracuseStep 820525 = 307697) (by norm_num)
theorem B3540293 : Blo 726324 3540293 := bbase (se 4 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 3540293 = 663805) (by norm_num)
theorem B820561 : Blo 726324 820561 := bbase (se 2 (by rfl) ⟨307710, by rfl⟩ : syracuseStep 820561 = 615421) (by norm_num)
theorem B1639781 : Blo 726324 1639781 := bbase (se 4 (by rfl) ⟨153729, by rfl⟩ : syracuseStep 1639781 = 307459) (by norm_num)
theorem B2458997 : Blo 726324 2458997 := bbase (se 5 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 2458997 = 230531) (by norm_num)
theorem B820597 : Blo 726324 820597 := bbase (se 5 (by rfl) ⟨38465, by rfl⟩ : syracuseStep 820597 = 76931) (by norm_num)
theorem B820633 : Blo 726324 820633 := bbase (se 2 (by rfl) ⟨307737, by rfl⟩ : syracuseStep 820633 = 615475) (by norm_num)
theorem B1639853 : Blo 726324 1639853 := bbase (se 3 (by rfl) ⟨307472, by rfl⟩ : syracuseStep 1639853 = 614945) (by norm_num)
theorem B820669 : Blo 726324 820669 := bbase (se 3 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 820669 = 307751) (by norm_num)
theorem B2950597 : Blo 726324 2950597 := bbase (se 4 (by rfl) ⟨276618, by rfl⟩ : syracuseStep 2950597 = 553237) (by norm_num)
theorem B1476053 : Blo 726324 1476053 := bbase (se 7 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 1476053 = 34595) (by norm_num)
theorem B820705 : Blo 726324 820705 := bbase (se 2 (by rfl) ⟨307764, by rfl⟩ : syracuseStep 820705 = 615529) (by norm_num)
theorem B1639925 : Blo 726324 1639925 := bbase (se 5 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 1639925 = 153743) (by norm_num)
theorem B820741 : Blo 726324 820741 := bbase (se 4 (by rfl) ⟨76944, by rfl⟩ : syracuseStep 820741 = 153889) (by norm_num)
theorem B820777 : Blo 726324 820777 := bbase (se 2 (by rfl) ⟨307791, by rfl⟩ : syracuseStep 820777 = 615583) (by norm_num)
theorem B1639997 : Blo 726324 1639997 := bbase (se 3 (by rfl) ⟨307499, by rfl⟩ : syracuseStep 1639997 = 614999) (by norm_num)
theorem B820813 : Blo 726324 820813 := bbase (se 3 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 820813 = 307805) (by norm_num)
theorem B820849 : Blo 726324 820849 := bbase (se 2 (by rfl) ⟨307818, by rfl⟩ : syracuseStep 820849 = 615637) (by norm_num)
theorem B1640069 : Blo 726324 1640069 := bbase (se 4 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 1640069 = 307513) (by norm_num)
theorem B820885 : Blo 726324 820885 := bbase (se 6 (by rfl) ⟨19239, by rfl⟩ : syracuseStep 820885 = 38479) (by norm_num)
theorem B2000533 : Blo 726324 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B820921 : Blo 726324 820921 := bbase (se 2 (by rfl) ⟨307845, by rfl⟩ : syracuseStep 820921 = 615691) (by norm_num)
theorem B1640141 : Blo 726324 1640141 := bbase (se 3 (by rfl) ⟨307526, by rfl⟩ : syracuseStep 1640141 = 615053) (by norm_num)
theorem B820957 : Blo 726324 820957 := bbase (se 3 (by rfl) ⟨153929, by rfl⟩ : syracuseStep 820957 = 307859) (by norm_num)
theorem B919289 : Blo 726324 919289 := bbase (se 2 (by rfl) ⟨344733, by rfl⟩ : syracuseStep 919289 = 689467) (by norm_num)
theorem B820993 : Blo 726324 820993 := bbase (se 2 (by rfl) ⟨307872, by rfl⟩ : syracuseStep 820993 = 615745) (by norm_num)
theorem B1640213 : Blo 726324 1640213 := bbase (se 6 (by rfl) ⟨38442, by rfl⟩ : syracuseStep 1640213 = 76885) (by norm_num)
theorem B2459429 : Blo 726324 2459429 := bbase (se 4 (by rfl) ⟨230571, by rfl⟩ : syracuseStep 2459429 = 461143) (by norm_num)
theorem B821029 : Blo 726324 821029 := bbase (se 4 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 821029 = 153943) (by norm_num)
theorem B919345 : Blo 726324 919345 := bbase (se 2 (by rfl) ⟨344754, by rfl⟩ : syracuseStep 919345 = 689509) (by norm_num)
theorem B821065 : Blo 726324 821065 := bbase (se 2 (by rfl) ⟨307899, by rfl⟩ : syracuseStep 821065 = 615799) (by norm_num)
theorem B1640285 : Blo 726324 1640285 := bbase (se 3 (by rfl) ⟨307553, by rfl⟩ : syracuseStep 1640285 = 615107) (by norm_num)
theorem B821101 : Blo 726324 821101 := bbase (se 3 (by rfl) ⟨153956, by rfl⟩ : syracuseStep 821101 = 307913) (by norm_num)
theorem B919441 : Blo 726324 919441 := bbase (se 2 (by rfl) ⟨344790, by rfl⟩ : syracuseStep 919441 = 689581) (by norm_num)
theorem B821137 : Blo 726324 821137 := bbase (se 2 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 821137 = 615853) (by norm_num)
theorem B1640357 : Blo 726324 1640357 := bbase (se 4 (by rfl) ⟨153783, by rfl⟩ : syracuseStep 1640357 = 307567) (by norm_num)
theorem B821173 : Blo 726324 821173 := bbase (se 5 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 821173 = 76985) (by norm_num)
theorem B821209 : Blo 726324 821209 := bbase (se 2 (by rfl) ⟨307953, by rfl⟩ : syracuseStep 821209 = 615907) (by norm_num)
theorem B1640429 : Blo 726324 1640429 := bbase (se 3 (by rfl) ⟨307580, by rfl⟩ : syracuseStep 1640429 = 615161) (by norm_num)
theorem B821245 : Blo 726324 821245 := bbase (se 3 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 821245 = 307967) (by norm_num)
theorem B821281 : Blo 726324 821281 := bbase (se 2 (by rfl) ⟨307980, by rfl⟩ : syracuseStep 821281 = 615961) (by norm_num)
theorem B1640501 : Blo 726324 1640501 := bbase (se 5 (by rfl) ⟨76898, by rfl⟩ : syracuseStep 1640501 = 153797) (by norm_num)
theorem B919613 : Blo 726324 919613 := bbase (se 3 (by rfl) ⟨172427, by rfl⟩ : syracuseStep 919613 = 344855) (by norm_num)
theorem B821317 : Blo 726324 821317 := bbase (se 4 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 821317 = 153997) (by norm_num)
theorem B1312861 : Blo 726324 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B821353 : Blo 726324 821353 := bbase (se 2 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 821353 = 616015) (by norm_num)
theorem B919669 : Blo 726324 919669 := bbase (se 5 (by rfl) ⟨43109, by rfl⟩ : syracuseStep 919669 = 86219) (by norm_num)
theorem B1476725 : Blo 726324 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B1640573 : Blo 726324 1640573 := bbase (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) (by norm_num)
theorem B821389 : Blo 726324 821389 := bbase (se 3 (by rfl) ⟨154010, by rfl⟩ : syracuseStep 821389 = 308021) (by norm_num)
theorem B821425 : Blo 726324 821425 := bbase (se 2 (by rfl) ⟨308034, by rfl⟩ : syracuseStep 821425 = 616069) (by norm_num)
theorem B1640645 : Blo 726324 1640645 := bbase (se 4 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 1640645 = 307621) (by norm_num)
theorem B919765 : Blo 726324 919765 := bbase (se 7 (by rfl) ⟨10778, by rfl⟩ : syracuseStep 919765 = 21557) (by norm_num)
theorem B2459861 : Blo 726324 2459861 := bbase (se 7 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 2459861 = 57653) (by norm_num)
theorem B821461 : Blo 726324 821461 := bbase (se 7 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 821461 = 19253) (by norm_num)
theorem B1313005 : Blo 726324 1313005 := bbase (se 3 (by rfl) ⟨246188, by rfl⟩ : syracuseStep 1313005 = 492377) (by norm_num)
theorem B821497 : Blo 726324 821497 := bbase (se 2 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 821497 = 616123) (by norm_num)
theorem B1640717 : Blo 726324 1640717 := bbase (se 3 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 1640717 = 615269) (by norm_num)
theorem B821533 : Blo 726324 821533 := bbase (se 3 (by rfl) ⟨154037, by rfl⟩ : syracuseStep 821533 = 308075) (by norm_num)
theorem B887105 : Blo 726324 887105 := bbase (se 2 (by rfl) ⟨332664, by rfl⟩ : syracuseStep 887105 = 665329) (by norm_num)
theorem B821569 : Blo 726324 821569 := bbase (se 2 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 821569 = 616177) (by norm_num)
theorem B4983125 : Blo 726324 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B1640789 : Blo 726324 1640789 := bbase (se 10 (by rfl) ⟨2403, by rfl⟩ : syracuseStep 1640789 = 4807) (by norm_num)
theorem B821605 : Blo 726324 821605 := bbase (se 4 (by rfl) ⟨77025, by rfl⟩ : syracuseStep 821605 = 154051) (by norm_num)
theorem B919937 : Blo 726324 919937 := bbase (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) (by norm_num)
theorem B2623877 : Blo 726324 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B1051013 : Blo 726324 1051013 := bbase (se 4 (by rfl) ⟨98532, by rfl⟩ : syracuseStep 1051013 = 197065) (by norm_num)
theorem B1640861 : Blo 726324 1640861 := bbase (se 3 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 1640861 = 615323) (by norm_num)
theorem B1771949 : Blo 726324 1771949 := bbase (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) (by norm_num)
theorem B919993 : Blo 726324 919993 := bbase (se 2 (by rfl) ⟨344997, by rfl⟩ : syracuseStep 919993 = 689995) (by norm_num)
theorem B1640933 : Blo 726324 1640933 := bbase (se 4 (by rfl) ⟨153837, by rfl⟩ : syracuseStep 1640933 = 307675) (by norm_num)
theorem B920089 : Blo 726324 920089 := bbase (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) (by norm_num)
theorem B1968677 : Blo 726324 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B1641005 : Blo 726324 1641005 := bbase (se 3 (by rfl) ⟨307688, by rfl⟩ : syracuseStep 1641005 = 615377) (by norm_num)
theorem B1641077 : Blo 726324 1641077 := bbase (se 5 (by rfl) ⟨76925, by rfl⟩ : syracuseStep 1641077 = 153851) (by norm_num)
theorem B2460293 : Blo 726324 2460293 := bbase (se 4 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 2460293 = 461305) (by norm_num)
theorem B1378957 : Blo 726324 1378957 := bbase (se 3 (by rfl) ⟨258554, by rfl⟩ : syracuseStep 1378957 = 517109) (by norm_num)
theorem B985765 : Blo 726324 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B1641149 : Blo 726324 1641149 := bbase (se 3 (by rfl) ⟨307715, by rfl⟩ : syracuseStep 1641149 = 615431) (by norm_num)
theorem B920261 : Blo 726324 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B985813 : Blo 726324 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B920317 : Blo 726324 920317 := bbase (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) (by norm_num)
theorem B1641221 : Blo 726324 1641221 := bbase (se 4 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 1641221 = 307729) (by norm_num)
theorem B1379101 : Blo 726324 1379101 := bbase (se 3 (by rfl) ⟨258581, by rfl⟩ : syracuseStep 1379101 = 517163) (by norm_num)
theorem B1641293 : Blo 726324 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B920413 : Blo 726324 920413 := bbase (se 3 (by rfl) ⟨172577, by rfl⟩ : syracuseStep 920413 = 345155) (by norm_num)
theorem B2493317 : Blo 726324 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B1641365 : Blo 726324 1641365 := bbase (se 6 (by rfl) ⟨38469, by rfl⟩ : syracuseStep 1641365 = 76939) (by norm_num)
theorem B1870757 : Blo 726324 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B1379261 : Blo 726324 1379261 := bbase (se 3 (by rfl) ⟨258611, by rfl⟩ : syracuseStep 1379261 = 517223) (by norm_num)
theorem B1641437 : Blo 726324 1641437 := bbase (se 3 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 1641437 = 615539) (by norm_num)
theorem B920585 : Blo 726324 920585 := bbase (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) (by norm_num)
theorem B1313813 : Blo 726324 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B5540885 : Blo 726324 5540885 := bbase (se 6 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 5540885 = 259729) (by norm_num)
theorem B1641509 : Blo 726324 1641509 := bbase (se 4 (by rfl) ⟨153891, by rfl⟩ : syracuseStep 1641509 = 307783) (by norm_num)
theorem B2460725 : Blo 726324 2460725 := bbase (se 5 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 2460725 = 230693) (by norm_num)
theorem B920641 : Blo 726324 920641 := bbase (se 2 (by rfl) ⟨345240, by rfl⟩ : syracuseStep 920641 = 690481) (by norm_num)
theorem B1379405 : Blo 726324 1379405 := bbase (se 3 (by rfl) ⟨258638, by rfl⟩ : syracuseStep 1379405 = 517277) (by norm_num)
theorem B1641581 : Blo 726324 1641581 := bbase (se 3 (by rfl) ⟨307796, by rfl⟩ : syracuseStep 1641581 = 615593) (by norm_num)
theorem B920737 : Blo 726324 920737 := bbase (se 2 (by rfl) ⟨345276, by rfl⟩ : syracuseStep 920737 = 690553) (by norm_num)
theorem B1313957 : Blo 726324 1313957 := bbase (se 4 (by rfl) ⟨123183, by rfl⟩ : syracuseStep 1313957 = 246367) (by norm_num)
theorem B1641653 : Blo 726324 1641653 := bbase (se 5 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 1641653 = 153905) (by norm_num)
theorem B1314029 : Blo 726324 1314029 := bbase (se 3 (by rfl) ⟨246380, by rfl⟩ : syracuseStep 1314029 = 492761) (by norm_num)
theorem B1641725 : Blo 726324 1641725 := bbase (se 3 (by rfl) ⟨307823, by rfl⟩ : syracuseStep 1641725 = 615647) (by norm_num)
theorem B1641797 : Blo 726324 1641797 := bbase (se 4 (by rfl) ⟨153918, by rfl⟩ : syracuseStep 1641797 = 307837) (by norm_num)
theorem B920909 : Blo 726324 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B1379693 : Blo 726324 1379693 := bbase (se 3 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 1379693 = 517385) (by norm_num)
theorem B920965 : Blo 726324 920965 := bbase (se 4 (by rfl) ⟨86340, by rfl⟩ : syracuseStep 920965 = 172681) (by norm_num)
theorem B1641869 : Blo 726324 1641869 := bbase (se 3 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 1641869 = 615701) (by norm_num)
theorem B1314245 : Blo 726324 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1641941 : Blo 726324 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B921061 : Blo 726324 921061 := bbase (se 4 (by rfl) ⟨86349, by rfl⟩ : syracuseStep 921061 = 172699) (by norm_num)
theorem B2461157 : Blo 726324 2461157 := bbase (se 4 (by rfl) ⟨230733, by rfl⟩ : syracuseStep 2461157 = 461467) (by norm_num)
theorem B1379845 : Blo 726324 1379845 := bbase (se 4 (by rfl) ⟨129360, by rfl⟩ : syracuseStep 1379845 = 258721) (by norm_num)
theorem B1642013 : Blo 726324 1642013 := bbase (se 3 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 1642013 = 615755) (by norm_num)
theorem B2428453 : Blo 726324 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1642085 : Blo 726324 1642085 := bbase (se 4 (by rfl) ⟨153945, by rfl⟩ : syracuseStep 1642085 = 307891) (by norm_num)
theorem B921233 : Blo 726324 921233 := bbase (se 2 (by rfl) ⟨345462, by rfl⟩ : syracuseStep 921233 = 690925) (by norm_num)
theorem B1642157 : Blo 726324 1642157 := bbase (se 3 (by rfl) ⟨307904, by rfl⟩ : syracuseStep 1642157 = 615809) (by norm_num)
theorem B2330309 : Blo 726324 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B921289 : Blo 726324 921289 := bbase (se 2 (by rfl) ⟨345483, by rfl⟩ : syracuseStep 921289 = 690967) (by norm_num)
theorem B1838821 : Blo 726324 1838821 := bbase (se 4 (by rfl) ⟨172389, by rfl⟩ : syracuseStep 1838821 = 344779) (by norm_num)
theorem B1642229 : Blo 726324 1642229 := bbase (se 5 (by rfl) ⟨76979, by rfl⟩ : syracuseStep 1642229 = 153959) (by norm_num)
theorem B921385 : Blo 726324 921385 := bbase (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) (by norm_num)
theorem B1380149 : Blo 726324 1380149 := bbase (se 5 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 1380149 = 129389) (by norm_num)
theorem B1642301 : Blo 726324 1642301 := bbase (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) (by norm_num)
theorem B1838933 : Blo 726324 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B1642373 : Blo 726324 1642373 := bbase (se 4 (by rfl) ⟨153972, by rfl⟩ : syracuseStep 1642373 = 307945) (by norm_num)
theorem B2461589 : Blo 726324 2461589 := bbase (se 6 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 2461589 = 115387) (by norm_num)
theorem B1642445 : Blo 726324 1642445 := bbase (se 3 (by rfl) ⟨307958, by rfl⟩ : syracuseStep 1642445 = 615917) (by norm_num)
theorem B921557 : Blo 726324 921557 := bbase (se 7 (by rfl) ⟨10799, by rfl⟩ : syracuseStep 921557 = 21599) (by norm_num)
theorem B921613 : Blo 726324 921613 := bbase (se 3 (by rfl) ⟨172802, by rfl⟩ : syracuseStep 921613 = 345605) (by norm_num)
theorem B1839125 : Blo 726324 1839125 := bbase (se 6 (by rfl) ⟨43104, by rfl⟩ : syracuseStep 1839125 = 86209) (by norm_num)
theorem B1642517 : Blo 726324 1642517 := bbase (se 6 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 1642517 = 76993) (by norm_num)
theorem B1642589 : Blo 726324 1642589 := bbase (se 3 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 1642589 = 615971) (by norm_num)
theorem B921709 : Blo 726324 921709 := bbase (se 3 (by rfl) ⟨172820, by rfl⟩ : syracuseStep 921709 = 345641) (by norm_num)
theorem B4198517 : Blo 726324 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B1642661 : Blo 726324 1642661 := bbase (se 4 (by rfl) ⟨153999, by rfl⟩ : syracuseStep 1642661 = 307999) (by norm_num)
theorem B1315045 : Blo 726324 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B1642733 : Blo 726324 1642733 := bbase (se 3 (by rfl) ⟨308012, by rfl⟩ : syracuseStep 1642733 = 616025) (by norm_num)
theorem B921881 : Blo 726324 921881 := bbase (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) (by norm_num)
theorem B1184053 : Blo 726324 1184053 := bbase (se 5 (by rfl) ⟨55502, by rfl⟩ : syracuseStep 1184053 = 111005) (by norm_num)
theorem B3117365 : Blo 726324 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B1642805 : Blo 726324 1642805 := bbase (se 5 (by rfl) ⟨77006, by rfl⟩ : syracuseStep 1642805 = 154013) (by norm_num)
theorem B2462021 : Blo 726324 2462021 := bbase (se 4 (by rfl) ⟨230814, by rfl⟩ : syracuseStep 2462021 = 461629) (by norm_num)
theorem B921937 : Blo 726324 921937 := bbase (se 2 (by rfl) ⟨345726, by rfl⟩ : syracuseStep 921937 = 691453) (by norm_num)
theorem B1839469 : Blo 726324 1839469 := bbase (se 3 (by rfl) ⟨344900, by rfl⟩ : syracuseStep 1839469 = 689801) (by norm_num)
theorem B1642877 : Blo 726324 1642877 := bbase (se 3 (by rfl) ⟨308039, by rfl⟩ : syracuseStep 1642877 = 616079) (by norm_num)
theorem B1479077 : Blo 726324 1479077 := bbase (se 4 (by rfl) ⟨138663, by rfl⟩ : syracuseStep 1479077 = 277327) (by norm_num)
theorem B922033 : Blo 726324 922033 := bbase (se 2 (by rfl) ⟨345762, by rfl⟩ : syracuseStep 922033 = 691525) (by norm_num)
theorem B1642949 : Blo 726324 1642949 := bbase (se 4 (by rfl) ⟨154026, by rfl⟩ : syracuseStep 1642949 = 308053) (by norm_num)
theorem B1839581 : Blo 726324 1839581 := bbase (se 3 (by rfl) ⟨344921, by rfl⟩ : syracuseStep 1839581 = 689843) (by norm_num)
theorem B1643021 : Blo 726324 1643021 := bbase (se 3 (by rfl) ⟨308066, by rfl⟩ : syracuseStep 1643021 = 616133) (by norm_num)
theorem B1380901 : Blo 726324 1380901 := bbase (se 4 (by rfl) ⟨129459, by rfl⟩ : syracuseStep 1380901 = 258919) (by norm_num)
theorem B1643093 : Blo 726324 1643093 := bbase (se 8 (by rfl) ⟨9627, by rfl⟩ : syracuseStep 1643093 = 19255) (by norm_num)
theorem B922205 : Blo 726324 922205 := bbase (se 3 (by rfl) ⟨172913, by rfl⟩ : syracuseStep 922205 = 345827) (by norm_num)
theorem B922261 : Blo 726324 922261 := bbase (se 6 (by rfl) ⟨21615, by rfl⟩ : syracuseStep 922261 = 43231) (by norm_num)
theorem B1839773 : Blo 726324 1839773 := bbase (se 3 (by rfl) ⟨344957, by rfl⟩ : syracuseStep 1839773 = 689915) (by norm_num)
theorem B1643165 : Blo 726324 1643165 := bbase (se 3 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 1643165 = 616187) (by norm_num)
theorem B1381045 : Blo 726324 1381045 := bbase (se 5 (by rfl) ⟨64736, by rfl⟩ : syracuseStep 1381045 = 129473) (by norm_num)
theorem B1774285 : Blo 726324 1774285 := bbase (se 3 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 1774285 = 665357) (by norm_num)
theorem B2069221 : Blo 726324 2069221 := bbase (se 4 (by rfl) ⟨193989, by rfl⟩ : syracuseStep 2069221 = 387979) (by norm_num)
theorem B922357 : Blo 726324 922357 := bbase (se 5 (by rfl) ⟨43235, by rfl⟩ : syracuseStep 922357 = 86471) (by norm_num)
theorem B2462453 : Blo 726324 2462453 := bbase (se 5 (by rfl) ⟨115427, by rfl⟩ : syracuseStep 2462453 = 230855) (by norm_num)
theorem B1381205 : Blo 726324 1381205 := bbase (se 9 (by rfl) ⟨4046, by rfl⟩ : syracuseStep 1381205 = 8093) (by norm_num)
theorem B2069381 : Blo 726324 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B922501 : Blo 726324 922501 := bbase (se 4 (by rfl) ⟨86484, by rfl⟩ : syracuseStep 922501 = 172969) (by norm_num)
theorem B922529 : Blo 726324 922529 := bbase (se 2 (by rfl) ⟨345948, by rfl⟩ : syracuseStep 922529 = 691897) (by norm_num)
theorem B1872821 : Blo 726324 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B2331605 : Blo 726324 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B922585 : Blo 726324 922585 := bbase (se 2 (by rfl) ⟨345969, by rfl⟩ : syracuseStep 922585 = 691939) (by norm_num)
theorem B1381349 : Blo 726324 1381349 := bbase (se 4 (by rfl) ⟨129501, by rfl⟩ : syracuseStep 1381349 = 259003) (by norm_num)
theorem B1840117 : Blo 726324 1840117 := bbase (se 5 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 1840117 = 172511) (by norm_num)
theorem B1315853 : Blo 726324 1315853 := bbase (se 3 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 1315853 = 493445) (by norm_num)
theorem B922681 : Blo 726324 922681 := bbase (se 2 (by rfl) ⟨346005, by rfl⟩ : syracuseStep 922681 = 692011) (by norm_num)
theorem B1840229 : Blo 726324 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B2069621 : Blo 726324 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B2462885 : Blo 726324 2462885 := bbase (se 4 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 2462885 = 461791) (by norm_num)
theorem B922853 : Blo 726324 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B1381637 : Blo 726324 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B1316125 : Blo 726324 1316125 := bbase (se 3 (by rfl) ⟨246773, by rfl⟩ : syracuseStep 1316125 = 493547) (by norm_num)
theorem B922909 : Blo 726324 922909 := bbase (se 3 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 922909 = 346091) (by norm_num)
theorem B1840421 : Blo 726324 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B2069813 : Blo 726324 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B2757989 : Blo 726324 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B923005 : Blo 726324 923005 := bbase (se 3 (by rfl) ⟨173063, by rfl⟩ : syracuseStep 923005 = 346127) (by norm_num)
theorem B3151237 : Blo 726324 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B1381789 : Blo 726324 1381789 := bbase (se 3 (by rfl) ⟨259085, by rfl⟩ : syracuseStep 1381789 = 518171) (by norm_num)
theorem B2627093 : Blo 726324 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B923177 : Blo 726324 923177 := bbase (se 2 (by rfl) ⟨346191, by rfl⟩ : syracuseStep 923177 = 692383) (by norm_num)
theorem B2463317 : Blo 726324 2463317 := bbase (se 8 (by rfl) ⟨14433, by rfl⟩ : syracuseStep 2463317 = 28867) (by norm_num)
theorem B923233 : Blo 726324 923233 := bbase (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) (by norm_num)
theorem B1840765 : Blo 726324 1840765 := bbase (se 3 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 1840765 = 690287) (by norm_num)
theorem B1971877 : Blo 726324 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B923329 : Blo 726324 923329 := bbase (se 2 (by rfl) ⟨346248, by rfl⟩ : syracuseStep 923329 = 692497) (by norm_num)
theorem B1382093 : Blo 726324 1382093 := bbase (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) (by norm_num)
theorem B1840877 : Blo 726324 1840877 := bbase (se 3 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 1840877 = 690329) (by norm_num)
theorem B4659029 : Blo 726324 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B923501 : Blo 726324 923501 := bbase (se 3 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 923501 = 346313) (by norm_num)
theorem B923557 : Blo 726324 923557 := bbase (se 4 (by rfl) ⟨86583, by rfl⟩ : syracuseStep 923557 = 173167) (by norm_num)
theorem B1841069 : Blo 726324 1841069 := bbase (se 3 (by rfl) ⟨345200, by rfl⟩ : syracuseStep 1841069 = 690401) (by norm_num)
theorem B923653 : Blo 726324 923653 := bbase (se 4 (by rfl) ⟨86592, by rfl⟩ : syracuseStep 923653 = 173185) (by norm_num)
theorem B2463749 : Blo 726324 2463749 := bbase (se 4 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 2463749 = 461953) (by norm_num)
theorem B3119141 : Blo 726324 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B923825 : Blo 726324 923825 := bbase (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) (by norm_num)
theorem B2627797 : Blo 726324 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B923881 : Blo 726324 923881 := bbase (se 2 (by rfl) ⟨346455, by rfl⟩ : syracuseStep 923881 = 692911) (by norm_num)
theorem B1841413 : Blo 726324 1841413 := bbase (se 4 (by rfl) ⟨172632, by rfl⟩ : syracuseStep 1841413 = 345265) (by norm_num)
theorem B2070805 : Blo 726324 2070805 := bbase (se 6 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 2070805 = 97069) (by norm_num)
theorem B6658325 : Blo 726324 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B3119381 : Blo 726324 3119381 := bbase (se 6 (by rfl) ⟨73110, by rfl⟩ : syracuseStep 3119381 = 146221) (by norm_num)
theorem B923977 : Blo 726324 923977 := bbase (se 2 (by rfl) ⟨346491, by rfl⟩ : syracuseStep 923977 = 692983) (by norm_num)
theorem B1841525 : Blo 726324 1841525 := bbase (se 5 (by rfl) ⟨86321, by rfl⟩ : syracuseStep 1841525 = 172643) (by norm_num)
theorem B1350029 : Blo 726324 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B2464181 : Blo 726324 2464181 := bbase (se 5 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 2464181 = 231017) (by norm_num)
theorem B1382845 : Blo 726324 1382845 := bbase (se 3 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 1382845 = 518567) (by norm_num)
theorem B924149 : Blo 726324 924149 := bbase (se 5 (by rfl) ⟨43319, by rfl⟩ : syracuseStep 924149 = 86639) (by norm_num)
theorem B924205 : Blo 726324 924205 := bbase (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) (by norm_num)
theorem B1841717 : Blo 726324 1841717 := bbase (se 5 (by rfl) ⟨86330, by rfl⟩ : syracuseStep 1841717 = 172661) (by norm_num)
theorem B1382989 : Blo 726324 1382989 := bbase (se 3 (by rfl) ⟨259310, by rfl⟩ : syracuseStep 1382989 = 518621) (by norm_num)
theorem B924301 : Blo 726324 924301 := bbase (se 3 (by rfl) ⟨173306, by rfl⟩ : syracuseStep 924301 = 346613) (by norm_num)
theorem B1383149 : Blo 726324 1383149 := bbase (se 3 (by rfl) ⟨259340, by rfl⟩ : syracuseStep 1383149 = 518681) (by norm_num)
theorem B2333461 : Blo 726324 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B2464613 : Blo 726324 2464613 := bbase (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) (by norm_num)
theorem B1383293 : Blo 726324 1383293 := bbase (se 3 (by rfl) ⟨259367, by rfl⟩ : syracuseStep 1383293 = 518735) (by norm_num)
theorem B1842061 : Blo 726324 1842061 := bbase (se 3 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 1842061 = 690773) (by norm_num)
theorem B9345941 : Blo 726324 9345941 := bbase (se 6 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 9345941 = 438091) (by norm_num)
theorem B1842173 : Blo 726324 1842173 := bbase (se 3 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 1842173 = 690815) (by norm_num)
theorem B3677237 : Blo 726324 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B3939445 : Blo 726324 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B1383581 : Blo 726324 1383581 := bbase (se 3 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 1383581 = 518843) (by norm_num)
theorem B3153077 : Blo 726324 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B1842365 : Blo 726324 1842365 := bbase (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) (by norm_num)
theorem B1023205 : Blo 726324 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B2956517 : Blo 726324 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B1383733 : Blo 726324 1383733 := bbase (se 5 (by rfl) ⟨64862, by rfl⟩ : syracuseStep 1383733 = 129725) (by norm_num)
theorem B23928149 : Blo 726324 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B2071909 : Blo 726324 2071909 := bbase (se 4 (by rfl) ⟨194241, by rfl⟩ : syracuseStep 2071909 = 388483) (by norm_num)
theorem B2760101 : Blo 726324 2760101 := bbase (se 4 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 2760101 = 517519) (by norm_num)
theorem B3317269 : Blo 726324 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B1842709 : Blo 726324 1842709 := bbase (se 6 (by rfl) ⟨43188, by rfl⟩ : syracuseStep 1842709 = 86377) (by norm_num)
theorem B1384037 : Blo 726324 1384037 := bbase (se 4 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 1384037 = 259507) (by norm_num)
theorem B1842821 : Blo 726324 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B2760389 : Blo 726324 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B18620117 : Blo 726324 18620117 := bbase (se 7 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 18620117 = 436409) (by norm_num)
theorem B1843013 : Blo 726324 1843013 := bbase (se 4 (by rfl) ⟨172782, by rfl⟩ : syracuseStep 1843013 = 345565) (by norm_num)
theorem B4202389 : Blo 726324 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B1089509 : Blo 726324 1089509 := bbase (se 4 (by rfl) ⟨102141, by rfl⟩ : syracuseStep 1089509 = 204283) (by norm_num)
theorem B1089533 : Blo 726324 1089533 := bbase (se 3 (by rfl) ⟨204287, by rfl⟩ : syracuseStep 1089533 = 408575) (by norm_num)
theorem B1089557 : Blo 726324 1089557 := bbase (se 6 (by rfl) ⟨25536, by rfl⟩ : syracuseStep 1089557 = 51073) (by norm_num)
theorem B1089581 : Blo 726324 1089581 := bbase (se 3 (by rfl) ⟨204296, by rfl⟩ : syracuseStep 1089581 = 408593) (by norm_num)
theorem B1089605 : Blo 726324 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B1089629 : Blo 726324 1089629 := bbase (se 3 (by rfl) ⟨204305, by rfl⟩ : syracuseStep 1089629 = 408611) (by norm_num)
theorem B1089653 : Blo 726324 1089653 := bbase (se 5 (by rfl) ⟨51077, by rfl⟩ : syracuseStep 1089653 = 102155) (by norm_num)
theorem B1089677 : Blo 726324 1089677 := bbase (se 3 (by rfl) ⟨204314, by rfl⟩ : syracuseStep 1089677 = 408629) (by norm_num)
theorem B1843357 : Blo 726324 1843357 := bbase (se 3 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 1843357 = 691259) (by norm_num)
theorem B1089701 : Blo 726324 1089701 := bbase (se 4 (by rfl) ⟨102159, by rfl⟩ : syracuseStep 1089701 = 204319) (by norm_num)
theorem B1089725 : Blo 726324 1089725 := bbase (se 3 (by rfl) ⟨204323, by rfl⟩ : syracuseStep 1089725 = 408647) (by norm_num)
theorem B1089749 : Blo 726324 1089749 := bbase (se 7 (by rfl) ⟨12770, by rfl⟩ : syracuseStep 1089749 = 25541) (by norm_num)
theorem B1089773 : Blo 726324 1089773 := bbase (se 3 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 1089773 = 408665) (by norm_num)
theorem B1089797 : Blo 726324 1089797 := bbase (se 4 (by rfl) ⟨102168, by rfl⟩ : syracuseStep 1089797 = 204337) (by norm_num)
theorem B1843469 : Blo 726324 1843469 := bbase (se 3 (by rfl) ⟨345650, by rfl⟩ : syracuseStep 1843469 = 691301) (by norm_num)
theorem B1089821 : Blo 726324 1089821 := bbase (se 3 (by rfl) ⟨204341, by rfl⟩ : syracuseStep 1089821 = 408683) (by norm_num)
theorem B1089845 : Blo 726324 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B3678533 : Blo 726324 3678533 := bbase (se 4 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 3678533 = 689725) (by norm_num)
theorem B1089869 : Blo 726324 1089869 := bbase (se 3 (by rfl) ⟨204350, by rfl⟩ : syracuseStep 1089869 = 408701) (by norm_num)
theorem B1384789 : Blo 726324 1384789 := bbase (se 10 (by rfl) ⟨2028, by rfl⟩ : syracuseStep 1384789 = 4057) (by norm_num)
theorem B1089893 : Blo 726324 1089893 := bbase (se 4 (by rfl) ⟨102177, by rfl⟩ : syracuseStep 1089893 = 204355) (by norm_num)
theorem B1089917 : Blo 726324 1089917 := bbase (se 3 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 1089917 = 408719) (by norm_num)
theorem B1089941 : Blo 726324 1089941 := bbase (se 6 (by rfl) ⟨25545, by rfl⟩ : syracuseStep 1089941 = 51091) (by norm_num)
theorem B1089965 : Blo 726324 1089965 := bbase (se 3 (by rfl) ⟨204368, by rfl⟩ : syracuseStep 1089965 = 408737) (by norm_num)
theorem B1089989 : Blo 726324 1089989 := bbase (se 4 (by rfl) ⟨102186, by rfl⟩ : syracuseStep 1089989 = 204373) (by norm_num)
theorem B1843661 : Blo 726324 1843661 := bbase (se 3 (by rfl) ⟨345686, by rfl⟩ : syracuseStep 1843661 = 691373) (by norm_num)
theorem B2105813 : Blo 726324 2105813 := bbase (se 7 (by rfl) ⟨24677, by rfl⟩ : syracuseStep 2105813 = 49355) (by norm_num)
theorem B1090013 : Blo 726324 1090013 := bbase (se 3 (by rfl) ⟨204377, by rfl⟩ : syracuseStep 1090013 = 408755) (by norm_num)
theorem B1384933 : Blo 726324 1384933 := bbase (se 4 (by rfl) ⟨129837, by rfl⟩ : syracuseStep 1384933 = 259675) (by norm_num)
theorem B1090037 : Blo 726324 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B1090061 : Blo 726324 1090061 := bbase (se 3 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 1090061 = 408773) (by norm_num)
theorem B1090085 : Blo 726324 1090085 := bbase (se 4 (by rfl) ⟨102195, by rfl⟩ : syracuseStep 1090085 = 204391) (by norm_num)
theorem B1090109 : Blo 726324 1090109 := bbase (se 3 (by rfl) ⟨204395, by rfl⟩ : syracuseStep 1090109 = 408791) (by norm_num)
theorem B1090133 : Blo 726324 1090133 := bbase (se 8 (by rfl) ⟨6387, by rfl⟩ : syracuseStep 1090133 = 12775) (by norm_num)
theorem B1090157 : Blo 726324 1090157 := bbase (se 3 (by rfl) ⟨204404, by rfl⟩ : syracuseStep 1090157 = 408809) (by norm_num)
theorem B1090181 : Blo 726324 1090181 := bbase (se 4 (by rfl) ⟨102204, by rfl⟩ : syracuseStep 1090181 = 204409) (by norm_num)
theorem B3154565 : Blo 726324 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B1385093 : Blo 726324 1385093 := bbase (se 4 (by rfl) ⟨129852, by rfl⟩ : syracuseStep 1385093 = 259705) (by norm_num)
theorem B1090205 : Blo 726324 1090205 := bbase (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) (by norm_num)
theorem B1090229 : Blo 726324 1090229 := bbase (se 5 (by rfl) ⟨51104, by rfl⟩ : syracuseStep 1090229 = 102209) (by norm_num)
theorem B1090253 : Blo 726324 1090253 := bbase (se 3 (by rfl) ⟨204422, by rfl⟩ : syracuseStep 1090253 = 408845) (by norm_num)
theorem B1090277 : Blo 726324 1090277 := bbase (se 4 (by rfl) ⟨102213, by rfl⟩ : syracuseStep 1090277 = 204427) (by norm_num)
theorem B1090301 : Blo 726324 1090301 := bbase (se 3 (by rfl) ⟨204431, by rfl⟩ : syracuseStep 1090301 = 408863) (by norm_num)
theorem B1090325 : Blo 726324 1090325 := bbase (se 6 (by rfl) ⟨25554, by rfl⟩ : syracuseStep 1090325 = 51109) (by norm_num)
theorem B1385237 : Blo 726324 1385237 := bbase (se 6 (by rfl) ⟨32466, by rfl⟩ : syracuseStep 1385237 = 64933) (by norm_num)
theorem B1844005 : Blo 726324 1844005 := bbase (se 4 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 1844005 = 345751) (by norm_num)
theorem B1090349 : Blo 726324 1090349 := bbase (se 3 (by rfl) ⟨204440, by rfl⟩ : syracuseStep 1090349 = 408881) (by norm_num)
theorem B1090373 : Blo 726324 1090373 := bbase (se 4 (by rfl) ⟨102222, by rfl⟩ : syracuseStep 1090373 = 204445) (by norm_num)
theorem B2073413 : Blo 726324 2073413 := bbase (se 4 (by rfl) ⟨194382, by rfl⟩ : syracuseStep 2073413 = 388765) (by norm_num)
theorem B1090397 : Blo 726324 1090397 := bbase (se 3 (by rfl) ⟨204449, by rfl⟩ : syracuseStep 1090397 = 408899) (by norm_num)
theorem B2761573 : Blo 726324 2761573 := bbase (se 4 (by rfl) ⟨258897, by rfl⟩ : syracuseStep 2761573 = 517795) (by norm_num)
theorem B1090421 : Blo 726324 1090421 := bbase (se 5 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 1090421 = 102227) (by norm_num)
theorem B1090445 : Blo 726324 1090445 := bbase (se 3 (by rfl) ⟨204458, by rfl⟩ : syracuseStep 1090445 = 408917) (by norm_num)
theorem B1844117 : Blo 726324 1844117 := bbase (se 6 (by rfl) ⟨43221, by rfl⟩ : syracuseStep 1844117 = 86443) (by norm_num)
theorem B1090469 : Blo 726324 1090469 := bbase (se 4 (by rfl) ⟨102231, by rfl⟩ : syracuseStep 1090469 = 204463) (by norm_num)
theorem B1090493 : Blo 726324 1090493 := bbase (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) (by norm_num)
theorem B1090517 : Blo 726324 1090517 := bbase (se 7 (by rfl) ⟨12779, by rfl⟩ : syracuseStep 1090517 = 25559) (by norm_num)
theorem B1090541 : Blo 726324 1090541 := bbase (se 3 (by rfl) ⟨204476, by rfl⟩ : syracuseStep 1090541 = 408953) (by norm_num)
theorem B1090565 : Blo 726324 1090565 := bbase (se 4 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 1090565 = 204481) (by norm_num)
theorem B1090589 : Blo 726324 1090589 := bbase (se 3 (by rfl) ⟨204485, by rfl⟩ : syracuseStep 1090589 = 408971) (by norm_num)
theorem B6628405 : Blo 726324 6628405 := bbase (se 5 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 6628405 = 621413) (by norm_num)
theorem B1090613 : Blo 726324 1090613 := bbase (se 5 (by rfl) ⟨51122, by rfl⟩ : syracuseStep 1090613 = 102245) (by norm_num)
theorem B1385525 : Blo 726324 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B1090637 : Blo 726324 1090637 := bbase (se 3 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 1090637 = 408989) (by norm_num)
theorem B1844309 : Blo 726324 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B1090661 : Blo 726324 1090661 := bbase (se 4 (by rfl) ⟨102249, by rfl⟩ : syracuseStep 1090661 = 204499) (by norm_num)
theorem B1090685 : Blo 726324 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B1090709 : Blo 726324 1090709 := bbase (se 6 (by rfl) ⟨25563, by rfl⟩ : syracuseStep 1090709 = 51127) (by norm_num)
theorem B2761877 : Blo 726324 2761877 := bbase (se 6 (by rfl) ⟨64731, by rfl⟩ : syracuseStep 2761877 = 129463) (by norm_num)
theorem B1090733 : Blo 726324 1090733 := bbase (se 3 (by rfl) ⟨204512, by rfl⟩ : syracuseStep 1090733 = 409025) (by norm_num)
theorem B1090757 : Blo 726324 1090757 := bbase (se 4 (by rfl) ⟨102258, by rfl⟩ : syracuseStep 1090757 = 204517) (by norm_num)
theorem B1385677 : Blo 726324 1385677 := bbase (se 3 (by rfl) ⟨259814, by rfl⟩ : syracuseStep 1385677 = 519629) (by norm_num)
theorem B1090781 : Blo 726324 1090781 := bbase (se 3 (by rfl) ⟨204521, by rfl⟩ : syracuseStep 1090781 = 409043) (by norm_num)
theorem B1090805 : Blo 726324 1090805 := bbase (se 5 (by rfl) ⟨51131, by rfl⟩ : syracuseStep 1090805 = 102263) (by norm_num)
theorem B1090829 : Blo 726324 1090829 := bbase (se 3 (by rfl) ⟨204530, by rfl⟩ : syracuseStep 1090829 = 409061) (by norm_num)
theorem B1090853 : Blo 726324 1090853 := bbase (se 4 (by rfl) ⟨102267, by rfl⟩ : syracuseStep 1090853 = 204535) (by norm_num)
theorem B1090877 : Blo 726324 1090877 := bbase (se 3 (by rfl) ⟨204539, by rfl⟩ : syracuseStep 1090877 = 409079) (by norm_num)
theorem B1090901 : Blo 726324 1090901 := bbase (se 12 (by rfl) ⟨399, by rfl⟩ : syracuseStep 1090901 = 799) (by norm_num)
theorem B1090925 : Blo 726324 1090925 := bbase (se 3 (by rfl) ⟨204548, by rfl⟩ : syracuseStep 1090925 = 409097) (by norm_num)
theorem B1090949 : Blo 726324 1090949 := bbase (se 4 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 1090949 = 204553) (by norm_num)
theorem B1090973 : Blo 726324 1090973 := bbase (se 3 (by rfl) ⟨204557, by rfl⟩ : syracuseStep 1090973 = 409115) (by norm_num)
theorem B1844653 : Blo 726324 1844653 := bbase (se 3 (by rfl) ⟨345872, by rfl⟩ : syracuseStep 1844653 = 691745) (by norm_num)
theorem B1090997 : Blo 726324 1090997 := bbase (se 5 (by rfl) ⟨51140, by rfl⟩ : syracuseStep 1090997 = 102281) (by norm_num)
theorem B1091021 : Blo 726324 1091021 := bbase (se 3 (by rfl) ⟨204566, by rfl⟩ : syracuseStep 1091021 = 409133) (by norm_num)
theorem B12461525 : Blo 726324 12461525 := bbase (se 7 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 12461525 = 292067) (by norm_num)
theorem B1091045 : Blo 726324 1091045 := bbase (se 4 (by rfl) ⟨102285, by rfl⟩ : syracuseStep 1091045 = 204571) (by norm_num)
theorem B1091069 : Blo 726324 1091069 := bbase (se 3 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 1091069 = 409151) (by norm_num)
theorem B1385981 : Blo 726324 1385981 := bbase (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) (by norm_num)
theorem B1091093 : Blo 726324 1091093 := bbase (se 6 (by rfl) ⟨25572, by rfl⟩ : syracuseStep 1091093 = 51145) (by norm_num)
theorem B1844765 : Blo 726324 1844765 := bbase (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) (by norm_num)
theorem B1123877 : Blo 726324 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B1091117 : Blo 726324 1091117 := bbase (se 3 (by rfl) ⟨204584, by rfl⟩ : syracuseStep 1091117 = 409169) (by norm_num)
theorem B1091141 : Blo 726324 1091141 := bbase (se 4 (by rfl) ⟨102294, by rfl⟩ : syracuseStep 1091141 = 204589) (by norm_num)
theorem B3679829 : Blo 726324 3679829 := bbase (se 8 (by rfl) ⟨21561, by rfl⟩ : syracuseStep 3679829 = 43123) (by norm_num)
theorem B1091165 : Blo 726324 1091165 := bbase (se 3 (by rfl) ⟨204593, by rfl⟩ : syracuseStep 1091165 = 409187) (by norm_num)
theorem B1091189 : Blo 726324 1091189 := bbase (se 5 (by rfl) ⟨51149, by rfl⟩ : syracuseStep 1091189 = 102299) (by norm_num)
theorem B1091213 : Blo 726324 1091213 := bbase (se 3 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 1091213 = 409205) (by norm_num)
theorem B1091237 : Blo 726324 1091237 := bbase (se 4 (by rfl) ⟨102303, by rfl⟩ : syracuseStep 1091237 = 204607) (by norm_num)
theorem B1091261 : Blo 726324 1091261 := bbase (se 3 (by rfl) ⟨204611, by rfl⟩ : syracuseStep 1091261 = 409223) (by norm_num)
theorem B1091285 : Blo 726324 1091285 := bbase (se 7 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 1091285 = 25577) (by norm_num)
theorem B1844957 : Blo 726324 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B1091309 : Blo 726324 1091309 := bbase (se 3 (by rfl) ⟨204620, by rfl⟩ : syracuseStep 1091309 = 409241) (by norm_num)
theorem B1091333 : Blo 726324 1091333 := bbase (se 4 (by rfl) ⟨102312, by rfl⟩ : syracuseStep 1091333 = 204625) (by norm_num)
theorem B1091357 : Blo 726324 1091357 := bbase (se 3 (by rfl) ⟨204629, by rfl⟩ : syracuseStep 1091357 = 409259) (by norm_num)
theorem B1091381 : Blo 726324 1091381 := bbase (se 5 (by rfl) ⟨51158, by rfl⟩ : syracuseStep 1091381 = 102317) (by norm_num)
theorem B1091405 : Blo 726324 1091405 := bbase (se 3 (by rfl) ⟨204638, by rfl⟩ : syracuseStep 1091405 = 409277) (by norm_num)
theorem B1091429 : Blo 726324 1091429 := bbase (se 4 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 1091429 = 204643) (by norm_num)
theorem B1091453 : Blo 726324 1091453 := bbase (se 3 (by rfl) ⟨204647, by rfl⟩ : syracuseStep 1091453 = 409295) (by norm_num)
theorem B1091477 : Blo 726324 1091477 := bbase (se 6 (by rfl) ⟨25581, by rfl⟩ : syracuseStep 1091477 = 51163) (by norm_num)
theorem B1091501 : Blo 726324 1091501 := bbase (se 3 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 1091501 = 409313) (by norm_num)
theorem B1091525 : Blo 726324 1091525 := bbase (se 4 (by rfl) ⟨102330, by rfl⟩ : syracuseStep 1091525 = 204661) (by norm_num)
theorem B1091549 : Blo 726324 1091549 := bbase (se 3 (by rfl) ⟨204665, by rfl⟩ : syracuseStep 1091549 = 409331) (by norm_num)
theorem B1091573 : Blo 726324 1091573 := bbase (se 5 (by rfl) ⟨51167, by rfl⟩ : syracuseStep 1091573 = 102335) (by norm_num)
theorem B1091597 : Blo 726324 1091597 := bbase (se 3 (by rfl) ⟨204674, by rfl⟩ : syracuseStep 1091597 = 409349) (by norm_num)
theorem B1091621 : Blo 726324 1091621 := bbase (se 4 (by rfl) ⟨102339, by rfl⟩ : syracuseStep 1091621 = 204679) (by norm_num)
theorem B1845301 : Blo 726324 1845301 := bbase (se 5 (by rfl) ⟨86498, by rfl⟩ : syracuseStep 1845301 = 172997) (by norm_num)
theorem B1091645 : Blo 726324 1091645 := bbase (se 3 (by rfl) ⟨204683, by rfl⟩ : syracuseStep 1091645 = 409367) (by norm_num)
theorem B1747021 : Blo 726324 1747021 := bbase (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) (by norm_num)
theorem B1091669 : Blo 726324 1091669 := bbase (se 8 (by rfl) ⟨6396, by rfl⟩ : syracuseStep 1091669 = 12793) (by norm_num)
theorem B1091693 : Blo 726324 1091693 := bbase (se 3 (by rfl) ⟨204692, by rfl⟩ : syracuseStep 1091693 = 409385) (by norm_num)
theorem B1091717 : Blo 726324 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B1091741 : Blo 726324 1091741 := bbase (se 3 (by rfl) ⟨204701, by rfl⟩ : syracuseStep 1091741 = 409403) (by norm_num)
theorem B1845413 : Blo 726324 1845413 := bbase (se 4 (by rfl) ⟨173007, by rfl⟩ : syracuseStep 1845413 = 346015) (by norm_num)
theorem B1747117 : Blo 726324 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B1091765 : Blo 726324 1091765 := bbase (se 5 (by rfl) ⟨51176, by rfl⟩ : syracuseStep 1091765 = 102353) (by norm_num)
theorem B1091789 : Blo 726324 1091789 := bbase (se 3 (by rfl) ⟨204710, by rfl⟩ : syracuseStep 1091789 = 409421) (by norm_num)
theorem B1091813 : Blo 726324 1091813 := bbase (se 4 (by rfl) ⟨102357, by rfl⟩ : syracuseStep 1091813 = 204715) (by norm_num)
theorem B1091837 : Blo 726324 1091837 := bbase (se 3 (by rfl) ⟨204719, by rfl⟩ : syracuseStep 1091837 = 409439) (by norm_num)
theorem B1091861 : Blo 726324 1091861 := bbase (se 6 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 1091861 = 51181) (by norm_num)
theorem B1091885 : Blo 726324 1091885 := bbase (se 3 (by rfl) ⟨204728, by rfl⟩ : syracuseStep 1091885 = 409457) (by norm_num)
theorem B1091909 : Blo 726324 1091909 := bbase (se 4 (by rfl) ⟨102366, by rfl⟩ : syracuseStep 1091909 = 204733) (by norm_num)
theorem B1091933 : Blo 726324 1091933 := bbase (se 3 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 1091933 = 409475) (by norm_num)
theorem B1845605 : Blo 726324 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B1091957 : Blo 726324 1091957 := bbase (se 5 (by rfl) ⟨51185, by rfl⟩ : syracuseStep 1091957 = 102371) (by norm_num)
theorem B2074997 : Blo 726324 2074997 := bbase (se 5 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 2074997 = 194531) (by norm_num)
theorem B1091981 : Blo 726324 1091981 := bbase (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) (by norm_num)
theorem B1092005 : Blo 726324 1092005 := bbase (se 4 (by rfl) ⟨102375, by rfl⟩ : syracuseStep 1092005 = 204751) (by norm_num)
theorem B1092029 : Blo 726324 1092029 := bbase (se 3 (by rfl) ⟨204755, by rfl⟩ : syracuseStep 1092029 = 409511) (by norm_num)
theorem B1092053 : Blo 726324 1092053 := bbase (se 7 (by rfl) ⟨12797, by rfl⟩ : syracuseStep 1092053 = 25595) (by norm_num)
theorem B1092077 : Blo 726324 1092077 := bbase (se 3 (by rfl) ⟨204764, by rfl⟩ : syracuseStep 1092077 = 409529) (by norm_num)
theorem B1092101 : Blo 726324 1092101 := bbase (se 4 (by rfl) ⟨102384, by rfl⟩ : syracuseStep 1092101 = 204769) (by norm_num)
theorem B1092125 : Blo 726324 1092125 := bbase (se 3 (by rfl) ⟨204773, by rfl⟩ : syracuseStep 1092125 = 409547) (by norm_num)
theorem B1092149 : Blo 726324 1092149 := bbase (se 5 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 1092149 = 102389) (by norm_num)
theorem B1092173 : Blo 726324 1092173 := bbase (se 3 (by rfl) ⟨204782, by rfl⟩ : syracuseStep 1092173 = 409565) (by norm_num)
theorem B1092197 : Blo 726324 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B1092221 : Blo 726324 1092221 := bbase (se 3 (by rfl) ⟨204791, by rfl⟩ : syracuseStep 1092221 = 409583) (by norm_num)
theorem B1092245 : Blo 726324 1092245 := bbase (se 6 (by rfl) ⟨25599, by rfl⟩ : syracuseStep 1092245 = 51199) (by norm_num)
theorem B2632357 : Blo 726324 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B1092269 : Blo 726324 1092269 := bbase (se 3 (by rfl) ⟨204800, by rfl⟩ : syracuseStep 1092269 = 409601) (by norm_num)
theorem B1845949 : Blo 726324 1845949 := bbase (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) (by norm_num)
theorem B1092293 : Blo 726324 1092293 := bbase (se 4 (by rfl) ⟨102402, by rfl⟩ : syracuseStep 1092293 = 204805) (by norm_num)
theorem B1092317 : Blo 726324 1092317 := bbase (se 3 (by rfl) ⟨204809, by rfl⟩ : syracuseStep 1092317 = 409619) (by norm_num)
theorem B1092341 : Blo 726324 1092341 := bbase (se 5 (by rfl) ⟨51203, by rfl⟩ : syracuseStep 1092341 = 102407) (by norm_num)
theorem B1092365 : Blo 726324 1092365 := bbase (se 3 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 1092365 = 409637) (by norm_num)
theorem B1092389 : Blo 726324 1092389 := bbase (se 4 (by rfl) ⟨102411, by rfl⟩ : syracuseStep 1092389 = 204823) (by norm_num)
theorem B2960165 : Blo 726324 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1846061 : Blo 726324 1846061 := bbase (se 3 (by rfl) ⟨346136, by rfl⟩ : syracuseStep 1846061 = 692273) (by norm_num)
theorem B1092413 : Blo 726324 1092413 := bbase (se 3 (by rfl) ⟨204827, by rfl⟩ : syracuseStep 1092413 = 409655) (by norm_num)
theorem B1092437 : Blo 726324 1092437 := bbase (se 9 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 1092437 = 6401) (by norm_num)
theorem B3681125 : Blo 726324 3681125 := bbase (se 4 (by rfl) ⟨345105, by rfl⟩ : syracuseStep 3681125 = 690211) (by norm_num)
theorem B1092461 : Blo 726324 1092461 := bbase (se 3 (by rfl) ⟨204836, by rfl⟩ : syracuseStep 1092461 = 409673) (by norm_num)
theorem B2337653 : Blo 726324 2337653 := bbase (se 5 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 2337653 = 219155) (by norm_num)
theorem B1092485 : Blo 726324 1092485 := bbase (se 4 (by rfl) ⟨102420, by rfl⟩ : syracuseStep 1092485 = 204841) (by norm_num)
theorem B1092509 : Blo 726324 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B2960293 : Blo 726324 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B1092533 : Blo 726324 1092533 := bbase (se 5 (by rfl) ⟨51212, by rfl⟩ : syracuseStep 1092533 = 102425) (by norm_num)
theorem B5909429 : Blo 726324 5909429 := bbase (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) (by norm_num)
theorem B830393 : Blo 726324 830393 := bbase (se 2 (by rfl) ⟨311397, by rfl⟩ : syracuseStep 830393 = 622795) (by norm_num)
theorem B1092557 : Blo 726324 1092557 := bbase (se 3 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 1092557 = 409709) (by norm_num)
theorem B1092581 : Blo 726324 1092581 := bbase (se 4 (by rfl) ⟨102429, by rfl⟩ : syracuseStep 1092581 = 204859) (by norm_num)
theorem B1846253 : Blo 726324 1846253 := bbase (se 3 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 1846253 = 692345) (by norm_num)
theorem B1092605 : Blo 726324 1092605 := bbase (se 3 (by rfl) ⟨204863, by rfl⟩ : syracuseStep 1092605 = 409727) (by norm_num)
theorem B1092629 : Blo 726324 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B2075669 : Blo 726324 2075669 := bbase (se 6 (by rfl) ⟨48648, by rfl⟩ : syracuseStep 2075669 = 97297) (by norm_num)
theorem B1092653 : Blo 726324 1092653 := bbase (se 3 (by rfl) ⟨204872, by rfl⟩ : syracuseStep 1092653 = 409745) (by norm_num)
theorem B1092677 : Blo 726324 1092677 := bbase (se 4 (by rfl) ⟨102438, by rfl⟩ : syracuseStep 1092677 = 204877) (by norm_num)
theorem B1092701 : Blo 726324 1092701 := bbase (se 3 (by rfl) ⟨204881, by rfl⟩ : syracuseStep 1092701 = 409763) (by norm_num)
theorem B1092725 : Blo 726324 1092725 := bbase (se 5 (by rfl) ⟨51221, by rfl⟩ : syracuseStep 1092725 = 102443) (by norm_num)
theorem B1092749 : Blo 726324 1092749 := bbase (se 3 (by rfl) ⟨204890, by rfl⟩ : syracuseStep 1092749 = 409781) (by norm_num)
theorem B1092773 : Blo 726324 1092773 := bbase (se 4 (by rfl) ⟨102447, by rfl⟩ : syracuseStep 1092773 = 204895) (by norm_num)
theorem B1092797 : Blo 726324 1092797 := bbase (se 3 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 1092797 = 409799) (by norm_num)
theorem B2763989 : Blo 726324 2763989 := bbase (se 7 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 2763989 = 64781) (by norm_num)
theorem B1092821 : Blo 726324 1092821 := bbase (se 7 (by rfl) ⟨12806, by rfl⟩ : syracuseStep 1092821 = 25613) (by norm_num)
theorem B1092845 : Blo 726324 1092845 := bbase (se 3 (by rfl) ⟨204908, by rfl⟩ : syracuseStep 1092845 = 409817) (by norm_num)
theorem B1748213 : Blo 726324 1748213 := bbase (se 5 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 1748213 = 163895) (by norm_num)
theorem B1092869 : Blo 726324 1092869 := bbase (se 4 (by rfl) ⟨102456, by rfl⟩ : syracuseStep 1092869 = 204913) (by norm_num)
theorem B1092893 : Blo 726324 1092893 := bbase (se 3 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 1092893 = 409835) (by norm_num)
theorem B1092917 : Blo 726324 1092917 := bbase (se 5 (by rfl) ⟨51230, by rfl⟩ : syracuseStep 1092917 = 102461) (by norm_num)
theorem B1846597 : Blo 726324 1846597 := bbase (se 4 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 1846597 = 346237) (by norm_num)
theorem B1092941 : Blo 726324 1092941 := bbase (se 3 (by rfl) ⟨204926, by rfl⟩ : syracuseStep 1092941 = 409853) (by norm_num)
theorem B1092965 : Blo 726324 1092965 := bbase (se 4 (by rfl) ⟨102465, by rfl⟩ : syracuseStep 1092965 = 204931) (by norm_num)
theorem B1092989 : Blo 726324 1092989 := bbase (se 3 (by rfl) ⟨204935, by rfl⟩ : syracuseStep 1092989 = 409871) (by norm_num)
theorem B1093013 : Blo 726324 1093013 := bbase (se 6 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 1093013 = 51235) (by norm_num)
theorem B1093037 : Blo 726324 1093037 := bbase (se 3 (by rfl) ⟨204944, by rfl⟩ : syracuseStep 1093037 = 409889) (by norm_num)
theorem B1846709 : Blo 726324 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B1093061 : Blo 726324 1093061 := bbase (se 4 (by rfl) ⟨102474, by rfl⟩ : syracuseStep 1093061 = 204949) (by norm_num)
theorem B2076101 : Blo 726324 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B1093085 : Blo 726324 1093085 := bbase (se 3 (by rfl) ⟨204953, by rfl⟩ : syracuseStep 1093085 = 409907) (by norm_num)
theorem B2764277 : Blo 726324 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B1093109 : Blo 726324 1093109 := bbase (se 5 (by rfl) ⟨51239, by rfl⟩ : syracuseStep 1093109 = 102479) (by norm_num)
theorem B1093133 : Blo 726324 1093133 := bbase (se 3 (by rfl) ⟨204962, by rfl⟩ : syracuseStep 1093133 = 409925) (by norm_num)
theorem B1093157 : Blo 726324 1093157 := bbase (se 4 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 1093157 = 204967) (by norm_num)
theorem B1093181 : Blo 726324 1093181 := bbase (se 3 (by rfl) ⟨204971, by rfl⟩ : syracuseStep 1093181 = 409943) (by norm_num)
theorem B4140629 : Blo 726324 4140629 := bbase (se 8 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 4140629 = 48523) (by norm_num)
theorem B1093205 : Blo 726324 1093205 := bbase (se 8 (by rfl) ⟨6405, by rfl⟩ : syracuseStep 1093205 = 12811) (by norm_num)
theorem B1093229 : Blo 726324 1093229 := bbase (se 3 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 1093229 = 409961) (by norm_num)
theorem B1846901 : Blo 726324 1846901 := bbase (se 5 (by rfl) ⟨86573, by rfl⟩ : syracuseStep 1846901 = 173147) (by norm_num)
theorem B1093253 : Blo 726324 1093253 := bbase (se 4 (by rfl) ⟨102492, by rfl⟩ : syracuseStep 1093253 = 204985) (by norm_num)
theorem B1093277 : Blo 726324 1093277 := bbase (se 3 (by rfl) ⟨204989, by rfl⟩ : syracuseStep 1093277 = 409979) (by norm_num)
theorem B1093301 : Blo 726324 1093301 := bbase (se 5 (by rfl) ⟨51248, by rfl⟩ : syracuseStep 1093301 = 102497) (by norm_num)
theorem B1683149 : Blo 726324 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B1093325 : Blo 726324 1093325 := bbase (se 3 (by rfl) ⟨204998, by rfl⟩ : syracuseStep 1093325 = 409997) (by norm_num)
theorem B1093349 : Blo 726324 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B4665077 : Blo 726324 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B5254901 : Blo 726324 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B1093373 : Blo 726324 1093373 := bbase (se 3 (by rfl) ⟨205007, by rfl⟩ : syracuseStep 1093373 = 410015) (by norm_num)
theorem B1093397 : Blo 726324 1093397 := bbase (se 6 (by rfl) ⟨25626, by rfl⟩ : syracuseStep 1093397 = 51253) (by norm_num)
theorem B1093421 : Blo 726324 1093421 := bbase (se 3 (by rfl) ⟨205016, by rfl⟩ : syracuseStep 1093421 = 410033) (by norm_num)
theorem B1093445 : Blo 726324 1093445 := bbase (se 4 (by rfl) ⟨102510, by rfl⟩ : syracuseStep 1093445 = 205021) (by norm_num)
theorem B1093469 : Blo 726324 1093469 := bbase (se 3 (by rfl) ⟨205025, by rfl⟩ : syracuseStep 1093469 = 410051) (by norm_num)
theorem B1093493 : Blo 726324 1093493 := bbase (se 5 (by rfl) ⟨51257, by rfl⟩ : syracuseStep 1093493 = 102515) (by norm_num)
theorem B1093517 : Blo 726324 1093517 := bbase (se 3 (by rfl) ⟨205034, by rfl⟩ : syracuseStep 1093517 = 410069) (by norm_num)
theorem B1093541 : Blo 726324 1093541 := bbase (se 4 (by rfl) ⟨102519, by rfl⟩ : syracuseStep 1093541 = 205039) (by norm_num)
theorem B1093565 : Blo 726324 1093565 := bbase (se 3 (by rfl) ⟨205043, by rfl⟩ : syracuseStep 1093565 = 410087) (by norm_num)
theorem B1847245 : Blo 726324 1847245 := bbase (se 3 (by rfl) ⟨346358, by rfl⟩ : syracuseStep 1847245 = 692717) (by norm_num)
theorem B1683413 : Blo 726324 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B1093589 : Blo 726324 1093589 := bbase (se 7 (by rfl) ⟨12815, by rfl⟩ : syracuseStep 1093589 = 25631) (by norm_num)
theorem B1093613 : Blo 726324 1093613 := bbase (se 3 (by rfl) ⟨205052, by rfl⟩ : syracuseStep 1093613 = 410105) (by norm_num)
theorem B1093637 : Blo 726324 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B1093661 : Blo 726324 1093661 := bbase (se 3 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 1093661 = 410123) (by norm_num)
theorem B1552421 : Blo 726324 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1093685 : Blo 726324 1093685 := bbase (se 5 (by rfl) ⟨51266, by rfl⟩ : syracuseStep 1093685 = 102533) (by norm_num)
theorem B1847357 : Blo 726324 1847357 := bbase (se 3 (by rfl) ⟨346379, by rfl⟩ : syracuseStep 1847357 = 692759) (by norm_num)
theorem B1093709 : Blo 726324 1093709 := bbase (se 3 (by rfl) ⟨205070, by rfl⟩ : syracuseStep 1093709 = 410141) (by norm_num)
theorem B1093733 : Blo 726324 1093733 := bbase (se 4 (by rfl) ⟨102537, by rfl⟩ : syracuseStep 1093733 = 205075) (by norm_num)
theorem B3682421 : Blo 726324 3682421 := bbase (se 5 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 3682421 = 345227) (by norm_num)
theorem B1093757 : Blo 726324 1093757 := bbase (se 3 (by rfl) ⟨205079, by rfl⟩ : syracuseStep 1093757 = 410159) (by norm_num)
theorem B1093781 : Blo 726324 1093781 := bbase (se 6 (by rfl) ⟨25635, by rfl⟩ : syracuseStep 1093781 = 51271) (by norm_num)
theorem B1093805 : Blo 726324 1093805 := bbase (se 3 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 1093805 = 410177) (by norm_num)
theorem B1552565 : Blo 726324 1552565 := bbase (se 5 (by rfl) ⟨72776, by rfl⟩ : syracuseStep 1552565 = 145553) (by norm_num)
theorem B1749173 : Blo 726324 1749173 := bbase (se 5 (by rfl) ⟨81992, by rfl⟩ : syracuseStep 1749173 = 163985) (by norm_num)
theorem B2076853 : Blo 726324 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B1093829 : Blo 726324 1093829 := bbase (se 4 (by rfl) ⟨102546, by rfl⟩ : syracuseStep 1093829 = 205093) (by norm_num)
theorem B1093853 : Blo 726324 1093853 := bbase (se 3 (by rfl) ⟨205097, by rfl⟩ : syracuseStep 1093853 = 410195) (by norm_num)
theorem B5517557 : Blo 726324 5517557 := bbase (se 5 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 5517557 = 517271) (by norm_num)
theorem B1093877 : Blo 726324 1093877 := bbase (se 5 (by rfl) ⟨51275, by rfl⟩ : syracuseStep 1093877 = 102551) (by norm_num)
theorem B1847549 : Blo 726324 1847549 := bbase (se 3 (by rfl) ⟨346415, by rfl⟩ : syracuseStep 1847549 = 692831) (by norm_num)
theorem B1093901 : Blo 726324 1093901 := bbase (se 3 (by rfl) ⟨205106, by rfl⟩ : syracuseStep 1093901 = 410213) (by norm_num)
theorem B1093925 : Blo 726324 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B1093949 : Blo 726324 1093949 := bbase (se 3 (by rfl) ⟨205115, by rfl⟩ : syracuseStep 1093949 = 410231) (by norm_num)
theorem B1093973 : Blo 726324 1093973 := bbase (se 10 (by rfl) ⟨1602, by rfl⟩ : syracuseStep 1093973 = 3205) (by norm_num)
theorem B1093997 : Blo 726324 1093997 := bbase (se 3 (by rfl) ⟨205124, by rfl⟩ : syracuseStep 1093997 = 410249) (by norm_num)
theorem B1094021 : Blo 726324 1094021 := bbase (se 4 (by rfl) ⟨102564, by rfl⟩ : syracuseStep 1094021 = 205129) (by norm_num)
theorem B1094045 : Blo 726324 1094045 := bbase (se 3 (by rfl) ⟨205133, by rfl⟩ : syracuseStep 1094045 = 410267) (by norm_num)
theorem B1094069 : Blo 726324 1094069 := bbase (se 5 (by rfl) ⟨51284, by rfl⟩ : syracuseStep 1094069 = 102569) (by norm_num)
theorem B1094093 : Blo 726324 1094093 := bbase (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) (by norm_num)
theorem B1094117 : Blo 726324 1094117 := bbase (se 4 (by rfl) ⟨102573, by rfl⟩ : syracuseStep 1094117 = 205147) (by norm_num)
theorem B831973 : Blo 726324 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1094141 : Blo 726324 1094141 := bbase (se 3 (by rfl) ⟨205151, by rfl⟩ : syracuseStep 1094141 = 410303) (by norm_num)
theorem B1094165 : Blo 726324 1094165 := bbase (se 6 (by rfl) ⟨25644, by rfl⟩ : syracuseStep 1094165 = 51289) (by norm_num)
theorem B3944981 : Blo 726324 3944981 := bbase (se 6 (by rfl) ⟨92460, by rfl⟩ : syracuseStep 3944981 = 184921) (by norm_num)
theorem B1552925 : Blo 726324 1552925 := bbase (se 3 (by rfl) ⟨291173, by rfl⟩ : syracuseStep 1552925 = 582347) (by norm_num)
theorem B1094189 : Blo 726324 1094189 := bbase (se 3 (by rfl) ⟨205160, by rfl⟩ : syracuseStep 1094189 = 410321) (by norm_num)
theorem B1094213 : Blo 726324 1094213 := bbase (se 4 (by rfl) ⟨102582, by rfl⟩ : syracuseStep 1094213 = 205165) (by norm_num)
theorem B1847893 : Blo 726324 1847893 := bbase (se 8 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 1847893 = 21655) (by norm_num)
theorem B1094237 : Blo 726324 1094237 := bbase (se 3 (by rfl) ⟨205169, by rfl⟩ : syracuseStep 1094237 = 410339) (by norm_num)
theorem B1094261 : Blo 726324 1094261 := bbase (se 5 (by rfl) ⟨51293, by rfl⟩ : syracuseStep 1094261 = 102587) (by norm_num)
theorem B1094285 : Blo 726324 1094285 := bbase (se 3 (by rfl) ⟨205178, by rfl⟩ : syracuseStep 1094285 = 410357) (by norm_num)
theorem B2765461 : Blo 726324 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B1094309 : Blo 726324 1094309 := bbase (se 4 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 1094309 = 205183) (by norm_num)
theorem B4207285 : Blo 726324 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B1094333 : Blo 726324 1094333 := bbase (se 3 (by rfl) ⟨205187, by rfl⟩ : syracuseStep 1094333 = 410375) (by norm_num)
theorem B1848005 : Blo 726324 1848005 := bbase (se 4 (by rfl) ⟨173250, by rfl⟩ : syracuseStep 1848005 = 346501) (by norm_num)
theorem B1094357 : Blo 726324 1094357 := bbase (se 7 (by rfl) ⟨12824, by rfl⟩ : syracuseStep 1094357 = 25649) (by norm_num)
theorem B1094381 : Blo 726324 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B4141813 : Blo 726324 4141813 := bbase (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) (by norm_num)
theorem B1094405 : Blo 726324 1094405 := bbase (se 4 (by rfl) ⟨102600, by rfl⟩ : syracuseStep 1094405 = 205201) (by norm_num)
theorem B1094429 : Blo 726324 1094429 := bbase (se 3 (by rfl) ⟨205205, by rfl⟩ : syracuseStep 1094429 = 410411) (by norm_num)
theorem B1094453 : Blo 726324 1094453 := bbase (se 5 (by rfl) ⟨51302, by rfl⟩ : syracuseStep 1094453 = 102605) (by norm_num)
theorem B1094477 : Blo 726324 1094477 := bbase (se 3 (by rfl) ⟨205214, by rfl⟩ : syracuseStep 1094477 = 410429) (by norm_num)
theorem B1094501 : Blo 726324 1094501 := bbase (se 4 (by rfl) ⟨102609, by rfl⟩ : syracuseStep 1094501 = 205219) (by norm_num)
theorem B1094525 : Blo 726324 1094525 := bbase (se 3 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 1094525 = 410447) (by norm_num)
theorem B1848197 : Blo 726324 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B1094549 : Blo 726324 1094549 := bbase (se 6 (by rfl) ⟨25653, by rfl⟩ : syracuseStep 1094549 = 51307) (by norm_num)
theorem B1094573 : Blo 726324 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B2765765 : Blo 726324 2765765 := bbase (se 4 (by rfl) ⟨259290, by rfl⟩ : syracuseStep 2765765 = 518581) (by norm_num)
theorem B1094597 : Blo 726324 1094597 := bbase (se 4 (by rfl) ⟨102618, by rfl⟩ : syracuseStep 1094597 = 205237) (by norm_num)
theorem B1225685 : Blo 726324 1225685 := bbase (se 7 (by rfl) ⟨14363, by rfl⟩ : syracuseStep 1225685 = 28727) (by norm_num)
theorem B1094621 : Blo 726324 1094621 := bbase (se 3 (by rfl) ⟨205241, by rfl⟩ : syracuseStep 1094621 = 410483) (by norm_num)
theorem B1094645 : Blo 726324 1094645 := bbase (se 5 (by rfl) ⟨51311, by rfl⟩ : syracuseStep 1094645 = 102623) (by norm_num)
theorem B1094669 : Blo 726324 1094669 := bbase (se 3 (by rfl) ⟨205250, by rfl⟩ : syracuseStep 1094669 = 410501) (by norm_num)
theorem B1094693 : Blo 726324 1094693 := bbase (se 4 (by rfl) ⟨102627, by rfl⟩ : syracuseStep 1094693 = 205255) (by norm_num)
theorem B1094717 : Blo 726324 1094717 := bbase (se 3 (by rfl) ⟨205259, by rfl⟩ : syracuseStep 1094717 = 410519) (by norm_num)
theorem B1225813 : Blo 726324 1225813 := bbase (se 8 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 1225813 = 14365) (by norm_num)
theorem B1094741 : Blo 726324 1094741 := bbase (se 8 (by rfl) ⟨6414, by rfl⟩ : syracuseStep 1094741 = 12829) (by norm_num)
theorem B1094765 : Blo 726324 1094765 := bbase (se 3 (by rfl) ⟨205268, by rfl⟩ : syracuseStep 1094765 = 410537) (by norm_num)
theorem B1094789 : Blo 726324 1094789 := bbase (se 4 (by rfl) ⟨102636, by rfl⟩ : syracuseStep 1094789 = 205273) (by norm_num)
theorem B1094813 : Blo 726324 1094813 := bbase (se 3 (by rfl) ⟨205277, by rfl⟩ : syracuseStep 1094813 = 410555) (by norm_num)
theorem B3159205 : Blo 726324 3159205 := bbase (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) (by norm_num)
theorem B1225901 : Blo 726324 1225901 := bbase (se 3 (by rfl) ⟨229856, by rfl⟩ : syracuseStep 1225901 = 459713) (by norm_num)
theorem B1094837 : Blo 726324 1094837 := bbase (se 5 (by rfl) ⟨51320, by rfl⟩ : syracuseStep 1094837 = 102641) (by norm_num)
theorem B1094861 : Blo 726324 1094861 := bbase (se 3 (by rfl) ⟨205286, by rfl⟩ : syracuseStep 1094861 = 410573) (by norm_num)
theorem B832729 : Blo 726324 832729 := bbase (se 2 (by rfl) ⟨312273, by rfl⟩ : syracuseStep 832729 = 624547) (by norm_num)
theorem B1848541 : Blo 726324 1848541 := bbase (se 3 (by rfl) ⟨346601, by rfl⟩ : syracuseStep 1848541 = 693203) (by norm_num)
theorem B1094885 : Blo 726324 1094885 := bbase (se 4 (by rfl) ⟨102645, by rfl⟩ : syracuseStep 1094885 = 205291) (by norm_num)
theorem B1094909 : Blo 726324 1094909 := bbase (se 3 (by rfl) ⟨205295, by rfl⟩ : syracuseStep 1094909 = 410591) (by norm_num)
theorem B1094933 : Blo 726324 1094933 := bbase (se 6 (by rfl) ⟨25662, by rfl⟩ : syracuseStep 1094933 = 51325) (by norm_num)
theorem B1226029 : Blo 726324 1226029 := bbase (se 3 (by rfl) ⟨229880, by rfl⟩ : syracuseStep 1226029 = 459761) (by norm_num)
theorem B1094957 : Blo 726324 1094957 := bbase (se 3 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 1094957 = 410609) (by norm_num)
theorem B1094981 : Blo 726324 1094981 := bbase (se 4 (by rfl) ⟨102654, by rfl⟩ : syracuseStep 1094981 = 205309) (by norm_num)
theorem B1095005 : Blo 726324 1095005 := bbase (se 3 (by rfl) ⟨205313, by rfl⟩ : syracuseStep 1095005 = 410627) (by norm_num)
theorem B1095029 : Blo 726324 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B1226117 : Blo 726324 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B3683717 : Blo 726324 3683717 := bbase (se 4 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 3683717 = 690697) (by norm_num)
theorem B1095053 : Blo 726324 1095053 := bbase (se 3 (by rfl) ⟨205322, by rfl⟩ : syracuseStep 1095053 = 410645) (by norm_num)
theorem B1553813 : Blo 726324 1553813 := bbase (se 6 (by rfl) ⟨36417, by rfl⟩ : syracuseStep 1553813 = 72835) (by norm_num)
theorem B1095077 : Blo 726324 1095077 := bbase (se 4 (by rfl) ⟨102663, by rfl⟩ : syracuseStep 1095077 = 205327) (by norm_num)
theorem B1095101 : Blo 726324 1095101 := bbase (se 3 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 1095101 = 410663) (by norm_num)
theorem B1095125 : Blo 726324 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B1095149 : Blo 726324 1095149 := bbase (se 3 (by rfl) ⟨205340, by rfl⟩ : syracuseStep 1095149 = 410681) (by norm_num)
theorem B1226245 : Blo 726324 1226245 := bbase (se 4 (by rfl) ⟨114960, by rfl⟩ : syracuseStep 1226245 = 229921) (by norm_num)
theorem B1095173 : Blo 726324 1095173 := bbase (se 4 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 1095173 = 205345) (by norm_num)
theorem B1095197 : Blo 726324 1095197 := bbase (se 3 (by rfl) ⟨205349, by rfl⟩ : syracuseStep 1095197 = 410699) (by norm_num)
theorem B1095221 : Blo 726324 1095221 := bbase (se 5 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 1095221 = 102677) (by norm_num)
theorem B1095245 : Blo 726324 1095245 := bbase (se 3 (by rfl) ⟨205358, by rfl⟩ : syracuseStep 1095245 = 410717) (by norm_num)
theorem B1226333 : Blo 726324 1226333 := bbase (se 3 (by rfl) ⟨229937, by rfl⟩ : syracuseStep 1226333 = 459875) (by norm_num)
theorem B1095269 : Blo 726324 1095269 := bbase (se 4 (by rfl) ⟨102681, by rfl⟩ : syracuseStep 1095269 = 205363) (by norm_num)
theorem B1095293 : Blo 726324 1095293 := bbase (se 3 (by rfl) ⟨205367, by rfl⟩ : syracuseStep 1095293 = 410735) (by norm_num)
theorem B1554061 : Blo 726324 1554061 := bbase (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) (by norm_num)
theorem B1095317 : Blo 726324 1095317 := bbase (se 6 (by rfl) ⟨25671, by rfl⟩ : syracuseStep 1095317 = 51343) (by norm_num)
theorem B1095341 : Blo 726324 1095341 := bbase (se 3 (by rfl) ⟨205376, by rfl⟩ : syracuseStep 1095341 = 410753) (by norm_num)
theorem B1095365 : Blo 726324 1095365 := bbase (se 4 (by rfl) ⟨102690, by rfl⟩ : syracuseStep 1095365 = 205381) (by norm_num)
theorem B1226461 : Blo 726324 1226461 := bbase (se 3 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 1226461 = 459923) (by norm_num)
theorem B1095389 : Blo 726324 1095389 := bbase (se 3 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 1095389 = 410771) (by norm_num)
theorem B1095413 : Blo 726324 1095413 := bbase (se 5 (by rfl) ⟨51347, by rfl⟩ : syracuseStep 1095413 = 102695) (by norm_num)
theorem B1095437 : Blo 726324 1095437 := bbase (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) (by norm_num)
theorem B1095461 : Blo 726324 1095461 := bbase (se 4 (by rfl) ⟨102699, by rfl⟩ : syracuseStep 1095461 = 205399) (by norm_num)
theorem B1226549 : Blo 726324 1226549 := bbase (se 5 (by rfl) ⟨57494, by rfl⟩ : syracuseStep 1226549 = 114989) (by norm_num)
theorem B1095485 : Blo 726324 1095485 := bbase (se 3 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 1095485 = 410807) (by norm_num)
theorem B1750933 : Blo 726324 1750933 := bbase (se 6 (by rfl) ⟨41037, by rfl⟩ : syracuseStep 1750933 = 82075) (by norm_num)
theorem B1226677 : Blo 726324 1226677 := bbase (se 5 (by rfl) ⟨57500, by rfl⟩ : syracuseStep 1226677 = 115001) (by norm_num)
theorem B1226765 : Blo 726324 1226765 := bbase (se 3 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 1226765 = 460037) (by norm_num)
theorem B5617781 : Blo 726324 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B1751165 : Blo 726324 1751165 := bbase (se 3 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 1751165 = 656687) (by norm_num)
theorem B1554565 : Blo 726324 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B1226893 : Blo 726324 1226893 := bbase (se 3 (by rfl) ⟨230042, by rfl⟩ : syracuseStep 1226893 = 460085) (by norm_num)
theorem B1226981 : Blo 726324 1226981 := bbase (se 4 (by rfl) ⟨115029, by rfl⟩ : syracuseStep 1226981 = 230059) (by norm_num)
theorem B1227109 : Blo 726324 1227109 := bbase (se 4 (by rfl) ⟨115041, by rfl⟩ : syracuseStep 1227109 = 230083) (by norm_num)
theorem B3160421 : Blo 726324 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B1227197 : Blo 726324 1227197 := bbase (se 3 (by rfl) ⟨230099, by rfl⟩ : syracuseStep 1227197 = 460199) (by norm_num)
theorem B1751557 : Blo 726324 1751557 := bbase (se 4 (by rfl) ⟨164208, by rfl⟩ : syracuseStep 1751557 = 328417) (by norm_num)
theorem B1227325 : Blo 726324 1227325 := bbase (se 3 (by rfl) ⟨230123, by rfl⟩ : syracuseStep 1227325 = 460247) (by norm_num)
theorem B1686101 : Blo 726324 1686101 := bbase (se 8 (by rfl) ⟨9879, by rfl⟩ : syracuseStep 1686101 = 19759) (by norm_num)
theorem B1227413 : Blo 726324 1227413 := bbase (se 6 (by rfl) ⟨28767, by rfl⟩ : syracuseStep 1227413 = 57535) (by norm_num)
theorem B3685013 : Blo 726324 3685013 := bbase (se 6 (by rfl) ⟨86367, by rfl⟩ : syracuseStep 3685013 = 172735) (by norm_num)
theorem B4143797 : Blo 726324 4143797 := bbase (se 5 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 4143797 = 388481) (by norm_num)
theorem B1227541 : Blo 726324 1227541 := bbase (se 6 (by rfl) ⟨28770, by rfl⟩ : syracuseStep 1227541 = 57541) (by norm_num)
theorem B1227629 : Blo 726324 1227629 := bbase (se 3 (by rfl) ⟨230180, by rfl⟩ : syracuseStep 1227629 = 460361) (by norm_num)
theorem B2079701 : Blo 726324 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B1227757 : Blo 726324 1227757 := bbase (se 3 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 1227757 = 460409) (by norm_num)
theorem B1260533 : Blo 726324 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1555453 : Blo 726324 1555453 := bbase (se 3 (by rfl) ⟨291647, by rfl⟩ : syracuseStep 1555453 = 583295) (by norm_num)
theorem B2767877 : Blo 726324 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B1227845 : Blo 726324 1227845 := bbase (se 4 (by rfl) ⟨115110, by rfl⟩ : syracuseStep 1227845 = 230221) (by norm_num)
theorem B1227973 : Blo 726324 1227973 := bbase (se 4 (by rfl) ⟨115122, by rfl⟩ : syracuseStep 1227973 = 230245) (by norm_num)
theorem B6208757 : Blo 726324 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B1228061 : Blo 726324 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B2768165 : Blo 726324 2768165 := bbase (se 4 (by rfl) ⟨259515, by rfl⟩ : syracuseStep 2768165 = 519031) (by norm_num)
theorem B1228189 : Blo 726324 1228189 := bbase (se 3 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 1228189 = 460571) (by norm_num)
theorem B933289 : Blo 726324 933289 := bbase (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) (by norm_num)
theorem B1555949 : Blo 726324 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B1228277 : Blo 726324 1228277 := bbase (se 5 (by rfl) ⟨57575, by rfl⟩ : syracuseStep 1228277 = 115151) (by norm_num)
theorem B2211365 : Blo 726324 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B1752653 : Blo 726324 1752653 := bbase (se 3 (by rfl) ⟨328622, by rfl⟩ : syracuseStep 1752653 = 657245) (by norm_num)
theorem B1228405 : Blo 726324 1228405 := bbase (se 5 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 1228405 = 115163) (by norm_num)
theorem B1228493 : Blo 726324 1228493 := bbase (se 3 (by rfl) ⟨230342, by rfl⟩ : syracuseStep 1228493 = 460685) (by norm_num)
theorem B1228621 : Blo 726324 1228621 := bbase (se 3 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 1228621 = 460733) (by norm_num)
theorem B1752941 : Blo 726324 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B1228709 : Blo 726324 1228709 := bbase (se 4 (by rfl) ⟨115191, by rfl⟩ : syracuseStep 1228709 = 230383) (by norm_num)
theorem B3686309 : Blo 726324 3686309 := bbase (se 4 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 3686309 = 691183) (by norm_num)
theorem B1228837 : Blo 726324 1228837 := bbase (se 4 (by rfl) ⟨115203, by rfl⟩ : syracuseStep 1228837 = 230407) (by norm_num)
theorem B1228925 : Blo 726324 1228925 := bbase (se 3 (by rfl) ⟨230423, by rfl⟩ : syracuseStep 1228925 = 460847) (by norm_num)
theorem B1229053 : Blo 726324 1229053 := bbase (se 3 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 1229053 = 460895) (by norm_num)
theorem B1229141 : Blo 726324 1229141 := bbase (se 10 (by rfl) ⟨1800, by rfl⟩ : syracuseStep 1229141 = 3601) (by norm_num)
theorem B1556837 : Blo 726324 1556837 := bbase (se 4 (by rfl) ⟨145953, by rfl⟩ : syracuseStep 1556837 = 291907) (by norm_num)
theorem B2769349 : Blo 726324 2769349 := bbase (se 4 (by rfl) ⟨259626, by rfl⟩ : syracuseStep 2769349 = 519253) (by norm_num)
theorem B934357 : Blo 726324 934357 := bbase (se 7 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 934357 = 21899) (by norm_num)
theorem B1229269 : Blo 726324 1229269 := bbase (se 7 (by rfl) ⟨14405, by rfl⟩ : syracuseStep 1229269 = 28811) (by norm_num)
theorem B1556957 : Blo 726324 1556957 := bbase (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) (by norm_num)
theorem B1229357 : Blo 726324 1229357 := bbase (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) (by norm_num)
theorem B1000021 : Blo 726324 1000021 := bbase (se 8 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 1000021 = 11719) (by norm_num)
theorem B3981973 : Blo 726324 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B1229485 : Blo 726324 1229485 := bbase (se 3 (by rfl) ⟨230528, by rfl⟩ : syracuseStep 1229485 = 461057) (by norm_num)
theorem B2769653 : Blo 726324 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1229573 : Blo 726324 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B4146005 : Blo 726324 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B1229701 : Blo 726324 1229701 := bbase (se 4 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 1229701 = 230569) (by norm_num)
theorem B1229789 : Blo 726324 1229789 := bbase (se 3 (by rfl) ⟨230585, by rfl⟩ : syracuseStep 1229789 = 461171) (by norm_num)
theorem B1557589 : Blo 726324 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B1229917 : Blo 726324 1229917 := bbase (se 3 (by rfl) ⟨230609, by rfl⟩ : syracuseStep 1229917 = 461219) (by norm_num)
theorem B3687605 : Blo 726324 3687605 := bbase (se 5 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 3687605 = 345713) (by norm_num)
theorem B1230005 : Blo 726324 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B3491045 : Blo 726324 3491045 := bbase (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) (by norm_num)
theorem B1230133 : Blo 726324 1230133 := bbase (se 5 (by rfl) ⟨57662, by rfl⟩ : syracuseStep 1230133 = 115325) (by norm_num)
theorem B1164629 : Blo 726324 1164629 := bbase (se 12 (by rfl) ⟨426, by rfl⟩ : syracuseStep 1164629 = 853) (by norm_num)
theorem B1230221 : Blo 726324 1230221 := bbase (se 3 (by rfl) ⟨230666, by rfl⟩ : syracuseStep 1230221 = 461333) (by norm_num)
theorem B1230349 : Blo 726324 1230349 := bbase (se 3 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 1230349 = 461381) (by norm_num)
theorem B1230437 : Blo 726324 1230437 := bbase (se 4 (by rfl) ⟨115353, by rfl⟩ : syracuseStep 1230437 = 230707) (by norm_num)
theorem B1230565 : Blo 726324 1230565 := bbase (se 4 (by rfl) ⟨115365, by rfl⟩ : syracuseStep 1230565 = 230731) (by norm_num)
theorem B1230653 : Blo 726324 1230653 := bbase (se 3 (by rfl) ⟨230747, by rfl⟩ : syracuseStep 1230653 = 461495) (by norm_num)
theorem B1230781 : Blo 726324 1230781 := bbase (se 3 (by rfl) ⟨230771, by rfl⟩ : syracuseStep 1230781 = 461543) (by norm_num)
theorem B1558477 : Blo 726324 1558477 := bbase (se 3 (by rfl) ⟨292214, by rfl⟩ : syracuseStep 1558477 = 584429) (by norm_num)
theorem B1230869 : Blo 726324 1230869 := bbase (se 6 (by rfl) ⟨28848, by rfl⟩ : syracuseStep 1230869 = 57697) (by norm_num)
theorem B1034309 : Blo 726324 1034309 := bbase (se 4 (by rfl) ⟨96966, by rfl⟩ : syracuseStep 1034309 = 193933) (by norm_num)
theorem B1558597 : Blo 726324 1558597 := bbase (se 4 (by rfl) ⟨146118, by rfl⟩ : syracuseStep 1558597 = 292237) (by norm_num)
theorem B1230997 : Blo 726324 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B1231085 : Blo 726324 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B1165565 : Blo 726324 1165565 := bbase (se 3 (by rfl) ⟨218543, by rfl⟩ : syracuseStep 1165565 = 437087) (by norm_num)
theorem B9324821 : Blo 726324 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B1558853 : Blo 726324 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1231213 : Blo 726324 1231213 := bbase (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) (by norm_num)
theorem B8309141 : Blo 726324 8309141 := bbase (se 6 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 8309141 = 389491) (by norm_num)
theorem B3688901 : Blo 726324 3688901 := bbase (se 4 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 3688901 = 691669) (by norm_num)
theorem B1231301 : Blo 726324 1231301 := bbase (se 4 (by rfl) ⟨115434, by rfl⟩ : syracuseStep 1231301 = 230869) (by norm_num)
theorem B3492389 : Blo 726324 3492389 := bbase (se 4 (by rfl) ⟨327411, by rfl⟩ : syracuseStep 3492389 = 654823) (by norm_num)
theorem B2214469 : Blo 726324 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B1231429 : Blo 726324 1231429 := bbase (se 4 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 1231429 = 230893) (by norm_num)
theorem B1034861 : Blo 726324 1034861 := bbase (se 3 (by rfl) ⟨194036, by rfl⟩ : syracuseStep 1034861 = 388073) (by norm_num)
theorem B1231517 : Blo 726324 1231517 := bbase (se 3 (by rfl) ⟨230909, by rfl⟩ : syracuseStep 1231517 = 461819) (by norm_num)
theorem B9358037 : Blo 726324 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B1231645 : Blo 726324 1231645 := bbase (se 3 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 1231645 = 461867) (by norm_num)
theorem B2771765 : Blo 726324 2771765 := bbase (se 5 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 2771765 = 259853) (by norm_num)
theorem B1231733 : Blo 726324 1231733 := bbase (se 5 (by rfl) ⟨57737, by rfl⟩ : syracuseStep 1231733 = 115475) (by norm_num)
theorem B1166213 : Blo 726324 1166213 := bbase (se 4 (by rfl) ⟨109332, by rfl⟩ : syracuseStep 1166213 = 218665) (by norm_num)
theorem B1657813 : Blo 726324 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B1231861 : Blo 726324 1231861 := bbase (se 5 (by rfl) ⟨57743, by rfl⟩ : syracuseStep 1231861 = 115487) (by norm_num)
theorem B1231949 : Blo 726324 1231949 := bbase (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) (by norm_num)
theorem B2772053 : Blo 726324 2772053 := bbase (se 8 (by rfl) ⟨16242, by rfl⟩ : syracuseStep 2772053 = 32485) (by norm_num)
theorem B1559741 : Blo 726324 1559741 := bbase (se 3 (by rfl) ⟨292451, by rfl⟩ : syracuseStep 1559741 = 584903) (by norm_num)
theorem B1232077 : Blo 726324 1232077 := bbase (se 3 (by rfl) ⟨231014, by rfl⟩ : syracuseStep 1232077 = 462029) (by norm_num)
theorem B1232165 : Blo 726324 1232165 := bbase (se 4 (by rfl) ⟨115515, by rfl⟩ : syracuseStep 1232165 = 231031) (by norm_num)
theorem B1035613 : Blo 726324 1035613 := bbase (se 3 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 1035613 = 388355) (by norm_num)
theorem B1232293 : Blo 726324 1232293 := bbase (se 4 (by rfl) ⟨115527, by rfl⟩ : syracuseStep 1232293 = 231055) (by norm_num)
theorem B1232381 : Blo 726324 1232381 := bbase (se 3 (by rfl) ⟨231071, by rfl⟩ : syracuseStep 1232381 = 462143) (by norm_num)
theorem B1330805 : Blo 726324 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B2215637 : Blo 726324 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B3690197 : Blo 726324 3690197 := bbase (se 7 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 3690197 = 86489) (by norm_num)
theorem B5525333 : Blo 726324 5525333 := bbase (se 9 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 5525333 = 32375) (by norm_num)
theorem B1167205 : Blo 726324 1167205 := bbase (se 4 (by rfl) ⟨109425, by rfl⟩ : syracuseStep 1167205 = 218851) (by norm_num)
theorem B5918741 : Blo 726324 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B1036405 : Blo 726324 1036405 := bbase (se 5 (by rfl) ⟨48581, by rfl⟩ : syracuseStep 1036405 = 97163) (by norm_num)
theorem B1659037 : Blo 726324 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B1167653 : Blo 726324 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B872857 : Blo 726324 872857 := bbase (se 2 (by rfl) ⟨327321, by rfl⟩ : syracuseStep 872857 = 654643) (by norm_num)
theorem B1036741 : Blo 726324 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B1167853 : Blo 726324 1167853 := bbase (se 3 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 1167853 = 437945) (by norm_num)
theorem B873049 : Blo 726324 873049 := bbase (se 2 (by rfl) ⟨327393, by rfl⟩ : syracuseStep 873049 = 654787) (by norm_num)
theorem B1036957 : Blo 726324 1036957 := bbase (se 3 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 1036957 = 388859) (by norm_num)
theorem B840389 : Blo 726324 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B1168109 : Blo 726324 1168109 := bbase (se 3 (by rfl) ⟨219020, by rfl⟩ : syracuseStep 1168109 = 438041) (by norm_num)
theorem B840449 : Blo 726324 840449 := bbase (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) (by norm_num)
theorem B3691493 : Blo 726324 3691493 := bbase (se 4 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 3691493 = 692155) (by norm_num)
theorem B1037333 : Blo 726324 1037333 := bbase (se 6 (by rfl) ⟨24312, by rfl⟩ : syracuseStep 1037333 = 48625) (by norm_num)
theorem B873929 : Blo 726324 873929 := bbase (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) (by norm_num)
theorem B775813 : Blo 726324 775813 := bbase (se 4 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 775813 = 145465) (by norm_num)
theorem B775937 : Blo 726324 775937 := bbase (se 2 (by rfl) ⟨290976, by rfl⟩ : syracuseStep 775937 = 581953) (by norm_num)
theorem B1660733 : Blo 726324 1660733 := bbase (se 3 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 1660733 = 622775) (by norm_num)
theorem B3102533 : Blo 726324 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B1169237 : Blo 726324 1169237 := bbase (se 9 (by rfl) ⟨3425, by rfl⟩ : syracuseStep 1169237 = 6851) (by norm_num)
theorem B874433 : Blo 726324 874433 := bbase (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) (by norm_num)
theorem B874481 : Blo 726324 874481 := bbase (se 2 (by rfl) ⟨327930, by rfl⟩ : syracuseStep 874481 = 655861) (by norm_num)
theorem B776189 : Blo 726324 776189 := bbase (se 3 (by rfl) ⟨145535, by rfl⟩ : syracuseStep 776189 = 291071) (by norm_num)
theorem B1660933 : Blo 726324 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B3496117 : Blo 726324 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B874741 : Blo 726324 874741 := bbase (se 5 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 874741 = 82007) (by norm_num)
theorem B3692789 : Blo 726324 3692789 := bbase (se 5 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 3692789 = 346199) (by norm_num)
theorem B1169749 : Blo 726324 1169749 := bbase (se 10 (by rfl) ⟨1713, by rfl⟩ : syracuseStep 1169749 = 3427) (by norm_num)
theorem B2218373 : Blo 726324 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B1038757 : Blo 726324 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B776633 : Blo 726324 776633 := bbase (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) (by norm_num)
theorem B875005 : Blo 726324 875005 := bbase (se 3 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 875005 = 328127) (by norm_num)
theorem B3103285 : Blo 726324 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B875125 : Blo 726324 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B776881 : Blo 726324 776881 := bbase (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) (by norm_num)
theorem B1399621 : Blo 726324 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B1039349 : Blo 726324 1039349 := bbase (se 5 (by rfl) ⟨48719, by rfl⟩ : syracuseStep 1039349 = 97439) (by norm_num)
theorem B1039429 : Blo 726324 1039429 := bbase (se 4 (by rfl) ⟨97446, by rfl⟩ : syracuseStep 1039429 = 194893) (by norm_num)
theorem B777325 : Blo 726324 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B6216821 : Blo 726324 6216821 := bbase (se 5 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 6216821 = 582827) (by norm_num)
theorem B777385 : Blo 726324 777385 := bbase (se 2 (by rfl) ⟨291519, by rfl⟩ : syracuseStep 777385 = 583039) (by norm_num)
theorem B1399997 : Blo 726324 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1039549 : Blo 726324 1039549 := bbase (se 3 (by rfl) ⟨194915, by rfl⟩ : syracuseStep 1039549 = 389831) (by norm_num)
theorem B3104021 : Blo 726324 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B1039645 : Blo 726324 1039645 := bbase (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) (by norm_num)
theorem B875981 : Blo 726324 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B777701 : Blo 726324 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B3694085 : Blo 726324 3694085 := bbase (se 4 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 3694085 = 692641) (by norm_num)
theorem B4677173 : Blo 726324 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B1400429 : Blo 726324 1400429 := bbase (se 3 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 1400429 = 525161) (by norm_num)
theorem B1793669 : Blo 726324 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1105805 : Blo 726324 1105805 := bbase (se 3 (by rfl) ⟨207338, by rfl⟩ : syracuseStep 1105805 = 414677) (by norm_num)
theorem B778145 : Blo 726324 778145 := bbase (se 2 (by rfl) ⟨291804, by rfl⟩ : syracuseStep 778145 = 583609) (by norm_num)
theorem B1105829 : Blo 726324 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B778205 : Blo 726324 778205 := bbase (se 3 (by rfl) ⟨145913, by rfl⟩ : syracuseStep 778205 = 291827) (by norm_num)
theorem B778333 : Blo 726324 778333 := bbase (se 3 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 778333 = 291875) (by norm_num)
theorem B843869 : Blo 726324 843869 := bbase (se 3 (by rfl) ⟨158225, by rfl⟩ : syracuseStep 843869 = 316451) (by norm_num)
theorem B876701 : Blo 726324 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B1401013 : Blo 726324 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B877009 : Blo 726324 877009 := bbase (se 2 (by rfl) ⟨328878, by rfl⟩ : syracuseStep 877009 = 657757) (by norm_num)
theorem B1106389 : Blo 726324 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B778777 : Blo 726324 778777 := bbase (se 2 (by rfl) ⟨292041, by rfl⟩ : syracuseStep 778777 = 584083) (by norm_num)
theorem B877105 : Blo 726324 877105 := bbase (se 2 (by rfl) ⟨328914, by rfl⟩ : syracuseStep 877105 = 657829) (by norm_num)
theorem B1892965 : Blo 726324 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B811661 : Blo 726324 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B778897 : Blo 726324 778897 := bbase (se 2 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 778897 = 584173) (by norm_num)
theorem B877249 : Blo 726324 877249 := bbase (se 2 (by rfl) ⟨328968, by rfl⟩ : syracuseStep 877249 = 657937) (by norm_num)
theorem B3695381 : Blo 726324 3695381 := bbase (se 6 (by rfl) ⟨86610, by rfl⟩ : syracuseStep 3695381 = 173221) (by norm_num)
theorem B779149 : Blo 726324 779149 := bbase (se 3 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 779149 = 292181) (by norm_num)
theorem B779153 : Blo 726324 779153 := bbase (se 2 (by rfl) ⟨292182, by rfl⟩ : syracuseStep 779153 = 584365) (by norm_num)
theorem B819193 : Blo 726324 819193 := bbase (se 2 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 819193 = 614395) (by norm_num)
theorem B1663997 : Blo 726324 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B3368213 : Blo 726324 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B1500493 : Blo 726324 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B779717 : Blo 726324 779717 := bbase (se 4 (by rfl) ⟨73098, by rfl⟩ : syracuseStep 779717 = 146197) (by norm_num)
theorem B1402645 : Blo 726324 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B10512341 : Blo 726324 10512341 := bbase (se 7 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 10512341 = 246383) (by norm_num)
theorem B3696677 : Blo 726324 3696677 := bbase (se 4 (by rfl) ⟨346563, by rfl⟩ : syracuseStep 3696677 = 693127) (by norm_num)
theorem B3500117 : Blo 726324 3500117 := bbase (se 8 (by rfl) ⟨20508, by rfl⟩ : syracuseStep 3500117 = 41017) (by norm_num)
theorem B2451653 : Blo 726324 2451653 := bbase (se 4 (by rfl) ⟨229842, by rfl⟩ : syracuseStep 2451653 = 459685) (by norm_num)
theorem B1010053 : Blo 726324 1010053 := bbase (se 4 (by rfl) ⟨94692, by rfl⟩ : syracuseStep 1010053 = 189385) (by norm_num)
theorem B1599925 : Blo 726324 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B3107317 : Blo 726324 3107317 := bbase (se 5 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 3107317 = 291311) (by norm_num)
theorem B4155893 : Blo 726324 4155893 := bbase (se 5 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 4155893 = 389615) (by norm_num)
theorem B2452085 : Blo 726324 2452085 := bbase (se 5 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 2452085 = 229883) (by norm_num)
theorem B5892821 : Blo 726324 5892821 := bbase (se 7 (by rfl) ⟨69056, by rfl⟩ : syracuseStep 5892821 = 138113) (by norm_num)
theorem B2452517 : Blo 726324 2452517 := bbase (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) (by norm_num)
theorem B1109053 : Blo 726324 1109053 := bbase (se 3 (by rfl) ⟨207947, by rfl⟩ : syracuseStep 1109053 = 415895) (by norm_num)
theorem B945329 : Blo 726324 945329 := bbase (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) (by norm_num)
theorem B3501269 : Blo 726324 3501269 := bbase (se 7 (by rfl) ⟨41030, by rfl⟩ : syracuseStep 3501269 = 82061) (by norm_num)
theorem B3796325 : Blo 726324 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B5533109 : Blo 726324 5533109 := bbase (se 5 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 5533109 = 518729) (by norm_num)
theorem B2452949 : Blo 726324 2452949 := bbase (se 7 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 2452949 = 57491) (by norm_num)
theorem B1109717 : Blo 726324 1109717 := bbase (se 7 (by rfl) ⟨13004, by rfl⟩ : syracuseStep 1109717 = 26009) (by norm_num)
theorem B2453381 : Blo 726324 2453381 := bbase (se 4 (by rfl) ⟨230004, by rfl⟩ : syracuseStep 2453381 = 460009) (by norm_num)
theorem B1634237 : Blo 726324 1634237 := bbase (se 3 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 1634237 = 612839) (by norm_num)
theorem B3502037 : Blo 726324 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B1634309 : Blo 726324 1634309 := bbase (se 4 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 1634309 = 306433) (by norm_num)
theorem B1634381 : Blo 726324 1634381 := bbase (se 3 (by rfl) ⟨306446, by rfl⟩ : syracuseStep 1634381 = 612893) (by norm_num)
theorem B1405045 : Blo 726324 1405045 := bbase (se 5 (by rfl) ⟨65861, by rfl⟩ : syracuseStep 1405045 = 131723) (by norm_num)
theorem B1634453 : Blo 726324 1634453 := bbase (se 6 (by rfl) ⟨38307, by rfl⟩ : syracuseStep 1634453 = 76615) (by norm_num)
theorem B1863869 : Blo 726324 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B1634525 : Blo 726324 1634525 := bbase (se 3 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 1634525 = 612947) (by norm_num)
theorem B1634597 : Blo 726324 1634597 := bbase (se 4 (by rfl) ⟨153243, by rfl⟩ : syracuseStep 1634597 = 306487) (by norm_num)
theorem B2453813 : Blo 726324 2453813 := bbase (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) (by norm_num)
theorem B1634669 : Blo 726324 1634669 := bbase (se 3 (by rfl) ⟨306500, by rfl⟩ : syracuseStep 1634669 = 613001) (by norm_num)
theorem B1634741 : Blo 726324 1634741 := bbase (se 5 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 1634741 = 153257) (by norm_num)
theorem B1634813 : Blo 726324 1634813 := bbase (se 3 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 1634813 = 613055) (by norm_num)
theorem B1634885 : Blo 726324 1634885 := bbase (se 4 (by rfl) ⟨153270, by rfl⟩ : syracuseStep 1634885 = 306541) (by norm_num)
theorem B1634957 : Blo 726324 1634957 := bbase (se 3 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 1634957 = 613109) (by norm_num)
theorem B1635029 : Blo 726324 1635029 := bbase (se 7 (by rfl) ⟨19160, by rfl⟩ : syracuseStep 1635029 = 38321) (by norm_num)
theorem B2454245 : Blo 726324 2454245 := bbase (se 4 (by rfl) ⟨230085, by rfl⟩ : syracuseStep 2454245 = 460171) (by norm_num)
theorem B1635101 : Blo 726324 1635101 := bbase (se 3 (by rfl) ⟨306581, by rfl⟩ : syracuseStep 1635101 = 613163) (by norm_num)
theorem B3371813 : Blo 726324 3371813 := bbase (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) (by norm_num)
theorem B1635173 : Blo 726324 1635173 := bbase (se 4 (by rfl) ⟨153297, by rfl⟩ : syracuseStep 1635173 = 306595) (by norm_num)
theorem B1635245 : Blo 726324 1635245 := bbase (se 3 (by rfl) ⟨306608, by rfl⟩ : syracuseStep 1635245 = 613217) (by norm_num)
theorem B1635317 : Blo 726324 1635317 := bbase (se 5 (by rfl) ⟨76655, by rfl⟩ : syracuseStep 1635317 = 153311) (by norm_num)
theorem B1635389 : Blo 726324 1635389 := bbase (se 3 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 1635389 = 613271) (by norm_num)
theorem B1635461 : Blo 726324 1635461 := bbase (se 4 (by rfl) ⟨153324, by rfl⟩ : syracuseStep 1635461 = 306649) (by norm_num)
theorem B2454677 : Blo 726324 2454677 := bbase (se 6 (by rfl) ⟨57531, by rfl⟩ : syracuseStep 2454677 = 115063) (by norm_num)
theorem B1635533 : Blo 726324 1635533 := bbase (se 3 (by rfl) ⟨306662, by rfl⟩ : syracuseStep 1635533 = 613325) (by norm_num)
theorem B1635605 : Blo 726324 1635605 := bbase (se 6 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 1635605 = 76669) (by norm_num)
theorem B1635677 : Blo 726324 1635677 := bbase (se 3 (by rfl) ⟨306689, by rfl⟩ : syracuseStep 1635677 = 613379) (by norm_num)
theorem B1635749 : Blo 726324 1635749 := bbase (se 4 (by rfl) ⟨153351, by rfl⟩ : syracuseStep 1635749 = 306703) (by norm_num)
theorem B3110309 : Blo 726324 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B1635821 : Blo 726324 1635821 := bbase (se 3 (by rfl) ⟨306716, by rfl⟩ : syracuseStep 1635821 = 613433) (by norm_num)
theorem B1635893 : Blo 726324 1635893 := bbase (se 5 (by rfl) ⟨76682, by rfl⟩ : syracuseStep 1635893 = 153365) (by norm_num)
theorem B2455109 : Blo 726324 2455109 := bbase (se 4 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 2455109 = 460333) (by norm_num)
theorem B1635965 : Blo 726324 1635965 := bbase (se 3 (by rfl) ⟨306743, by rfl⟩ : syracuseStep 1635965 = 613487) (by norm_num)
theorem B1636037 : Blo 726324 1636037 := bbase (se 4 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 1636037 = 306757) (by norm_num)
theorem B1636109 : Blo 726324 1636109 := bbase (se 3 (by rfl) ⟨306770, by rfl⟩ : syracuseStep 1636109 = 613541) (by norm_num)
theorem B1636181 : Blo 726324 1636181 := bbase (se 9 (by rfl) ⟨4793, by rfl⟩ : syracuseStep 1636181 = 9587) (by norm_num)
theorem B1636253 : Blo 726324 1636253 := bbase (se 3 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 1636253 = 613595) (by norm_num)
theorem B1636325 : Blo 726324 1636325 := bbase (se 4 (by rfl) ⟨153405, by rfl⟩ : syracuseStep 1636325 = 306811) (by norm_num)
theorem B817141 : Blo 726324 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B2455541 : Blo 726324 2455541 := bbase (se 5 (by rfl) ⟨115103, by rfl⟩ : syracuseStep 2455541 = 230207) (by norm_num)
theorem B1472509 : Blo 726324 1472509 := bbase (se 3 (by rfl) ⟨276095, by rfl⟩ : syracuseStep 1472509 = 552191) (by norm_num)
theorem B817177 : Blo 726324 817177 := bbase (se 2 (by rfl) ⟨306441, by rfl⟩ : syracuseStep 817177 = 612883) (by norm_num)
theorem B1636397 : Blo 726324 1636397 := bbase (se 3 (by rfl) ⟨306824, by rfl⟩ : syracuseStep 1636397 = 613649) (by norm_num)
theorem B817213 : Blo 726324 817213 := bbase (se 3 (by rfl) ⟨153227, by rfl⟩ : syracuseStep 817213 = 306455) (by norm_num)
theorem B817249 : Blo 726324 817249 := bbase (se 2 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 817249 = 612937) (by norm_num)
theorem B1636469 : Blo 726324 1636469 := bbase (se 5 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 1636469 = 153419) (by norm_num)
theorem B817285 : Blo 726324 817285 := bbase (se 4 (by rfl) ⟨76620, by rfl⟩ : syracuseStep 817285 = 153241) (by norm_num)
theorem B817321 : Blo 726324 817321 := bbase (se 2 (by rfl) ⟨306495, by rfl⟩ : syracuseStep 817321 = 612991) (by norm_num)
theorem B1636541 : Blo 726324 1636541 := bbase (se 3 (by rfl) ⟨306851, by rfl⟩ : syracuseStep 1636541 = 613703) (by norm_num)
theorem B817357 : Blo 726324 817357 := bbase (se 3 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 817357 = 306509) (by norm_num)
theorem B817393 : Blo 726324 817393 := bbase (se 2 (by rfl) ⟨306522, by rfl⟩ : syracuseStep 817393 = 613045) (by norm_num)
theorem B1636613 : Blo 726324 1636613 := bbase (se 4 (by rfl) ⟨153432, by rfl⟩ : syracuseStep 1636613 = 306865) (by norm_num)
theorem B817429 : Blo 726324 817429 := bbase (se 6 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 817429 = 38317) (by norm_num)
theorem B817465 : Blo 726324 817465 := bbase (se 2 (by rfl) ⟨306549, by rfl⟩ : syracuseStep 817465 = 613099) (by norm_num)
theorem B1308997 : Blo 726324 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B1636685 : Blo 726324 1636685 := bbase (se 3 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 1636685 = 613757) (by norm_num)
theorem B817501 : Blo 726324 817501 := bbase (se 3 (by rfl) ⟨153281, by rfl⟩ : syracuseStep 817501 = 306563) (by norm_num)
theorem B1964405 : Blo 726324 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B817537 : Blo 726324 817537 := bbase (se 2 (by rfl) ⟨306576, by rfl⟩ : syracuseStep 817537 = 613153) (by norm_num)
theorem B1636757 : Blo 726324 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B3111317 : Blo 726324 3111317 := bbase (se 6 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 3111317 = 145843) (by norm_num)
theorem B817573 : Blo 726324 817573 := bbase (se 4 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 817573 = 153295) (by norm_num)
theorem B2455973 : Blo 726324 2455973 := bbase (se 4 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 2455973 = 460495) (by norm_num)
theorem B1997237 : Blo 726324 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B817609 : Blo 726324 817609 := bbase (se 2 (by rfl) ⟨306603, by rfl⟩ : syracuseStep 817609 = 613207) (by norm_num)
theorem B1636829 : Blo 726324 1636829 := bbase (se 3 (by rfl) ⟨306905, by rfl⟩ : syracuseStep 1636829 = 613811) (by norm_num)
theorem B817645 : Blo 726324 817645 := bbase (se 3 (by rfl) ⟨153308, by rfl⟩ : syracuseStep 817645 = 306617) (by norm_num)
theorem B817681 : Blo 726324 817681 := bbase (se 2 (by rfl) ⟨306630, by rfl⟩ : syracuseStep 817681 = 613261) (by norm_num)
theorem B1243669 : Blo 726324 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1636901 : Blo 726324 1636901 := bbase (se 4 (by rfl) ⟨153459, by rfl⟩ : syracuseStep 1636901 = 306919) (by norm_num)
theorem B817717 : Blo 726324 817717 := bbase (se 5 (by rfl) ⟨38330, by rfl⟩ : syracuseStep 817717 = 76661) (by norm_num)
theorem B817753 : Blo 726324 817753 := bbase (se 2 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 817753 = 613315) (by norm_num)
theorem B1636973 : Blo 726324 1636973 := bbase (se 3 (by rfl) ⟨306932, by rfl⟩ : syracuseStep 1636973 = 613865) (by norm_num)
theorem B817789 : Blo 726324 817789 := bbase (se 3 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 817789 = 306671) (by norm_num)
theorem B817825 : Blo 726324 817825 := bbase (se 2 (by rfl) ⟨306684, by rfl⟩ : syracuseStep 817825 = 613369) (by norm_num)
theorem B1637045 : Blo 726324 1637045 := bbase (se 5 (by rfl) ⟨76736, by rfl⟩ : syracuseStep 1637045 = 153473) (by norm_num)
theorem B817861 : Blo 726324 817861 := bbase (se 4 (by rfl) ⟨76674, by rfl⟩ : syracuseStep 817861 = 153349) (by norm_num)
theorem B817897 : Blo 726324 817897 := bbase (se 2 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 817897 = 613423) (by norm_num)
theorem B1637117 : Blo 726324 1637117 := bbase (se 3 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 1637117 = 613919) (by norm_num)
theorem B817933 : Blo 726324 817933 := bbase (se 3 (by rfl) ⟨153362, by rfl⟩ : syracuseStep 817933 = 306725) (by norm_num)
theorem B1964837 : Blo 726324 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B817969 : Blo 726324 817969 := bbase (se 2 (by rfl) ⟨306738, by rfl⟩ : syracuseStep 817969 = 613477) (by norm_num)
theorem B1637189 : Blo 726324 1637189 := bbase (se 4 (by rfl) ⟨153486, by rfl⟩ : syracuseStep 1637189 = 306973) (by norm_num)
theorem B818005 : Blo 726324 818005 := bbase (se 9 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 818005 = 4793) (by norm_num)
theorem B2456405 : Blo 726324 2456405 := bbase (se 9 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 2456405 = 14393) (by norm_num)
theorem B818041 : Blo 726324 818041 := bbase (se 2 (by rfl) ⟨306765, by rfl⟩ : syracuseStep 818041 = 613531) (by norm_num)
theorem B1637261 : Blo 726324 1637261 := bbase (se 3 (by rfl) ⟨306986, by rfl⟩ : syracuseStep 1637261 = 613973) (by norm_num)
theorem B818077 : Blo 726324 818077 := bbase (se 3 (by rfl) ⟨153389, by rfl⟩ : syracuseStep 818077 = 306779) (by norm_num)
theorem B818113 : Blo 726324 818113 := bbase (se 2 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 818113 = 613585) (by norm_num)
theorem B1637333 : Blo 726324 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B818149 : Blo 726324 818149 := bbase (se 4 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 818149 = 153403) (by norm_num)
theorem B818185 : Blo 726324 818185 := bbase (se 2 (by rfl) ⟨306819, by rfl⟩ : syracuseStep 818185 = 613639) (by norm_num)
theorem B1637405 : Blo 726324 1637405 := bbase (se 3 (by rfl) ⟨307013, by rfl⟩ : syracuseStep 1637405 = 614027) (by norm_num)
theorem B818221 : Blo 726324 818221 := bbase (se 3 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 818221 = 306833) (by norm_num)
theorem B818257 : Blo 726324 818257 := bbase (se 2 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 818257 = 613693) (by norm_num)
theorem B1637477 : Blo 726324 1637477 := bbase (se 4 (by rfl) ⟨153513, by rfl⟩ : syracuseStep 1637477 = 307027) (by norm_num)
theorem B2948213 : Blo 726324 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B818293 : Blo 726324 818293 := bbase (se 5 (by rfl) ⟨38357, by rfl⟩ : syracuseStep 818293 = 76715) (by norm_num)
theorem B3734677 : Blo 726324 3734677 := bbase (se 6 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 3734677 = 175063) (by norm_num)
theorem B818329 : Blo 726324 818329 := bbase (se 2 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 818329 = 613747) (by norm_num)
theorem B1637549 : Blo 726324 1637549 := bbase (se 3 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 1637549 = 614081) (by norm_num)
theorem B818365 : Blo 726324 818365 := bbase (se 3 (by rfl) ⟨153443, by rfl⟩ : syracuseStep 818365 = 306887) (by norm_num)
theorem B818401 : Blo 726324 818401 := bbase (se 2 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 818401 = 613801) (by norm_num)
theorem B1637621 : Blo 726324 1637621 := bbase (se 5 (by rfl) ⟨76763, by rfl⟩ : syracuseStep 1637621 = 153527) (by norm_num)
theorem B818437 : Blo 726324 818437 := bbase (se 4 (by rfl) ⟨76728, by rfl⟩ : syracuseStep 818437 = 153457) (by norm_num)
theorem B2456837 : Blo 726324 2456837 := bbase (se 4 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 2456837 = 460657) (by norm_num)
theorem B818473 : Blo 726324 818473 := bbase (se 2 (by rfl) ⟨306927, by rfl⟩ : syracuseStep 818473 = 613855) (by norm_num)
theorem B1637693 : Blo 726324 1637693 := bbase (se 3 (by rfl) ⟨307067, by rfl⟩ : syracuseStep 1637693 = 614135) (by norm_num)
theorem B818509 : Blo 726324 818509 := bbase (se 3 (by rfl) ⟨153470, by rfl⟩ : syracuseStep 818509 = 306941) (by norm_num)
theorem B818545 : Blo 726324 818545 := bbase (se 2 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 818545 = 613909) (by norm_num)
theorem B1637765 : Blo 726324 1637765 := bbase (se 4 (by rfl) ⟨153540, by rfl⟩ : syracuseStep 1637765 = 307081) (by norm_num)
theorem B818581 : Blo 726324 818581 := bbase (se 6 (by rfl) ⟨19185, by rfl⟩ : syracuseStep 818581 = 38371) (by norm_num)
theorem B818617 : Blo 726324 818617 := bbase (se 2 (by rfl) ⟨306981, by rfl⟩ : syracuseStep 818617 = 613963) (by norm_num)
theorem B1637837 : Blo 726324 1637837 := bbase (se 3 (by rfl) ⟨307094, by rfl⟩ : syracuseStep 1637837 = 614189) (by norm_num)
theorem B818653 : Blo 726324 818653 := bbase (se 3 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 818653 = 306995) (by norm_num)
theorem B818689 : Blo 726324 818689 := bbase (se 2 (by rfl) ⟨307008, by rfl⟩ : syracuseStep 818689 = 614017) (by norm_num)
theorem B1637909 : Blo 726324 1637909 := bbase (se 6 (by rfl) ⟨38388, by rfl⟩ : syracuseStep 1637909 = 76777) (by norm_num)
theorem B818725 : Blo 726324 818725 := bbase (se 4 (by rfl) ⟨76755, by rfl⟩ : syracuseStep 818725 = 153511) (by norm_num)
theorem B5242421 : Blo 726324 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B818761 : Blo 726324 818761 := bbase (se 2 (by rfl) ⟨307035, by rfl⟩ : syracuseStep 818761 = 614071) (by norm_num)
theorem B1637981 : Blo 726324 1637981 := bbase (se 3 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 1637981 = 614243) (by norm_num)
theorem B818797 : Blo 726324 818797 := bbase (se 3 (by rfl) ⟨153524, by rfl⟩ : syracuseStep 818797 = 307049) (by norm_num)
theorem B818833 : Blo 726324 818833 := bbase (se 2 (by rfl) ⟨307062, by rfl⟩ : syracuseStep 818833 = 614125) (by norm_num)
theorem B1638053 : Blo 726324 1638053 := bbase (se 4 (by rfl) ⟨153567, by rfl⟩ : syracuseStep 1638053 = 307135) (by norm_num)
theorem B1310381 : Blo 726324 1310381 := bbase (se 3 (by rfl) ⟨245696, by rfl⟩ : syracuseStep 1310381 = 491393) (by norm_num)
theorem B818869 : Blo 726324 818869 := bbase (se 5 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 818869 = 76769) (by norm_num)
theorem B2457269 : Blo 726324 2457269 := bbase (se 5 (by rfl) ⟨115184, by rfl⟩ : syracuseStep 2457269 = 230369) (by norm_num)
theorem B818905 : Blo 726324 818905 := bbase (se 2 (by rfl) ⟨307089, by rfl⟩ : syracuseStep 818905 = 614179) (by norm_num)
theorem B1638125 : Blo 726324 1638125 := bbase (se 3 (by rfl) ⟨307148, by rfl⟩ : syracuseStep 1638125 = 614297) (by norm_num)
theorem B1179389 : Blo 726324 1179389 := bbase (se 3 (by rfl) ⟨221135, by rfl⟩ : syracuseStep 1179389 = 442271) (by norm_num)
theorem B818941 : Blo 726324 818941 := bbase (se 3 (by rfl) ⟨153551, by rfl⟩ : syracuseStep 818941 = 307103) (by norm_num)
theorem B818977 : Blo 726324 818977 := bbase (se 2 (by rfl) ⟨307116, by rfl⟩ : syracuseStep 818977 = 614233) (by norm_num)
theorem B1703717 : Blo 726324 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B1638197 : Blo 726324 1638197 := bbase (se 5 (by rfl) ⟨76790, by rfl⟩ : syracuseStep 1638197 = 153581) (by norm_num)
theorem B1212221 : Blo 726324 1212221 := bbase (se 3 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 1212221 = 454583) (by norm_num)
theorem B819013 : Blo 726324 819013 := bbase (se 4 (by rfl) ⟨76782, by rfl⟩ : syracuseStep 819013 = 153565) (by norm_num)
theorem B1572709 : Blo 726324 1572709 := bbase (se 4 (by rfl) ⟨147441, by rfl⟩ : syracuseStep 1572709 = 294883) (by norm_num)
theorem B819049 : Blo 726324 819049 := bbase (se 2 (by rfl) ⟨307143, by rfl⟩ : syracuseStep 819049 = 614287) (by norm_num)
theorem B1638269 : Blo 726324 1638269 := bbase (se 3 (by rfl) ⟨307175, by rfl⟩ : syracuseStep 1638269 = 614351) (by norm_num)
theorem B819085 : Blo 726324 819085 := bbase (se 3 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 819085 = 307157) (by norm_num)
theorem B819121 : Blo 726324 819121 := bbase (se 2 (by rfl) ⟨307170, by rfl⟩ : syracuseStep 819121 = 614341) (by norm_num)
theorem B1638341 : Blo 726324 1638341 := bbase (se 4 (by rfl) ⟨153594, by rfl⟩ : syracuseStep 1638341 = 307189) (by norm_num)
theorem B819157 : Blo 726324 819157 := bbase (se 7 (by rfl) ⟨9599, by rfl⟩ : syracuseStep 819157 = 19199) (by norm_num)
theorem B1638449 : Blo 726324 1638449 := bstep (se 2 (by rfl) ⟨614418, by rfl⟩ : syracuseStep 1638449 = 1228837) B1228837
theorem B1638467 : Blo 726324 1638467 := bstep (se 1 (by rfl) ⟨1228850, by rfl⟩ : syracuseStep 1638467 = 2457701) B2457701
theorem B819283 : Blo 726324 819283 := bstep (se 1 (by rfl) ⟨614462, by rfl⟩ : syracuseStep 819283 = 1228925) B1228925
theorem B2457809 : Blo 726324 2457809 := bstep (se 2 (by rfl) ⟨921678, by rfl⟩ : syracuseStep 2457809 = 1843357) B1843357
theorem B819427 : Blo 726324 819427 := bstep (se 1 (by rfl) ⟨614570, by rfl⟩ : syracuseStep 819427 = 1229141) B1229141
theorem B1868017 : Blo 726324 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B1638737 : Blo 726324 1638737 := bstep (se 2 (by rfl) ⟨614526, by rfl⟩ : syracuseStep 1638737 = 1229053) B1229053
theorem B1638755 : Blo 726324 1638755 := bstep (se 1 (by rfl) ⟨1229066, by rfl⟩ : syracuseStep 1638755 = 2458133) B2458133
theorem B819571 : Blo 726324 819571 := bstep (se 1 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 819571 = 1229357) B1229357
theorem B1180051 : Blo 726324 1180051 := bstep (se 1 (by rfl) ⟨885038, by rfl⟩ : syracuseStep 1180051 = 1770077) B1770077
theorem B819715 : Blo 726324 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B1475185 : Blo 726324 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B1245809 : Blo 726324 1245809 := bstep (se 2 (by rfl) ⟨467178, by rfl⟩ : syracuseStep 1245809 = 934357) B934357
theorem B1639025 : Blo 726324 1639025 := bstep (se 2 (by rfl) ⟨614634, by rfl⟩ : syracuseStep 1639025 = 1229269) B1229269
theorem B1639043 : Blo 726324 1639043 := bstep (se 1 (by rfl) ⟨1229282, by rfl⟩ : syracuseStep 1639043 = 2458565) B2458565
theorem B819859 : Blo 726324 819859 := bstep (se 1 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 819859 = 1229789) B1229789
theorem B2458349 : Blo 726324 2458349 := bstep (se 3 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 2458349 = 921881) B921881
theorem B3113741 : Blo 726324 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B2458403 : Blo 726324 2458403 := bstep (se 1 (by rfl) ⟨1843802, by rfl⟩ : syracuseStep 2458403 = 3687605) B3687605
theorem B820003 : Blo 726324 820003 := bstep (se 1 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 820003 = 1230005) B1230005
theorem B2523953 : Blo 726324 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B2327363 : Blo 726324 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B5309297 : Blo 726324 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B2360195 : Blo 726324 2360195 := bstep (se 1 (by rfl) ⟨1770146, by rfl⟩ : syracuseStep 2360195 = 3540293) B3540293
theorem B1639313 : Blo 726324 1639313 := bstep (se 2 (by rfl) ⟨614742, by rfl⟩ : syracuseStep 1639313 = 1229485) B1229485
theorem B1639331 : Blo 726324 1639331 := bstep (se 1 (by rfl) ⟨1229498, by rfl⟩ : syracuseStep 1639331 = 2458997) B2458997
theorem B820147 : Blo 726324 820147 := bstep (se 1 (by rfl) ⟨615110, by rfl⟩ : syracuseStep 820147 = 1230221) B1230221
theorem B984035 : Blo 726324 984035 := bstep (se 1 (by rfl) ⟨738026, by rfl⟩ : syracuseStep 984035 = 1476053) B1476053
theorem B2458673 : Blo 726324 2458673 := bstep (se 2 (by rfl) ⟨922002, by rfl⟩ : syracuseStep 2458673 = 1844005) B1844005
theorem B820291 : Blo 726324 820291 := bstep (se 1 (by rfl) ⟨615218, by rfl⟩ : syracuseStep 820291 = 1230437) B1230437
theorem B1639601 : Blo 726324 1639601 := bstep (se 2 (by rfl) ⟨614850, by rfl⟩ : syracuseStep 1639601 = 1229701) B1229701
theorem B1639619 : Blo 726324 1639619 := bstep (se 1 (by rfl) ⟨1229714, by rfl⟩ : syracuseStep 1639619 = 2459429) B2459429
theorem B7013573 : Blo 726324 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B820435 : Blo 726324 820435 := bstep (se 1 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 820435 = 1230653) B1230653
theorem B820579 : Blo 726324 820579 := bstep (se 1 (by rfl) ⟨615434, by rfl⟩ : syracuseStep 820579 = 1230869) B1230869
theorem B10519949 : Blo 726324 10519949 := bstep (se 3 (by rfl) ⟨1972490, by rfl⟩ : syracuseStep 10519949 = 3944981) B3944981
theorem B1574321 : Blo 726324 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B1639889 : Blo 726324 1639889 := bstep (se 2 (by rfl) ⟨614958, by rfl⟩ : syracuseStep 1639889 = 1229917) B1229917
theorem B1639907 : Blo 726324 1639907 := bstep (se 1 (by rfl) ⟨1229930, by rfl⟩ : syracuseStep 1639907 = 2459861) B2459861
theorem B820723 : Blo 726324 820723 := bstep (se 1 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 820723 = 1231085) B1231085
theorem B2459213 : Blo 726324 2459213 := bstep (se 3 (by rfl) ⟨461102, by rfl⟩ : syracuseStep 2459213 = 922205) B922205
theorem B5539427 : Blo 726324 5539427 := bstep (se 1 (by rfl) ⟨4154570, by rfl⟩ : syracuseStep 5539427 = 8309141) B8309141
theorem B1181299 : Blo 726324 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B2459267 : Blo 726324 2459267 := bstep (se 1 (by rfl) ⟨1844450, by rfl⟩ : syracuseStep 2459267 = 3688901) B3688901
theorem B820867 : Blo 726324 820867 := bstep (se 1 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 820867 = 1231301) B1231301
theorem B2328259 : Blo 726324 2328259 := bstep (se 1 (by rfl) ⟨1746194, by rfl⟩ : syracuseStep 2328259 = 3492389) B3492389
theorem B1312451 : Blo 726324 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B2164429 : Blo 726324 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B1640177 : Blo 726324 1640177 := bstep (se 2 (by rfl) ⟨615066, by rfl⟩ : syracuseStep 1640177 = 1230133) B1230133
theorem B1640195 : Blo 726324 1640195 := bstep (se 1 (by rfl) ⟨1230146, by rfl⟩ : syracuseStep 1640195 = 2460293) B2460293
theorem B2000657 : Blo 726324 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B821011 : Blo 726324 821011 := bstep (se 1 (by rfl) ⟨615758, by rfl⟩ : syracuseStep 821011 = 1231517) B1231517
theorem B2459537 : Blo 726324 2459537 := bstep (se 2 (by rfl) ⟨922326, by rfl⟩ : syracuseStep 2459537 = 1844653) B1844653
theorem B821155 : Blo 726324 821155 := bstep (se 1 (by rfl) ⟨615866, by rfl⟩ : syracuseStep 821155 = 1231733) B1231733
theorem B3934129 : Blo 726324 3934129 := bstep (se 2 (by rfl) ⟨1475298, by rfl⟩ : syracuseStep 3934129 = 2950597) B2950597
theorem B1247171 : Blo 726324 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B919507 : Blo 726324 919507 := bstep (se 1 (by rfl) ⟨689630, by rfl⟩ : syracuseStep 919507 = 1379261) B1379261
theorem B1640465 : Blo 726324 1640465 := bstep (se 2 (by rfl) ⟨615174, by rfl⟩ : syracuseStep 1640465 = 1230349) B1230349
theorem B1640483 : Blo 726324 1640483 := bstep (se 1 (by rfl) ⟨1230362, by rfl⟩ : syracuseStep 1640483 = 2460725) B2460725
theorem B919603 : Blo 726324 919603 := bstep (se 1 (by rfl) ⟨689702, by rfl⟩ : syracuseStep 919603 = 1379405) B1379405
theorem B821299 : Blo 726324 821299 := bstep (se 1 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 821299 = 1231949) B1231949
theorem B821443 : Blo 726324 821443 := bstep (se 1 (by rfl) ⟨616082, by rfl⟩ : syracuseStep 821443 = 1232165) B1232165
theorem B1640753 : Blo 726324 1640753 := bstep (se 2 (by rfl) ⟨615282, by rfl⟩ : syracuseStep 1640753 = 1230565) B1230565
theorem B1640771 : Blo 726324 1640771 := bstep (se 1 (by rfl) ⟨1230578, by rfl⟩ : syracuseStep 1640771 = 2461157) B2461157
theorem B821587 : Blo 726324 821587 := bstep (se 1 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 821587 = 1232381) B1232381
theorem B1870193 : Blo 726324 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B887203 : Blo 726324 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B2460077 : Blo 726324 2460077 := bstep (se 3 (by rfl) ⟨461264, by rfl⟩ : syracuseStep 2460077 = 922529) B922529
theorem B1477091 : Blo 726324 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B2460131 : Blo 726324 2460131 := bstep (se 1 (by rfl) ⟨1845098, by rfl⟩ : syracuseStep 2460131 = 3690197) B3690197
theorem B920099 : Blo 726324 920099 := bstep (se 1 (by rfl) ⟨690074, by rfl⟩ : syracuseStep 920099 = 1380149) B1380149
theorem B1641041 : Blo 726324 1641041 := bstep (se 2 (by rfl) ⟨615390, by rfl⟩ : syracuseStep 1641041 = 1230781) B1230781
theorem B1641059 : Blo 726324 1641059 := bstep (se 1 (by rfl) ⟨1230794, by rfl⟩ : syracuseStep 1641059 = 2461589) B2461589
theorem B2460401 : Blo 726324 2460401 := bstep (se 2 (by rfl) ⟨922650, by rfl⟩ : syracuseStep 2460401 = 1845301) B1845301
theorem B2329361 : Blo 726324 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B1641329 : Blo 726324 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B1641347 : Blo 726324 1641347 := bstep (se 1 (by rfl) ⟨1231010, by rfl⟩ : syracuseStep 1641347 = 2462021) B2462021
theorem B2329489 : Blo 726324 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B986051 : Blo 726324 986051 := bstep (se 1 (by rfl) ⟨739538, by rfl⟩ : syracuseStep 986051 = 1479077) B1479077
theorem B5246021 : Blo 726324 5246021 := bstep (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) B983629
theorem B1641617 : Blo 726324 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B1641635 : Blo 726324 1641635 := bstep (se 1 (by rfl) ⟨1231226, by rfl⟩ : syracuseStep 1641635 = 2462453) B2462453
theorem B1346737 : Blo 726324 1346737 := bstep (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) B1010053
theorem B920803 : Blo 726324 920803 := bstep (se 1 (by rfl) ⟨690602, by rfl⟩ : syracuseStep 920803 = 1381205) B1381205
theorem B2133233 : Blo 726324 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B1379587 : Blo 726324 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B2460941 : Blo 726324 2460941 := bstep (se 3 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 2460941 = 922853) B922853
theorem B1248547 : Blo 726324 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B920899 : Blo 726324 920899 := bstep (se 1 (by rfl) ⟨690674, by rfl⟩ : syracuseStep 920899 = 1381349) B1381349
theorem B2460995 : Blo 726324 2460995 := bstep (se 1 (by rfl) ⟨1845746, by rfl⟩ : syracuseStep 2460995 = 3691493) B3691493
theorem B1379747 : Blo 726324 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B2952625 : Blo 726324 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B1641905 : Blo 726324 1641905 := bstep (se 2 (by rfl) ⟨615714, by rfl⟩ : syracuseStep 1641905 = 1231429) B1231429
theorem B1641923 : Blo 726324 1641923 := bstep (se 1 (by rfl) ⟨1231442, by rfl⟩ : syracuseStep 1641923 = 2462885) B2462885
theorem B1838609 : Blo 726324 1838609 := bstep (se 2 (by rfl) ⟨689478, by rfl⟩ : syracuseStep 1838609 = 1378957) B1378957
theorem B1314353 : Blo 726324 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B1838659 : Blo 726324 1838659 := bstep (se 1 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 1838659 = 2757989) B2757989
theorem B2461265 : Blo 726324 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B1838801 : Blo 726324 1838801 := bstep (se 2 (by rfl) ⟨689550, by rfl⟩ : syracuseStep 1838801 = 1379101) B1379101
theorem B1642193 : Blo 726324 1642193 := bstep (se 2 (by rfl) ⟨615822, by rfl⟩ : syracuseStep 1642193 = 1231645) B1231645
theorem B1642211 : Blo 726324 1642211 := bstep (se 1 (by rfl) ⟨1231658, by rfl⟩ : syracuseStep 1642211 = 2463317) B2463317
theorem B921395 : Blo 726324 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B2330477 : Blo 726324 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B2068355 : Blo 726324 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B1642481 : Blo 726324 1642481 := bstep (se 2 (by rfl) ⟨615930, by rfl⟩ : syracuseStep 1642481 = 1231861) B1231861
theorem B1642499 : Blo 726324 1642499 := bstep (se 1 (by rfl) ⟨1231874, by rfl⟩ : syracuseStep 1642499 = 2463749) B2463749
theorem B1478737 : Blo 726324 1478737 := bstep (se 2 (by rfl) ⟨554526, by rfl⟩ : syracuseStep 1478737 = 1109053) B1109053
theorem B2461805 : Blo 726324 2461805 := bstep (se 3 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 2461805 = 923177) B923177
theorem B2461859 : Blo 726324 2461859 := bstep (se 1 (by rfl) ⟨1846394, by rfl⟩ : syracuseStep 2461859 = 3692789) B3692789
theorem B1478915 : Blo 726324 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B1642769 : Blo 726324 1642769 := bstep (se 2 (by rfl) ⟨616038, by rfl⟩ : syracuseStep 1642769 = 1232077) B1232077
theorem B1642787 : Blo 726324 1642787 := bstep (se 1 (by rfl) ⟨1232090, by rfl⟩ : syracuseStep 1642787 = 2464181) B2464181
theorem B2462129 : Blo 726324 2462129 := bstep (se 2 (by rfl) ⟨923298, by rfl⟩ : syracuseStep 2462129 = 1846597) B1846597
theorem B1380817 : Blo 726324 1380817 := bstep (se 2 (by rfl) ⟨517806, by rfl⟩ : syracuseStep 1380817 = 1035613) B1035613
theorem B922099 : Blo 726324 922099 := bstep (se 1 (by rfl) ⟨691574, by rfl⟩ : syracuseStep 922099 = 1383149) B1383149
theorem B1643057 : Blo 726324 1643057 := bstep (se 2 (by rfl) ⟨616146, by rfl⟩ : syracuseStep 1643057 = 1232293) B1232293
theorem B1643075 : Blo 726324 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B922195 : Blo 726324 922195 := bstep (se 1 (by rfl) ⟨691646, by rfl⟩ : syracuseStep 922195 = 1383293) B1383293
theorem B6230627 : Blo 726324 6230627 := bstep (se 1 (by rfl) ⟨4672970, by rfl⟩ : syracuseStep 6230627 = 9345941) B9345941
theorem B2069165 : Blo 726324 2069165 := bstep (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) B775937
theorem B1839793 : Blo 726324 1839793 := bstep (se 2 (by rfl) ⟨689922, by rfl⟩ : syracuseStep 1839793 = 1379845) B1379845
theorem B2102051 : Blo 726324 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B1971011 : Blo 726324 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B2069347 : Blo 726324 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B1840067 : Blo 726324 1840067 := bstep (se 1 (by rfl) ⟨1380050, by rfl⟩ : syracuseStep 1840067 = 2760101) B2760101
theorem B2462669 : Blo 726324 2462669 := bstep (se 3 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 2462669 = 923501) B923501
theorem B2462723 : Blo 726324 2462723 := bstep (se 1 (by rfl) ⟨1847042, by rfl⟩ : syracuseStep 2462723 = 3694085) B3694085
theorem B3118115 : Blo 726324 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B922691 : Blo 726324 922691 := bstep (se 1 (by rfl) ⟨692018, by rfl⟩ : syracuseStep 922691 = 1384037) B1384037
theorem B1840259 : Blo 726324 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B2331821 : Blo 726324 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B2462993 : Blo 726324 2462993 := bstep (se 2 (by rfl) ⟨923622, by rfl⟩ : syracuseStep 2462993 = 1847245) B1847245
theorem B726339 : Blo 726324 726339 := bstep (se 1 (by rfl) ⟨544754, by rfl⟩ : syracuseStep 726339 = 1089509) B1089509
theorem B2069837 : Blo 726324 2069837 := bstep (se 3 (by rfl) ⟨388094, by rfl⟩ : syracuseStep 2069837 = 776189) B776189
theorem B726355 : Blo 726324 726355 := bstep (se 1 (by rfl) ⟨544766, by rfl⟩ : syracuseStep 726355 = 1089533) B1089533
theorem B726371 : Blo 726324 726371 := bstep (se 1 (by rfl) ⟨544778, by rfl⟩ : syracuseStep 726371 = 1089557) B1089557
theorem B726387 : Blo 726324 726387 := bstep (se 1 (by rfl) ⟨544790, by rfl⟩ : syracuseStep 726387 = 1089581) B1089581
theorem B726403 : Blo 726324 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B726419 : Blo 726324 726419 := bstep (se 1 (by rfl) ⟨544814, by rfl⟩ : syracuseStep 726419 = 1089629) B1089629
theorem B726435 : Blo 726324 726435 := bstep (se 1 (by rfl) ⟨544826, by rfl⟩ : syracuseStep 726435 = 1089653) B1089653
theorem B726451 : Blo 726324 726451 := bstep (se 1 (by rfl) ⟨544838, by rfl⟩ : syracuseStep 726451 = 1089677) B1089677
theorem B726467 : Blo 726324 726467 := bstep (se 1 (by rfl) ⟨544850, by rfl⟩ : syracuseStep 726467 = 1089701) B1089701
theorem B726483 : Blo 726324 726483 := bstep (se 1 (by rfl) ⟨544862, by rfl⟩ : syracuseStep 726483 = 1089725) B1089725
theorem B726499 : Blo 726324 726499 := bstep (se 1 (by rfl) ⟨544874, by rfl⟩ : syracuseStep 726499 = 1089749) B1089749
theorem B1381873 : Blo 726324 1381873 := bstep (se 2 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 1381873 = 1036405) B1036405
theorem B726515 : Blo 726324 726515 := bstep (se 1 (by rfl) ⟨544886, by rfl⟩ : syracuseStep 726515 = 1089773) B1089773
theorem B726531 : Blo 726324 726531 := bstep (se 1 (by rfl) ⟨544898, by rfl⟩ : syracuseStep 726531 = 1089797) B1089797
theorem B2758157 : Blo 726324 2758157 := bstep (se 3 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 2758157 = 1034309) B1034309
theorem B726547 : Blo 726324 726547 := bstep (se 1 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 726547 = 1089821) B1089821
theorem B726563 : Blo 726324 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B726579 : Blo 726324 726579 := bstep (se 1 (by rfl) ⟨544934, by rfl⟩ : syracuseStep 726579 = 1089869) B1089869
theorem B726595 : Blo 726324 726595 := bstep (se 1 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 726595 = 1089893) B1089893
theorem B726611 : Blo 726324 726611 := bstep (se 1 (by rfl) ⟨544958, by rfl⟩ : syracuseStep 726611 = 1089917) B1089917
theorem B726627 : Blo 726324 726627 := bstep (se 1 (by rfl) ⟨544970, by rfl⟩ : syracuseStep 726627 = 1089941) B1089941
theorem B726643 : Blo 726324 726643 := bstep (se 1 (by rfl) ⟨544982, by rfl⟩ : syracuseStep 726643 = 1089965) B1089965
theorem B726659 : Blo 726324 726659 := bstep (se 1 (by rfl) ⟨544994, by rfl⟩ : syracuseStep 726659 = 1089989) B1089989
theorem B3937933 : Blo 726324 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B726675 : Blo 726324 726675 := bstep (se 1 (by rfl) ⟨545006, by rfl⟩ : syracuseStep 726675 = 1090013) B1090013
theorem B726691 : Blo 726324 726691 := bstep (se 1 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 726691 = 1090037) B1090037
theorem B726707 : Blo 726324 726707 := bstep (se 1 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 726707 = 1090061) B1090061
theorem B726723 : Blo 726324 726723 := bstep (se 1 (by rfl) ⟨545042, by rfl⟩ : syracuseStep 726723 = 1090085) B1090085
theorem B726739 : Blo 726324 726739 := bstep (se 1 (by rfl) ⟨545054, by rfl⟩ : syracuseStep 726739 = 1090109) B1090109
theorem B726755 : Blo 726324 726755 := bstep (se 1 (by rfl) ⟨545066, by rfl⟩ : syracuseStep 726755 = 1090133) B1090133
theorem B1578737 : Blo 726324 1578737 := bstep (se 2 (by rfl) ⟨592026, by rfl⟩ : syracuseStep 1578737 = 1184053) B1184053
theorem B726771 : Blo 726324 726771 := bstep (se 1 (by rfl) ⟨545078, by rfl⟩ : syracuseStep 726771 = 1090157) B1090157
theorem B726787 : Blo 726324 726787 := bstep (se 1 (by rfl) ⟨545090, by rfl⟩ : syracuseStep 726787 = 1090181) B1090181
theorem B2103043 : Blo 726324 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B923395 : Blo 726324 923395 := bstep (se 1 (by rfl) ⟨692546, by rfl⟩ : syracuseStep 923395 = 1385093) B1385093
theorem B726803 : Blo 726324 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B726819 : Blo 726324 726819 := bstep (se 1 (by rfl) ⟨545114, by rfl⟩ : syracuseStep 726819 = 1090229) B1090229
theorem B2463533 : Blo 726324 2463533 := bstep (se 3 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 2463533 = 923825) B923825
theorem B726835 : Blo 726324 726835 := bstep (se 1 (by rfl) ⟨545126, by rfl⟩ : syracuseStep 726835 = 1090253) B1090253
theorem B726851 : Blo 726324 726851 := bstep (se 1 (by rfl) ⟨545138, by rfl⟩ : syracuseStep 726851 = 1090277) B1090277
theorem B726867 : Blo 726324 726867 := bstep (se 1 (by rfl) ⟨545150, by rfl⟩ : syracuseStep 726867 = 1090301) B1090301
theorem B726883 : Blo 726324 726883 := bstep (se 1 (by rfl) ⟨545162, by rfl⟩ : syracuseStep 726883 = 1090325) B1090325
theorem B923491 : Blo 726324 923491 := bstep (se 1 (by rfl) ⟨692618, by rfl⟩ : syracuseStep 923491 = 1385237) B1385237
theorem B2463587 : Blo 726324 2463587 := bstep (se 1 (by rfl) ⟨1847690, by rfl⟩ : syracuseStep 2463587 = 3695381) B3695381
theorem B726899 : Blo 726324 726899 := bstep (se 1 (by rfl) ⟨545174, by rfl⟩ : syracuseStep 726899 = 1090349) B1090349
theorem B726915 : Blo 726324 726915 := bstep (se 1 (by rfl) ⟨545186, by rfl⟩ : syracuseStep 726915 = 1090373) B1090373
theorem B1382275 : Blo 726324 1382275 := bstep (se 1 (by rfl) ⟨1036706, by rfl⟩ : syracuseStep 1382275 = 2073413) B2073413
theorem B726931 : Blo 726324 726931 := bstep (se 1 (by rfl) ⟨545198, by rfl⟩ : syracuseStep 726931 = 1090397) B1090397
theorem B726947 : Blo 726324 726947 := bstep (se 1 (by rfl) ⟨545210, by rfl⟩ : syracuseStep 726947 = 1090421) B1090421
theorem B1382321 : Blo 726324 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B726963 : Blo 726324 726963 := bstep (se 1 (by rfl) ⟨545222, by rfl⟩ : syracuseStep 726963 = 1090445) B1090445
theorem B726979 : Blo 726324 726979 := bstep (se 1 (by rfl) ⟨545234, by rfl⟩ : syracuseStep 726979 = 1090469) B1090469
theorem B21010373 : Blo 726324 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B726995 : Blo 726324 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B727011 : Blo 726324 727011 := bstep (se 1 (by rfl) ⟨545258, by rfl⟩ : syracuseStep 727011 = 1090517) B1090517
theorem B727027 : Blo 726324 727027 := bstep (se 1 (by rfl) ⟨545270, by rfl⟩ : syracuseStep 727027 = 1090541) B1090541
theorem B727043 : Blo 726324 727043 := bstep (se 1 (by rfl) ⟨545282, by rfl⟩ : syracuseStep 727043 = 1090565) B1090565
theorem B727059 : Blo 726324 727059 := bstep (se 1 (by rfl) ⟨545294, by rfl⟩ : syracuseStep 727059 = 1090589) B1090589
theorem B727075 : Blo 726324 727075 := bstep (se 1 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 727075 = 1090613) B1090613
theorem B1841201 : Blo 726324 1841201 := bstep (se 2 (by rfl) ⟨690450, by rfl⟩ : syracuseStep 1841201 = 1380901) B1380901
theorem B727091 : Blo 726324 727091 := bstep (se 1 (by rfl) ⟨545318, by rfl⟩ : syracuseStep 727091 = 1090637) B1090637
theorem B727107 : Blo 726324 727107 := bstep (se 1 (by rfl) ⟨545330, by rfl⟩ : syracuseStep 727107 = 1090661) B1090661
theorem B727123 : Blo 726324 727123 := bstep (se 1 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 727123 = 1090685) B1090685
theorem B727139 : Blo 726324 727139 := bstep (se 1 (by rfl) ⟨545354, by rfl⟩ : syracuseStep 727139 = 1090709) B1090709
theorem B1841251 : Blo 726324 1841251 := bstep (se 1 (by rfl) ⟨1380938, by rfl⟩ : syracuseStep 1841251 = 2761877) B2761877
theorem B2463857 : Blo 726324 2463857 := bstep (se 2 (by rfl) ⟨923946, by rfl⟩ : syracuseStep 2463857 = 1847893) B1847893
theorem B727155 : Blo 726324 727155 := bstep (se 1 (by rfl) ⟨545366, by rfl⟩ : syracuseStep 727155 = 1090733) B1090733
theorem B727171 : Blo 726324 727171 := bstep (se 1 (by rfl) ⟨545378, by rfl⟩ : syracuseStep 727171 = 1090757) B1090757
theorem B727187 : Blo 726324 727187 := bstep (se 1 (by rfl) ⟨545390, by rfl⟩ : syracuseStep 727187 = 1090781) B1090781
theorem B727203 : Blo 726324 727203 := bstep (se 1 (by rfl) ⟨545402, by rfl⟩ : syracuseStep 727203 = 1090805) B1090805
theorem B2365613 : Blo 726324 2365613 := bstep (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) B887105
theorem B727219 : Blo 726324 727219 := bstep (se 1 (by rfl) ⟨545414, by rfl⟩ : syracuseStep 727219 = 1090829) B1090829
theorem B727235 : Blo 726324 727235 := bstep (se 1 (by rfl) ⟨545426, by rfl⟩ : syracuseStep 727235 = 1090853) B1090853
theorem B16849093 : Blo 726324 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B1382609 : Blo 726324 1382609 := bstep (se 2 (by rfl) ⟨518478, by rfl⟩ : syracuseStep 1382609 = 1036957) B1036957
theorem B727251 : Blo 726324 727251 := bstep (se 1 (by rfl) ⟨545438, by rfl⟩ : syracuseStep 727251 = 1090877) B1090877
theorem B727267 : Blo 726324 727267 := bstep (se 1 (by rfl) ⟨545450, by rfl⟩ : syracuseStep 727267 = 1090901) B1090901
theorem B1841393 : Blo 726324 1841393 := bstep (se 2 (by rfl) ⟨690522, by rfl⟩ : syracuseStep 1841393 = 1381045) B1381045
theorem B727283 : Blo 726324 727283 := bstep (se 1 (by rfl) ⟨545462, by rfl⟩ : syracuseStep 727283 = 1090925) B1090925
theorem B727299 : Blo 726324 727299 := bstep (se 1 (by rfl) ⟨545474, by rfl⟩ : syracuseStep 727299 = 1090949) B1090949
theorem B727315 : Blo 726324 727315 := bstep (se 1 (by rfl) ⟨545486, by rfl⟩ : syracuseStep 727315 = 1090973) B1090973
theorem B727331 : Blo 726324 727331 := bstep (se 1 (by rfl) ⟨545498, by rfl⟩ : syracuseStep 727331 = 1090997) B1090997
theorem B2758961 : Blo 726324 2758961 := bstep (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) B2069221
theorem B727347 : Blo 726324 727347 := bstep (se 1 (by rfl) ⟨545510, by rfl⟩ : syracuseStep 727347 = 1091021) B1091021
theorem B727363 : Blo 726324 727363 := bstep (se 1 (by rfl) ⟨545522, by rfl⟩ : syracuseStep 727363 = 1091045) B1091045
theorem B727379 : Blo 726324 727379 := bstep (se 1 (by rfl) ⟨545534, by rfl⟩ : syracuseStep 727379 = 1091069) B1091069
theorem B923987 : Blo 726324 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B727395 : Blo 726324 727395 := bstep (se 1 (by rfl) ⟨545546, by rfl⟩ : syracuseStep 727395 = 1091093) B1091093
theorem B727411 : Blo 726324 727411 := bstep (se 1 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 727411 = 1091117) B1091117
theorem B727427 : Blo 726324 727427 := bstep (se 1 (by rfl) ⟨545570, by rfl⟩ : syracuseStep 727427 = 1091141) B1091141
theorem B727443 : Blo 726324 727443 := bstep (se 1 (by rfl) ⟨545582, by rfl⟩ : syracuseStep 727443 = 1091165) B1091165
theorem B727459 : Blo 726324 727459 := bstep (se 1 (by rfl) ⟨545594, by rfl⟩ : syracuseStep 727459 = 1091189) B1091189
theorem B727475 : Blo 726324 727475 := bstep (se 1 (by rfl) ⟨545606, by rfl⟩ : syracuseStep 727475 = 1091213) B1091213
theorem B727491 : Blo 726324 727491 := bstep (se 1 (by rfl) ⟨545618, by rfl⟩ : syracuseStep 727491 = 1091237) B1091237
theorem B727507 : Blo 726324 727507 := bstep (se 1 (by rfl) ⟨545630, by rfl⟩ : syracuseStep 727507 = 1091261) B1091261
theorem B727523 : Blo 726324 727523 := bstep (se 1 (by rfl) ⟨545642, by rfl⟩ : syracuseStep 727523 = 1091285) B1091285
theorem B2071021 : Blo 726324 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B727539 : Blo 726324 727539 := bstep (se 1 (by rfl) ⟨545654, by rfl⟩ : syracuseStep 727539 = 1091309) B1091309
theorem B727555 : Blo 726324 727555 := bstep (se 1 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 727555 = 1091333) B1091333
theorem B727571 : Blo 726324 727571 := bstep (se 1 (by rfl) ⟨545678, by rfl⟩ : syracuseStep 727571 = 1091357) B1091357
theorem B727587 : Blo 726324 727587 := bstep (se 1 (by rfl) ⟨545690, by rfl⟩ : syracuseStep 727587 = 1091381) B1091381
theorem B727603 : Blo 726324 727603 := bstep (se 1 (by rfl) ⟨545702, by rfl⟩ : syracuseStep 727603 = 1091405) B1091405
theorem B727619 : Blo 726324 727619 := bstep (se 1 (by rfl) ⟨545714, by rfl⟩ : syracuseStep 727619 = 1091429) B1091429
theorem B727635 : Blo 726324 727635 := bstep (se 1 (by rfl) ⟨545726, by rfl⟩ : syracuseStep 727635 = 1091453) B1091453
theorem B727651 : Blo 726324 727651 := bstep (se 1 (by rfl) ⟨545738, by rfl⟩ : syracuseStep 727651 = 1091477) B1091477
theorem B727667 : Blo 726324 727667 := bstep (se 1 (by rfl) ⟨545750, by rfl⟩ : syracuseStep 727667 = 1091501) B1091501
theorem B727683 : Blo 726324 727683 := bstep (se 1 (by rfl) ⟨545762, by rfl⟩ : syracuseStep 727683 = 1091525) B1091525
theorem B2464397 : Blo 726324 2464397 := bstep (se 3 (by rfl) ⟨462074, by rfl⟩ : syracuseStep 2464397 = 924149) B924149
theorem B727699 : Blo 726324 727699 := bstep (se 1 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 727699 = 1091549) B1091549
theorem B727715 : Blo 726324 727715 := bstep (se 1 (by rfl) ⟨545786, by rfl⟩ : syracuseStep 727715 = 1091573) B1091573
theorem B727731 : Blo 726324 727731 := bstep (se 1 (by rfl) ⟨545798, by rfl⟩ : syracuseStep 727731 = 1091597) B1091597
theorem B727747 : Blo 726324 727747 := bstep (se 1 (by rfl) ⟨545810, by rfl⟩ : syracuseStep 727747 = 1091621) B1091621
theorem B2464451 : Blo 726324 2464451 := bstep (se 1 (by rfl) ⟨1848338, by rfl⟩ : syracuseStep 2464451 = 3696677) B3696677
theorem B727763 : Blo 726324 727763 := bstep (se 1 (by rfl) ⟨545822, by rfl⟩ : syracuseStep 727763 = 1091645) B1091645
theorem B727779 : Blo 726324 727779 := bstep (se 1 (by rfl) ⟨545834, by rfl⟩ : syracuseStep 727779 = 1091669) B1091669
theorem B2333411 : Blo 726324 2333411 := bstep (se 1 (by rfl) ⟨1750058, by rfl⟩ : syracuseStep 2333411 = 3500117) B3500117
theorem B727795 : Blo 726324 727795 := bstep (se 1 (by rfl) ⟨545846, by rfl⟩ : syracuseStep 727795 = 1091693) B1091693
theorem B727811 : Blo 726324 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B727827 : Blo 726324 727827 := bstep (se 1 (by rfl) ⟨545870, by rfl⟩ : syracuseStep 727827 = 1091741) B1091741
theorem B727843 : Blo 726324 727843 := bstep (se 1 (by rfl) ⟨545882, by rfl⟩ : syracuseStep 727843 = 1091765) B1091765
theorem B727859 : Blo 726324 727859 := bstep (se 1 (by rfl) ⟨545894, by rfl⟩ : syracuseStep 727859 = 1091789) B1091789
theorem B727875 : Blo 726324 727875 := bstep (se 1 (by rfl) ⟨545906, by rfl⟩ : syracuseStep 727875 = 1091813) B1091813
theorem B5544773 : Blo 726324 5544773 := bstep (se 4 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 5544773 = 1039645) B1039645
theorem B727891 : Blo 726324 727891 := bstep (se 1 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 727891 = 1091837) B1091837
theorem B727907 : Blo 726324 727907 := bstep (se 1 (by rfl) ⟨545930, by rfl⟩ : syracuseStep 727907 = 1091861) B1091861
theorem B727923 : Blo 726324 727923 := bstep (se 1 (by rfl) ⟨545942, by rfl⟩ : syracuseStep 727923 = 1091885) B1091885
theorem B727939 : Blo 726324 727939 := bstep (se 1 (by rfl) ⟨545954, by rfl⟩ : syracuseStep 727939 = 1091909) B1091909
theorem B727955 : Blo 726324 727955 := bstep (se 1 (by rfl) ⟨545966, by rfl⟩ : syracuseStep 727955 = 1091933) B1091933
theorem B727971 : Blo 726324 727971 := bstep (se 1 (by rfl) ⟨545978, by rfl⟩ : syracuseStep 727971 = 1091957) B1091957
theorem B1383331 : Blo 726324 1383331 := bstep (se 1 (by rfl) ⟨1037498, by rfl⟩ : syracuseStep 1383331 = 2074997) B2074997
theorem B727987 : Blo 726324 727987 := bstep (se 1 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 727987 = 1091981) B1091981
theorem B728003 : Blo 726324 728003 := bstep (se 1 (by rfl) ⟨546002, by rfl⟩ : syracuseStep 728003 = 1092005) B1092005
theorem B2759629 : Blo 726324 2759629 := bstep (se 3 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 2759629 = 1034861) B1034861
theorem B2464721 : Blo 726324 2464721 := bstep (se 2 (by rfl) ⟨924270, by rfl⟩ : syracuseStep 2464721 = 1848541) B1848541
theorem B728019 : Blo 726324 728019 := bstep (se 1 (by rfl) ⟨546014, by rfl⟩ : syracuseStep 728019 = 1092029) B1092029
theorem B728035 : Blo 726324 728035 := bstep (se 1 (by rfl) ⟨546026, by rfl⟩ : syracuseStep 728035 = 1092053) B1092053
theorem B728051 : Blo 726324 728051 := bstep (se 1 (by rfl) ⟨546038, by rfl⟩ : syracuseStep 728051 = 1092077) B1092077
theorem B728067 : Blo 726324 728067 := bstep (se 1 (by rfl) ⟨546050, by rfl⟩ : syracuseStep 728067 = 1092101) B1092101
theorem B728083 : Blo 726324 728083 := bstep (se 1 (by rfl) ⟨546062, by rfl⟩ : syracuseStep 728083 = 1092125) B1092125
theorem B728099 : Blo 726324 728099 := bstep (se 1 (by rfl) ⟨546074, by rfl⟩ : syracuseStep 728099 = 1092149) B1092149
theorem B728115 : Blo 726324 728115 := bstep (se 1 (by rfl) ⟨546086, by rfl⟩ : syracuseStep 728115 = 1092173) B1092173
theorem B728131 : Blo 726324 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B728147 : Blo 726324 728147 := bstep (se 1 (by rfl) ⟨546110, by rfl⟩ : syracuseStep 728147 = 1092221) B1092221
theorem B728163 : Blo 726324 728163 := bstep (se 1 (by rfl) ⟨546122, by rfl⟩ : syracuseStep 728163 = 1092245) B1092245
theorem B728179 : Blo 726324 728179 := bstep (se 1 (by rfl) ⟨546134, by rfl⟩ : syracuseStep 728179 = 1092269) B1092269
theorem B728195 : Blo 726324 728195 := bstep (se 1 (by rfl) ⟨546146, by rfl⟩ : syracuseStep 728195 = 1092293) B1092293
theorem B728211 : Blo 726324 728211 := bstep (se 1 (by rfl) ⟨546158, by rfl⟩ : syracuseStep 728211 = 1092317) B1092317
theorem B728227 : Blo 726324 728227 := bstep (se 1 (by rfl) ⟨546170, by rfl⟩ : syracuseStep 728227 = 1092341) B1092341
theorem B4201649 : Blo 726324 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B728243 : Blo 726324 728243 := bstep (se 1 (by rfl) ⟨546182, by rfl⟩ : syracuseStep 728243 = 1092365) B1092365
theorem B728259 : Blo 726324 728259 := bstep (se 1 (by rfl) ⟨546194, by rfl⟩ : syracuseStep 728259 = 1092389) B1092389
theorem B1842385 : Blo 726324 1842385 := bstep (se 2 (by rfl) ⟨690894, by rfl⟩ : syracuseStep 1842385 = 1381789) B1381789
theorem B728275 : Blo 726324 728275 := bstep (se 1 (by rfl) ⟨546206, by rfl⟩ : syracuseStep 728275 = 1092413) B1092413
theorem B728291 : Blo 726324 728291 := bstep (se 1 (by rfl) ⟨546218, by rfl⟩ : syracuseStep 728291 = 1092437) B1092437
theorem B728307 : Blo 726324 728307 := bstep (se 1 (by rfl) ⟨546230, by rfl⟩ : syracuseStep 728307 = 1092461) B1092461
theorem B728323 : Blo 726324 728323 := bstep (se 1 (by rfl) ⟨546242, by rfl⟩ : syracuseStep 728323 = 1092485) B1092485
theorem B728339 : Blo 726324 728339 := bstep (se 1 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 728339 = 1092509) B1092509
theorem B728355 : Blo 726324 728355 := bstep (se 1 (by rfl) ⟨546266, by rfl⟩ : syracuseStep 728355 = 1092533) B1092533
theorem B3939619 : Blo 726324 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B728371 : Blo 726324 728371 := bstep (se 1 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 728371 = 1092557) B1092557
theorem B728387 : Blo 726324 728387 := bstep (se 1 (by rfl) ⟨546290, by rfl⟩ : syracuseStep 728387 = 1092581) B1092581
theorem B728403 : Blo 726324 728403 := bstep (se 1 (by rfl) ⟨546302, by rfl⟩ : syracuseStep 728403 = 1092605) B1092605
theorem B728419 : Blo 726324 728419 := bstep (se 1 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 728419 = 1092629) B1092629
theorem B1383779 : Blo 726324 1383779 := bstep (se 1 (by rfl) ⟨1037834, by rfl⟩ : syracuseStep 1383779 = 2075669) B2075669
theorem B728435 : Blo 726324 728435 := bstep (se 1 (by rfl) ⟨546326, by rfl⟩ : syracuseStep 728435 = 1092653) B1092653
theorem B728451 : Blo 726324 728451 := bstep (se 1 (by rfl) ⟨546338, by rfl⟩ : syracuseStep 728451 = 1092677) B1092677
theorem B728467 : Blo 726324 728467 := bstep (se 1 (by rfl) ⟨546350, by rfl⟩ : syracuseStep 728467 = 1092701) B1092701
theorem B728483 : Blo 726324 728483 := bstep (se 1 (by rfl) ⟨546362, by rfl⟩ : syracuseStep 728483 = 1092725) B1092725
theorem B728499 : Blo 726324 728499 := bstep (se 1 (by rfl) ⟨546374, by rfl⟩ : syracuseStep 728499 = 1092749) B1092749
theorem B728515 : Blo 726324 728515 := bstep (se 1 (by rfl) ⟨546386, by rfl⟩ : syracuseStep 728515 = 1092773) B1092773
theorem B728531 : Blo 726324 728531 := bstep (se 1 (by rfl) ⟨546398, by rfl⟩ : syracuseStep 728531 = 1092797) B1092797
theorem B1842659 : Blo 726324 1842659 := bstep (se 1 (by rfl) ⟨1381994, by rfl⟩ : syracuseStep 1842659 = 2763989) B2763989
theorem B728547 : Blo 726324 728547 := bstep (se 1 (by rfl) ⟨546410, by rfl⟩ : syracuseStep 728547 = 1092821) B1092821
theorem B2334179 : Blo 726324 2334179 := bstep (se 1 (by rfl) ⟨1750634, by rfl⟩ : syracuseStep 2334179 = 3501269) B3501269
theorem B728563 : Blo 726324 728563 := bstep (se 1 (by rfl) ⟨546422, by rfl⟩ : syracuseStep 728563 = 1092845) B1092845
theorem B728579 : Blo 726324 728579 := bstep (se 1 (by rfl) ⟨546434, by rfl⟩ : syracuseStep 728579 = 1092869) B1092869
theorem B2072081 : Blo 726324 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B728595 : Blo 726324 728595 := bstep (se 1 (by rfl) ⟨546446, by rfl⟩ : syracuseStep 728595 = 1092893) B1092893
theorem B728611 : Blo 726324 728611 := bstep (se 1 (by rfl) ⟨546458, by rfl⟩ : syracuseStep 728611 = 1092917) B1092917
theorem B2629169 : Blo 726324 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B728627 : Blo 726324 728627 := bstep (se 1 (by rfl) ⟨546470, by rfl⟩ : syracuseStep 728627 = 1092941) B1092941
theorem B728643 : Blo 726324 728643 := bstep (se 1 (by rfl) ⟨546482, by rfl⟩ : syracuseStep 728643 = 1092965) B1092965
theorem B2530883 : Blo 726324 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B728659 : Blo 726324 728659 := bstep (se 1 (by rfl) ⟨546494, by rfl⟩ : syracuseStep 728659 = 1092989) B1092989
theorem B728675 : Blo 726324 728675 := bstep (se 1 (by rfl) ⟨546506, by rfl⟩ : syracuseStep 728675 = 1093013) B1093013
theorem B728691 : Blo 726324 728691 := bstep (se 1 (by rfl) ⟨546518, by rfl⟩ : syracuseStep 728691 = 1093037) B1093037
theorem B728707 : Blo 726324 728707 := bstep (se 1 (by rfl) ⟨546530, by rfl⟩ : syracuseStep 728707 = 1093061) B1093061
theorem B1384067 : Blo 726324 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B728723 : Blo 726324 728723 := bstep (se 1 (by rfl) ⟨546542, by rfl⟩ : syracuseStep 728723 = 1093085) B1093085
theorem B1842851 : Blo 726324 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B728739 : Blo 726324 728739 := bstep (se 1 (by rfl) ⟨546554, by rfl⟩ : syracuseStep 728739 = 1093109) B1093109
theorem B728755 : Blo 726324 728755 := bstep (se 1 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 728755 = 1093133) B1093133
theorem B728771 : Blo 726324 728771 := bstep (se 1 (by rfl) ⟨546578, by rfl⟩ : syracuseStep 728771 = 1093157) B1093157
theorem B728787 : Blo 726324 728787 := bstep (se 1 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 728787 = 1093181) B1093181
theorem B2760419 : Blo 726324 2760419 := bstep (se 1 (by rfl) ⟨2070314, by rfl⟩ : syracuseStep 2760419 = 4140629) B4140629
theorem B728803 : Blo 726324 728803 := bstep (se 1 (by rfl) ⟨546602, by rfl⟩ : syracuseStep 728803 = 1093205) B1093205
theorem B728819 : Blo 726324 728819 := bstep (se 1 (by rfl) ⟨546614, by rfl⟩ : syracuseStep 728819 = 1093229) B1093229
theorem B728835 : Blo 726324 728835 := bstep (se 1 (by rfl) ⟨546626, by rfl⟩ : syracuseStep 728835 = 1093253) B1093253
theorem B728851 : Blo 726324 728851 := bstep (se 1 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 728851 = 1093277) B1093277
theorem B728867 : Blo 726324 728867 := bstep (se 1 (by rfl) ⟨546650, by rfl⟩ : syracuseStep 728867 = 1093301) B1093301
theorem B728883 : Blo 726324 728883 := bstep (se 1 (by rfl) ⟨546662, by rfl⟩ : syracuseStep 728883 = 1093325) B1093325
theorem B728899 : Blo 726324 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B728915 : Blo 726324 728915 := bstep (se 1 (by rfl) ⟨546686, by rfl⟩ : syracuseStep 728915 = 1093373) B1093373
theorem B728931 : Blo 726324 728931 := bstep (se 1 (by rfl) ⟨546698, by rfl⟩ : syracuseStep 728931 = 1093397) B1093397
theorem B2334577 : Blo 726324 2334577 := bstep (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) B1750933
theorem B728947 : Blo 726324 728947 := bstep (se 1 (by rfl) ⟨546710, by rfl⟩ : syracuseStep 728947 = 1093421) B1093421
theorem B728963 : Blo 726324 728963 := bstep (se 1 (by rfl) ⟨546722, by rfl⟩ : syracuseStep 728963 = 1093445) B1093445
theorem B728979 : Blo 726324 728979 := bstep (se 1 (by rfl) ⟨546734, by rfl⟩ : syracuseStep 728979 = 1093469) B1093469
theorem B728995 : Blo 726324 728995 := bstep (se 1 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 728995 = 1093493) B1093493
theorem B729011 : Blo 726324 729011 := bstep (se 1 (by rfl) ⟨546758, by rfl⟩ : syracuseStep 729011 = 1093517) B1093517
theorem B729027 : Blo 726324 729027 := bstep (se 1 (by rfl) ⟨546770, by rfl⟩ : syracuseStep 729027 = 1093541) B1093541
theorem B1089491 : Blo 726324 1089491 := bstep (se 1 (by rfl) ⟨817118, by rfl⟩ : syracuseStep 1089491 = 1634237) B1634237
theorem B729043 : Blo 726324 729043 := bstep (se 1 (by rfl) ⟨546782, by rfl⟩ : syracuseStep 729043 = 1093565) B1093565
theorem B1122275 : Blo 726324 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B2334691 : Blo 726324 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B729059 : Blo 726324 729059 := bstep (se 1 (by rfl) ⟨546794, by rfl⟩ : syracuseStep 729059 = 1093589) B1093589
theorem B1089521 : Blo 726324 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B729075 : Blo 726324 729075 := bstep (se 1 (by rfl) ⟨546806, by rfl⟩ : syracuseStep 729075 = 1093613) B1093613
theorem B1089539 : Blo 726324 1089539 := bstep (se 1 (by rfl) ⟨817154, by rfl⟩ : syracuseStep 1089539 = 1634309) B1634309
theorem B729091 : Blo 726324 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B729107 : Blo 726324 729107 := bstep (se 1 (by rfl) ⟨546830, by rfl⟩ : syracuseStep 729107 = 1093661) B1093661
theorem B1089569 : Blo 726324 1089569 := bstep (se 2 (by rfl) ⟨408588, by rfl⟩ : syracuseStep 1089569 = 817177) B817177
theorem B729123 : Blo 726324 729123 := bstep (se 1 (by rfl) ⟨546842, by rfl⟩ : syracuseStep 729123 = 1093685) B1093685
theorem B1089587 : Blo 726324 1089587 := bstep (se 1 (by rfl) ⟨817190, by rfl⟩ : syracuseStep 1089587 = 1634381) B1634381
theorem B729139 : Blo 726324 729139 := bstep (se 1 (by rfl) ⟨546854, by rfl⟩ : syracuseStep 729139 = 1093709) B1093709
theorem B729155 : Blo 726324 729155 := bstep (se 1 (by rfl) ⟨546866, by rfl⟩ : syracuseStep 729155 = 1093733) B1093733
theorem B1089617 : Blo 726324 1089617 := bstep (se 2 (by rfl) ⟨408606, by rfl⟩ : syracuseStep 1089617 = 817213) B817213
theorem B729171 : Blo 726324 729171 := bstep (se 1 (by rfl) ⟨546878, by rfl⟩ : syracuseStep 729171 = 1093757) B1093757
theorem B1089635 : Blo 726324 1089635 := bstep (se 1 (by rfl) ⟨817226, by rfl⟩ : syracuseStep 1089635 = 1634453) B1634453
theorem B729187 : Blo 726324 729187 := bstep (se 1 (by rfl) ⟨546890, by rfl⟩ : syracuseStep 729187 = 1093781) B1093781
theorem B729203 : Blo 726324 729203 := bstep (se 1 (by rfl) ⟨546902, by rfl⟩ : syracuseStep 729203 = 1093805) B1093805
theorem B1089665 : Blo 726324 1089665 := bstep (se 2 (by rfl) ⟨408624, by rfl⟩ : syracuseStep 1089665 = 817249) B817249
theorem B729219 : Blo 726324 729219 := bstep (se 1 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 729219 = 1093829) B1093829
theorem B1089683 : Blo 726324 1089683 := bstep (se 1 (by rfl) ⟨817262, by rfl⟩ : syracuseStep 1089683 = 1634525) B1634525
theorem B729235 : Blo 726324 729235 := bstep (se 1 (by rfl) ⟨546926, by rfl⟩ : syracuseStep 729235 = 1093853) B1093853
theorem B3678371 : Blo 726324 3678371 := bstep (se 1 (by rfl) ⟨2758778, by rfl⟩ : syracuseStep 3678371 = 5517557) B5517557
theorem B729251 : Blo 726324 729251 := bstep (se 1 (by rfl) ⟨546938, by rfl⟩ : syracuseStep 729251 = 1093877) B1093877
theorem B1089713 : Blo 726324 1089713 := bstep (se 2 (by rfl) ⟨408642, by rfl⟩ : syracuseStep 1089713 = 817285) B817285
theorem B2072753 : Blo 726324 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B729267 : Blo 726324 729267 := bstep (se 1 (by rfl) ⟨546950, by rfl⟩ : syracuseStep 729267 = 1093901) B1093901
theorem B1089731 : Blo 726324 1089731 := bstep (se 1 (by rfl) ⟨817298, by rfl⟩ : syracuseStep 1089731 = 1634597) B1634597
theorem B729283 : Blo 726324 729283 := bstep (se 1 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 729283 = 1093925) B1093925
theorem B729299 : Blo 726324 729299 := bstep (se 1 (by rfl) ⟨546974, by rfl⟩ : syracuseStep 729299 = 1093949) B1093949
theorem B1089761 : Blo 726324 1089761 := bstep (se 2 (by rfl) ⟨408660, by rfl⟩ : syracuseStep 1089761 = 817321) B817321
theorem B729315 : Blo 726324 729315 := bstep (se 1 (by rfl) ⟨546986, by rfl⟩ : syracuseStep 729315 = 1093973) B1093973
theorem B4661489 : Blo 726324 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B1089779 : Blo 726324 1089779 := bstep (se 1 (by rfl) ⟨817334, by rfl⟩ : syracuseStep 1089779 = 1634669) B1634669
theorem B729331 : Blo 726324 729331 := bstep (se 1 (by rfl) ⟨546998, by rfl⟩ : syracuseStep 729331 = 1093997) B1093997
theorem B729347 : Blo 726324 729347 := bstep (se 1 (by rfl) ⟨547010, by rfl⟩ : syracuseStep 729347 = 1094021) B1094021
theorem B1089809 : Blo 726324 1089809 := bstep (se 2 (by rfl) ⟨408678, by rfl⟩ : syracuseStep 1089809 = 817357) B817357
theorem B729363 : Blo 726324 729363 := bstep (se 1 (by rfl) ⟨547022, by rfl⟩ : syracuseStep 729363 = 1094045) B1094045
theorem B1089827 : Blo 726324 1089827 := bstep (se 1 (by rfl) ⟨817370, by rfl⟩ : syracuseStep 1089827 = 1634741) B1634741
theorem B729379 : Blo 726324 729379 := bstep (se 1 (by rfl) ⟨547034, by rfl⟩ : syracuseStep 729379 = 1094069) B1094069
theorem B729395 : Blo 726324 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B1089857 : Blo 726324 1089857 := bstep (se 2 (by rfl) ⟨408696, by rfl⟩ : syracuseStep 1089857 = 817393) B817393
theorem B729411 : Blo 726324 729411 := bstep (se 1 (by rfl) ⟨547058, by rfl⟩ : syracuseStep 729411 = 1094117) B1094117
theorem B1089875 : Blo 726324 1089875 := bstep (se 1 (by rfl) ⟨817406, by rfl⟩ : syracuseStep 1089875 = 1634813) B1634813
theorem B729427 : Blo 726324 729427 := bstep (se 1 (by rfl) ⟨547070, by rfl⟩ : syracuseStep 729427 = 1094141) B1094141
theorem B729443 : Blo 726324 729443 := bstep (se 1 (by rfl) ⟨547082, by rfl⟩ : syracuseStep 729443 = 1094165) B1094165
theorem B1089905 : Blo 726324 1089905 := bstep (se 2 (by rfl) ⟨408714, by rfl⟩ : syracuseStep 1089905 = 817429) B817429
theorem B2761073 : Blo 726324 2761073 := bstep (se 2 (by rfl) ⟨1035402, by rfl⟩ : syracuseStep 2761073 = 2070805) B2070805
theorem B729459 : Blo 726324 729459 := bstep (se 1 (by rfl) ⟨547094, by rfl⟩ : syracuseStep 729459 = 1094189) B1094189
theorem B1089923 : Blo 726324 1089923 := bstep (se 1 (by rfl) ⟨817442, by rfl⟩ : syracuseStep 1089923 = 1634885) B1634885
theorem B729475 : Blo 726324 729475 := bstep (se 1 (by rfl) ⟨547106, by rfl⟩ : syracuseStep 729475 = 1094213) B1094213
theorem B729491 : Blo 726324 729491 := bstep (se 1 (by rfl) ⟨547118, by rfl⟩ : syracuseStep 729491 = 1094237) B1094237
theorem B1089953 : Blo 726324 1089953 := bstep (se 2 (by rfl) ⟨408732, by rfl⟩ : syracuseStep 1089953 = 817465) B817465
theorem B729507 : Blo 726324 729507 := bstep (se 1 (by rfl) ⟨547130, by rfl⟩ : syracuseStep 729507 = 1094261) B1094261
theorem B1745329 : Blo 726324 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B1089971 : Blo 726324 1089971 := bstep (se 1 (by rfl) ⟨817478, by rfl⟩ : syracuseStep 1089971 = 1634957) B1634957
theorem B729523 : Blo 726324 729523 := bstep (se 1 (by rfl) ⟨547142, by rfl⟩ : syracuseStep 729523 = 1094285) B1094285
theorem B729539 : Blo 726324 729539 := bstep (se 1 (by rfl) ⟨547154, by rfl⟩ : syracuseStep 729539 = 1094309) B1094309
theorem B1090001 : Blo 726324 1090001 := bstep (se 2 (by rfl) ⟨408750, by rfl⟩ : syracuseStep 1090001 = 817501) B817501
theorem B729555 : Blo 726324 729555 := bstep (se 1 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 729555 = 1094333) B1094333
theorem B1090019 : Blo 726324 1090019 := bstep (se 1 (by rfl) ⟨817514, by rfl⟩ : syracuseStep 1090019 = 1635029) B1635029
theorem B729571 : Blo 726324 729571 := bstep (se 1 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 729571 = 1094357) B1094357
theorem B729587 : Blo 726324 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B1090049 : Blo 726324 1090049 := bstep (se 2 (by rfl) ⟨408768, by rfl⟩ : syracuseStep 1090049 = 817537) B817537
theorem B729603 : Blo 726324 729603 := bstep (se 1 (by rfl) ⟨547202, by rfl⟩ : syracuseStep 729603 = 1094405) B1094405
theorem B1090067 : Blo 726324 1090067 := bstep (se 1 (by rfl) ⟨817550, by rfl⟩ : syracuseStep 1090067 = 1635101) B1635101
theorem B729619 : Blo 726324 729619 := bstep (se 1 (by rfl) ⟨547214, by rfl⟩ : syracuseStep 729619 = 1094429) B1094429
theorem B729635 : Blo 726324 729635 := bstep (se 1 (by rfl) ⟨547226, by rfl⟩ : syracuseStep 729635 = 1094453) B1094453
theorem B1090097 : Blo 726324 1090097 := bstep (se 2 (by rfl) ⟨408786, by rfl⟩ : syracuseStep 1090097 = 817573) B817573
theorem B1385009 : Blo 726324 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B729651 : Blo 726324 729651 := bstep (se 1 (by rfl) ⟨547238, by rfl⟩ : syracuseStep 729651 = 1094477) B1094477
theorem B1090115 : Blo 726324 1090115 := bstep (se 1 (by rfl) ⟨817586, by rfl⟩ : syracuseStep 1090115 = 1635173) B1635173
theorem B729667 : Blo 726324 729667 := bstep (se 1 (by rfl) ⟨547250, by rfl⟩ : syracuseStep 729667 = 1094501) B1094501
theorem B1843793 : Blo 726324 1843793 := bstep (se 2 (by rfl) ⟨691422, by rfl⟩ : syracuseStep 1843793 = 1382845) B1382845
theorem B729683 : Blo 726324 729683 := bstep (se 1 (by rfl) ⟨547262, by rfl⟩ : syracuseStep 729683 = 1094525) B1094525
theorem B1090145 : Blo 726324 1090145 := bstep (se 2 (by rfl) ⟨408804, by rfl⟩ : syracuseStep 1090145 = 817609) B817609
theorem B729699 : Blo 726324 729699 := bstep (se 1 (by rfl) ⟨547274, by rfl⟩ : syracuseStep 729699 = 1094549) B1094549
theorem B1090163 : Blo 726324 1090163 := bstep (se 1 (by rfl) ⟨817622, by rfl⟩ : syracuseStep 1090163 = 1635245) B1635245
theorem B729715 : Blo 726324 729715 := bstep (se 1 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 729715 = 1094573) B1094573
theorem B1843843 : Blo 726324 1843843 := bstep (se 1 (by rfl) ⟨1382882, by rfl⟩ : syracuseStep 1843843 = 2765765) B2765765
theorem B729731 : Blo 726324 729731 := bstep (se 1 (by rfl) ⟨547298, by rfl⟩ : syracuseStep 729731 = 1094597) B1094597
theorem B1090193 : Blo 726324 1090193 := bstep (se 2 (by rfl) ⟨408822, by rfl⟩ : syracuseStep 1090193 = 817645) B817645
theorem B729747 : Blo 726324 729747 := bstep (se 1 (by rfl) ⟨547310, by rfl⟩ : syracuseStep 729747 = 1094621) B1094621
theorem B1090211 : Blo 726324 1090211 := bstep (se 1 (by rfl) ⟨817658, by rfl⟩ : syracuseStep 1090211 = 1635317) B1635317
theorem B729763 : Blo 726324 729763 := bstep (se 1 (by rfl) ⟨547322, by rfl⟩ : syracuseStep 729763 = 1094645) B1094645
theorem B2335409 : Blo 726324 2335409 := bstep (se 2 (by rfl) ⟨875778, by rfl⟩ : syracuseStep 2335409 = 1751557) B1751557
theorem B729779 : Blo 726324 729779 := bstep (se 1 (by rfl) ⟨547334, by rfl⟩ : syracuseStep 729779 = 1094669) B1094669
theorem B1090241 : Blo 726324 1090241 := bstep (se 2 (by rfl) ⟨408840, by rfl⟩ : syracuseStep 1090241 = 817681) B817681
theorem B729795 : Blo 726324 729795 := bstep (se 1 (by rfl) ⟨547346, by rfl⟩ : syracuseStep 729795 = 1094693) B1094693
theorem B1090259 : Blo 726324 1090259 := bstep (se 1 (by rfl) ⟨817694, by rfl⟩ : syracuseStep 1090259 = 1635389) B1635389
theorem B729811 : Blo 726324 729811 := bstep (se 1 (by rfl) ⟨547358, by rfl⟩ : syracuseStep 729811 = 1094717) B1094717
theorem B729827 : Blo 726324 729827 := bstep (se 1 (by rfl) ⟨547370, by rfl⟩ : syracuseStep 729827 = 1094741) B1094741
theorem B4137713 : Blo 726324 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B1090289 : Blo 726324 1090289 := bstep (se 2 (by rfl) ⟨408858, by rfl⟩ : syracuseStep 1090289 = 817717) B817717
theorem B729843 : Blo 726324 729843 := bstep (se 1 (by rfl) ⟨547382, by rfl⟩ : syracuseStep 729843 = 1094765) B1094765
theorem B1090307 : Blo 726324 1090307 := bstep (se 1 (by rfl) ⟨817730, by rfl⟩ : syracuseStep 1090307 = 1635461) B1635461
theorem B729859 : Blo 726324 729859 := bstep (se 1 (by rfl) ⟨547394, by rfl⟩ : syracuseStep 729859 = 1094789) B1094789
theorem B1843985 : Blo 726324 1843985 := bstep (se 2 (by rfl) ⟨691494, by rfl⟩ : syracuseStep 1843985 = 1382989) B1382989
theorem B729875 : Blo 726324 729875 := bstep (se 1 (by rfl) ⟨547406, by rfl⟩ : syracuseStep 729875 = 1094813) B1094813
theorem B1090337 : Blo 726324 1090337 := bstep (se 2 (by rfl) ⟨408876, by rfl⟩ : syracuseStep 1090337 = 817753) B817753
theorem B729891 : Blo 726324 729891 := bstep (se 1 (by rfl) ⟨547418, by rfl⟩ : syracuseStep 729891 = 1094837) B1094837
theorem B1090355 : Blo 726324 1090355 := bstep (se 1 (by rfl) ⟨817766, by rfl⟩ : syracuseStep 1090355 = 1635533) B1635533
theorem B729907 : Blo 726324 729907 := bstep (se 1 (by rfl) ⟨547430, by rfl⟩ : syracuseStep 729907 = 1094861) B1094861
theorem B729923 : Blo 726324 729923 := bstep (se 1 (by rfl) ⟨547442, by rfl⟩ : syracuseStep 729923 = 1094885) B1094885
theorem B1090385 : Blo 726324 1090385 := bstep (se 2 (by rfl) ⟨408894, by rfl⟩ : syracuseStep 1090385 = 817789) B817789
theorem B729939 : Blo 726324 729939 := bstep (se 1 (by rfl) ⟨547454, by rfl⟩ : syracuseStep 729939 = 1094909) B1094909
theorem B1090403 : Blo 726324 1090403 := bstep (se 1 (by rfl) ⟨817802, by rfl⟩ : syracuseStep 1090403 = 1635605) B1635605
theorem B729955 : Blo 726324 729955 := bstep (se 1 (by rfl) ⟨547466, by rfl⟩ : syracuseStep 729955 = 1094933) B1094933
theorem B729971 : Blo 726324 729971 := bstep (se 1 (by rfl) ⟨547478, by rfl⟩ : syracuseStep 729971 = 1094957) B1094957
theorem B1090433 : Blo 726324 1090433 := bstep (se 2 (by rfl) ⟨408912, by rfl⟩ : syracuseStep 1090433 = 817825) B817825
theorem B729987 : Blo 726324 729987 := bstep (se 1 (by rfl) ⟨547490, by rfl⟩ : syracuseStep 729987 = 1094981) B1094981
theorem B1090451 : Blo 726324 1090451 := bstep (se 1 (by rfl) ⟨817838, by rfl⟩ : syracuseStep 1090451 = 1635677) B1635677
theorem B730003 : Blo 726324 730003 := bstep (se 1 (by rfl) ⟨547502, by rfl⟩ : syracuseStep 730003 = 1095005) B1095005
theorem B730019 : Blo 726324 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B1090481 : Blo 726324 1090481 := bstep (se 2 (by rfl) ⟨408930, by rfl⟩ : syracuseStep 1090481 = 817861) B817861
theorem B730035 : Blo 726324 730035 := bstep (se 1 (by rfl) ⟨547526, by rfl⟩ : syracuseStep 730035 = 1095053) B1095053
theorem B1090499 : Blo 726324 1090499 := bstep (se 1 (by rfl) ⟨817874, by rfl⟩ : syracuseStep 1090499 = 1635749) B1635749
theorem B2073539 : Blo 726324 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B730051 : Blo 726324 730051 := bstep (se 1 (by rfl) ⟨547538, by rfl⟩ : syracuseStep 730051 = 1095077) B1095077
theorem B3679181 : Blo 726324 3679181 := bstep (se 3 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 3679181 = 1379693) B1379693
theorem B730067 : Blo 726324 730067 := bstep (se 1 (by rfl) ⟨547550, by rfl⟩ : syracuseStep 730067 = 1095101) B1095101
theorem B1090529 : Blo 726324 1090529 := bstep (se 2 (by rfl) ⟨408948, by rfl⟩ : syracuseStep 1090529 = 817897) B817897
theorem B730083 : Blo 726324 730083 := bstep (se 1 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 730083 = 1095125) B1095125
theorem B1090547 : Blo 726324 1090547 := bstep (se 1 (by rfl) ⟨817910, by rfl⟩ : syracuseStep 1090547 = 1635821) B1635821
theorem B730099 : Blo 726324 730099 := bstep (se 1 (by rfl) ⟨547574, by rfl⟩ : syracuseStep 730099 = 1095149) B1095149
theorem B730115 : Blo 726324 730115 := bstep (se 1 (by rfl) ⟨547586, by rfl⟩ : syracuseStep 730115 = 1095173) B1095173
theorem B1090577 : Blo 726324 1090577 := bstep (se 2 (by rfl) ⟨408966, by rfl⟩ : syracuseStep 1090577 = 817933) B817933
theorem B730131 : Blo 726324 730131 := bstep (se 1 (by rfl) ⟨547598, by rfl⟩ : syracuseStep 730131 = 1095197) B1095197
theorem B1090595 : Blo 726324 1090595 := bstep (se 1 (by rfl) ⟨817946, by rfl⟩ : syracuseStep 1090595 = 1635893) B1635893
theorem B730147 : Blo 726324 730147 := bstep (se 1 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 730147 = 1095221) B1095221
theorem B730163 : Blo 726324 730163 := bstep (se 1 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 730163 = 1095245) B1095245
theorem B1090625 : Blo 726324 1090625 := bstep (se 2 (by rfl) ⟨408984, by rfl⟩ : syracuseStep 1090625 = 817969) B817969
theorem B730179 : Blo 726324 730179 := bstep (se 1 (by rfl) ⟨547634, by rfl⟩ : syracuseStep 730179 = 1095269) B1095269
theorem B1090643 : Blo 726324 1090643 := bstep (se 1 (by rfl) ⟨817982, by rfl⟩ : syracuseStep 1090643 = 1635965) B1635965
theorem B730195 : Blo 726324 730195 := bstep (se 1 (by rfl) ⟨547646, by rfl⟩ : syracuseStep 730195 = 1095293) B1095293
theorem B730211 : Blo 726324 730211 := bstep (se 1 (by rfl) ⟨547658, by rfl⟩ : syracuseStep 730211 = 1095317) B1095317
theorem B1090673 : Blo 726324 1090673 := bstep (se 2 (by rfl) ⟨409002, by rfl⟩ : syracuseStep 1090673 = 818005) B818005
theorem B730227 : Blo 726324 730227 := bstep (se 1 (by rfl) ⟨547670, by rfl⟩ : syracuseStep 730227 = 1095341) B1095341
theorem B1090691 : Blo 726324 1090691 := bstep (se 1 (by rfl) ⟨818018, by rfl⟩ : syracuseStep 1090691 = 1636037) B1636037
theorem B730243 : Blo 726324 730243 := bstep (se 1 (by rfl) ⟨547682, by rfl⟩ : syracuseStep 730243 = 1095365) B1095365
theorem B730259 : Blo 726324 730259 := bstep (se 1 (by rfl) ⟨547694, by rfl⟩ : syracuseStep 730259 = 1095389) B1095389
theorem B1090721 : Blo 726324 1090721 := bstep (se 2 (by rfl) ⟨409020, by rfl⟩ : syracuseStep 1090721 = 818041) B818041
theorem B730275 : Blo 726324 730275 := bstep (se 1 (by rfl) ⟨547706, by rfl⟩ : syracuseStep 730275 = 1095413) B1095413
theorem B1090739 : Blo 726324 1090739 := bstep (se 1 (by rfl) ⟨818054, by rfl⟩ : syracuseStep 1090739 = 1636109) B1636109
theorem B730291 : Blo 726324 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B730307 : Blo 726324 730307 := bstep (se 1 (by rfl) ⟨547730, by rfl⟩ : syracuseStep 730307 = 1095461) B1095461
theorem B2335949 : Blo 726324 2335949 := bstep (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) B875981
theorem B1090769 : Blo 726324 1090769 := bstep (se 2 (by rfl) ⟨409038, by rfl⟩ : syracuseStep 1090769 = 818077) B818077
theorem B730323 : Blo 726324 730323 := bstep (se 1 (by rfl) ⟨547742, by rfl⟩ : syracuseStep 730323 = 1095485) B1095485
theorem B1090787 : Blo 726324 1090787 := bstep (se 1 (by rfl) ⟨818090, by rfl⟩ : syracuseStep 1090787 = 1636181) B1636181
theorem B1090817 : Blo 726324 1090817 := bstep (se 2 (by rfl) ⟨409056, by rfl⟩ : syracuseStep 1090817 = 818113) B818113
theorem B2073869 : Blo 726324 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B1090835 : Blo 726324 1090835 := bstep (se 1 (by rfl) ⟨818126, by rfl⟩ : syracuseStep 1090835 = 1636253) B1636253
theorem B1090865 : Blo 726324 1090865 := bstep (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) B818149
theorem B1090883 : Blo 726324 1090883 := bstep (se 1 (by rfl) ⟨818162, by rfl⟩ : syracuseStep 1090883 = 1636325) B1636325
theorem B2073937 : Blo 726324 2073937 := bstep (se 2 (by rfl) ⟨777726, by rfl⟩ : syracuseStep 2073937 = 1555453) B1555453
theorem B1090913 : Blo 726324 1090913 := bstep (se 2 (by rfl) ⟨409092, by rfl⟩ : syracuseStep 1090913 = 818185) B818185
theorem B1090931 : Blo 726324 1090931 := bstep (se 1 (by rfl) ⟨818198, by rfl⟩ : syracuseStep 1090931 = 1636397) B1636397
theorem B1090961 : Blo 726324 1090961 := bstep (se 2 (by rfl) ⟨409110, by rfl⟩ : syracuseStep 1090961 = 818221) B818221
theorem B1090979 : Blo 726324 1090979 := bstep (se 1 (by rfl) ⟨818234, by rfl⟩ : syracuseStep 1090979 = 1636469) B1636469
theorem B3745187 : Blo 726324 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B1385905 : Blo 726324 1385905 := bstep (se 2 (by rfl) ⟨519714, by rfl⟩ : syracuseStep 1385905 = 1039429) B1039429
theorem B1091009 : Blo 726324 1091009 := bstep (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) B818257
theorem B1091027 : Blo 726324 1091027 := bstep (se 1 (by rfl) ⟨818270, by rfl⟩ : syracuseStep 1091027 = 1636541) B1636541
theorem B1091057 : Blo 726324 1091057 := bstep (se 2 (by rfl) ⟨409146, by rfl⟩ : syracuseStep 1091057 = 818293) B818293
theorem B1091075 : Blo 726324 1091075 := bstep (se 1 (by rfl) ⟨818306, by rfl⟩ : syracuseStep 1091075 = 1636613) B1636613
theorem B1091105 : Blo 726324 1091105 := bstep (se 2 (by rfl) ⟨409164, by rfl⟩ : syracuseStep 1091105 = 818329) B818329
theorem B1091123 : Blo 726324 1091123 := bstep (se 1 (by rfl) ⟨818342, by rfl⟩ : syracuseStep 1091123 = 1636685) B1636685
theorem B2106947 : Blo 726324 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B1091153 : Blo 726324 1091153 := bstep (se 2 (by rfl) ⟨409182, by rfl⟩ : syracuseStep 1091153 = 818365) B818365
theorem B1386065 : Blo 726324 1386065 := bstep (se 2 (by rfl) ⟨519774, by rfl⟩ : syracuseStep 1386065 = 1039549) B1039549
theorem B1091171 : Blo 726324 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B2074211 : Blo 726324 2074211 := bstep (se 1 (by rfl) ⟨1555658, by rfl⟩ : syracuseStep 2074211 = 3111317) B3111317
theorem B1091201 : Blo 726324 1091201 := bstep (se 2 (by rfl) ⟨409200, by rfl⟩ : syracuseStep 1091201 = 818401) B818401
theorem B1091219 : Blo 726324 1091219 := bstep (se 1 (by rfl) ⟨818414, by rfl⟩ : syracuseStep 1091219 = 1636829) B1636829
theorem B1091249 : Blo 726324 1091249 := bstep (se 2 (by rfl) ⟨409218, by rfl⟩ : syracuseStep 1091249 = 818437) B818437
theorem B1091267 : Blo 726324 1091267 := bstep (se 1 (by rfl) ⟨818450, by rfl⟩ : syracuseStep 1091267 = 1636901) B1636901
theorem B1091297 : Blo 726324 1091297 := bstep (se 2 (by rfl) ⟨409236, by rfl⟩ : syracuseStep 1091297 = 818473) B818473
theorem B1844977 : Blo 726324 1844977 := bstep (se 2 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 1844977 = 1383733) B1383733
theorem B1091315 : Blo 726324 1091315 := bstep (se 1 (by rfl) ⟨818486, by rfl⟩ : syracuseStep 1091315 = 1636973) B1636973
theorem B1091345 : Blo 726324 1091345 := bstep (se 2 (by rfl) ⟨409254, by rfl⟩ : syracuseStep 1091345 = 818509) B818509
theorem B1091363 : Blo 726324 1091363 := bstep (se 1 (by rfl) ⟨818522, by rfl⟩ : syracuseStep 1091363 = 1637045) B1637045
theorem B2762531 : Blo 726324 2762531 := bstep (se 1 (by rfl) ⟨2071898, by rfl⟩ : syracuseStep 2762531 = 4143797) B4143797
theorem B2762545 : Blo 726324 2762545 := bstep (se 2 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 2762545 = 2071909) B2071909
theorem B1091393 : Blo 726324 1091393 := bstep (se 2 (by rfl) ⟨409272, by rfl⟩ : syracuseStep 1091393 = 818545) B818545
theorem B1091411 : Blo 726324 1091411 := bstep (se 1 (by rfl) ⟨818558, by rfl⟩ : syracuseStep 1091411 = 1637117) B1637117
theorem B1091441 : Blo 726324 1091441 := bstep (se 2 (by rfl) ⟨409290, by rfl⟩ : syracuseStep 1091441 = 818581) B818581
theorem B1091459 : Blo 726324 1091459 := bstep (se 1 (by rfl) ⟨818594, by rfl⟩ : syracuseStep 1091459 = 1637189) B1637189
theorem B1091489 : Blo 726324 1091489 := bstep (se 2 (by rfl) ⟨409308, by rfl⟩ : syracuseStep 1091489 = 818617) B818617
theorem B1091507 : Blo 726324 1091507 := bstep (se 1 (by rfl) ⟨818630, by rfl⟩ : syracuseStep 1091507 = 1637261) B1637261
theorem B8857525 : Blo 726324 8857525 := bstep (se 5 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 8857525 = 830393) B830393
theorem B1091537 : Blo 726324 1091537 := bstep (se 2 (by rfl) ⟨409326, by rfl⟩ : syracuseStep 1091537 = 818653) B818653
theorem B1091555 : Blo 726324 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B1386467 : Blo 726324 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B1091585 : Blo 726324 1091585 := bstep (se 2 (by rfl) ⟨409344, by rfl⟩ : syracuseStep 1091585 = 818689) B818689
theorem B1845251 : Blo 726324 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B1091603 : Blo 726324 1091603 := bstep (se 1 (by rfl) ⟨818702, by rfl⟩ : syracuseStep 1091603 = 1637405) B1637405
theorem B1091633 : Blo 726324 1091633 := bstep (se 2 (by rfl) ⟨409362, by rfl⟩ : syracuseStep 1091633 = 818725) B818725
theorem B1091651 : Blo 726324 1091651 := bstep (se 1 (by rfl) ⟨818738, by rfl⟩ : syracuseStep 1091651 = 1637477) B1637477
theorem B1091681 : Blo 726324 1091681 := bstep (se 2 (by rfl) ⟨409380, by rfl⟩ : syracuseStep 1091681 = 818761) B818761
theorem B1091699 : Blo 726324 1091699 := bstep (se 1 (by rfl) ⟨818774, by rfl⟩ : syracuseStep 1091699 = 1637549) B1637549
theorem B1091729 : Blo 726324 1091729 := bstep (se 2 (by rfl) ⟨409398, by rfl⟩ : syracuseStep 1091729 = 818797) B818797
theorem B4139171 : Blo 726324 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B1091747 : Blo 726324 1091747 := bstep (se 1 (by rfl) ⟨818810, by rfl⟩ : syracuseStep 1091747 = 1637621) B1637621
theorem B1091777 : Blo 726324 1091777 := bstep (se 2 (by rfl) ⟨409416, by rfl⟩ : syracuseStep 1091777 = 818833) B818833
theorem B1845443 : Blo 726324 1845443 := bstep (se 1 (by rfl) ⟨1384082, by rfl⟩ : syracuseStep 1845443 = 2768165) B2768165
theorem B1091795 : Blo 726324 1091795 := bstep (se 1 (by rfl) ⟨818846, by rfl⟩ : syracuseStep 1091795 = 1637693) B1637693
theorem B1091825 : Blo 726324 1091825 := bstep (se 2 (by rfl) ⟨409434, by rfl⟩ : syracuseStep 1091825 = 818869) B818869
theorem B1091843 : Blo 726324 1091843 := bstep (se 1 (by rfl) ⟨818882, by rfl⟩ : syracuseStep 1091843 = 1637765) B1637765
theorem B1091873 : Blo 726324 1091873 := bstep (se 2 (by rfl) ⟨409452, by rfl⟩ : syracuseStep 1091873 = 818905) B818905
theorem B1091891 : Blo 726324 1091891 := bstep (se 1 (by rfl) ⟨818918, by rfl⟩ : syracuseStep 1091891 = 1637837) B1637837
theorem B1091921 : Blo 726324 1091921 := bstep (se 2 (by rfl) ⟨409470, by rfl⟩ : syracuseStep 1091921 = 818941) B818941
theorem B1091939 : Blo 726324 1091939 := bstep (se 1 (by rfl) ⟨818954, by rfl⟩ : syracuseStep 1091939 = 1637909) B1637909
theorem B1091969 : Blo 726324 1091969 := bstep (se 2 (by rfl) ⟨409488, by rfl⟩ : syracuseStep 1091969 = 818977) B818977
theorem B1091987 : Blo 726324 1091987 := bstep (se 1 (by rfl) ⟨818990, by rfl⟩ : syracuseStep 1091987 = 1637981) B1637981
theorem B2075053 : Blo 726324 2075053 := bstep (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) B778145
theorem B1092017 : Blo 726324 1092017 := bstep (se 2 (by rfl) ⟨409506, by rfl⟩ : syracuseStep 1092017 = 819013) B819013
theorem B1092035 : Blo 726324 1092035 := bstep (se 1 (by rfl) ⟨819026, by rfl⟩ : syracuseStep 1092035 = 1638053) B1638053
theorem B1092065 : Blo 726324 1092065 := bstep (se 2 (by rfl) ⟨409524, by rfl⟩ : syracuseStep 1092065 = 819049) B819049
theorem B1092083 : Blo 726324 1092083 := bstep (se 1 (by rfl) ⟨819062, by rfl⟩ : syracuseStep 1092083 = 1638125) B1638125
theorem B1092113 : Blo 726324 1092113 := bstep (se 2 (by rfl) ⟨409542, by rfl⟩ : syracuseStep 1092113 = 819085) B819085
theorem B1092131 : Blo 726324 1092131 := bstep (se 1 (by rfl) ⟨819098, by rfl⟩ : syracuseStep 1092131 = 1638197) B1638197
theorem B1092161 : Blo 726324 1092161 := bstep (se 2 (by rfl) ⟨409560, by rfl⟩ : syracuseStep 1092161 = 819121) B819121
theorem B2075213 : Blo 726324 2075213 := bstep (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) B778205
theorem B1092179 : Blo 726324 1092179 := bstep (se 1 (by rfl) ⟨819134, by rfl⟩ : syracuseStep 1092179 = 1638269) B1638269
theorem B1092209 : Blo 726324 1092209 := bstep (se 2 (by rfl) ⟨409578, by rfl⟩ : syracuseStep 1092209 = 819157) B819157
theorem B1092227 : Blo 726324 1092227 := bstep (se 1 (by rfl) ⟨819170, by rfl⟩ : syracuseStep 1092227 = 1638341) B1638341
theorem B1092257 : Blo 726324 1092257 := bstep (se 2 (by rfl) ⟨409596, by rfl⟩ : syracuseStep 1092257 = 819193) B819193
theorem B1092275 : Blo 726324 1092275 := bstep (se 1 (by rfl) ⟨819206, by rfl⟩ : syracuseStep 1092275 = 1638413) B1638413
theorem B1092305 : Blo 726324 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B1092323 : Blo 726324 1092323 := bstep (se 1 (by rfl) ⟨819242, by rfl⟩ : syracuseStep 1092323 = 1638485) B1638485
theorem B1092353 : Blo 726324 1092353 := bstep (se 2 (by rfl) ⟨409632, by rfl⟩ : syracuseStep 1092353 = 819265) B819265
theorem B2075395 : Blo 726324 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1092371 : Blo 726324 1092371 := bstep (se 1 (by rfl) ⟨819278, by rfl⟩ : syracuseStep 1092371 = 1638557) B1638557
theorem B1092401 : Blo 726324 1092401 := bstep (se 2 (by rfl) ⟨409650, by rfl⟩ : syracuseStep 1092401 = 819301) B819301
theorem B1092419 : Blo 726324 1092419 := bstep (se 1 (by rfl) ⟨819314, by rfl⟩ : syracuseStep 1092419 = 1638629) B1638629
theorem B1092449 : Blo 726324 1092449 := bstep (se 2 (by rfl) ⟨409668, by rfl⟩ : syracuseStep 1092449 = 819337) B819337
theorem B1092467 : Blo 726324 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B1092497 : Blo 726324 1092497 := bstep (se 2 (by rfl) ⟨409686, by rfl⟩ : syracuseStep 1092497 = 819373) B819373
theorem B1092515 : Blo 726324 1092515 := bstep (se 1 (by rfl) ⟨819386, by rfl⟩ : syracuseStep 1092515 = 1638773) B1638773
theorem B1092545 : Blo 726324 1092545 := bstep (se 2 (by rfl) ⟨409704, by rfl⟩ : syracuseStep 1092545 = 819409) B819409
theorem B1092563 : Blo 726324 1092563 := bstep (se 1 (by rfl) ⟨819422, by rfl⟩ : syracuseStep 1092563 = 1638845) B1638845
theorem B1092593 : Blo 726324 1092593 := bstep (se 2 (by rfl) ⟨409722, by rfl⟩ : syracuseStep 1092593 = 819445) B819445
theorem B1092611 : Blo 726324 1092611 := bstep (se 1 (by rfl) ⟨819458, by rfl⟩ : syracuseStep 1092611 = 1638917) B1638917
theorem B1092641 : Blo 726324 1092641 := bstep (se 2 (by rfl) ⟨409740, by rfl⟩ : syracuseStep 1092641 = 819481) B819481
theorem B1092659 : Blo 726324 1092659 := bstep (se 1 (by rfl) ⟨819494, by rfl⟩ : syracuseStep 1092659 = 1638989) B1638989
theorem B2337869 : Blo 726324 2337869 := bstep (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) B876701
theorem B1092689 : Blo 726324 1092689 := bstep (se 2 (by rfl) ⟨409758, by rfl⟩ : syracuseStep 1092689 = 819517) B819517
theorem B1092707 : Blo 726324 1092707 := bstep (se 1 (by rfl) ⟨819530, by rfl⟩ : syracuseStep 1092707 = 1639061) B1639061
theorem B1846385 : Blo 726324 1846385 := bstep (se 2 (by rfl) ⟨692394, by rfl⟩ : syracuseStep 1846385 = 1384789) B1384789
theorem B1092737 : Blo 726324 1092737 := bstep (se 2 (by rfl) ⟨409776, by rfl⟩ : syracuseStep 1092737 = 819553) B819553
theorem B4140173 : Blo 726324 4140173 := bstep (se 3 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 4140173 = 1552565) B1552565
theorem B4664461 : Blo 726324 4664461 := bstep (se 3 (by rfl) ⟨874586, by rfl⟩ : syracuseStep 4664461 = 1749173) B1749173
theorem B1092755 : Blo 726324 1092755 := bstep (se 1 (by rfl) ⟨819566, by rfl⟩ : syracuseStep 1092755 = 1639133) B1639133
theorem B1617059 : Blo 726324 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B1846435 : Blo 726324 1846435 := bstep (se 1 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 1846435 = 2769653) B2769653
theorem B1092785 : Blo 726324 1092785 := bstep (se 2 (by rfl) ⟨409794, by rfl⟩ : syracuseStep 1092785 = 819589) B819589
theorem B1092803 : Blo 726324 1092803 := bstep (se 1 (by rfl) ⟨819602, by rfl⟩ : syracuseStep 1092803 = 1639205) B1639205
theorem B1092833 : Blo 726324 1092833 := bstep (se 2 (by rfl) ⟨409812, by rfl⟩ : syracuseStep 1092833 = 819625) B819625
theorem B2764003 : Blo 726324 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B1092851 : Blo 726324 1092851 := bstep (se 1 (by rfl) ⟨819638, by rfl⟩ : syracuseStep 1092851 = 1639277) B1639277
theorem B1092881 : Blo 726324 1092881 := bstep (se 2 (by rfl) ⟨409830, by rfl⟩ : syracuseStep 1092881 = 819661) B819661
theorem B1092899 : Blo 726324 1092899 := bstep (se 1 (by rfl) ⟨819674, by rfl⟩ : syracuseStep 1092899 = 1639349) B1639349
theorem B1846577 : Blo 726324 1846577 := bstep (se 2 (by rfl) ⟨692466, by rfl⟩ : syracuseStep 1846577 = 1384933) B1384933
theorem B1092929 : Blo 726324 1092929 := bstep (se 2 (by rfl) ⟨409848, by rfl⟩ : syracuseStep 1092929 = 819697) B819697
theorem B1092947 : Blo 726324 1092947 := bstep (se 1 (by rfl) ⟨819710, by rfl⟩ : syracuseStep 1092947 = 1639421) B1639421
theorem B1092977 : Blo 726324 1092977 := bstep (se 2 (by rfl) ⟨409866, by rfl⟩ : syracuseStep 1092977 = 819733) B819733
theorem B1092995 : Blo 726324 1092995 := bstep (se 1 (by rfl) ⟨819746, by rfl⟩ : syracuseStep 1092995 = 1639493) B1639493
theorem B1093025 : Blo 726324 1093025 := bstep (se 2 (by rfl) ⟨409884, by rfl⟩ : syracuseStep 1093025 = 819769) B819769
theorem B1093043 : Blo 726324 1093043 := bstep (se 1 (by rfl) ⟨819782, by rfl⟩ : syracuseStep 1093043 = 1639565) B1639565
theorem B1093073 : Blo 726324 1093073 := bstep (se 2 (by rfl) ⟨409902, by rfl⟩ : syracuseStep 1093073 = 819805) B819805
theorem B1093091 : Blo 726324 1093091 := bstep (se 1 (by rfl) ⟨819818, by rfl⟩ : syracuseStep 1093091 = 1639637) B1639637
theorem B1093121 : Blo 726324 1093121 := bstep (se 2 (by rfl) ⟨409920, by rfl⟩ : syracuseStep 1093121 = 819841) B819841
theorem B1093139 : Blo 726324 1093139 := bstep (se 1 (by rfl) ⟨819854, by rfl⟩ : syracuseStep 1093139 = 1639709) B1639709
theorem B1093169 : Blo 726324 1093169 := bstep (se 2 (by rfl) ⟨409938, by rfl⟩ : syracuseStep 1093169 = 819877) B819877
theorem B1093187 : Blo 726324 1093187 := bstep (se 1 (by rfl) ⟨819890, by rfl⟩ : syracuseStep 1093187 = 1639781) B1639781
theorem B1093217 : Blo 726324 1093217 := bstep (se 2 (by rfl) ⟨409956, by rfl⟩ : syracuseStep 1093217 = 819913) B819913
theorem B1093235 : Blo 726324 1093235 := bstep (se 1 (by rfl) ⟨819926, by rfl⟩ : syracuseStep 1093235 = 1639853) B1639853
theorem B1093265 : Blo 726324 1093265 := bstep (se 2 (by rfl) ⟨409974, by rfl⟩ : syracuseStep 1093265 = 819949) B819949
theorem B1093283 : Blo 726324 1093283 := bstep (se 1 (by rfl) ⟨819962, by rfl⟩ : syracuseStep 1093283 = 1639925) B1639925
theorem B1093313 : Blo 726324 1093313 := bstep (se 2 (by rfl) ⟨409992, by rfl⟩ : syracuseStep 1093313 = 819985) B819985
theorem B1093331 : Blo 726324 1093331 := bstep (se 1 (by rfl) ⟨819998, by rfl⟩ : syracuseStep 1093331 = 1639997) B1639997
theorem B1093361 : Blo 726324 1093361 := bstep (se 2 (by rfl) ⟨410010, by rfl⟩ : syracuseStep 1093361 = 820021) B820021
theorem B1093379 : Blo 726324 1093379 := bstep (se 1 (by rfl) ⟨820034, by rfl⟩ : syracuseStep 1093379 = 1640069) B1640069
theorem B1093409 : Blo 726324 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B3682097 : Blo 726324 3682097 := bstep (se 2 (by rfl) ⟨1380786, by rfl⟩ : syracuseStep 3682097 = 2761573) B2761573
theorem B1093427 : Blo 726324 1093427 := bstep (se 1 (by rfl) ⟨820070, by rfl⟩ : syracuseStep 1093427 = 1640141) B1640141
theorem B1093457 : Blo 726324 1093457 := bstep (se 2 (by rfl) ⟨410046, by rfl⟩ : syracuseStep 1093457 = 820093) B820093
theorem B1093475 : Blo 726324 1093475 := bstep (se 1 (by rfl) ⟨820106, by rfl⟩ : syracuseStep 1093475 = 1640213) B1640213
theorem B1093505 : Blo 726324 1093505 := bstep (se 2 (by rfl) ⟨410064, by rfl⟩ : syracuseStep 1093505 = 820129) B820129
theorem B1093523 : Blo 726324 1093523 := bstep (se 1 (by rfl) ⟨820142, by rfl⟩ : syracuseStep 1093523 = 1640285) B1640285
theorem B1093553 : Blo 726324 1093553 := bstep (se 2 (by rfl) ⟨410082, by rfl⟩ : syracuseStep 1093553 = 820165) B820165
theorem B1093571 : Blo 726324 1093571 := bstep (se 1 (by rfl) ⟨820178, by rfl⟩ : syracuseStep 1093571 = 1640357) B1640357
theorem B1093601 : Blo 726324 1093601 := bstep (se 2 (by rfl) ⟨410100, by rfl⟩ : syracuseStep 1093601 = 820201) B820201
theorem B1093619 : Blo 726324 1093619 := bstep (se 1 (by rfl) ⟨820214, by rfl⟩ : syracuseStep 1093619 = 1640429) B1640429
theorem B1093649 : Blo 726324 1093649 := bstep (se 2 (by rfl) ⟨410118, by rfl⟩ : syracuseStep 1093649 = 820237) B820237
theorem B1093667 : Blo 726324 1093667 := bstep (se 1 (by rfl) ⟨820250, by rfl⟩ : syracuseStep 1093667 = 1640501) B1640501
theorem B1093697 : Blo 726324 1093697 := bstep (se 2 (by rfl) ⟨410136, by rfl⟩ : syracuseStep 1093697 = 820273) B820273
theorem B1093715 : Blo 726324 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B1093745 : Blo 726324 1093745 := bstep (se 2 (by rfl) ⟨410154, by rfl⟩ : syracuseStep 1093745 = 820309) B820309
theorem B2076785 : Blo 726324 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B1093763 : Blo 726324 1093763 := bstep (se 1 (by rfl) ⟨820322, by rfl⟩ : syracuseStep 1093763 = 1640645) B1640645
theorem B1093793 : Blo 726324 1093793 := bstep (se 2 (by rfl) ⟨410172, by rfl⟩ : syracuseStep 1093793 = 820345) B820345
theorem B1093811 : Blo 726324 1093811 := bstep (se 1 (by rfl) ⟨820358, by rfl⟩ : syracuseStep 1093811 = 1640717) B1640717
theorem B1093841 : Blo 726324 1093841 := bstep (se 2 (by rfl) ⟨410190, by rfl⟩ : syracuseStep 1093841 = 820381) B820381
theorem B1093859 : Blo 726324 1093859 := bstep (se 1 (by rfl) ⟨820394, by rfl⟩ : syracuseStep 1093859 = 1640789) B1640789
theorem B1749251 : Blo 726324 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B1093889 : Blo 726324 1093889 := bstep (se 2 (by rfl) ⟨410208, by rfl⟩ : syracuseStep 1093889 = 820417) B820417
theorem B1847569 : Blo 726324 1847569 := bstep (se 2 (by rfl) ⟨692838, by rfl⟩ : syracuseStep 1847569 = 1385677) B1385677
theorem B1093907 : Blo 726324 1093907 := bstep (se 1 (by rfl) ⟨820430, by rfl⟩ : syracuseStep 1093907 = 1640861) B1640861
theorem B1093937 : Blo 726324 1093937 := bstep (se 2 (by rfl) ⟨410226, by rfl⟩ : syracuseStep 1093937 = 820453) B820453
theorem B1093955 : Blo 726324 1093955 := bstep (se 1 (by rfl) ⟨820466, by rfl⟩ : syracuseStep 1093955 = 1640933) B1640933
theorem B1093985 : Blo 726324 1093985 := bstep (se 2 (by rfl) ⟨410244, by rfl⟩ : syracuseStep 1093985 = 820489) B820489
theorem B1094003 : Blo 726324 1094003 := bstep (se 1 (by rfl) ⟨820502, by rfl⟩ : syracuseStep 1094003 = 1641005) B1641005
theorem B1094033 : Blo 726324 1094033 := bstep (se 2 (by rfl) ⟨410262, by rfl⟩ : syracuseStep 1094033 = 820525) B820525
theorem B1094051 : Blo 726324 1094051 := bstep (se 1 (by rfl) ⟨820538, by rfl⟩ : syracuseStep 1094051 = 1641077) B1641077
theorem B1094081 : Blo 726324 1094081 := bstep (se 2 (by rfl) ⟨410280, by rfl⟩ : syracuseStep 1094081 = 820561) B820561
theorem B1094099 : Blo 726324 1094099 := bstep (se 1 (by rfl) ⟨820574, by rfl⟩ : syracuseStep 1094099 = 1641149) B1641149
theorem B6238691 : Blo 726324 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B1094129 : Blo 726324 1094129 := bstep (se 2 (by rfl) ⟨410298, by rfl⟩ : syracuseStep 1094129 = 820597) B820597
theorem B1094147 : Blo 726324 1094147 := bstep (se 1 (by rfl) ⟨820610, by rfl⟩ : syracuseStep 1094147 = 1641221) B1641221
theorem B2241037 : Blo 726324 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B1094177 : Blo 726324 1094177 := bstep (se 2 (by rfl) ⟨410316, by rfl⟩ : syracuseStep 1094177 = 820633) B820633
theorem B1847843 : Blo 726324 1847843 := bstep (se 1 (by rfl) ⟨1385882, by rfl⟩ : syracuseStep 1847843 = 2771765) B2771765
theorem B1094195 : Blo 726324 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B1094225 : Blo 726324 1094225 := bstep (se 2 (by rfl) ⟨410334, by rfl⟩ : syracuseStep 1094225 = 820669) B820669
theorem B1094243 : Blo 726324 1094243 := bstep (se 1 (by rfl) ⟨820682, by rfl⟩ : syracuseStep 1094243 = 1641365) B1641365
theorem B1094273 : Blo 726324 1094273 := bstep (se 2 (by rfl) ⟨410352, by rfl⟩ : syracuseStep 1094273 = 820705) B820705
theorem B1094291 : Blo 726324 1094291 := bstep (se 1 (by rfl) ⟨820718, by rfl⟩ : syracuseStep 1094291 = 1641437) B1641437
theorem B2241197 : Blo 726324 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B1094321 : Blo 726324 1094321 := bstep (se 2 (by rfl) ⟨410370, by rfl⟩ : syracuseStep 1094321 = 820741) B820741
theorem B1094339 : Blo 726324 1094339 := bstep (se 1 (by rfl) ⟨820754, by rfl⟩ : syracuseStep 1094339 = 1641509) B1641509
theorem B1094369 : Blo 726324 1094369 := bstep (se 2 (by rfl) ⟨410388, by rfl⟩ : syracuseStep 1094369 = 820777) B820777
theorem B1848035 : Blo 726324 1848035 := bstep (se 1 (by rfl) ⟨1386026, by rfl⟩ : syracuseStep 1848035 = 2772053) B2772053
theorem B1094387 : Blo 726324 1094387 := bstep (se 1 (by rfl) ⟨820790, by rfl⟩ : syracuseStep 1094387 = 1641581) B1641581
theorem B1094417 : Blo 726324 1094417 := bstep (se 2 (by rfl) ⟨410406, by rfl⟩ : syracuseStep 1094417 = 820813) B820813
theorem B1094435 : Blo 726324 1094435 := bstep (se 1 (by rfl) ⟨820826, by rfl⟩ : syracuseStep 1094435 = 1641653) B1641653
theorem B1094465 : Blo 726324 1094465 := bstep (se 2 (by rfl) ⟨410424, by rfl⟩ : syracuseStep 1094465 = 820849) B820849
theorem B1094483 : Blo 726324 1094483 := bstep (se 1 (by rfl) ⟨820862, by rfl⟩ : syracuseStep 1094483 = 1641725) B1641725
theorem B1094513 : Blo 726324 1094513 := bstep (se 2 (by rfl) ⟨410442, by rfl⟩ : syracuseStep 1094513 = 820885) B820885
theorem B2667377 : Blo 726324 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1094531 : Blo 726324 1094531 := bstep (se 1 (by rfl) ⟨820898, by rfl⟩ : syracuseStep 1094531 = 1641797) B1641797
theorem B1094561 : Blo 726324 1094561 := bstep (se 2 (by rfl) ⟨410460, by rfl⟩ : syracuseStep 1094561 = 820921) B820921
theorem B1094579 : Blo 726324 1094579 := bstep (se 1 (by rfl) ⟨820934, by rfl⟩ : syracuseStep 1094579 = 1641869) B1641869
theorem B1094609 : Blo 726324 1094609 := bstep (se 2 (by rfl) ⟨410478, by rfl⟩ : syracuseStep 1094609 = 820957) B820957
theorem B1094627 : Blo 726324 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B1094657 : Blo 726324 1094657 := bstep (se 2 (by rfl) ⟨410496, by rfl⟩ : syracuseStep 1094657 = 820993) B820993
theorem B1094675 : Blo 726324 1094675 := bstep (se 1 (by rfl) ⟨821006, by rfl⟩ : syracuseStep 1094675 = 1642013) B1642013
theorem B2077741 : Blo 726324 2077741 := bstep (se 3 (by rfl) ⟨389576, by rfl⟩ : syracuseStep 2077741 = 779153) B779153
theorem B1094705 : Blo 726324 1094705 := bstep (se 2 (by rfl) ⟨410514, by rfl⟩ : syracuseStep 1094705 = 821029) B821029
theorem B1225793 : Blo 726324 1225793 := bstep (se 2 (by rfl) ⟨459672, by rfl⟩ : syracuseStep 1225793 = 919345) B919345
theorem B1094723 : Blo 726324 1094723 := bstep (se 1 (by rfl) ⟨821042, by rfl⟩ : syracuseStep 1094723 = 1642085) B1642085
theorem B1094753 : Blo 726324 1094753 := bstep (se 2 (by rfl) ⟨410532, by rfl⟩ : syracuseStep 1094753 = 821065) B821065
theorem B1094771 : Blo 726324 1094771 := bstep (se 1 (by rfl) ⟨821078, by rfl⟩ : syracuseStep 1094771 = 1642157) B1642157
theorem B1094801 : Blo 726324 1094801 := bstep (se 2 (by rfl) ⟨410550, by rfl⟩ : syracuseStep 1094801 = 821101) B821101
theorem B1094819 : Blo 726324 1094819 := bstep (se 1 (by rfl) ⟨821114, by rfl⟩ : syracuseStep 1094819 = 1642229) B1642229
theorem B1225921 : Blo 726324 1225921 := bstep (se 2 (by rfl) ⟨459720, by rfl⟩ : syracuseStep 1225921 = 919441) B919441
theorem B1094849 : Blo 726324 1094849 := bstep (se 2 (by rfl) ⟨410568, by rfl⟩ : syracuseStep 1094849 = 821137) B821137
theorem B1094867 : Blo 726324 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B1225955 : Blo 726324 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B3683555 : Blo 726324 3683555 := bstep (se 1 (by rfl) ⟨2762666, by rfl⟩ : syracuseStep 3683555 = 5525333) B5525333
theorem B1094897 : Blo 726324 1094897 := bstep (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) B821173
theorem B1094915 : Blo 726324 1094915 := bstep (se 1 (by rfl) ⟨821186, by rfl⟩ : syracuseStep 1094915 = 1642373) B1642373
theorem B2077969 : Blo 726324 2077969 := bstep (se 2 (by rfl) ⟨779238, by rfl⟩ : syracuseStep 2077969 = 1558477) B1558477
theorem B1094945 : Blo 726324 1094945 := bstep (se 2 (by rfl) ⟨410604, by rfl⟩ : syracuseStep 1094945 = 821209) B821209
theorem B1094963 : Blo 726324 1094963 := bstep (se 1 (by rfl) ⟨821222, by rfl⟩ : syracuseStep 1094963 = 1642445) B1642445
theorem B4666693 : Blo 726324 4666693 := bstep (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) B875005
theorem B4437325 : Blo 726324 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B1094993 : Blo 726324 1094993 := bstep (se 2 (by rfl) ⟨410622, by rfl⟩ : syracuseStep 1094993 = 821245) B821245
theorem B1226083 : Blo 726324 1226083 := bstep (se 1 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 1226083 = 1839125) B1839125
theorem B3945827 : Blo 726324 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B1095011 : Blo 726324 1095011 := bstep (se 1 (by rfl) ⟨821258, by rfl⟩ : syracuseStep 1095011 = 1642517) B1642517
theorem B1095041 : Blo 726324 1095041 := bstep (se 2 (by rfl) ⟨410640, by rfl⟩ : syracuseStep 1095041 = 821281) B821281
theorem B2766221 : Blo 726324 2766221 := bstep (se 3 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 2766221 = 1037333) B1037333
theorem B1095059 : Blo 726324 1095059 := bstep (se 1 (by rfl) ⟨821294, by rfl⟩ : syracuseStep 1095059 = 1642589) B1642589
theorem B2799011 : Blo 726324 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B2078129 : Blo 726324 2078129 := bstep (se 2 (by rfl) ⟨779298, by rfl⟩ : syracuseStep 2078129 = 1558597) B1558597
theorem B1095089 : Blo 726324 1095089 := bstep (se 2 (by rfl) ⟨410658, by rfl⟩ : syracuseStep 1095089 = 821317) B821317
theorem B1095107 : Blo 726324 1095107 := bstep (se 1 (by rfl) ⟨821330, by rfl⟩ : syracuseStep 1095107 = 1642661) B1642661
theorem B1750481 : Blo 726324 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B1095137 : Blo 726324 1095137 := bstep (se 2 (by rfl) ⟨410676, by rfl⟩ : syracuseStep 1095137 = 821353) B821353
theorem B1226225 : Blo 726324 1226225 := bstep (se 2 (by rfl) ⟨459834, by rfl⟩ : syracuseStep 1226225 = 919669) B919669
theorem B1095155 : Blo 726324 1095155 := bstep (se 1 (by rfl) ⟨821366, by rfl⟩ : syracuseStep 1095155 = 1642733) B1642733
theorem B1095185 : Blo 726324 1095185 := bstep (se 2 (by rfl) ⟨410694, by rfl⟩ : syracuseStep 1095185 = 821389) B821389
theorem B2078243 : Blo 726324 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B1095203 : Blo 726324 1095203 := bstep (se 1 (by rfl) ⟨821402, by rfl⟩ : syracuseStep 1095203 = 1642805) B1642805
theorem B1095233 : Blo 726324 1095233 := bstep (se 2 (by rfl) ⟨410712, by rfl⟩ : syracuseStep 1095233 = 821425) B821425
theorem B1095251 : Blo 726324 1095251 := bstep (se 1 (by rfl) ⟨821438, by rfl⟩ : syracuseStep 1095251 = 1642877) B1642877
theorem B1226353 : Blo 726324 1226353 := bstep (se 2 (by rfl) ⟨459882, by rfl⟩ : syracuseStep 1226353 = 919765) B919765
theorem B1095281 : Blo 726324 1095281 := bstep (se 2 (by rfl) ⟨410730, by rfl⟩ : syracuseStep 1095281 = 821461) B821461
theorem B1095299 : Blo 726324 1095299 := bstep (se 1 (by rfl) ⟨821474, by rfl⟩ : syracuseStep 1095299 = 1642949) B1642949
theorem B1750673 : Blo 726324 1750673 := bstep (se 2 (by rfl) ⟨656502, by rfl⟩ : syracuseStep 1750673 = 1313005) B1313005
theorem B1226387 : Blo 726324 1226387 := bstep (se 1 (by rfl) ⟨919790, by rfl⟩ : syracuseStep 1226387 = 1839581) B1839581
theorem B1095329 : Blo 726324 1095329 := bstep (se 2 (by rfl) ⟨410748, by rfl⟩ : syracuseStep 1095329 = 821497) B821497
theorem B1095347 : Blo 726324 1095347 := bstep (se 1 (by rfl) ⟨821510, by rfl⟩ : syracuseStep 1095347 = 1643021) B1643021
theorem B1095377 : Blo 726324 1095377 := bstep (se 2 (by rfl) ⟨410766, by rfl⟩ : syracuseStep 1095377 = 821533) B821533
theorem B1095395 : Blo 726324 1095395 := bstep (se 1 (by rfl) ⟨821546, by rfl⟩ : syracuseStep 1095395 = 1643093) B1643093
theorem B1095425 : Blo 726324 1095425 := bstep (se 2 (by rfl) ⟨410784, by rfl⟩ : syracuseStep 1095425 = 821569) B821569
theorem B1226515 : Blo 726324 1226515 := bstep (se 1 (by rfl) ⟨919886, by rfl⟩ : syracuseStep 1226515 = 1839773) B1839773
theorem B1095443 : Blo 726324 1095443 := bstep (se 1 (by rfl) ⟨821582, by rfl⟩ : syracuseStep 1095443 = 1643165) B1643165
theorem B1095473 : Blo 726324 1095473 := bstep (se 2 (by rfl) ⟨410802, by rfl⟩ : syracuseStep 1095473 = 821605) B821605
theorem B1226657 : Blo 726324 1226657 := bstep (se 2 (by rfl) ⟨459996, by rfl⟩ : syracuseStep 1226657 = 919993) B919993
theorem B1554403 : Blo 726324 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B4143089 : Blo 726324 4143089 := bstep (se 2 (by rfl) ⟨1553658, by rfl⟩ : syracuseStep 4143089 = 3107317) B3107317
theorem B3684365 : Blo 726324 3684365 := bstep (se 3 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 3684365 = 1381637) B1381637
theorem B1226785 : Blo 726324 1226785 := bstep (se 2 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 1226785 = 920089) B920089
theorem B1226819 : Blo 726324 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B5519501 : Blo 726324 5519501 := bstep (se 3 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 5519501 = 2069813) B2069813
theorem B1226947 : Blo 726324 1226947 := bstep (se 1 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 1226947 = 1840421) B1840421
theorem B14039237 : Blo 726324 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B1227089 : Blo 726324 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B1751395 : Blo 726324 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B5257669 : Blo 726324 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B1227217 : Blo 726324 1227217 := bstep (se 2 (by rfl) ⟨460206, by rfl⟩ : syracuseStep 1227217 = 920413) B920413
theorem B1227251 : Blo 726324 1227251 := bstep (se 1 (by rfl) ⟨920438, by rfl⟩ : syracuseStep 1227251 = 1840877) B1840877
theorem B2079245 : Blo 726324 2079245 := bstep (se 3 (by rfl) ⟨389858, by rfl⟩ : syracuseStep 2079245 = 779717) B779717
theorem B3947057 : Blo 726324 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B2210417 : Blo 726324 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B1227379 : Blo 726324 1227379 := bstep (se 1 (by rfl) ⟨920534, by rfl⟩ : syracuseStep 1227379 = 1841069) B1841069
theorem B2079427 : Blo 726324 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B1227521 : Blo 726324 1227521 := bstep (se 2 (by rfl) ⟨460320, by rfl⟩ : syracuseStep 1227521 = 920641) B920641
theorem B4438883 : Blo 726324 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B2079587 : Blo 726324 2079587 := bstep (se 1 (by rfl) ⟨1559690, by rfl⟩ : syracuseStep 2079587 = 3119381) B3119381
theorem B1227649 : Blo 726324 1227649 := bstep (se 2 (by rfl) ⟨460368, by rfl⟩ : syracuseStep 1227649 = 920737) B920737
theorem B1227683 : Blo 726324 1227683 := bstep (se 1 (by rfl) ⟨920762, by rfl⟩ : syracuseStep 1227683 = 1841525) B1841525
theorem B900019 : Blo 726324 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B1227811 : Blo 726324 1227811 := bstep (se 1 (by rfl) ⟨920858, by rfl⟩ : syracuseStep 1227811 = 1841717) B1841717
theorem B1227953 : Blo 726324 1227953 := bstep (se 2 (by rfl) ⟨460482, by rfl⟩ : syracuseStep 1227953 = 920965) B920965
theorem B1228081 : Blo 726324 1228081 := bstep (se 2 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 1228081 = 921061) B921061
theorem B1228115 : Blo 726324 1228115 := bstep (se 1 (by rfl) ⟨921086, by rfl⟩ : syracuseStep 1228115 = 1842173) B1842173
theorem B4144547 : Blo 726324 4144547 := bstep (se 1 (by rfl) ⟨3108410, by rfl⟩ : syracuseStep 4144547 = 6216821) B6216821
theorem B933331 : Blo 726324 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1228243 : Blo 726324 1228243 := bstep (se 1 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 1228243 = 1842365) B1842365
theorem B1228385 : Blo 726324 1228385 := bstep (se 2 (by rfl) ⟨460644, by rfl⟩ : syracuseStep 1228385 = 921289) B921289
theorem B1228513 : Blo 726324 1228513 := bstep (se 2 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 1228513 = 921385) B921385
theorem B933619 : Blo 726324 933619 := bstep (se 1 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 933619 = 1400429) B1400429
theorem B1228547 : Blo 726324 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B1556273 : Blo 726324 1556273 := bstep (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) B1167205
theorem B1228675 : Blo 726324 1228675 := bstep (se 1 (by rfl) ⟨921506, by rfl⟩ : syracuseStep 1228675 = 1843013) B1843013
theorem B737203 : Blo 726324 737203 := bstep (se 1 (by rfl) ⟨552902, by rfl⟩ : syracuseStep 737203 = 1105805) B1105805
theorem B737219 : Blo 726324 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B1228817 : Blo 726324 1228817 := bstep (se 2 (by rfl) ⟨460806, by rfl⟩ : syracuseStep 1228817 = 921613) B921613
theorem B1228945 : Blo 726324 1228945 := bstep (se 2 (by rfl) ⟨460854, by rfl⟩ : syracuseStep 1228945 = 921709) B921709
theorem B1228979 : Blo 726324 1228979 := bstep (se 1 (by rfl) ⟨921734, by rfl⟩ : syracuseStep 1228979 = 1843469) B1843469
theorem B2212049 : Blo 726324 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B2769137 : Blo 726324 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B1229107 : Blo 726324 1229107 := bstep (se 1 (by rfl) ⟨921830, by rfl⟩ : syracuseStep 1229107 = 1843661) B1843661
theorem B1229249 : Blo 726324 1229249 := bstep (se 2 (by rfl) ⟨460968, by rfl⟩ : syracuseStep 1229249 = 921937) B921937
theorem B1163809 : Blo 726324 1163809 := bstep (se 2 (by rfl) ⟨436428, by rfl⟩ : syracuseStep 1163809 = 872857) B872857
theorem B1229377 : Blo 726324 1229377 := bstep (se 2 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 1229377 = 922033) B922033
theorem B1229411 : Blo 726324 1229411 := bstep (se 1 (by rfl) ⟨922058, by rfl⟩ : syracuseStep 1229411 = 1844117) B1844117
theorem B1557137 : Blo 726324 1557137 := bstep (se 2 (by rfl) ⟨583926, by rfl⟩ : syracuseStep 1557137 = 1167853) B1167853
theorem B1229539 : Blo 726324 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B1164065 : Blo 726324 1164065 := bstep (se 2 (by rfl) ⟨436524, by rfl⟩ : syracuseStep 1164065 = 873049) B873049
theorem B2245475 : Blo 726324 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B3687281 : Blo 726324 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B1229681 : Blo 726324 1229681 := bstep (se 2 (by rfl) ⟨461130, by rfl⟩ : syracuseStep 1229681 = 922261) B922261
theorem B13288333 : Blo 726324 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B8307683 : Blo 726324 8307683 := bstep (se 1 (by rfl) ⟨6230762, by rfl⟩ : syracuseStep 8307683 = 12461525) B12461525
theorem B5522417 : Blo 726324 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B1229809 : Blo 726324 1229809 := bstep (se 2 (by rfl) ⟨461178, by rfl⟩ : syracuseStep 1229809 = 922357) B922357
theorem B2802701 : Blo 726324 2802701 := bstep (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) B1051013
theorem B1229843 : Blo 726324 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B1229971 : Blo 726324 1229971 := bstep (se 1 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 1229971 = 1844957) B1844957
theorem B1230001 : Blo 726324 1230001 := bstep (se 2 (by rfl) ⟨461250, by rfl⟩ : syracuseStep 1230001 = 922501) B922501
theorem B1230113 : Blo 726324 1230113 := bstep (se 2 (by rfl) ⟨461292, by rfl⟩ : syracuseStep 1230113 = 922585) B922585
theorem B1230241 : Blo 726324 1230241 := bstep (se 2 (by rfl) ⟨461340, by rfl⟩ : syracuseStep 1230241 = 922681) B922681
theorem B1230275 : Blo 726324 1230275 := bstep (se 1 (by rfl) ⟨922706, by rfl⟩ : syracuseStep 1230275 = 1845413) B1845413
theorem B1230403 : Blo 726324 1230403 := bstep (se 1 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 1230403 = 1845605) B1845605
theorem B2770595 : Blo 726324 2770595 := bstep (se 1 (by rfl) ⟨2077946, by rfl⟩ : syracuseStep 2770595 = 4155893) B4155893
theorem B1754833 : Blo 726324 1754833 := bstep (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) B1316125
theorem B1230545 : Blo 726324 1230545 := bstep (se 2 (by rfl) ⟨461454, by rfl⟩ : syracuseStep 1230545 = 922909) B922909
theorem B1230673 : Blo 726324 1230673 := bstep (se 2 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 1230673 = 923005) B923005
theorem B1230707 : Blo 726324 1230707 := bstep (se 1 (by rfl) ⟨923030, by rfl⟩ : syracuseStep 1230707 = 1846061) B1846061
theorem B1558435 : Blo 726324 1558435 := bstep (se 1 (by rfl) ⟨1168826, by rfl⟩ : syracuseStep 1558435 = 2337653) B2337653
theorem B1230835 : Blo 726324 1230835 := bstep (se 1 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 1230835 = 1846253) B1846253
theorem B1230977 : Blo 726324 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B1165475 : Blo 726324 1165475 := bstep (se 1 (by rfl) ⟨874106, by rfl⟩ : syracuseStep 1165475 = 1748213) B1748213
theorem B1034417 : Blo 726324 1034417 := bstep (se 2 (by rfl) ⟨387906, by rfl⟩ : syracuseStep 1034417 = 775813) B775813
theorem B1231105 : Blo 726324 1231105 := bstep (se 2 (by rfl) ⟨461664, by rfl⟩ : syracuseStep 1231105 = 923329) B923329
theorem B3688739 : Blo 726324 3688739 := bstep (se 1 (by rfl) ⟨2766554, by rfl⟩ : syracuseStep 3688739 = 5533109) B5533109
theorem B1231139 : Blo 726324 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B1231267 : Blo 726324 1231267 := bstep (se 1 (by rfl) ⟨923450, by rfl⟩ : syracuseStep 1231267 = 1846901) B1846901
theorem B739811 : Blo 726324 739811 := bstep (se 1 (by rfl) ⟨554858, by rfl⟩ : syracuseStep 739811 = 1109717) B1109717
theorem B1231409 : Blo 726324 1231409 := bstep (se 2 (by rfl) ⟨461778, by rfl⟩ : syracuseStep 1231409 = 923557) B923557
theorem B3361421 : Blo 726324 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B2771597 : Blo 726324 2771597 := bstep (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) B1039349
theorem B2214577 : Blo 726324 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B1231537 : Blo 726324 1231537 := bstep (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) B923653
theorem B1034947 : Blo 726324 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B1231571 : Blo 726324 1231571 := bstep (se 1 (by rfl) ⟨923678, by rfl⟩ : syracuseStep 1231571 = 1847357) B1847357
theorem B1231699 : Blo 726324 1231699 := bstep (se 1 (by rfl) ⟨923774, by rfl⟩ : syracuseStep 1231699 = 1847549) B1847549
theorem B1231841 : Blo 726324 1231841 := bstep (se 2 (by rfl) ⟨461940, by rfl⟩ : syracuseStep 1231841 = 923881) B923881
theorem B1166321 : Blo 726324 1166321 := bstep (se 2 (by rfl) ⟨437370, by rfl⟩ : syracuseStep 1166321 = 874741) B874741
theorem B1035283 : Blo 726324 1035283 := bstep (se 1 (by rfl) ⟨776462, by rfl⟩ : syracuseStep 1035283 = 1552925) B1552925
theorem B3689549 : Blo 726324 3689549 := bstep (se 3 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 3689549 = 1383581) B1383581
theorem B1231969 : Blo 726324 1231969 := bstep (se 2 (by rfl) ⟨461988, by rfl⟩ : syracuseStep 1231969 = 923977) B923977
theorem B1559665 : Blo 726324 1559665 := bstep (se 2 (by rfl) ⟨584874, by rfl⟩ : syracuseStep 1559665 = 1169749) B1169749
theorem B1232003 : Blo 726324 1232003 := bstep (se 1 (by rfl) ⟨924002, by rfl⟩ : syracuseStep 1232003 = 1848005) B1848005
theorem B2247875 : Blo 726324 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B1232131 : Blo 726324 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B1658225 : Blo 726324 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B1232273 : Blo 726324 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B1166833 : Blo 726324 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B1232401 : Blo 726324 1232401 := bstep (se 2 (by rfl) ⟨462150, by rfl⟩ : syracuseStep 1232401 = 924301) B924301
theorem B1035841 : Blo 726324 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B1035875 : Blo 726324 1035875 := bstep (se 1 (by rfl) ⟨776906, by rfl⟩ : syracuseStep 1035875 = 1553813) B1553813
theorem B1167443 : Blo 726324 1167443 := bstep (se 1 (by rfl) ⟨875582, by rfl⟩ : syracuseStep 1167443 = 1751165) B1751165
theorem B1036433 : Blo 726324 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B1036513 : Blo 726324 1036513 := bstep (se 2 (by rfl) ⟨388692, by rfl⟩ : syracuseStep 1036513 = 777385) B777385
theorem B1331491 : Blo 726324 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1364273 : Blo 726324 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B6214157 : Blo 726324 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B4674509 : Blo 726324 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B1037299 : Blo 726324 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B3494947 : Blo 726324 3494947 := bstep (se 1 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 3494947 = 5242421) B5242421
theorem B1168435 : Blo 726324 1168435 := bstep (se 1 (by rfl) ⟨876326, by rfl⟩ : syracuseStep 1168435 = 1752653) B1752653
theorem B873587 : Blo 726324 873587 := bstep (se 1 (by rfl) ⟨655190, by rfl⟩ : syracuseStep 873587 = 1310381) B1310381
theorem B9327797 : Blo 726324 9327797 := bstep (se 5 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 9327797 = 874481) B874481
theorem B1135811 : Blo 726324 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B808147 : Blo 726324 808147 := bstep (se 1 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 808147 = 1212221) B1212221
theorem B7853381 : Blo 726324 7853381 := bstep (se 4 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 7853381 = 1472509) B1472509
theorem B1037777 : Blo 726324 1037777 := bstep (se 2 (by rfl) ⟨389166, by rfl⟩ : syracuseStep 1037777 = 778333) B778333
theorem B1037891 : Blo 726324 1037891 := bstep (se 1 (by rfl) ⟨778418, by rfl⟩ : syracuseStep 1037891 = 1556837) B1556837
theorem B2250317 : Blo 726324 2250317 := bstep (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) B843869
theorem B1037971 : Blo 726324 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B4970317 : Blo 726324 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B3692465 : Blo 726324 3692465 := bstep (se 2 (by rfl) ⟨1384674, by rfl⟩ : syracuseStep 3692465 = 2769349) B2769349
theorem B1169345 : Blo 726324 1169345 := bstep (se 2 (by rfl) ⟨438504, by rfl⟩ : syracuseStep 1169345 = 877009) B877009
theorem B7493573 : Blo 726324 7493573 := bstep (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) B1405045
theorem B1169473 : Blo 726324 1169473 := bstep (se 2 (by rfl) ⟨438552, by rfl⟩ : syracuseStep 1169473 = 877105) B877105
theorem B1333361 : Blo 726324 1333361 := bstep (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) B1000021
theorem B1038529 : Blo 726324 1038529 := bstep (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) B778897
theorem B3103217 : Blo 726324 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B8837873 : Blo 726324 8837873 := bstep (se 2 (by rfl) ⟨3314202, by rfl⟩ : syracuseStep 8837873 = 6628405) B6628405
theorem B777043 : Blo 726324 777043 := bstep (se 1 (by rfl) ⟨582782, by rfl⟩ : syracuseStep 777043 = 1165565) B1165565
theorem B6216547 : Blo 726324 6216547 := bstep (se 1 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 6216547 = 9324821) B9324821
theorem B1039235 : Blo 726324 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B3496945 : Blo 726324 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B777475 : Blo 726324 777475 := bstep (se 1 (by rfl) ⟨583106, by rfl⟩ : syracuseStep 777475 = 1166213) B1166213
theorem B1662211 : Blo 726324 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B875875 : Blo 726324 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B3693923 : Blo 726324 3693923 := bstep (se 1 (by rfl) ⟨2770442, by rfl⟩ : syracuseStep 3693923 = 5540885) B5540885
theorem B875971 : Blo 726324 875971 := bstep (se 1 (by rfl) ⟨656978, by rfl⟩ : syracuseStep 875971 = 1313957) B1313957
theorem B876019 : Blo 726324 876019 := bstep (se 1 (by rfl) ⟨657014, by rfl⟩ : syracuseStep 876019 = 1314029) B1314029
theorem B4153477 : Blo 726324 4153477 := bstep (se 4 (by rfl) ⟨389388, by rfl⟩ : syracuseStep 4153477 = 778777) B778777
theorem B3694733 : Blo 726324 3694733 := bstep (se 3 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 3694733 = 1385525) B1385525
theorem B778739 : Blo 726324 778739 := bstep (se 1 (by rfl) ⟨584054, by rfl⟩ : syracuseStep 778739 = 1168109) B1168109
theorem B877235 : Blo 726324 877235 := bstep (se 1 (by rfl) ⟨657926, by rfl⟩ : syracuseStep 877235 = 1315853) B1315853
theorem B3105677 : Blo 726324 3105677 := bstep (se 3 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 3105677 = 1164629) B1164629
theorem B22438853 : Blo 726324 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B4678661 : Blo 726324 4678661 := bstep (se 4 (by rfl) ⟨438624, by rfl⟩ : syracuseStep 4678661 = 877249) B877249
theorem B9462853 : Blo 726324 9462853 := bstep (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) B1774285
theorem B1107155 : Blo 726324 1107155 := bstep (se 1 (by rfl) ⟨830366, by rfl⟩ : syracuseStep 1107155 = 1660733) B1660733
theorem B3106019 : Blo 726324 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B779491 : Blo 726324 779491 := bstep (se 1 (by rfl) ⟨584618, by rfl⟩ : syracuseStep 779491 = 1169237) B1169237
theorem B2451437 : Blo 726324 2451437 := bstep (se 3 (by rfl) ⟨459644, by rfl⟩ : syracuseStep 2451437 = 919289) B919289
theorem B2451491 : Blo 726324 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B3237937 : Blo 726324 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B4155461 : Blo 726324 4155461 := bstep (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) B779149
theorem B15952099 : Blo 726324 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B2451761 : Blo 726324 2451761 := bstep (se 2 (by rfl) ⟨919410, by rfl⟩ : syracuseStep 2451761 = 1838821) B1838821
theorem B12413411 : Blo 726324 12413411 := bstep (se 1 (by rfl) ⟨9310058, by rfl⟩ : syracuseStep 12413411 = 18620117) B18620117
theorem B2452301 : Blo 726324 2452301 := bstep (se 3 (by rfl) ⟨459806, by rfl⟩ : syracuseStep 2452301 = 919613) B919613
theorem B2452355 : Blo 726324 2452355 := bstep (se 1 (by rfl) ⟨1839266, by rfl⟩ : syracuseStep 2452355 = 3678533) B3678533
theorem B1403875 : Blo 726324 1403875 := bstep (se 1 (by rfl) ⟨1052906, by rfl⟩ : syracuseStep 1403875 = 2105813) B2105813
theorem B2452625 : Blo 726324 2452625 := bstep (se 2 (by rfl) ⟨919734, by rfl⟩ : syracuseStep 2452625 = 1839469) B1839469
theorem B1109297 : Blo 726324 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B17985077 : Blo 726324 17985077 := bstep (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) B1686101
theorem B2453165 : Blo 726324 2453165 := bstep (se 3 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 2453165 = 919937) B919937
theorem B749251 : Blo 726324 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B2453219 : Blo 726324 2453219 := bstep (se 1 (by rfl) ⟨1839914, by rfl⟩ : syracuseStep 2453219 = 3679829) B3679829
theorem B7008227 : Blo 726324 7008227 := bstep (se 1 (by rfl) ⟨5256170, by rfl⟩ : syracuseStep 7008227 = 10512341) B10512341
theorem B2453489 : Blo 726324 2453489 := bstep (se 2 (by rfl) ⟨920058, by rfl⟩ : syracuseStep 2453489 = 1840117) B1840117
theorem B19132469 : Blo 726324 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B1634417 : Blo 726324 1634417 := bstep (se 2 (by rfl) ⟨612906, by rfl⟩ : syracuseStep 1634417 = 1225813) B1225813
theorem B1634435 : Blo 726324 1634435 := bstep (se 1 (by rfl) ⟨1225826, by rfl⟩ : syracuseStep 1634435 = 2451653) B2451653
theorem B1110305 : Blo 726324 1110305 := bstep (se 2 (by rfl) ⟨416364, by rfl⟩ : syracuseStep 1110305 = 832729) B832729
theorem B1634705 : Blo 726324 1634705 := bstep (se 2 (by rfl) ⟨613014, by rfl⟩ : syracuseStep 1634705 = 1226029) B1226029
theorem B1634723 : Blo 726324 1634723 := bstep (se 1 (by rfl) ⟨1226042, by rfl⟩ : syracuseStep 1634723 = 2452085) B2452085
theorem B3928547 : Blo 726324 3928547 := bstep (se 1 (by rfl) ⟨2946410, by rfl⟩ : syracuseStep 3928547 = 5892821) B5892821
theorem B2454029 : Blo 726324 2454029 := bstep (se 3 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 2454029 = 920261) B920261
theorem B2454083 : Blo 726324 2454083 := bstep (se 1 (by rfl) ⟨1840562, by rfl⟩ : syracuseStep 2454083 = 3681125) B3681125
theorem B1634993 : Blo 726324 1634993 := bstep (se 2 (by rfl) ⟨613122, by rfl⟩ : syracuseStep 1634993 = 1226245) B1226245
theorem B1635011 : Blo 726324 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B5239565 : Blo 726324 5239565 := bstep (se 3 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 5239565 = 1964837) B1964837
theorem B7893773 : Blo 726324 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B17953589 : Blo 726324 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B2454353 : Blo 726324 2454353 := bstep (se 2 (by rfl) ⟨920382, by rfl⟩ : syracuseStep 2454353 = 1840765) B1840765
theorem B4977541 : Blo 726324 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B1635281 : Blo 726324 1635281 := bstep (se 2 (by rfl) ⟨613230, by rfl⟩ : syracuseStep 1635281 = 1226461) B1226461
theorem B1635299 : Blo 726324 1635299 := bstep (se 1 (by rfl) ⟨1226474, by rfl⟩ : syracuseStep 1635299 = 2452949) B2452949
theorem B3110051 : Blo 726324 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B3503267 : Blo 726324 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B1635569 : Blo 726324 1635569 := bstep (se 2 (by rfl) ⟨613338, by rfl⟩ : syracuseStep 1635569 = 1226677) B1226677
theorem B1635587 : Blo 726324 1635587 := bstep (se 1 (by rfl) ⟨1226690, by rfl⟩ : syracuseStep 1635587 = 2453381) B2453381
theorem B2454893 : Blo 726324 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B2454947 : Blo 726324 2454947 := bstep (se 1 (by rfl) ⟨1841210, by rfl⟩ : syracuseStep 2454947 = 3682421) B3682421
theorem B1635857 : Blo 726324 1635857 := bstep (se 2 (by rfl) ⟨613446, by rfl⟩ : syracuseStep 1635857 = 1226893) B1226893
theorem B1635875 : Blo 726324 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B3503729 : Blo 726324 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B2455217 : Blo 726324 2455217 := bstep (se 2 (by rfl) ⟨920706, by rfl⟩ : syracuseStep 2455217 = 1841413) B1841413
theorem B2520877 : Blo 726324 2520877 := bstep (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) B945329
theorem B1636145 : Blo 726324 1636145 := bstep (se 2 (by rfl) ⟨613554, by rfl⟩ : syracuseStep 1636145 = 1227109) B1227109
theorem B1636163 : Blo 726324 1636163 := bstep (se 1 (by rfl) ⟨1227122, by rfl⟩ : syracuseStep 1636163 = 2454245) B2454245
theorem B4159309 : Blo 726324 4159309 := bstep (se 3 (by rfl) ⟨779870, by rfl⟩ : syracuseStep 4159309 = 1559741) B1559741
theorem B817123 : Blo 726324 817123 := bstep (se 1 (by rfl) ⟨612842, by rfl⟩ : syracuseStep 817123 = 1225685) B1225685
theorem B1636433 : Blo 726324 1636433 := bstep (se 2 (by rfl) ⟨613662, by rfl⟩ : syracuseStep 1636433 = 1227325) B1227325
theorem B1636451 : Blo 726324 1636451 := bstep (se 1 (by rfl) ⟨1227338, by rfl⟩ : syracuseStep 1636451 = 2454677) B2454677
theorem B817267 : Blo 726324 817267 := bstep (se 1 (by rfl) ⟨612950, by rfl⟩ : syracuseStep 817267 = 1225901) B1225901
theorem B2455757 : Blo 726324 2455757 := bstep (se 3 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 2455757 = 920909) B920909
theorem B817411 : Blo 726324 817411 := bstep (se 1 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 817411 = 1226117) B1226117
theorem B2455811 : Blo 726324 2455811 := bstep (se 1 (by rfl) ⟨1841858, by rfl⟩ : syracuseStep 2455811 = 3683717) B3683717
theorem B1636721 : Blo 726324 1636721 := bstep (se 2 (by rfl) ⟨613770, by rfl⟩ : syracuseStep 1636721 = 1227541) B1227541
theorem B3111281 : Blo 726324 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B1636739 : Blo 726324 1636739 := bstep (se 1 (by rfl) ⟨1227554, by rfl⟩ : syracuseStep 1636739 = 2455109) B2455109
theorem B817555 : Blo 726324 817555 := bstep (se 1 (by rfl) ⟨613166, by rfl⟩ : syracuseStep 817555 = 1226333) B1226333
theorem B1866161 : Blo 726324 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B3504653 : Blo 726324 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B2456081 : Blo 726324 2456081 := bstep (se 2 (by rfl) ⟨921030, by rfl⟩ : syracuseStep 2456081 = 1842061) B1842061
theorem B817699 : Blo 726324 817699 := bstep (se 1 (by rfl) ⟨613274, by rfl⟩ : syracuseStep 817699 = 1226549) B1226549
theorem B1637009 : Blo 726324 1637009 := bstep (se 2 (by rfl) ⟨613878, by rfl⟩ : syracuseStep 1637009 = 1227757) B1227757
theorem B1637027 : Blo 726324 1637027 := bstep (se 1 (by rfl) ⟨1227770, by rfl⟩ : syracuseStep 1637027 = 2455541) B2455541
theorem B817843 : Blo 726324 817843 := bstep (se 1 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 817843 = 1226765) B1226765
theorem B817987 : Blo 726324 817987 := bstep (se 1 (by rfl) ⟨613490, by rfl⟩ : syracuseStep 817987 = 1226981) B1226981
theorem B4979569 : Blo 726324 4979569 := bstep (se 2 (by rfl) ⟨1867338, by rfl⟩ : syracuseStep 4979569 = 3734677) B3734677
theorem B1309603 : Blo 726324 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1637297 : Blo 726324 1637297 := bstep (se 2 (by rfl) ⟨613986, by rfl⟩ : syracuseStep 1637297 = 1227973) B1227973
theorem B1637315 : Blo 726324 1637315 := bstep (se 1 (by rfl) ⟨1227986, by rfl⟩ : syracuseStep 1637315 = 2455973) B2455973
theorem B818131 : Blo 726324 818131 := bstep (se 1 (by rfl) ⟨613598, by rfl⟩ : syracuseStep 818131 = 1227197) B1227197
theorem B2456621 : Blo 726324 2456621 := bstep (se 3 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 2456621 = 921233) B921233
theorem B818275 : Blo 726324 818275 := bstep (se 1 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 818275 = 1227413) B1227413
theorem B2456675 : Blo 726324 2456675 := bstep (se 1 (by rfl) ⟨1842506, by rfl⟩ : syracuseStep 2456675 = 3685013) B3685013
theorem B1637585 : Blo 726324 1637585 := bstep (se 2 (by rfl) ⟨614094, by rfl⟩ : syracuseStep 1637585 = 1228189) B1228189
theorem B1637603 : Blo 726324 1637603 := bstep (se 1 (by rfl) ⟨1228202, by rfl⟩ : syracuseStep 1637603 = 2456405) B2456405
theorem B818419 : Blo 726324 818419 := bstep (se 1 (by rfl) ⟨613814, by rfl⟩ : syracuseStep 818419 = 1227629) B1227629
theorem B3145037 : Blo 726324 3145037 := bstep (se 3 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 3145037 = 1179389) B1179389
theorem B4423025 : Blo 726324 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B2456945 : Blo 726324 2456945 := bstep (se 2 (by rfl) ⟨921354, by rfl⟩ : syracuseStep 2456945 = 1842709) B1842709
theorem B818563 : Blo 726324 818563 := bstep (se 1 (by rfl) ⟨613922, by rfl⟩ : syracuseStep 818563 = 1227845) B1227845
theorem B1965475 : Blo 726324 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B1637873 : Blo 726324 1637873 := bstep (se 2 (by rfl) ⟨614202, by rfl⟩ : syracuseStep 1637873 = 1228405) B1228405
theorem B1637891 : Blo 726324 1637891 := bstep (se 1 (by rfl) ⟨1228418, by rfl⟩ : syracuseStep 1637891 = 2456837) B2456837
theorem B818707 : Blo 726324 818707 := bstep (se 1 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 818707 = 1228061) B1228061
theorem B818851 : Blo 726324 818851 := bstep (se 1 (by rfl) ⟨614138, by rfl⟩ : syracuseStep 818851 = 1228277) B1228277
theorem B1474243 : Blo 726324 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B1638161 : Blo 726324 1638161 := bstep (se 2 (by rfl) ⟨614310, by rfl⟩ : syracuseStep 1638161 = 1228621) B1228621
theorem B1638179 : Blo 726324 1638179 := bstep (se 1 (by rfl) ⟨1228634, by rfl⟩ : syracuseStep 1638179 = 2457269) B2457269
theorem B2096945 : Blo 726324 2096945 := bstep (se 2 (by rfl) ⟨786354, by rfl⟩ : syracuseStep 2096945 = 1572709) B1572709
theorem B818995 : Blo 726324 818995 := bstep (se 1 (by rfl) ⟨614246, by rfl⟩ : syracuseStep 818995 = 1228493) B1228493
theorem B5603185 : Blo 726324 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B2457485 : Blo 726324 2457485 := bstep (se 3 (by rfl) ⟨460778, by rfl⟩ : syracuseStep 2457485 = 921557) B921557
theorem B819139 : Blo 726324 819139 := bstep (se 1 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 819139 = 1228709) B1228709
theorem B2457539 : Blo 726324 2457539 := bstep (se 1 (by rfl) ⟨1843154, by rfl⟩ : syracuseStep 2457539 = 3686309) B3686309
theorem B819211 : Blo 726324 819211 := bstep (se 1 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 819211 = 1228817) B1228817
theorem B819319 : Blo 726324 819319 := bstep (se 1 (by rfl) ⟨614489, by rfl⟩ : syracuseStep 819319 = 1228979) B1228979
theorem B1474699 : Blo 726324 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B1638539 : Blo 726324 1638539 := bstep (se 1 (by rfl) ⟨1228904, by rfl⟩ : syracuseStep 1638539 = 2457809) B2457809
theorem B5537969 : Blo 726324 5537969 := bstep (se 2 (by rfl) ⟨2076738, by rfl⟩ : syracuseStep 5537969 = 4153477) B4153477
theorem B1638593 : Blo 726324 1638593 := bstep (se 2 (by rfl) ⟨614472, by rfl⟩ : syracuseStep 1638593 = 1228945) B1228945
theorem B17268997 : Blo 726324 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B819499 : Blo 726324 819499 := bstep (se 1 (by rfl) ⟨614624, by rfl⟩ : syracuseStep 819499 = 1229249) B1229249
theorem B2490689 : Blo 726324 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B819607 : Blo 726324 819607 := bstep (se 1 (by rfl) ⟨614705, by rfl⟩ : syracuseStep 819607 = 1229411) B1229411
theorem B1638809 : Blo 726324 1638809 := bstep (se 2 (by rfl) ⟨614553, by rfl⟩ : syracuseStep 1638809 = 1229107) B1229107
theorem B1638899 : Blo 726324 1638899 := bstep (se 1 (by rfl) ⟨1229174, by rfl⟩ : syracuseStep 1638899 = 2458349) B2458349
theorem B1638935 : Blo 726324 1638935 := bstep (se 1 (by rfl) ⟨1229201, by rfl⟩ : syracuseStep 1638935 = 2458403) B2458403
theorem B2327105 : Blo 726324 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B3539531 : Blo 726324 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B2458187 : Blo 726324 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B819787 : Blo 726324 819787 := bstep (se 1 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 819787 = 1229681) B1229681
theorem B1573463 : Blo 726324 1573463 := bstep (se 1 (by rfl) ⟨1180097, by rfl⟩ : syracuseStep 1573463 = 2360195) B2360195
theorem B5538455 : Blo 726324 5538455 := bstep (se 1 (by rfl) ⟨4153841, by rfl⟩ : syracuseStep 5538455 = 8307683) B8307683
theorem B819895 : Blo 726324 819895 := bstep (se 1 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 819895 = 1229843) B1229843
theorem B1639115 : Blo 726324 1639115 := bstep (se 1 (by rfl) ⟨1229336, by rfl⟩ : syracuseStep 1639115 = 2458673) B2458673
theorem B1639169 : Blo 726324 1639169 := bstep (se 2 (by rfl) ⟨614688, by rfl⟩ : syracuseStep 1639169 = 1229377) B1229377
theorem B1966913 : Blo 726324 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B2458457 : Blo 726324 2458457 := bstep (se 2 (by rfl) ⟨921921, by rfl⟩ : syracuseStep 2458457 = 1843843) B1843843
theorem B820075 : Blo 726324 820075 := bstep (se 1 (by rfl) ⟨615056, by rfl⟩ : syracuseStep 820075 = 1230113) B1230113
theorem B7013299 : Blo 726324 7013299 := bstep (se 1 (by rfl) ⟨5259974, by rfl⟩ : syracuseStep 7013299 = 10519949) B10519949
theorem B820183 : Blo 726324 820183 := bstep (se 1 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 820183 = 1230275) B1230275
theorem B1639385 : Blo 726324 1639385 := bstep (se 2 (by rfl) ⟨614769, by rfl⟩ : syracuseStep 1639385 = 1229539) B1229539
theorem B1639475 : Blo 726324 1639475 := bstep (se 1 (by rfl) ⟨1229606, by rfl⟩ : syracuseStep 1639475 = 2459213) B2459213
theorem B1639511 : Blo 726324 1639511 := bstep (se 1 (by rfl) ⟨1229633, by rfl⟩ : syracuseStep 1639511 = 2459267) B2459267
theorem B820363 : Blo 726324 820363 := bstep (se 1 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 820363 = 1230545) B1230545
theorem B820471 : Blo 726324 820471 := bstep (se 1 (by rfl) ⟨615353, by rfl⟩ : syracuseStep 820471 = 1230707) B1230707
theorem B1639691 : Blo 726324 1639691 := bstep (se 1 (by rfl) ⟨1229768, by rfl⟩ : syracuseStep 1639691 = 2459537) B2459537
theorem B1639745 : Blo 726324 1639745 := bstep (se 2 (by rfl) ⟨614904, by rfl⟩ : syracuseStep 1639745 = 1229809) B1229809
theorem B820651 : Blo 726324 820651 := bstep (se 1 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 820651 = 1230977) B1230977
theorem B12617137 : Blo 726324 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B2459159 : Blo 726324 2459159 := bstep (se 1 (by rfl) ⟨1844369, by rfl⟩ : syracuseStep 2459159 = 3688739) B3688739
theorem B820759 : Blo 726324 820759 := bstep (se 1 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 820759 = 1231139) B1231139
theorem B1639961 : Blo 726324 1639961 := bstep (se 2 (by rfl) ⟨614985, by rfl⟩ : syracuseStep 1639961 = 1229971) B1229971
theorem B1246795 : Blo 726324 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B1640051 : Blo 726324 1640051 := bstep (se 1 (by rfl) ⟨1230038, by rfl⟩ : syracuseStep 1640051 = 2460077) B2460077
theorem B984727 : Blo 726324 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B1640087 : Blo 726324 1640087 := bstep (se 1 (by rfl) ⟨1230065, by rfl⟩ : syracuseStep 1640087 = 2460131) B2460131
theorem B820939 : Blo 726324 820939 := bstep (se 1 (by rfl) ⟨615704, by rfl⟩ : syracuseStep 820939 = 1231409) B1231409
theorem B821047 : Blo 726324 821047 := bstep (se 1 (by rfl) ⟨615785, by rfl⟩ : syracuseStep 821047 = 1231571) B1231571
theorem B1640267 : Blo 726324 1640267 := bstep (se 1 (by rfl) ⟨1230200, by rfl⟩ : syracuseStep 1640267 = 2460401) B2460401
theorem B1640321 : Blo 726324 1640321 := bstep (se 2 (by rfl) ⟨615120, by rfl⟩ : syracuseStep 1640321 = 1230241) B1230241
theorem B821227 : Blo 726324 821227 := bstep (se 1 (by rfl) ⟨615920, by rfl⟩ : syracuseStep 821227 = 1231841) B1231841
theorem B2459699 : Blo 726324 2459699 := bstep (se 1 (by rfl) ⟨1844774, by rfl⟩ : syracuseStep 2459699 = 3689549) B3689549
theorem B821335 : Blo 726324 821335 := bstep (se 1 (by rfl) ⟨616001, by rfl⟩ : syracuseStep 821335 = 1232003) B1232003
theorem B1640537 : Blo 726324 1640537 := bstep (se 2 (by rfl) ⟨615201, by rfl⟩ : syracuseStep 1640537 = 1230403) B1230403
theorem B1575065 : Blo 726324 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B1640627 : Blo 726324 1640627 := bstep (se 1 (by rfl) ⟨1230470, by rfl⟩ : syracuseStep 1640627 = 2460941) B2460941
theorem B1640663 : Blo 726324 1640663 := bstep (se 1 (by rfl) ⟨1230497, by rfl⟩ : syracuseStep 1640663 = 2460995) B2460995
theorem B821515 : Blo 726324 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B2885905 : Blo 726324 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B919831 : Blo 726324 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B7113005 : Blo 726324 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B2459969 : Blo 726324 2459969 := bstep (se 2 (by rfl) ⟨922488, by rfl⟩ : syracuseStep 2459969 = 1844977) B1844977
theorem B1640843 : Blo 726324 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B1640897 : Blo 726324 1640897 := bstep (se 2 (by rfl) ⟨615336, by rfl⟩ : syracuseStep 1640897 = 1230673) B1230673
theorem B5245505 : Blo 726324 5245505 := bstep (se 2 (by rfl) ⟨1967064, by rfl⟩ : syracuseStep 5245505 = 3934129) B3934129
theorem B2624093 : Blo 726324 2624093 := bstep (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) B984035
theorem B1641113 : Blo 726324 1641113 := bstep (se 2 (by rfl) ⟨615417, by rfl⟩ : syracuseStep 1641113 = 1230835) B1230835
theorem B7473869 : Blo 726324 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B1641203 : Blo 726324 1641203 := bstep (se 1 (by rfl) ⟨1230902, by rfl⟩ : syracuseStep 1641203 = 2461805) B2461805
theorem B1641239 : Blo 726324 1641239 := bstep (se 1 (by rfl) ⟨1230929, by rfl⟩ : syracuseStep 1641239 = 2461859) B2461859
theorem B985943 : Blo 726324 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B2460509 : Blo 726324 2460509 := bstep (se 3 (by rfl) ⟨461345, by rfl⟩ : syracuseStep 2460509 = 922691) B922691
theorem B1641419 : Blo 726324 1641419 := bstep (se 1 (by rfl) ⟨1231064, by rfl⟩ : syracuseStep 1641419 = 2462129) B2462129
theorem B21269465 : Blo 726324 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B2329565 : Blo 726324 2329565 := bstep (se 3 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 2329565 = 873587) B873587
theorem B1641473 : Blo 726324 1641473 := bstep (se 2 (by rfl) ⟨615552, by rfl⟩ : syracuseStep 1641473 = 1231105) B1231105
theorem B1379443 : Blo 726324 1379443 := bstep (se 1 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 1379443 = 2069165) B2069165
theorem B1182937 : Blo 726324 1182937 := bstep (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) B887203
theorem B1641689 : Blo 726324 1641689 := bstep (se 2 (by rfl) ⟨615633, by rfl⟩ : syracuseStep 1641689 = 1231267) B1231267
theorem B2952413 : Blo 726324 2952413 := bstep (se 3 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 2952413 = 1107155) B1107155
theorem B3116339 : Blo 726324 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B1641779 : Blo 726324 1641779 := bstep (se 1 (by rfl) ⟨1231334, by rfl⟩ : syracuseStep 1641779 = 2462669) B2462669
theorem B1641815 : Blo 726324 1641815 := bstep (se 1 (by rfl) ⟨1231361, by rfl⟩ : syracuseStep 1641815 = 2462723) B2462723
theorem B757207 : Blo 726324 757207 := bstep (se 1 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 757207 = 1135811) B1135811
theorem B1641995 : Blo 726324 1641995 := bstep (se 1 (by rfl) ⟨1231496, by rfl⟩ : syracuseStep 1641995 = 2462993) B2462993
theorem B1379891 : Blo 726324 1379891 := bstep (se 1 (by rfl) ⟨1034918, by rfl⟩ : syracuseStep 1379891 = 2069837) B2069837
theorem B2952769 : Blo 726324 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B1642049 : Blo 726324 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B1379929 : Blo 726324 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B1838771 : Blo 726324 1838771 := bstep (se 1 (by rfl) ⟨1379078, by rfl⟩ : syracuseStep 1838771 = 2758157) B2758157
theorem B1642265 : Blo 726324 1642265 := bstep (se 2 (by rfl) ⟨615849, by rfl⟩ : syracuseStep 1642265 = 1231699) B1231699
theorem B1642355 : Blo 726324 1642355 := bstep (se 1 (by rfl) ⟨1231766, by rfl⟩ : syracuseStep 1642355 = 2463533) B2463533
theorem B1642391 : Blo 726324 1642391 := bstep (se 1 (by rfl) ⟨1231793, by rfl⟩ : syracuseStep 1642391 = 2463587) B2463587
theorem B921547 : Blo 726324 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B2461643 : Blo 726324 2461643 := bstep (se 1 (by rfl) ⟨1846232, by rfl⟩ : syracuseStep 2461643 = 3692465) B3692465
theorem B1871833 : Blo 726324 1871833 := bstep (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) B1403875
theorem B1380377 : Blo 726324 1380377 := bstep (se 2 (by rfl) ⟨517641, by rfl⟩ : syracuseStep 1380377 = 1035283) B1035283
theorem B888907 : Blo 726324 888907 := bstep (se 1 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 888907 = 1333361) B1333361
theorem B1642571 : Blo 726324 1642571 := bstep (se 1 (by rfl) ⟨1231928, by rfl⟩ : syracuseStep 1642571 = 2463857) B2463857
theorem B1577075 : Blo 726324 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B1642625 : Blo 726324 1642625 := bstep (se 2 (by rfl) ⟨615984, by rfl⟩ : syracuseStep 1642625 = 1231969) B1231969
theorem B1839307 : Blo 726324 1839307 := bstep (se 1 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 1839307 = 2758961) B2758961
theorem B2461913 : Blo 726324 2461913 := bstep (se 2 (by rfl) ⟨923217, by rfl⟩ : syracuseStep 2461913 = 1846435) B1846435
theorem B2068811 : Blo 726324 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1839449 : Blo 726324 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B1642841 : Blo 726324 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B1642931 : Blo 726324 1642931 := bstep (se 1 (by rfl) ⟨1232198, by rfl⟩ : syracuseStep 1642931 = 2464397) B2464397
theorem B1642967 : Blo 726324 1642967 := bstep (se 1 (by rfl) ⟨1232225, by rfl⟩ : syracuseStep 1642967 = 2464451) B2464451
theorem B3936833 : Blo 726324 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B1643147 : Blo 726324 1643147 := bstep (se 1 (by rfl) ⟨1232360, by rfl⟩ : syracuseStep 1643147 = 2464721) B2464721
theorem B1643201 : Blo 726324 1643201 := bstep (se 2 (by rfl) ⟨616200, by rfl⟩ : syracuseStep 1643201 = 1232401) B1232401
theorem B26546885 : Blo 726324 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B1381121 : Blo 726324 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B922519 : Blo 726324 922519 := bstep (se 1 (by rfl) ⟨691889, by rfl⟩ : syracuseStep 922519 = 1383779) B1383779
theorem B2462615 : Blo 726324 2462615 := bstep (se 1 (by rfl) ⟨1846961, by rfl⟩ : syracuseStep 2462615 = 3693923) B3693923
theorem B1381387 : Blo 726324 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B1840279 : Blo 726324 1840279 := bstep (se 1 (by rfl) ⟨1380209, by rfl⟩ : syracuseStep 1840279 = 2760419) B2760419
theorem B726327 : Blo 726324 726327 := bstep (se 1 (by rfl) ⟨544745, by rfl⟩ : syracuseStep 726327 = 1089491) B1089491
theorem B726347 : Blo 726324 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B726359 : Blo 726324 726359 := bstep (se 1 (by rfl) ⟨544769, by rfl⟩ : syracuseStep 726359 = 1089539) B1089539
theorem B726379 : Blo 726324 726379 := bstep (se 1 (by rfl) ⟨544784, by rfl⟩ : syracuseStep 726379 = 1089569) B1089569
theorem B726391 : Blo 726324 726391 := bstep (se 1 (by rfl) ⟨544793, by rfl⟩ : syracuseStep 726391 = 1089587) B1089587
theorem B726411 : Blo 726324 726411 := bstep (se 1 (by rfl) ⟨544808, by rfl⟩ : syracuseStep 726411 = 1089617) B1089617
theorem B726423 : Blo 726324 726423 := bstep (se 1 (by rfl) ⟨544817, by rfl⟩ : syracuseStep 726423 = 1089635) B1089635
theorem B726443 : Blo 726324 726443 := bstep (se 1 (by rfl) ⟨544832, by rfl⟩ : syracuseStep 726443 = 1089665) B1089665
theorem B2463155 : Blo 726324 2463155 := bstep (se 1 (by rfl) ⟨1847366, by rfl⟩ : syracuseStep 2463155 = 3694733) B3694733
theorem B726455 : Blo 726324 726455 := bstep (se 1 (by rfl) ⟨544841, by rfl⟩ : syracuseStep 726455 = 1089683) B1089683
theorem B1971649 : Blo 726324 1971649 := bstep (se 2 (by rfl) ⟨739368, by rfl⟩ : syracuseStep 1971649 = 1478737) B1478737
theorem B726475 : Blo 726324 726475 := bstep (se 1 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 726475 = 1089713) B1089713
theorem B1381835 : Blo 726324 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B726487 : Blo 726324 726487 := bstep (se 1 (by rfl) ⟨544865, by rfl⟩ : syracuseStep 726487 = 1089731) B1089731
theorem B726507 : Blo 726324 726507 := bstep (se 1 (by rfl) ⟨544880, by rfl⟩ : syracuseStep 726507 = 1089761) B1089761
theorem B726519 : Blo 726324 726519 := bstep (se 1 (by rfl) ⟨544889, by rfl⟩ : syracuseStep 726519 = 1089779) B1089779
theorem B726539 : Blo 726324 726539 := bstep (se 1 (by rfl) ⟨544904, by rfl⟩ : syracuseStep 726539 = 1089809) B1089809
theorem B726551 : Blo 726324 726551 := bstep (se 1 (by rfl) ⟨544913, by rfl⟩ : syracuseStep 726551 = 1089827) B1089827
theorem B726571 : Blo 726324 726571 := bstep (se 1 (by rfl) ⟨544928, by rfl⟩ : syracuseStep 726571 = 1089857) B1089857
theorem B726583 : Blo 726324 726583 := bstep (se 1 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 726583 = 1089875) B1089875
theorem B726603 : Blo 726324 726603 := bstep (se 1 (by rfl) ⟨544952, by rfl⟩ : syracuseStep 726603 = 1089905) B1089905
theorem B1840715 : Blo 726324 1840715 := bstep (se 1 (by rfl) ⟨1380536, by rfl⟩ : syracuseStep 1840715 = 2761073) B2761073
theorem B726615 : Blo 726324 726615 := bstep (se 1 (by rfl) ⟨544961, by rfl⟩ : syracuseStep 726615 = 1089923) B1089923
theorem B6231653 : Blo 726324 6231653 := bstep (se 4 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 6231653 = 1168435) B1168435
theorem B726635 : Blo 726324 726635 := bstep (se 1 (by rfl) ⟨544976, by rfl⟩ : syracuseStep 726635 = 1089953) B1089953
theorem B726647 : Blo 726324 726647 := bstep (se 1 (by rfl) ⟨544985, by rfl⟩ : syracuseStep 726647 = 1089971) B1089971
theorem B1382017 : Blo 726324 1382017 := bstep (se 2 (by rfl) ⟨518256, by rfl⟩ : syracuseStep 1382017 = 1036513) B1036513
theorem B726667 : Blo 726324 726667 := bstep (se 1 (by rfl) ⟨545000, by rfl⟩ : syracuseStep 726667 = 1090001) B1090001
theorem B726679 : Blo 726324 726679 := bstep (se 1 (by rfl) ⟨545009, by rfl⟩ : syracuseStep 726679 = 1090019) B1090019
theorem B726699 : Blo 726324 726699 := bstep (se 1 (by rfl) ⟨545024, by rfl⟩ : syracuseStep 726699 = 1090049) B1090049
theorem B726711 : Blo 726324 726711 := bstep (se 1 (by rfl) ⟨545033, by rfl⟩ : syracuseStep 726711 = 1090067) B1090067
theorem B2463425 : Blo 726324 2463425 := bstep (se 2 (by rfl) ⟨923784, by rfl⟩ : syracuseStep 2463425 = 1847569) B1847569
theorem B726731 : Blo 726324 726731 := bstep (se 1 (by rfl) ⟨545048, by rfl⟩ : syracuseStep 726731 = 1090097) B1090097
theorem B923339 : Blo 726324 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B726743 : Blo 726324 726743 := bstep (se 1 (by rfl) ⟨545057, by rfl⟩ : syracuseStep 726743 = 1090115) B1090115
theorem B1775321 : Blo 726324 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B726763 : Blo 726324 726763 := bstep (se 1 (by rfl) ⟨545072, by rfl⟩ : syracuseStep 726763 = 1090145) B1090145
theorem B726775 : Blo 726324 726775 := bstep (se 1 (by rfl) ⟨545081, by rfl⟩ : syracuseStep 726775 = 1090163) B1090163
theorem B726795 : Blo 726324 726795 := bstep (se 1 (by rfl) ⟨545096, by rfl⟩ : syracuseStep 726795 = 1090193) B1090193
theorem B726807 : Blo 726324 726807 := bstep (se 1 (by rfl) ⟨545105, by rfl⟩ : syracuseStep 726807 = 1090211) B1090211
theorem B726827 : Blo 726324 726827 := bstep (se 1 (by rfl) ⟨545120, by rfl⟩ : syracuseStep 726827 = 1090241) B1090241
theorem B2758445 : Blo 726324 2758445 := bstep (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) B1034417
theorem B726839 : Blo 726324 726839 := bstep (se 1 (by rfl) ⟨545129, by rfl⟩ : syracuseStep 726839 = 1090259) B1090259
theorem B2758475 : Blo 726324 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B726859 : Blo 726324 726859 := bstep (se 1 (by rfl) ⟨545144, by rfl⟩ : syracuseStep 726859 = 1090289) B1090289
theorem B726871 : Blo 726324 726871 := bstep (se 1 (by rfl) ⟨545153, by rfl⟩ : syracuseStep 726871 = 1090307) B1090307
theorem B726891 : Blo 726324 726891 := bstep (se 1 (by rfl) ⟨545168, by rfl⟩ : syracuseStep 726891 = 1090337) B1090337
theorem B726903 : Blo 726324 726903 := bstep (se 1 (by rfl) ⟨545177, by rfl⟩ : syracuseStep 726903 = 1090355) B1090355
theorem B726923 : Blo 726324 726923 := bstep (se 1 (by rfl) ⟨545192, by rfl⟩ : syracuseStep 726923 = 1090385) B1090385
theorem B726935 : Blo 726324 726935 := bstep (se 1 (by rfl) ⟨545201, by rfl⟩ : syracuseStep 726935 = 1090403) B1090403
theorem B726955 : Blo 726324 726955 := bstep (se 1 (by rfl) ⟨545216, by rfl⟩ : syracuseStep 726955 = 1090433) B1090433
theorem B2070451 : Blo 726324 2070451 := bstep (se 1 (by rfl) ⟨1552838, by rfl⟩ : syracuseStep 2070451 = 3105677) B3105677
theorem B726967 : Blo 726324 726967 := bstep (se 1 (by rfl) ⟨545225, by rfl⟩ : syracuseStep 726967 = 1090451) B1090451
theorem B1841089 : Blo 726324 1841089 := bstep (se 2 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 1841089 = 1380817) B1380817
theorem B726987 : Blo 726324 726987 := bstep (se 1 (by rfl) ⟨545240, by rfl⟩ : syracuseStep 726987 = 1090481) B1090481
theorem B726999 : Blo 726324 726999 := bstep (se 1 (by rfl) ⟨545249, by rfl⟩ : syracuseStep 726999 = 1090499) B1090499
theorem B1382359 : Blo 726324 1382359 := bstep (se 1 (by rfl) ⟨1036769, by rfl⟩ : syracuseStep 1382359 = 2073539) B2073539
theorem B727019 : Blo 726324 727019 := bstep (se 1 (by rfl) ⟨545264, by rfl⟩ : syracuseStep 727019 = 1090529) B1090529
theorem B727031 : Blo 726324 727031 := bstep (se 1 (by rfl) ⟨545273, by rfl⟩ : syracuseStep 727031 = 1090547) B1090547
theorem B3119107 : Blo 726324 3119107 := bstep (se 1 (by rfl) ⟨2339330, by rfl⟩ : syracuseStep 3119107 = 4678661) B4678661
theorem B727051 : Blo 726324 727051 := bstep (se 1 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 727051 = 1090577) B1090577
theorem B727063 : Blo 726324 727063 := bstep (se 1 (by rfl) ⟨545297, by rfl⟩ : syracuseStep 727063 = 1090595) B1090595
theorem B727083 : Blo 726324 727083 := bstep (se 1 (by rfl) ⟨545312, by rfl⟩ : syracuseStep 727083 = 1090625) B1090625
theorem B727095 : Blo 726324 727095 := bstep (se 1 (by rfl) ⟨545321, by rfl⟩ : syracuseStep 727095 = 1090643) B1090643
theorem B727115 : Blo 726324 727115 := bstep (se 1 (by rfl) ⟨545336, by rfl⟩ : syracuseStep 727115 = 1090673) B1090673
theorem B727127 : Blo 726324 727127 := bstep (se 1 (by rfl) ⟨545345, by rfl⟩ : syracuseStep 727127 = 1090691) B1090691
theorem B727147 : Blo 726324 727147 := bstep (se 1 (by rfl) ⟨545360, by rfl⟩ : syracuseStep 727147 = 1090721) B1090721
theorem B727159 : Blo 726324 727159 := bstep (se 1 (by rfl) ⟨545369, by rfl⟩ : syracuseStep 727159 = 1090739) B1090739
theorem B727179 : Blo 726324 727179 := bstep (se 1 (by rfl) ⟨545384, by rfl⟩ : syracuseStep 727179 = 1090769) B1090769
theorem B2070679 : Blo 726324 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B727191 : Blo 726324 727191 := bstep (se 1 (by rfl) ⟨545393, by rfl⟩ : syracuseStep 727191 = 1090787) B1090787
theorem B727211 : Blo 726324 727211 := bstep (se 1 (by rfl) ⟨545408, by rfl⟩ : syracuseStep 727211 = 1090817) B1090817
theorem B1382579 : Blo 726324 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B727223 : Blo 726324 727223 := bstep (se 1 (by rfl) ⟨545417, by rfl⟩ : syracuseStep 727223 = 1090835) B1090835
theorem B727243 : Blo 726324 727243 := bstep (se 1 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 727243 = 1090865) B1090865
theorem B727255 : Blo 726324 727255 := bstep (se 1 (by rfl) ⟨545441, by rfl⟩ : syracuseStep 727255 = 1090883) B1090883
theorem B2463965 : Blo 726324 2463965 := bstep (se 3 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 2463965 = 923987) B923987
theorem B727275 : Blo 726324 727275 := bstep (se 1 (by rfl) ⟨545456, by rfl⟩ : syracuseStep 727275 = 1090913) B1090913
theorem B727287 : Blo 726324 727287 := bstep (se 1 (by rfl) ⟨545465, by rfl⟩ : syracuseStep 727287 = 1090931) B1090931
theorem B727307 : Blo 726324 727307 := bstep (se 1 (by rfl) ⟨545480, by rfl⟩ : syracuseStep 727307 = 1090961) B1090961
theorem B727319 : Blo 726324 727319 := bstep (se 1 (by rfl) ⟨545489, by rfl⟩ : syracuseStep 727319 = 1090979) B1090979
theorem B2496791 : Blo 726324 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B727339 : Blo 726324 727339 := bstep (se 1 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 727339 = 1091009) B1091009
theorem B727351 : Blo 726324 727351 := bstep (se 1 (by rfl) ⟨545513, by rfl⟩ : syracuseStep 727351 = 1091027) B1091027
theorem B727371 : Blo 726324 727371 := bstep (se 1 (by rfl) ⟨545528, by rfl⟩ : syracuseStep 727371 = 1091057) B1091057
theorem B727383 : Blo 726324 727383 := bstep (se 1 (by rfl) ⟨545537, by rfl⟩ : syracuseStep 727383 = 1091075) B1091075
theorem B727403 : Blo 726324 727403 := bstep (se 1 (by rfl) ⟨545552, by rfl⟩ : syracuseStep 727403 = 1091105) B1091105
theorem B727415 : Blo 726324 727415 := bstep (se 1 (by rfl) ⟨545561, by rfl⟩ : syracuseStep 727415 = 1091123) B1091123
theorem B727435 : Blo 726324 727435 := bstep (se 1 (by rfl) ⟨545576, by rfl⟩ : syracuseStep 727435 = 1091153) B1091153
theorem B924043 : Blo 726324 924043 := bstep (se 1 (by rfl) ⟨693032, by rfl⟩ : syracuseStep 924043 = 1386065) B1386065
theorem B727447 : Blo 726324 727447 := bstep (se 1 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 727447 = 1091171) B1091171
theorem B1382807 : Blo 726324 1382807 := bstep (se 1 (by rfl) ⟨1037105, by rfl⟩ : syracuseStep 1382807 = 2074211) B2074211
theorem B727467 : Blo 726324 727467 := bstep (se 1 (by rfl) ⟨545600, by rfl⟩ : syracuseStep 727467 = 1091201) B1091201
theorem B727479 : Blo 726324 727479 := bstep (se 1 (by rfl) ⟨545609, by rfl⟩ : syracuseStep 727479 = 1091219) B1091219
theorem B727499 : Blo 726324 727499 := bstep (se 1 (by rfl) ⟨545624, by rfl⟩ : syracuseStep 727499 = 1091249) B1091249
theorem B727511 : Blo 726324 727511 := bstep (se 1 (by rfl) ⟨545633, by rfl⟩ : syracuseStep 727511 = 1091267) B1091267
theorem B2759129 : Blo 726324 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B727531 : Blo 726324 727531 := bstep (se 1 (by rfl) ⟨545648, by rfl⟩ : syracuseStep 727531 = 1091297) B1091297
theorem B727543 : Blo 726324 727543 := bstep (se 1 (by rfl) ⟨545657, by rfl⟩ : syracuseStep 727543 = 1091315) B1091315
theorem B727563 : Blo 726324 727563 := bstep (se 1 (by rfl) ⟨545672, by rfl⟩ : syracuseStep 727563 = 1091345) B1091345
theorem B727575 : Blo 726324 727575 := bstep (se 1 (by rfl) ⟨545681, by rfl⟩ : syracuseStep 727575 = 1091363) B1091363
theorem B1841687 : Blo 726324 1841687 := bstep (se 1 (by rfl) ⟨1381265, by rfl⟩ : syracuseStep 1841687 = 2762531) B2762531
theorem B727595 : Blo 726324 727595 := bstep (se 1 (by rfl) ⟨545696, by rfl⟩ : syracuseStep 727595 = 1091393) B1091393
theorem B727607 : Blo 726324 727607 := bstep (se 1 (by rfl) ⟨545705, by rfl⟩ : syracuseStep 727607 = 1091411) B1091411
theorem B727627 : Blo 726324 727627 := bstep (se 1 (by rfl) ⟨545720, by rfl⟩ : syracuseStep 727627 = 1091441) B1091441
theorem B727639 : Blo 726324 727639 := bstep (se 1 (by rfl) ⟨545729, by rfl⟩ : syracuseStep 727639 = 1091459) B1091459
theorem B1972829 : Blo 726324 1972829 := bstep (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) B739811
theorem B727659 : Blo 726324 727659 := bstep (se 1 (by rfl) ⟨545744, by rfl⟩ : syracuseStep 727659 = 1091489) B1091489
theorem B727671 : Blo 726324 727671 := bstep (se 1 (by rfl) ⟨545753, by rfl⟩ : syracuseStep 727671 = 1091507) B1091507
theorem B727691 : Blo 726324 727691 := bstep (se 1 (by rfl) ⟨545768, by rfl⟩ : syracuseStep 727691 = 1091537) B1091537
theorem B727703 : Blo 726324 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B924311 : Blo 726324 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B1383065 : Blo 726324 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B727723 : Blo 726324 727723 := bstep (se 1 (by rfl) ⟨545792, by rfl⟩ : syracuseStep 727723 = 1091585) B1091585
theorem B727735 : Blo 726324 727735 := bstep (se 1 (by rfl) ⟨545801, by rfl⟩ : syracuseStep 727735 = 1091603) B1091603
theorem B727755 : Blo 726324 727755 := bstep (se 1 (by rfl) ⟨545816, by rfl⟩ : syracuseStep 727755 = 1091633) B1091633
theorem B727767 : Blo 726324 727767 := bstep (se 1 (by rfl) ⟨545825, by rfl⟩ : syracuseStep 727767 = 1091651) B1091651
theorem B4659929 : Blo 726324 4659929 := bstep (se 2 (by rfl) ⟨1747473, by rfl⟩ : syracuseStep 4659929 = 3494947) B3494947
theorem B727787 : Blo 726324 727787 := bstep (se 1 (by rfl) ⟨545840, by rfl⟩ : syracuseStep 727787 = 1091681) B1091681
theorem B727799 : Blo 726324 727799 := bstep (se 1 (by rfl) ⟨545849, by rfl⟩ : syracuseStep 727799 = 1091699) B1091699
theorem B727819 : Blo 726324 727819 := bstep (se 1 (by rfl) ⟨545864, by rfl⟩ : syracuseStep 727819 = 1091729) B1091729
theorem B2759447 : Blo 726324 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B727831 : Blo 726324 727831 := bstep (se 1 (by rfl) ⟨545873, by rfl⟩ : syracuseStep 727831 = 1091747) B1091747
theorem B727851 : Blo 726324 727851 := bstep (se 1 (by rfl) ⟨545888, by rfl⟩ : syracuseStep 727851 = 1091777) B1091777
theorem B727863 : Blo 726324 727863 := bstep (se 1 (by rfl) ⟨545897, by rfl⟩ : syracuseStep 727863 = 1091795) B1091795
theorem B727883 : Blo 726324 727883 := bstep (se 1 (by rfl) ⟨545912, by rfl⟩ : syracuseStep 727883 = 1091825) B1091825
theorem B727895 : Blo 726324 727895 := bstep (se 1 (by rfl) ⟨545921, by rfl⟩ : syracuseStep 727895 = 1091843) B1091843
theorem B727915 : Blo 726324 727915 := bstep (se 1 (by rfl) ⟨545936, by rfl⟩ : syracuseStep 727915 = 1091873) B1091873
theorem B727927 : Blo 726324 727927 := bstep (se 1 (by rfl) ⟨545945, by rfl⟩ : syracuseStep 727927 = 1091891) B1091891
theorem B727947 : Blo 726324 727947 := bstep (se 1 (by rfl) ⟨545960, by rfl⟩ : syracuseStep 727947 = 1091921) B1091921
theorem B727959 : Blo 726324 727959 := bstep (se 1 (by rfl) ⟨545969, by rfl⟩ : syracuseStep 727959 = 1091939) B1091939
theorem B727979 : Blo 726324 727979 := bstep (se 1 (by rfl) ⟨545984, by rfl⟩ : syracuseStep 727979 = 1091969) B1091969
theorem B727991 : Blo 726324 727991 := bstep (se 1 (by rfl) ⟨545993, by rfl⟩ : syracuseStep 727991 = 1091987) B1091987
theorem B728011 : Blo 726324 728011 := bstep (se 1 (by rfl) ⟨546008, by rfl⟩ : syracuseStep 728011 = 1092017) B1092017
theorem B728023 : Blo 726324 728023 := bstep (se 1 (by rfl) ⟨546017, by rfl⟩ : syracuseStep 728023 = 1092035) B1092035
theorem B728043 : Blo 726324 728043 := bstep (se 1 (by rfl) ⟨546032, by rfl⟩ : syracuseStep 728043 = 1092065) B1092065
theorem B728055 : Blo 726324 728055 := bstep (se 1 (by rfl) ⟨546041, by rfl⟩ : syracuseStep 728055 = 1092083) B1092083
theorem B728075 : Blo 726324 728075 := bstep (se 1 (by rfl) ⟨546056, by rfl⟩ : syracuseStep 728075 = 1092113) B1092113
theorem B728087 : Blo 726324 728087 := bstep (se 1 (by rfl) ⟨546065, by rfl⟩ : syracuseStep 728087 = 1092131) B1092131
theorem B728107 : Blo 726324 728107 := bstep (se 1 (by rfl) ⟨546080, by rfl⟩ : syracuseStep 728107 = 1092161) B1092161
theorem B1383475 : Blo 726324 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B728119 : Blo 726324 728119 := bstep (se 1 (by rfl) ⟨546089, by rfl⟩ : syracuseStep 728119 = 1092179) B1092179
theorem B23665733 : Blo 726324 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B728139 : Blo 726324 728139 := bstep (se 1 (by rfl) ⟨546104, by rfl⟩ : syracuseStep 728139 = 1092209) B1092209
theorem B728151 : Blo 726324 728151 := bstep (se 1 (by rfl) ⟨546113, by rfl⟩ : syracuseStep 728151 = 1092227) B1092227
theorem B728171 : Blo 726324 728171 := bstep (se 1 (by rfl) ⟨546128, by rfl⟩ : syracuseStep 728171 = 1092257) B1092257
theorem B728183 : Blo 726324 728183 := bstep (se 1 (by rfl) ⟨546137, by rfl⟩ : syracuseStep 728183 = 1092275) B1092275
theorem B728203 : Blo 726324 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B728215 : Blo 726324 728215 := bstep (se 1 (by rfl) ⟨546161, by rfl⟩ : syracuseStep 728215 = 1092323) B1092323
theorem B728235 : Blo 726324 728235 := bstep (se 1 (by rfl) ⟨546176, by rfl⟩ : syracuseStep 728235 = 1092353) B1092353
theorem B728247 : Blo 726324 728247 := bstep (se 1 (by rfl) ⟨546185, by rfl⟩ : syracuseStep 728247 = 1092371) B1092371
theorem B728267 : Blo 726324 728267 := bstep (se 1 (by rfl) ⟨546200, by rfl⟩ : syracuseStep 728267 = 1092401) B1092401
theorem B728279 : Blo 726324 728279 := bstep (se 1 (by rfl) ⟨546209, by rfl⟩ : syracuseStep 728279 = 1092419) B1092419
theorem B728299 : Blo 726324 728299 := bstep (se 1 (by rfl) ⟨546224, by rfl⟩ : syracuseStep 728299 = 1092449) B1092449
theorem B728311 : Blo 726324 728311 := bstep (se 1 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 728311 = 1092467) B1092467
theorem B728331 : Blo 726324 728331 := bstep (se 1 (by rfl) ⟨546248, by rfl⟩ : syracuseStep 728331 = 1092497) B1092497
theorem B728343 : Blo 726324 728343 := bstep (se 1 (by rfl) ⟨546257, by rfl⟩ : syracuseStep 728343 = 1092515) B1092515
theorem B728363 : Blo 726324 728363 := bstep (se 1 (by rfl) ⟨546272, by rfl⟩ : syracuseStep 728363 = 1092545) B1092545
theorem B728375 : Blo 726324 728375 := bstep (se 1 (by rfl) ⟨546281, by rfl⟩ : syracuseStep 728375 = 1092563) B1092563
theorem B1842497 : Blo 726324 1842497 := bstep (se 2 (by rfl) ⟨690936, by rfl⟩ : syracuseStep 1842497 = 1381873) B1381873
theorem B728395 : Blo 726324 728395 := bstep (se 1 (by rfl) ⟨546296, by rfl⟩ : syracuseStep 728395 = 1092593) B1092593
theorem B728407 : Blo 726324 728407 := bstep (se 1 (by rfl) ⟨546305, by rfl⟩ : syracuseStep 728407 = 1092611) B1092611
theorem B728427 : Blo 726324 728427 := bstep (se 1 (by rfl) ⟨546320, by rfl⟩ : syracuseStep 728427 = 1092641) B1092641
theorem B728439 : Blo 726324 728439 := bstep (se 1 (by rfl) ⟨546329, by rfl⟩ : syracuseStep 728439 = 1092659) B1092659
theorem B728459 : Blo 726324 728459 := bstep (se 1 (by rfl) ⟨546344, by rfl⟩ : syracuseStep 728459 = 1092689) B1092689
theorem B728471 : Blo 726324 728471 := bstep (se 1 (by rfl) ⟨546353, by rfl⟩ : syracuseStep 728471 = 1092707) B1092707
theorem B728491 : Blo 726324 728491 := bstep (se 1 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 728491 = 1092737) B1092737
theorem B2760115 : Blo 726324 2760115 := bstep (se 1 (by rfl) ⟨2070086, by rfl⟩ : syracuseStep 2760115 = 4140173) B4140173
theorem B728503 : Blo 726324 728503 := bstep (se 1 (by rfl) ⟨546377, by rfl⟩ : syracuseStep 728503 = 1092755) B1092755
theorem B728523 : Blo 726324 728523 := bstep (se 1 (by rfl) ⟨546392, by rfl⟩ : syracuseStep 728523 = 1092785) B1092785
theorem B728535 : Blo 726324 728535 := bstep (se 1 (by rfl) ⟨546401, by rfl⟩ : syracuseStep 728535 = 1092803) B1092803
theorem B728555 : Blo 726324 728555 := bstep (se 1 (by rfl) ⟨546416, by rfl⟩ : syracuseStep 728555 = 1092833) B1092833
theorem B728567 : Blo 726324 728567 := bstep (se 1 (by rfl) ⟨546425, by rfl⟩ : syracuseStep 728567 = 1092851) B1092851
theorem B728587 : Blo 726324 728587 := bstep (se 1 (by rfl) ⟨546440, by rfl⟩ : syracuseStep 728587 = 1092881) B1092881
theorem B5250577 : Blo 726324 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B728599 : Blo 726324 728599 := bstep (se 1 (by rfl) ⟨546449, by rfl⟩ : syracuseStep 728599 = 1092899) B1092899
theorem B1383961 : Blo 726324 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B728619 : Blo 726324 728619 := bstep (se 1 (by rfl) ⟨546464, by rfl⟩ : syracuseStep 728619 = 1092929) B1092929
theorem B728631 : Blo 726324 728631 := bstep (se 1 (by rfl) ⟨546473, by rfl⟩ : syracuseStep 728631 = 1092947) B1092947
theorem B728651 : Blo 726324 728651 := bstep (se 1 (by rfl) ⟨546488, by rfl⟩ : syracuseStep 728651 = 1092977) B1092977
theorem B728663 : Blo 726324 728663 := bstep (se 1 (by rfl) ⟨546497, by rfl⟩ : syracuseStep 728663 = 1092995) B1092995
theorem B728683 : Blo 726324 728683 := bstep (se 1 (by rfl) ⟨546512, by rfl⟩ : syracuseStep 728683 = 1093025) B1093025
theorem B728695 : Blo 726324 728695 := bstep (se 1 (by rfl) ⟨546521, by rfl⟩ : syracuseStep 728695 = 1093043) B1093043
theorem B728715 : Blo 726324 728715 := bstep (se 1 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 728715 = 1093073) B1093073
theorem B728727 : Blo 726324 728727 := bstep (se 1 (by rfl) ⟨546545, by rfl⟩ : syracuseStep 728727 = 1093091) B1093091
theorem B728747 : Blo 726324 728747 := bstep (se 1 (by rfl) ⟨546560, by rfl⟩ : syracuseStep 728747 = 1093121) B1093121
theorem B728759 : Blo 726324 728759 := bstep (se 1 (by rfl) ⟨546569, by rfl⟩ : syracuseStep 728759 = 1093139) B1093139
theorem B728779 : Blo 726324 728779 := bstep (se 1 (by rfl) ⟨546584, by rfl⟩ : syracuseStep 728779 = 1093169) B1093169
theorem B728791 : Blo 726324 728791 := bstep (se 1 (by rfl) ⟨546593, by rfl⟩ : syracuseStep 728791 = 1093187) B1093187
theorem B728811 : Blo 726324 728811 := bstep (se 1 (by rfl) ⟨546608, by rfl⟩ : syracuseStep 728811 = 1093217) B1093217
theorem B728823 : Blo 726324 728823 := bstep (se 1 (by rfl) ⟨546617, by rfl⟩ : syracuseStep 728823 = 1093235) B1093235
theorem B728843 : Blo 726324 728843 := bstep (se 1 (by rfl) ⟨546632, by rfl⟩ : syracuseStep 728843 = 1093265) B1093265
theorem B6627089 : Blo 726324 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B5545745 : Blo 726324 5545745 := bstep (se 2 (by rfl) ⟨2079654, by rfl⟩ : syracuseStep 5545745 = 4159309) B4159309
theorem B728855 : Blo 726324 728855 := bstep (se 1 (by rfl) ⟨546641, by rfl⟩ : syracuseStep 728855 = 1093283) B1093283
theorem B728875 : Blo 726324 728875 := bstep (se 1 (by rfl) ⟨546656, by rfl⟩ : syracuseStep 728875 = 1093313) B1093313
theorem B728887 : Blo 726324 728887 := bstep (se 1 (by rfl) ⟨546665, by rfl⟩ : syracuseStep 728887 = 1093331) B1093331
theorem B728907 : Blo 726324 728907 := bstep (se 1 (by rfl) ⟨546680, by rfl⟩ : syracuseStep 728907 = 1093361) B1093361
theorem B728919 : Blo 726324 728919 := bstep (se 1 (by rfl) ⟨546689, by rfl⟩ : syracuseStep 728919 = 1093379) B1093379
theorem B1843033 : Blo 726324 1843033 := bstep (se 2 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 1843033 = 1382275) B1382275
theorem B2629469 : Blo 726324 2629469 := bstep (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) B986051
theorem B728939 : Blo 726324 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B728951 : Blo 726324 728951 := bstep (se 1 (by rfl) ⟨546713, by rfl⟩ : syracuseStep 728951 = 1093427) B1093427
theorem B728971 : Blo 726324 728971 := bstep (se 1 (by rfl) ⟨546728, by rfl⟩ : syracuseStep 728971 = 1093457) B1093457
theorem B728983 : Blo 726324 728983 := bstep (se 1 (by rfl) ⟨546737, by rfl⟩ : syracuseStep 728983 = 1093475) B1093475
theorem B729003 : Blo 726324 729003 := bstep (se 1 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 729003 = 1093505) B1093505
theorem B729015 : Blo 726324 729015 := bstep (se 1 (by rfl) ⟨546761, by rfl⟩ : syracuseStep 729015 = 1093523) B1093523
theorem B729035 : Blo 726324 729035 := bstep (se 1 (by rfl) ⟨546776, by rfl⟩ : syracuseStep 729035 = 1093553) B1093553
theorem B729047 : Blo 726324 729047 := bstep (se 1 (by rfl) ⟨546785, by rfl⟩ : syracuseStep 729047 = 1093571) B1093571
theorem B1089497 : Blo 726324 1089497 := bstep (se 2 (by rfl) ⟨408561, by rfl⟩ : syracuseStep 1089497 = 817123) B817123
theorem B2072537 : Blo 726324 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B729067 : Blo 726324 729067 := bstep (se 1 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 729067 = 1093601) B1093601
theorem B729079 : Blo 726324 729079 := bstep (se 1 (by rfl) ⟨546809, by rfl⟩ : syracuseStep 729079 = 1093619) B1093619
theorem B729099 : Blo 726324 729099 := bstep (se 1 (by rfl) ⟨546824, by rfl⟩ : syracuseStep 729099 = 1093649) B1093649
theorem B729111 : Blo 726324 729111 := bstep (se 1 (by rfl) ⟨546833, by rfl⟩ : syracuseStep 729111 = 1093667) B1093667
theorem B12754979 : Blo 726324 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B729131 : Blo 726324 729131 := bstep (se 1 (by rfl) ⟨546848, by rfl⟩ : syracuseStep 729131 = 1093697) B1093697
theorem B729143 : Blo 726324 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B1089611 : Blo 726324 1089611 := bstep (se 1 (by rfl) ⟨817208, by rfl⟩ : syracuseStep 1089611 = 1634417) B1634417
theorem B729163 : Blo 726324 729163 := bstep (se 1 (by rfl) ⟨546872, by rfl⟩ : syracuseStep 729163 = 1093745) B1093745
theorem B1384523 : Blo 726324 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B1089623 : Blo 726324 1089623 := bstep (se 1 (by rfl) ⟨817217, by rfl⟩ : syracuseStep 1089623 = 1634435) B1634435
theorem B729175 : Blo 726324 729175 := bstep (se 1 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 729175 = 1093763) B1093763
theorem B729195 : Blo 726324 729195 := bstep (se 1 (by rfl) ⟨546896, by rfl⟩ : syracuseStep 729195 = 1093793) B1093793
theorem B729207 : Blo 726324 729207 := bstep (se 1 (by rfl) ⟨546905, by rfl⟩ : syracuseStep 729207 = 1093811) B1093811
theorem B729227 : Blo 726324 729227 := bstep (se 1 (by rfl) ⟨546920, by rfl⟩ : syracuseStep 729227 = 1093841) B1093841
theorem B729239 : Blo 726324 729239 := bstep (se 1 (by rfl) ⟨546929, by rfl⟩ : syracuseStep 729239 = 1093859) B1093859
theorem B1089689 : Blo 726324 1089689 := bstep (se 2 (by rfl) ⟨408633, by rfl⟩ : syracuseStep 1089689 = 817267) B817267
theorem B729259 : Blo 726324 729259 := bstep (se 1 (by rfl) ⟨546944, by rfl⟩ : syracuseStep 729259 = 1093889) B1093889
theorem B729271 : Blo 726324 729271 := bstep (se 1 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 729271 = 1093907) B1093907
theorem B729291 : Blo 726324 729291 := bstep (se 1 (by rfl) ⟨546968, by rfl⟩ : syracuseStep 729291 = 1093937) B1093937
theorem B6234317 : Blo 726324 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B729303 : Blo 726324 729303 := bstep (se 1 (by rfl) ⟨546977, by rfl⟩ : syracuseStep 729303 = 1093955) B1093955
theorem B729323 : Blo 726324 729323 := bstep (se 1 (by rfl) ⟨546992, by rfl⟩ : syracuseStep 729323 = 1093985) B1093985
theorem B729335 : Blo 726324 729335 := bstep (se 1 (by rfl) ⟨547001, by rfl⟩ : syracuseStep 729335 = 1094003) B1094003
theorem B1384705 : Blo 726324 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B1089803 : Blo 726324 1089803 := bstep (se 1 (by rfl) ⟨817352, by rfl⟩ : syracuseStep 1089803 = 1634705) B1634705
theorem B729355 : Blo 726324 729355 := bstep (se 1 (by rfl) ⟨547016, by rfl⟩ : syracuseStep 729355 = 1094033) B1094033
theorem B1089815 : Blo 726324 1089815 := bstep (se 1 (by rfl) ⟨817361, by rfl⟩ : syracuseStep 1089815 = 1634723) B1634723
theorem B729367 : Blo 726324 729367 := bstep (se 1 (by rfl) ⟨547025, by rfl⟩ : syracuseStep 729367 = 1094051) B1094051
theorem B729387 : Blo 726324 729387 := bstep (se 1 (by rfl) ⟨547040, by rfl⟩ : syracuseStep 729387 = 1094081) B1094081
theorem B729399 : Blo 726324 729399 := bstep (se 1 (by rfl) ⟨547049, by rfl⟩ : syracuseStep 729399 = 1094099) B1094099
theorem B729419 : Blo 726324 729419 := bstep (se 1 (by rfl) ⟨547064, by rfl⟩ : syracuseStep 729419 = 1094129) B1094129
theorem B729431 : Blo 726324 729431 := bstep (se 1 (by rfl) ⟨547073, by rfl⟩ : syracuseStep 729431 = 1094147) B1094147
theorem B1089881 : Blo 726324 1089881 := bstep (se 2 (by rfl) ⟨408705, by rfl⟩ : syracuseStep 1089881 = 817411) B817411
theorem B729451 : Blo 726324 729451 := bstep (se 1 (by rfl) ⟨547088, by rfl⟩ : syracuseStep 729451 = 1094177) B1094177
theorem B729463 : Blo 726324 729463 := bstep (se 1 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 729463 = 1094195) B1094195
theorem B729483 : Blo 726324 729483 := bstep (se 1 (by rfl) ⟨547112, by rfl⟩ : syracuseStep 729483 = 1094225) B1094225
theorem B25174421 : Blo 726324 25174421 := bstep (se 6 (by rfl) ⟨590025, by rfl⟩ : syracuseStep 25174421 = 1180051) B1180051
theorem B729495 : Blo 726324 729495 := bstep (se 1 (by rfl) ⟨547121, by rfl⟩ : syracuseStep 729495 = 1094243) B1094243
theorem B729515 : Blo 726324 729515 := bstep (se 1 (by rfl) ⟨547136, by rfl⟩ : syracuseStep 729515 = 1094273) B1094273
theorem B729527 : Blo 726324 729527 := bstep (se 1 (by rfl) ⟨547145, by rfl⟩ : syracuseStep 729527 = 1094291) B1094291
theorem B1089995 : Blo 726324 1089995 := bstep (se 1 (by rfl) ⟨817496, by rfl⟩ : syracuseStep 1089995 = 1634993) B1634993
theorem B729547 : Blo 726324 729547 := bstep (se 1 (by rfl) ⟨547160, by rfl⟩ : syracuseStep 729547 = 1094321) B1094321
theorem B1090007 : Blo 726324 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B729559 : Blo 726324 729559 := bstep (se 1 (by rfl) ⟨547169, by rfl⟩ : syracuseStep 729559 = 1094339) B1094339
theorem B2335193 : Blo 726324 2335193 := bstep (se 2 (by rfl) ⟨875697, by rfl⟩ : syracuseStep 2335193 = 1751395) B1751395
theorem B729579 : Blo 726324 729579 := bstep (se 1 (by rfl) ⟨547184, by rfl⟩ : syracuseStep 729579 = 1094369) B1094369
theorem B729591 : Blo 726324 729591 := bstep (se 1 (by rfl) ⟨547193, by rfl⟩ : syracuseStep 729591 = 1094387) B1094387
theorem B729611 : Blo 726324 729611 := bstep (se 1 (by rfl) ⟨547208, by rfl⟩ : syracuseStep 729611 = 1094417) B1094417
theorem B729623 : Blo 726324 729623 := bstep (se 1 (by rfl) ⟨547217, by rfl⟩ : syracuseStep 729623 = 1094435) B1094435
theorem B1090073 : Blo 726324 1090073 := bstep (se 2 (by rfl) ⟨408777, by rfl⟩ : syracuseStep 1090073 = 817555) B817555
theorem B11969059 : Blo 726324 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B729643 : Blo 726324 729643 := bstep (se 1 (by rfl) ⟨547232, by rfl⟩ : syracuseStep 729643 = 1094465) B1094465
theorem B729655 : Blo 726324 729655 := bstep (se 1 (by rfl) ⟨547241, by rfl⟩ : syracuseStep 729655 = 1094483) B1094483
theorem B729675 : Blo 726324 729675 := bstep (se 1 (by rfl) ⟨547256, by rfl⟩ : syracuseStep 729675 = 1094513) B1094513
theorem B729687 : Blo 726324 729687 := bstep (se 1 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 729687 = 1094531) B1094531
theorem B729707 : Blo 726324 729707 := bstep (se 1 (by rfl) ⟨547280, by rfl⟩ : syracuseStep 729707 = 1094561) B1094561
theorem B729719 : Blo 726324 729719 := bstep (se 1 (by rfl) ⟨547289, by rfl⟩ : syracuseStep 729719 = 1094579) B1094579
theorem B1090187 : Blo 726324 1090187 := bstep (se 1 (by rfl) ⟨817640, by rfl⟩ : syracuseStep 1090187 = 1635281) B1635281
theorem B729739 : Blo 726324 729739 := bstep (se 1 (by rfl) ⟨547304, by rfl⟩ : syracuseStep 729739 = 1094609) B1094609
theorem B2761361 : Blo 726324 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B1090199 : Blo 726324 1090199 := bstep (se 1 (by rfl) ⟨817649, by rfl⟩ : syracuseStep 1090199 = 1635299) B1635299
theorem B729751 : Blo 726324 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B729771 : Blo 726324 729771 := bstep (se 1 (by rfl) ⟨547328, by rfl⟩ : syracuseStep 729771 = 1094657) B1094657
theorem B729783 : Blo 726324 729783 := bstep (se 1 (by rfl) ⟨547337, by rfl⟩ : syracuseStep 729783 = 1094675) B1094675
theorem B729803 : Blo 726324 729803 := bstep (se 1 (by rfl) ⟨547352, by rfl⟩ : syracuseStep 729803 = 1094705) B1094705
theorem B729815 : Blo 726324 729815 := bstep (se 1 (by rfl) ⟨547361, by rfl⟩ : syracuseStep 729815 = 1094723) B1094723
theorem B1090265 : Blo 726324 1090265 := bstep (se 2 (by rfl) ⟨408849, by rfl⟩ : syracuseStep 1090265 = 817699) B817699
theorem B729835 : Blo 726324 729835 := bstep (se 1 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 729835 = 1094753) B1094753
theorem B729847 : Blo 726324 729847 := bstep (se 1 (by rfl) ⟨547385, by rfl⟩ : syracuseStep 729847 = 1094771) B1094771
theorem B729867 : Blo 726324 729867 := bstep (se 1 (by rfl) ⟨547400, by rfl⟩ : syracuseStep 729867 = 1094801) B1094801
theorem B2073367 : Blo 726324 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B2335511 : Blo 726324 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B729879 : Blo 726324 729879 := bstep (se 1 (by rfl) ⟨547409, by rfl⟩ : syracuseStep 729879 = 1094819) B1094819
theorem B729899 : Blo 726324 729899 := bstep (se 1 (by rfl) ⟨547424, by rfl⟩ : syracuseStep 729899 = 1094849) B1094849
theorem B729911 : Blo 726324 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B1090379 : Blo 726324 1090379 := bstep (se 1 (by rfl) ⟨817784, by rfl⟩ : syracuseStep 1090379 = 1635569) B1635569
theorem B729931 : Blo 726324 729931 := bstep (se 1 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 729931 = 1094897) B1094897
theorem B1090391 : Blo 726324 1090391 := bstep (se 1 (by rfl) ⟨817793, by rfl⟩ : syracuseStep 1090391 = 1635587) B1635587
theorem B729943 : Blo 726324 729943 := bstep (se 1 (by rfl) ⟨547457, by rfl⟩ : syracuseStep 729943 = 1094915) B1094915
theorem B729963 : Blo 726324 729963 := bstep (se 1 (by rfl) ⟨547472, by rfl⟩ : syracuseStep 729963 = 1094945) B1094945
theorem B729975 : Blo 726324 729975 := bstep (se 1 (by rfl) ⟨547481, by rfl⟩ : syracuseStep 729975 = 1094963) B1094963
theorem B729995 : Blo 726324 729995 := bstep (se 1 (by rfl) ⟨547496, by rfl⟩ : syracuseStep 729995 = 1094993) B1094993
theorem B2630551 : Blo 726324 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B730007 : Blo 726324 730007 := bstep (se 1 (by rfl) ⟨547505, by rfl⟩ : syracuseStep 730007 = 1095011) B1095011
theorem B1090457 : Blo 726324 1090457 := bstep (se 2 (by rfl) ⟨408921, by rfl⟩ : syracuseStep 1090457 = 817843) B817843
theorem B730027 : Blo 726324 730027 := bstep (se 1 (by rfl) ⟨547520, by rfl⟩ : syracuseStep 730027 = 1095041) B1095041
theorem B1844147 : Blo 726324 1844147 := bstep (se 1 (by rfl) ⟨1383110, by rfl⟩ : syracuseStep 1844147 = 2766221) B2766221
theorem B730039 : Blo 726324 730039 := bstep (se 1 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 730039 = 1095059) B1095059
theorem B1385419 : Blo 726324 1385419 := bstep (se 1 (by rfl) ⟨1039064, by rfl⟩ : syracuseStep 1385419 = 2078129) B2078129
theorem B730059 : Blo 726324 730059 := bstep (se 1 (by rfl) ⟨547544, by rfl⟩ : syracuseStep 730059 = 1095089) B1095089
theorem B730071 : Blo 726324 730071 := bstep (se 1 (by rfl) ⟨547553, by rfl⟩ : syracuseStep 730071 = 1095107) B1095107
theorem B730091 : Blo 726324 730091 := bstep (se 1 (by rfl) ⟨547568, by rfl⟩ : syracuseStep 730091 = 1095137) B1095137
theorem B730103 : Blo 726324 730103 := bstep (se 1 (by rfl) ⟨547577, by rfl⟩ : syracuseStep 730103 = 1095155) B1095155
theorem B1090571 : Blo 726324 1090571 := bstep (se 1 (by rfl) ⟨817928, by rfl⟩ : syracuseStep 1090571 = 1635857) B1635857
theorem B730123 : Blo 726324 730123 := bstep (se 1 (by rfl) ⟨547592, by rfl⟩ : syracuseStep 730123 = 1095185) B1095185
theorem B1090583 : Blo 726324 1090583 := bstep (se 1 (by rfl) ⟨817937, by rfl⟩ : syracuseStep 1090583 = 1635875) B1635875
theorem B1385495 : Blo 726324 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B730135 : Blo 726324 730135 := bstep (se 1 (by rfl) ⟨547601, by rfl⟩ : syracuseStep 730135 = 1095203) B1095203
theorem B730155 : Blo 726324 730155 := bstep (se 1 (by rfl) ⟨547616, by rfl⟩ : syracuseStep 730155 = 1095233) B1095233
theorem B730167 : Blo 726324 730167 := bstep (se 1 (by rfl) ⟨547625, by rfl⟩ : syracuseStep 730167 = 1095251) B1095251
theorem B2335819 : Blo 726324 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B730187 : Blo 726324 730187 := bstep (se 1 (by rfl) ⟨547640, by rfl⟩ : syracuseStep 730187 = 1095281) B1095281
theorem B730199 : Blo 726324 730199 := bstep (se 1 (by rfl) ⟨547649, by rfl⟩ : syracuseStep 730199 = 1095299) B1095299
theorem B1090649 : Blo 726324 1090649 := bstep (se 2 (by rfl) ⟨408993, by rfl⟩ : syracuseStep 1090649 = 817987) B817987
theorem B730219 : Blo 726324 730219 := bstep (se 1 (by rfl) ⟨547664, by rfl⟩ : syracuseStep 730219 = 1095329) B1095329
theorem B730231 : Blo 726324 730231 := bstep (se 1 (by rfl) ⟨547673, by rfl⟩ : syracuseStep 730231 = 1095347) B1095347
theorem B730251 : Blo 726324 730251 := bstep (se 1 (by rfl) ⟨547688, by rfl⟩ : syracuseStep 730251 = 1095377) B1095377
theorem B730263 : Blo 726324 730263 := bstep (se 1 (by rfl) ⟨547697, by rfl⟩ : syracuseStep 730263 = 1095395) B1095395
theorem B730283 : Blo 726324 730283 := bstep (se 1 (by rfl) ⟨547712, by rfl⟩ : syracuseStep 730283 = 1095425) B1095425
theorem B730295 : Blo 726324 730295 := bstep (se 1 (by rfl) ⟨547721, by rfl⟩ : syracuseStep 730295 = 1095443) B1095443
theorem B1090763 : Blo 726324 1090763 := bstep (se 1 (by rfl) ⟨818072, by rfl⟩ : syracuseStep 1090763 = 1636145) B1636145
theorem B730315 : Blo 726324 730315 := bstep (se 1 (by rfl) ⟨547736, by rfl⟩ : syracuseStep 730315 = 1095473) B1095473
theorem B1090775 : Blo 726324 1090775 := bstep (se 1 (by rfl) ⟨818081, by rfl⟩ : syracuseStep 1090775 = 1636163) B1636163
theorem B1746137 : Blo 726324 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1844441 : Blo 726324 1844441 := bstep (se 2 (by rfl) ⟨691665, by rfl⟩ : syracuseStep 1844441 = 1383331) B1383331
theorem B3679505 : Blo 726324 3679505 := bstep (se 2 (by rfl) ⟨1379814, by rfl⟩ : syracuseStep 3679505 = 2759629) B2759629
theorem B1090841 : Blo 726324 1090841 := bstep (se 2 (by rfl) ⟨409065, by rfl⟩ : syracuseStep 1090841 = 818131) B818131
theorem B4662593 : Blo 726324 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B2762059 : Blo 726324 2762059 := bstep (se 1 (by rfl) ⟨2071544, by rfl⟩ : syracuseStep 2762059 = 4143089) B4143089
theorem B1090955 : Blo 726324 1090955 := bstep (se 1 (by rfl) ⟨818216, by rfl⟩ : syracuseStep 1090955 = 1636433) B1636433
theorem B1090967 : Blo 726324 1090967 := bstep (se 1 (by rfl) ⟨818225, by rfl⟩ : syracuseStep 1090967 = 1636451) B1636451
theorem B3679667 : Blo 726324 3679667 := bstep (se 1 (by rfl) ⟨2759750, by rfl⟩ : syracuseStep 3679667 = 5519501) B5519501
theorem B1091033 : Blo 726324 1091033 := bstep (se 2 (by rfl) ⟨409137, by rfl⟩ : syracuseStep 1091033 = 818275) B818275
theorem B1091147 : Blo 726324 1091147 := bstep (se 1 (by rfl) ⟨818360, by rfl⟩ : syracuseStep 1091147 = 1636721) B1636721
theorem B2074187 : Blo 726324 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B1091159 : Blo 726324 1091159 := bstep (se 1 (by rfl) ⟨818369, by rfl⟩ : syracuseStep 1091159 = 1636739) B1636739
theorem B2762333 : Blo 726324 2762333 := bstep (se 3 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 2762333 = 1035875) B1035875
theorem B1091225 : Blo 726324 1091225 := bstep (se 2 (by rfl) ⟨409209, by rfl⟩ : syracuseStep 1091225 = 818419) B818419
theorem B2336435 : Blo 726324 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B1386163 : Blo 726324 1386163 := bstep (se 1 (by rfl) ⟨1039622, by rfl⟩ : syracuseStep 1386163 = 2079245) B2079245
theorem B2631371 : Blo 726324 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B5252825 : Blo 726324 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B1091339 : Blo 726324 1091339 := bstep (se 1 (by rfl) ⟨818504, by rfl⟩ : syracuseStep 1091339 = 1637009) B1637009
theorem B1091351 : Blo 726324 1091351 := bstep (se 1 (by rfl) ⟨818513, by rfl⟩ : syracuseStep 1091351 = 1637027) B1637027
theorem B1091417 : Blo 726324 1091417 := bstep (se 2 (by rfl) ⟨409281, by rfl⟩ : syracuseStep 1091417 = 818563) B818563
theorem B2959255 : Blo 726324 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B1386391 : Blo 726324 1386391 := bstep (se 1 (by rfl) ⟨1039793, by rfl⟩ : syracuseStep 1386391 = 2079587) B2079587
theorem B1091531 : Blo 726324 1091531 := bstep (se 1 (by rfl) ⟨818648, by rfl⟩ : syracuseStep 1091531 = 1637297) B1637297
theorem B1091543 : Blo 726324 1091543 := bstep (se 1 (by rfl) ⟨818657, by rfl⟩ : syracuseStep 1091543 = 1637315) B1637315
theorem B1091609 : Blo 726324 1091609 := bstep (se 2 (by rfl) ⟨409353, by rfl⟩ : syracuseStep 1091609 = 818707) B818707
theorem B1091723 : Blo 726324 1091723 := bstep (se 1 (by rfl) ⟨818792, by rfl⟩ : syracuseStep 1091723 = 1637585) B1637585
theorem B1091735 : Blo 726324 1091735 := bstep (se 1 (by rfl) ⟨818801, by rfl⟩ : syracuseStep 1091735 = 1637603) B1637603
theorem B1091801 : Blo 726324 1091801 := bstep (se 2 (by rfl) ⟨409425, by rfl⟩ : syracuseStep 1091801 = 818851) B818851
theorem B2763031 : Blo 726324 2763031 := bstep (se 1 (by rfl) ⟨2072273, by rfl⟩ : syracuseStep 2763031 = 4144547) B4144547
theorem B1091915 : Blo 726324 1091915 := bstep (se 1 (by rfl) ⟨818936, by rfl⟩ : syracuseStep 1091915 = 1637873) B1637873
theorem B1091927 : Blo 726324 1091927 := bstep (se 1 (by rfl) ⟨818945, by rfl⟩ : syracuseStep 1091927 = 1637891) B1637891
theorem B5515613 : Blo 726324 5515613 := bstep (se 3 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 5515613 = 2068355) B2068355
theorem B1091993 : Blo 726324 1091993 := bstep (se 2 (by rfl) ⟨409497, by rfl⟩ : syracuseStep 1091993 = 818995) B818995
theorem B1092107 : Blo 726324 1092107 := bstep (se 1 (by rfl) ⟨819080, by rfl⟩ : syracuseStep 1092107 = 1638161) B1638161
theorem B1092119 : Blo 726324 1092119 := bstep (se 1 (by rfl) ⟨819089, by rfl⟩ : syracuseStep 1092119 = 1638179) B1638179
theorem B1092185 : Blo 726324 1092185 := bstep (se 2 (by rfl) ⟨409569, by rfl⟩ : syracuseStep 1092185 = 819139) B819139
theorem B2992733 : Blo 726324 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B1092299 : Blo 726324 1092299 := bstep (se 1 (by rfl) ⟨819224, by rfl⟩ : syracuseStep 1092299 = 1638449) B1638449
theorem B1092311 : Blo 726324 1092311 := bstep (se 1 (by rfl) ⟨819233, by rfl⟩ : syracuseStep 1092311 = 1638467) B1638467
theorem B1092377 : Blo 726324 1092377 := bstep (se 2 (by rfl) ⟨409641, by rfl⟩ : syracuseStep 1092377 = 819283) B819283
theorem B1846091 : Blo 726324 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B1092491 : Blo 726324 1092491 := bstep (se 1 (by rfl) ⟨819368, by rfl⟩ : syracuseStep 1092491 = 1638737) B1638737
theorem B1092503 : Blo 726324 1092503 := bstep (se 1 (by rfl) ⟨819377, by rfl⟩ : syracuseStep 1092503 = 1638755) B1638755
theorem B1092569 : Blo 726324 1092569 := bstep (se 2 (by rfl) ⟨409713, by rfl⟩ : syracuseStep 1092569 = 819427) B819427
theorem B2763821 : Blo 726324 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B830539 : Blo 726324 830539 := bstep (se 1 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 830539 = 1245809) B1245809
theorem B1092683 : Blo 726324 1092683 := bstep (se 1 (by rfl) ⟨819512, by rfl⟩ : syracuseStep 1092683 = 1639025) B1639025
theorem B1092695 : Blo 726324 1092695 := bstep (se 1 (by rfl) ⟨819521, by rfl⟩ : syracuseStep 1092695 = 1639043) B1639043
theorem B1092761 : Blo 726324 1092761 := bstep (se 2 (by rfl) ⟨409785, by rfl⟩ : syracuseStep 1092761 = 819571) B819571
theorem B1682635 : Blo 726324 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B1551575 : Blo 726324 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B1092875 : Blo 726324 1092875 := bstep (se 1 (by rfl) ⟨819656, by rfl⟩ : syracuseStep 1092875 = 1639313) B1639313
theorem B1092887 : Blo 726324 1092887 := bstep (se 1 (by rfl) ⟨819665, by rfl⟩ : syracuseStep 1092887 = 1639331) B1639331
theorem B3681611 : Blo 726324 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B1092953 : Blo 726324 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B1551745 : Blo 726324 1551745 := bstep (se 2 (by rfl) ⟨581904, by rfl⟩ : syracuseStep 1551745 = 1163809) B1163809
theorem B2960813 : Blo 726324 2960813 := bstep (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) B1110305
theorem B1093067 : Blo 726324 1093067 := bstep (se 1 (by rfl) ⟨819800, by rfl⟩ : syracuseStep 1093067 = 1639601) B1639601
theorem B1093079 : Blo 726324 1093079 := bstep (se 1 (by rfl) ⟨819809, by rfl⟩ : syracuseStep 1093079 = 1639619) B1639619
theorem B1093145 : Blo 726324 1093145 := bstep (se 2 (by rfl) ⟨409929, by rfl⟩ : syracuseStep 1093145 = 819859) B819859
theorem B1093259 : Blo 726324 1093259 := bstep (se 1 (by rfl) ⟨819944, by rfl⟩ : syracuseStep 1093259 = 1639889) B1639889
theorem B1093271 : Blo 726324 1093271 := bstep (se 1 (by rfl) ⟨819953, by rfl⟩ : syracuseStep 1093271 = 1639907) B1639907
theorem B1093337 : Blo 726324 1093337 := bstep (se 2 (by rfl) ⟨410001, by rfl⟩ : syracuseStep 1093337 = 820003) B820003
theorem B1847063 : Blo 726324 1847063 := bstep (se 1 (by rfl) ⟨1385297, by rfl⟩ : syracuseStep 1847063 = 2770595) B2770595
theorem B1093451 : Blo 726324 1093451 := bstep (se 1 (by rfl) ⟨820088, by rfl⟩ : syracuseStep 1093451 = 1640177) B1640177
theorem B1093463 : Blo 726324 1093463 := bstep (se 1 (by rfl) ⟨820097, by rfl⟩ : syracuseStep 1093463 = 1640195) B1640195
theorem B1093529 : Blo 726324 1093529 := bstep (se 2 (by rfl) ⟨410073, by rfl⟩ : syracuseStep 1093529 = 820147) B820147
theorem B2076637 : Blo 726324 2076637 := bstep (se 3 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 2076637 = 778739) B778739
theorem B1093643 : Blo 726324 1093643 := bstep (se 1 (by rfl) ⟨820232, by rfl⟩ : syracuseStep 1093643 = 1640465) B1640465
theorem B1093655 : Blo 726324 1093655 := bstep (se 1 (by rfl) ⟨820241, by rfl⟩ : syracuseStep 1093655 = 1640483) B1640483
theorem B1093721 : Blo 726324 1093721 := bstep (se 2 (by rfl) ⟨410145, by rfl⟩ : syracuseStep 1093721 = 820291) B820291
theorem B1093835 : Blo 726324 1093835 := bstep (se 1 (by rfl) ⟨820376, by rfl⟩ : syracuseStep 1093835 = 1640753) B1640753
theorem B1093847 : Blo 726324 1093847 := bstep (se 1 (by rfl) ⟨820385, by rfl⟩ : syracuseStep 1093847 = 1640771) B1640771
theorem B1093913 : Blo 726324 1093913 := bstep (se 2 (by rfl) ⟨410217, by rfl⟩ : syracuseStep 1093913 = 820435) B820435
theorem B1094027 : Blo 726324 1094027 := bstep (se 1 (by rfl) ⟨820520, by rfl⟩ : syracuseStep 1094027 = 1641041) B1641041
theorem B1094039 : Blo 726324 1094039 := bstep (se 1 (by rfl) ⟨820529, by rfl⟩ : syracuseStep 1094039 = 1641059) B1641059
theorem B2240947 : Blo 726324 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1847731 : Blo 726324 1847731 := bstep (se 1 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 1847731 = 2771597) B2771597
theorem B2765249 : Blo 726324 2765249 := bstep (se 2 (by rfl) ⟨1036968, by rfl⟩ : syracuseStep 2765249 = 2073937) B2073937
theorem B1094105 : Blo 726324 1094105 := bstep (se 2 (by rfl) ⟨410289, by rfl⟩ : syracuseStep 1094105 = 820579) B820579
theorem B2339293 : Blo 726324 2339293 := bstep (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) B877235
theorem B1552907 : Blo 726324 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1847873 : Blo 726324 1847873 := bstep (se 2 (by rfl) ⟨692952, by rfl⟩ : syracuseStep 1847873 = 1385905) B1385905
theorem B1094219 : Blo 726324 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B1094231 : Blo 726324 1094231 := bstep (se 1 (by rfl) ⟨820673, by rfl⟩ : syracuseStep 1094231 = 1641347) B1641347
theorem B1094297 : Blo 726324 1094297 := bstep (se 2 (by rfl) ⟨410361, by rfl⟩ : syracuseStep 1094297 = 820723) B820723
theorem B8303309 : Blo 726324 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B1094411 : Blo 726324 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B1094423 : Blo 726324 1094423 := bstep (se 1 (by rfl) ⟨820817, by rfl⟩ : syracuseStep 1094423 = 1641635) B1641635
theorem B1422155 : Blo 726324 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1094489 : Blo 726324 1094489 := bstep (se 2 (by rfl) ⟨410433, by rfl⟩ : syracuseStep 1094489 = 820867) B820867
theorem B5256029 : Blo 726324 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B2339777 : Blo 726324 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B1094603 : Blo 726324 1094603 := bstep (se 1 (by rfl) ⟨820952, by rfl⟩ : syracuseStep 1094603 = 1641905) B1641905
theorem B1094615 : Blo 726324 1094615 := bstep (se 1 (by rfl) ⟨820961, by rfl⟩ : syracuseStep 1094615 = 1641923) B1641923
theorem B1225739 : Blo 726324 1225739 := bstep (se 1 (by rfl) ⟨919304, by rfl⟩ : syracuseStep 1225739 = 1838609) B1838609
theorem B1094681 : Blo 726324 1094681 := bstep (se 2 (by rfl) ⟨410505, by rfl⟩ : syracuseStep 1094681 = 821011) B821011
theorem B3683393 : Blo 726324 3683393 := bstep (se 2 (by rfl) ⟨1381272, by rfl⟩ : syracuseStep 3683393 = 2762545) B2762545
theorem B1225867 : Blo 726324 1225867 := bstep (se 1 (by rfl) ⟨919400, by rfl⟩ : syracuseStep 1225867 = 1838801) B1838801
theorem B1094795 : Blo 726324 1094795 := bstep (se 1 (by rfl) ⟨821096, by rfl⟩ : syracuseStep 1094795 = 1642193) B1642193
theorem B1094807 : Blo 726324 1094807 := bstep (se 1 (by rfl) ⟨821105, by rfl⟩ : syracuseStep 1094807 = 1642211) B1642211
theorem B2077913 : Blo 726324 2077913 := bstep (se 2 (by rfl) ⟨779217, by rfl⟩ : syracuseStep 2077913 = 1558435) B1558435
theorem B1094873 : Blo 726324 1094873 := bstep (se 2 (by rfl) ⟨410577, by rfl⟩ : syracuseStep 1094873 = 821155) B821155
theorem B11810033 : Blo 726324 11810033 := bstep (se 2 (by rfl) ⟨4428762, by rfl⟩ : syracuseStep 11810033 = 8857525) B8857525
theorem B1553651 : Blo 726324 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1226009 : Blo 726324 1226009 := bstep (se 2 (by rfl) ⟨459753, by rfl⟩ : syracuseStep 1226009 = 919507) B919507
theorem B1094987 : Blo 726324 1094987 := bstep (se 1 (by rfl) ⟨821240, by rfl⟩ : syracuseStep 1094987 = 1642481) B1642481
theorem B1094999 : Blo 726324 1094999 := bstep (se 1 (by rfl) ⟨821249, by rfl⟩ : syracuseStep 1094999 = 1642499) B1642499
theorem B1226137 : Blo 726324 1226137 := bstep (se 2 (by rfl) ⟨459801, by rfl⟩ : syracuseStep 1226137 = 919603) B919603
theorem B1095065 : Blo 726324 1095065 := bstep (se 2 (by rfl) ⟨410649, by rfl⟩ : syracuseStep 1095065 = 821299) B821299
theorem B1095179 : Blo 726324 1095179 := bstep (se 1 (by rfl) ⟨821384, by rfl⟩ : syracuseStep 1095179 = 1642769) B1642769
theorem B1095191 : Blo 726324 1095191 := bstep (se 1 (by rfl) ⟨821393, by rfl⟩ : syracuseStep 1095191 = 1642787) B1642787
theorem B1095257 : Blo 726324 1095257 := bstep (se 2 (by rfl) ⟨410721, by rfl⟩ : syracuseStep 1095257 = 821443) B821443
theorem B4142771 : Blo 726324 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B1095371 : Blo 726324 1095371 := bstep (se 1 (by rfl) ⟨821528, by rfl⟩ : syracuseStep 1095371 = 1643057) B1643057
theorem B1095383 : Blo 726324 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B1095449 : Blo 726324 1095449 := bstep (se 2 (by rfl) ⟨410793, by rfl⟩ : syracuseStep 1095449 = 821587) B821587
theorem B2766737 : Blo 726324 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B1226711 : Blo 726324 1226711 := bstep (se 1 (by rfl) ⟨920033, by rfl⟩ : syracuseStep 1226711 = 1840067) B1840067
theorem B1226839 : Blo 726324 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B1554547 : Blo 726324 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B2767193 : Blo 726324 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B2767405 : Blo 726324 2767405 := bstep (se 3 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 2767405 = 1037777) B1037777
theorem B14006915 : Blo 726324 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B1227467 : Blo 726324 1227467 := bstep (se 1 (by rfl) ⟨920600, by rfl⟩ : syracuseStep 1227467 = 1841201) B1841201
theorem B2079553 : Blo 726324 2079553 := bstep (se 2 (by rfl) ⟨779832, by rfl⟩ : syracuseStep 2079553 = 1559665) B1559665
theorem B1227595 : Blo 726324 1227595 := bstep (se 1 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 1227595 = 1841393) B1841393
theorem B2767709 : Blo 726324 2767709 := bstep (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) B1037891
theorem B1227737 : Blo 726324 1227737 := bstep (se 2 (by rfl) ⟨460401, by rfl⟩ : syracuseStep 1227737 = 920803) B920803
theorem B3685337 : Blo 726324 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B4668461 : Blo 726324 4668461 := bstep (se 3 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 4668461 = 1750673) B1750673
theorem B1227865 : Blo 726324 1227865 := bstep (se 2 (by rfl) ⟨460449, by rfl⟩ : syracuseStep 1227865 = 920899) B920899
theorem B4144229 : Blo 726324 4144229 := bstep (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) B777043
theorem B1555607 : Blo 726324 1555607 := bstep (se 1 (by rfl) ⟨1166705, by rfl⟩ : syracuseStep 1555607 = 2333411) B2333411
theorem B16792757 : Blo 726324 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B4209965 : Blo 726324 4209965 := bstep (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) B1578737
theorem B1555777 : Blo 726324 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B2801099 : Blo 726324 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B999001 : Blo 726324 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B1228439 : Blo 726324 1228439 := bstep (se 1 (by rfl) ⟨921329, by rfl⟩ : syracuseStep 1228439 = 1842659) B1842659
theorem B1556119 : Blo 726324 1556119 := bstep (se 1 (by rfl) ⟨1167089, by rfl⟩ : syracuseStep 1556119 = 2334179) B2334179
theorem B1752779 : Blo 726324 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1228567 : Blo 726324 1228567 := bstep (se 1 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 1228567 = 1842851) B1842851
theorem B3325789 : Blo 726324 3325789 := bstep (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) B1247171
theorem B1229195 : Blo 726324 1229195 := bstep (se 1 (by rfl) ⟨921896, by rfl⟩ : syracuseStep 1229195 = 1843793) B1843793
theorem B1556939 : Blo 726324 1556939 := bstep (se 1 (by rfl) ⟨1167704, by rfl⟩ : syracuseStep 1556939 = 2335409) B2335409
theorem B1229323 : Blo 726324 1229323 := bstep (se 1 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 1229323 = 1843985) B1843985
theorem B3686957 : Blo 726324 3686957 := bstep (se 3 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 3686957 = 1382609) B1382609
theorem B14959235 : Blo 726324 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1229465 : Blo 726324 1229465 := bstep (se 2 (by rfl) ⟨461049, by rfl⟩ : syracuseStep 1229465 = 922099) B922099
theorem B1229593 : Blo 726324 1229593 := bstep (se 2 (by rfl) ⟨461097, by rfl⟩ : syracuseStep 1229593 = 922195) B922195
theorem B1557299 : Blo 726324 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B4310117 : Blo 726324 4310117 := bstep (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) B808147
theorem B1230167 : Blo 726324 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B2770307 : Blo 726324 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B2770321 : Blo 726324 2770321 := bstep (se 2 (by rfl) ⟨1038870, by rfl⟩ : syracuseStep 2770321 = 2077741) B2077741
theorem B1230295 : Blo 726324 1230295 := bstep (se 1 (by rfl) ⟨922721, by rfl⟩ : syracuseStep 1230295 = 1845443) B1845443
theorem B8275607 : Blo 726324 8275607 := bstep (se 1 (by rfl) ⟨6206705, by rfl⟩ : syracuseStep 8275607 = 12413411) B12413411
theorem B2770625 : Blo 726324 2770625 := bstep (se 2 (by rfl) ⟨1038984, by rfl⟩ : syracuseStep 2770625 = 2077969) B2077969
theorem B1230923 : Blo 726324 1230923 := bstep (se 1 (by rfl) ⟨923192, by rfl⟩ : syracuseStep 1230923 = 1846385) B1846385
theorem B1231051 : Blo 726324 1231051 := bstep (se 1 (by rfl) ⟨923288, by rfl⟩ : syracuseStep 1231051 = 1846577) B1846577
theorem B739531 : Blo 726324 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B2804057 : Blo 726324 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B1231193 : Blo 726324 1231193 := bstep (se 2 (by rfl) ⟨461697, by rfl⟩ : syracuseStep 1231193 = 923395) B923395
theorem B2771293 : Blo 726324 2771293 := bstep (se 3 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 2771293 = 1039235) B1039235
theorem B3361169 : Blo 726324 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1231321 : Blo 726324 1231321 := bstep (se 2 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 1231321 = 923491) B923491
theorem B4672151 : Blo 726324 4672151 := bstep (se 1 (by rfl) ⟨3504113, by rfl⟩ : syracuseStep 4672151 = 7008227) B7008227
theorem B1559297 : Blo 726324 1559297 := bstep (se 2 (by rfl) ⟨584736, by rfl⟩ : syracuseStep 1559297 = 1169473) B1169473
theorem B1166167 : Blo 726324 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B22465457 : Blo 726324 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B1231895 : Blo 726324 1231895 := bstep (se 1 (by rfl) ⟨923921, by rfl⟩ : syracuseStep 1231895 = 1847843) B1847843
theorem B1494131 : Blo 726324 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B1232023 : Blo 726324 1232023 := bstep (se 1 (by rfl) ⟨924017, by rfl⟩ : syracuseStep 1232023 = 1848035) B1848035
theorem B3493043 : Blo 726324 3493043 := bstep (se 1 (by rfl) ⟨2619782, by rfl⟩ : syracuseStep 3493043 = 5239565) B5239565
theorem B5262515 : Blo 726324 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B2772569 : Blo 726324 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B1166987 : Blo 726324 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B6639425 : Blo 726324 6639425 := bstep (se 2 (by rfl) ⟨2489784, by rfl⟩ : syracuseStep 6639425 = 4979569) B4979569
theorem B1200025 : Blo 726324 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B9359491 : Blo 726324 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B1036633 : Blo 726324 1036633 := bstep (se 2 (by rfl) ⟨388737, by rfl⟩ : syracuseStep 1036633 = 777475) B777475
theorem B2216281 : Blo 726324 2216281 := bstep (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) B1662211
theorem B3690845 : Blo 726324 3690845 := bstep (se 3 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 3690845 = 1384067) B1384067
theorem B1167833 : Blo 726324 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B1167961 : Blo 726324 1167961 := bstep (se 2 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 1167961 = 875971) B875971
theorem B1168025 : Blo 726324 1168025 := bstep (se 2 (by rfl) ⟨438009, by rfl⟩ : syracuseStep 1168025 = 876019) B876019
theorem B4150061 : Blo 726324 4150061 := bstep (se 3 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 4150061 = 1556273) B1556273
theorem B1397963 : Blo 726324 1397963 := bstep (se 1 (by rfl) ⟨1048472, by rfl⟩ : syracuseStep 1397963 = 2096945) B2096945
theorem B1038091 : Blo 726324 1038091 := bstep (se 1 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 1038091 = 1557137) B1557137
theorem B1496983 : Blo 726324 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B4675715 : Blo 726324 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B3692951 : Blo 726324 3692951 := bstep (se 1 (by rfl) ⟨2769713, by rfl⟩ : syracuseStep 3692951 = 5539427) B5539427
theorem B874967 : Blo 726324 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B17717777 : Blo 726324 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B10476125 : Blo 726324 10476125 := bstep (se 3 (by rfl) ⟨1964273, by rfl⟩ : syracuseStep 10476125 = 3928547) B3928547
theorem B1039321 : Blo 726324 1039321 := bstep (se 2 (by rfl) ⟨389745, by rfl⟩ : syracuseStep 1039321 = 779491) B779491
theorem B777547 : Blo 726324 777547 := bstep (se 1 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 777547 = 1166321) B1166321
theorem B3497347 : Blo 726324 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B3104173 : Blo 726324 3104173 := bstep (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) B1164065
theorem B1498583 : Blo 726324 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B1105483 : Blo 726324 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B3104345 : Blo 726324 3104345 := bstep (se 2 (by rfl) ⟨1164129, by rfl⟩ : syracuseStep 3104345 = 2328259) B2328259
theorem B778295 : Blo 726324 778295 := bstep (se 1 (by rfl) ⟨583721, by rfl⟩ : syracuseStep 778295 = 1167443) B1167443
theorem B11952197 : Blo 726324 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B8314973 : Blo 726324 8314973 := bstep (se 3 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 8314973 = 3118115) B3118115
theorem B909515 : Blo 726324 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B4153751 : Blo 726324 4153751 := bstep (se 1 (by rfl) ⟨3115313, by rfl⟩ : syracuseStep 4153751 = 6230627) B6230627
theorem B1401367 : Blo 726324 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B6218531 : Blo 726324 6218531 := bstep (se 1 (by rfl) ⟨4663898, by rfl⟩ : syracuseStep 6218531 = 9327797) B9327797
theorem B33547061 : Blo 726324 33547061 := bstep (se 5 (by rfl) ⟨1572518, by rfl⟩ : syracuseStep 33547061 = 3145037) B3145037
theorem B5235587 : Blo 726324 5235587 := bstep (se 1 (by rfl) ⟨3926690, by rfl⟩ : syracuseStep 5235587 = 7853381) B7853381
theorem B26240021 : Blo 726324 26240021 := bstep (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) B1230001
theorem B1500211 : Blo 726324 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B3105985 : Blo 726324 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B779563 : Blo 726324 779563 := bstep (se 1 (by rfl) ⟨584672, by rfl⟩ : syracuseStep 779563 = 1169345) B1169345
theorem B31450517 : Blo 726324 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B6219281 : Blo 726324 6219281 := bstep (se 2 (by rfl) ⟨2332230, by rfl⟩ : syracuseStep 6219281 = 4664461) B4664461
theorem B1795649 : Blo 726324 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B1664729 : Blo 726324 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B5891915 : Blo 726324 5891915 := bstep (se 1 (by rfl) ⟨4418936, by rfl⟩ : syracuseStep 5891915 = 8837873) B8837873
theorem B3696515 : Blo 726324 3696515 := bstep (se 1 (by rfl) ⟨2772386, by rfl⟩ : syracuseStep 3696515 = 5544773) B5544773
theorem B5335085 : Blo 726324 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B2451545 : Blo 726324 2451545 := bstep (se 2 (by rfl) ⟨919329, by rfl⟩ : syracuseStep 2451545 = 1838659) B1838659
theorem B19982861 : Blo 726324 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B2452247 : Blo 726324 2452247 := bstep (se 1 (by rfl) ⟨1839185, by rfl⟩ : syracuseStep 2452247 = 3678371) B3678371
theorem B3107659 : Blo 726324 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B3107933 : Blo 726324 3107933 := bstep (se 3 (by rfl) ⟨582737, by rfl⟩ : syracuseStep 3107933 = 1165475) B1165475
theorem B2452787 : Blo 726324 2452787 := bstep (se 1 (by rfl) ⟨1839590, by rfl⟩ : syracuseStep 2452787 = 3679181) B3679181
theorem B2453057 : Blo 726324 2453057 := bstep (se 2 (by rfl) ⟨919896, by rfl⟩ : syracuseStep 2453057 = 1839793) B1839793
theorem B1404631 : Blo 726324 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1634291 : Blo 726324 1634291 := bstep (se 1 (by rfl) ⟨1225718, by rfl⟩ : syracuseStep 1634291 = 2451437) B2451437
theorem B1634327 : Blo 726324 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B2453597 : Blo 726324 2453597 := bstep (se 3 (by rfl) ⟨460049, by rfl⟩ : syracuseStep 2453597 = 920099) B920099
theorem B1634507 : Blo 726324 1634507 := bstep (se 1 (by rfl) ⟨1225880, by rfl⟩ : syracuseStep 1634507 = 2451761) B2451761
theorem B1634561 : Blo 726324 1634561 := bstep (se 2 (by rfl) ⟨612960, by rfl⟩ : syracuseStep 1634561 = 1225921) B1225921
theorem B6222257 : Blo 726324 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B1634777 : Blo 726324 1634777 := bstep (se 2 (by rfl) ⟨613041, by rfl⟩ : syracuseStep 1634777 = 1226083) B1226083
theorem B1634867 : Blo 726324 1634867 := bstep (se 1 (by rfl) ⟨1226150, by rfl⟩ : syracuseStep 1634867 = 2452301) B2452301
theorem B1634903 : Blo 726324 1634903 := bstep (se 1 (by rfl) ⟨1226177, by rfl⟩ : syracuseStep 1634903 = 2452355) B2452355
theorem B1635083 : Blo 726324 1635083 := bstep (se 1 (by rfl) ⟨1226312, by rfl⟩ : syracuseStep 1635083 = 2452625) B2452625
theorem B1078039 : Blo 726324 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B1635137 : Blo 726324 1635137 := bstep (se 2 (by rfl) ⟨613176, by rfl⟩ : syracuseStep 1635137 = 1226353) B1226353
theorem B10482533 : Blo 726324 10482533 := bstep (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) B1965475
theorem B1635353 : Blo 726324 1635353 := bstep (se 2 (by rfl) ⟨613257, by rfl⟩ : syracuseStep 1635353 = 1226515) B1226515
theorem B11990051 : Blo 726324 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B1635443 : Blo 726324 1635443 := bstep (se 1 (by rfl) ⟨1226582, by rfl⟩ : syracuseStep 1635443 = 2453165) B2453165
theorem B1635479 : Blo 726324 1635479 := bstep (se 1 (by rfl) ⟨1226609, by rfl⟩ : syracuseStep 1635479 = 2453219) B2453219
theorem B2454731 : Blo 726324 2454731 := bstep (se 1 (by rfl) ⟨1841048, by rfl⟩ : syracuseStep 2454731 = 3682097) B3682097
theorem B1635659 : Blo 726324 1635659 := bstep (se 1 (by rfl) ⟨1226744, by rfl⟩ : syracuseStep 1635659 = 2453489) B2453489
theorem B1635713 : Blo 726324 1635713 := bstep (se 2 (by rfl) ⟨613392, by rfl⟩ : syracuseStep 1635713 = 1226785) B1226785
theorem B2455001 : Blo 726324 2455001 := bstep (se 2 (by rfl) ⟨920625, by rfl⟩ : syracuseStep 2455001 = 1841251) B1841251
theorem B1635929 : Blo 726324 1635929 := bstep (se 2 (by rfl) ⟨613473, by rfl⟩ : syracuseStep 1635929 = 1226947) B1226947
theorem B4159127 : Blo 726324 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B1636019 : Blo 726324 1636019 := bstep (se 1 (by rfl) ⟨1227014, by rfl⟩ : syracuseStep 1636019 = 2454029) B2454029
theorem B1636055 : Blo 726324 1636055 := bstep (se 1 (by rfl) ⟨1227041, by rfl⟩ : syracuseStep 1636055 = 2454083) B2454083
theorem B1636235 : Blo 726324 1636235 := bstep (se 1 (by rfl) ⟨1227176, by rfl⟩ : syracuseStep 1636235 = 2454353) B2454353
theorem B7010225 : Blo 726324 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B1636289 : Blo 726324 1636289 := bstep (se 2 (by rfl) ⟨613608, by rfl⟩ : syracuseStep 1636289 = 1227217) B1227217
theorem B817195 : Blo 726324 817195 := bstep (se 1 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 817195 = 1225793) B1225793
theorem B817303 : Blo 726324 817303 := bstep (se 1 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 817303 = 1225955) B1225955
theorem B2455703 : Blo 726324 2455703 := bstep (se 1 (by rfl) ⟨1841777, by rfl⟩ : syracuseStep 2455703 = 3683555) B3683555
theorem B1636505 : Blo 726324 1636505 := bstep (se 2 (by rfl) ⟨613689, by rfl⟩ : syracuseStep 1636505 = 1227379) B1227379
theorem B1636595 : Blo 726324 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B1866007 : Blo 726324 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B1636631 : Blo 726324 1636631 := bstep (se 1 (by rfl) ⟨1227473, by rfl⟩ : syracuseStep 1636631 = 2454947) B2454947
theorem B11794733 : Blo 726324 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B817483 : Blo 726324 817483 := bstep (se 1 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 817483 = 1226225) B1226225
theorem B817591 : Blo 726324 817591 := bstep (se 1 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 817591 = 1226387) B1226387
theorem B1636811 : Blo 726324 1636811 := bstep (se 1 (by rfl) ⟨1227608, by rfl⟩ : syracuseStep 1636811 = 2455217) B2455217
theorem B8288729 : Blo 726324 8288729 := bstep (se 2 (by rfl) ⟨3108273, by rfl⟩ : syracuseStep 8288729 = 6216547) B6216547
theorem B1636865 : Blo 726324 1636865 := bstep (se 2 (by rfl) ⟨613824, by rfl⟩ : syracuseStep 1636865 = 1227649) B1227649
theorem B817771 : Blo 726324 817771 := bstep (se 1 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 817771 = 1226657) B1226657
theorem B2456243 : Blo 726324 2456243 := bstep (se 1 (by rfl) ⟨1842182, by rfl⟩ : syracuseStep 2456243 = 3684365) B3684365
theorem B817879 : Blo 726324 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B1637081 : Blo 726324 1637081 := bstep (se 2 (by rfl) ⟨613905, by rfl⟩ : syracuseStep 1637081 = 1227811) B1227811
theorem B3504941 : Blo 726324 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B1637171 : Blo 726324 1637171 := bstep (se 1 (by rfl) ⟨1227878, by rfl⟩ : syracuseStep 1637171 = 2455757) B2455757
theorem B1637207 : Blo 726324 1637207 := bstep (se 1 (by rfl) ⟨1227905, by rfl⟩ : syracuseStep 1637207 = 2455811) B2455811
theorem B6749021 : Blo 726324 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B818059 : Blo 726324 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B2456513 : Blo 726324 2456513 := bstep (se 2 (by rfl) ⟨921192, by rfl⟩ : syracuseStep 2456513 = 1842385) B1842385
theorem B1244107 : Blo 726324 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B818167 : Blo 726324 818167 := bstep (se 1 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 818167 = 1227251) B1227251
theorem B1637387 : Blo 726324 1637387 := bstep (se 1 (by rfl) ⟨1228040, by rfl⟩ : syracuseStep 1637387 = 2456081) B2456081
theorem B1637441 : Blo 726324 1637441 := bstep (se 2 (by rfl) ⟨614040, by rfl⟩ : syracuseStep 1637441 = 1228081) B1228081
theorem B1473611 : Blo 726324 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B818347 : Blo 726324 818347 := bstep (se 1 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 818347 = 1227521) B1227521
theorem B818455 : Blo 726324 818455 := bstep (se 1 (by rfl) ⟨613841, by rfl⟩ : syracuseStep 818455 = 1227683) B1227683
theorem B1244441 : Blo 726324 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B1637657 : Blo 726324 1637657 := bstep (se 2 (by rfl) ⟨614121, by rfl⟩ : syracuseStep 1637657 = 1228243) B1228243
theorem B1637747 : Blo 726324 1637747 := bstep (se 1 (by rfl) ⟨1228310, by rfl⟩ : syracuseStep 1637747 = 2456621) B2456621
theorem B1637783 : Blo 726324 1637783 := bstep (se 1 (by rfl) ⟨1228337, by rfl⟩ : syracuseStep 1637783 = 2456675) B2456675
theorem B818635 : Blo 726324 818635 := bstep (se 1 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 818635 = 1227953) B1227953
theorem B2457053 : Blo 726324 2457053 := bstep (se 3 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 2457053 = 921395) B921395
theorem B818743 : Blo 726324 818743 := bstep (se 1 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 818743 = 1228115) B1228115
theorem B1637963 : Blo 726324 1637963 := bstep (se 1 (by rfl) ⟨1228472, by rfl⟩ : syracuseStep 1637963 = 2456945) B2456945
theorem B1638017 : Blo 726324 1638017 := bstep (se 2 (by rfl) ⟨614256, by rfl⟩ : syracuseStep 1638017 = 1228513) B1228513
theorem B1244825 : Blo 726324 1244825 := bstep (se 2 (by rfl) ⟨466809, by rfl⟩ : syracuseStep 1244825 = 933619) B933619
theorem B818923 : Blo 726324 818923 := bstep (se 1 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 818923 = 1228385) B1228385
theorem B7470913 : Blo 726324 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B3112769 : Blo 726324 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B819031 : Blo 726324 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B1638233 : Blo 726324 1638233 := bstep (se 2 (by rfl) ⟨614337, by rfl⟩ : syracuseStep 1638233 = 1228675) B1228675
theorem B1965917 : Blo 726324 1965917 := bstep (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) B737219
theorem B982937 : Blo 726324 982937 := bstep (se 2 (by rfl) ⟨368601, by rfl⟩ : syracuseStep 982937 = 737203) B737203
theorem B1638323 : Blo 726324 1638323 := bstep (se 1 (by rfl) ⟨1228742, by rfl⟩ : syracuseStep 1638323 = 2457485) B2457485
theorem B1638359 : Blo 726324 1638359 := bstep (se 1 (by rfl) ⟨1228769, by rfl⟩ : syracuseStep 1638359 = 2457539) B2457539
theorem B3112921 : Blo 726324 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1966265 : Blo 726324 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B819463 : Blo 726324 819463 := bstep (se 1 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 819463 = 1229195) B1229195
theorem B2457971 : Blo 726324 2457971 := bstep (se 1 (by rfl) ⟨1843478, by rfl⟩ : syracuseStep 2457971 = 3686957) B3686957
theorem B2359687 : Blo 726324 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B1638791 : Blo 726324 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B819643 : Blo 726324 819643 := bstep (se 1 (by rfl) ⟨614732, by rfl⟩ : syracuseStep 819643 = 1229465) B1229465
theorem B2425373 : Blo 726324 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B1311275 : Blo 726324 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B1638971 : Blo 726324 1638971 := bstep (se 1 (by rfl) ⟨1229228, by rfl⟩ : syracuseStep 1638971 = 2458457) B2458457
theorem B1639097 : Blo 726324 1639097 := bstep (se 2 (by rfl) ⟨614661, by rfl⟩ : syracuseStep 1639097 = 1229323) B1229323
theorem B1868489 : Blo 726324 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B15958745 : Blo 726324 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B820111 : Blo 726324 820111 := bstep (se 1 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 820111 = 1230167) B1230167
theorem B1639439 : Blo 726324 1639439 := bstep (se 1 (by rfl) ⟨1229579, by rfl⟩ : syracuseStep 1639439 = 2459159) B2459159
theorem B1639457 : Blo 726324 1639457 := bstep (se 2 (by rfl) ⟨614796, by rfl⟩ : syracuseStep 1639457 = 1229593) B1229593
theorem B3507401 : Blo 726324 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B1639799 : Blo 726324 1639799 := bstep (se 1 (by rfl) ⟨1229849, by rfl⟩ : syracuseStep 1639799 = 2459699) B2459699
theorem B820615 : Blo 726324 820615 := bstep (se 1 (by rfl) ⟨615461, by rfl⟩ : syracuseStep 820615 = 1230923) B1230923
theorem B3114425 : Blo 726324 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B1639979 : Blo 726324 1639979 := bstep (se 1 (by rfl) ⟨1229984, by rfl⟩ : syracuseStep 1639979 = 2459969) B2459969
theorem B1869371 : Blo 726324 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B820795 : Blo 726324 820795 := bstep (se 1 (by rfl) ⟨615596, by rfl⟩ : syracuseStep 820795 = 1231193) B1231193
theorem B4195901 : Blo 726324 4195901 := bstep (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) B1573463
theorem B3114733 : Blo 726324 3114733 := bstep (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) B1168025
theorem B3114767 : Blo 726324 3114767 := bstep (se 1 (by rfl) ⟨2336075, by rfl⟩ : syracuseStep 3114767 = 4672151) B4672151
theorem B4982579 : Blo 726324 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B1640339 : Blo 726324 1640339 := bstep (se 1 (by rfl) ⟨1230254, by rfl⟩ : syracuseStep 1640339 = 2460509) B2460509
theorem B1640393 : Blo 726324 1640393 := bstep (se 2 (by rfl) ⟨615147, by rfl⟩ : syracuseStep 1640393 = 1230295) B1230295
theorem B14976971 : Blo 726324 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B821263 : Blo 726324 821263 := bstep (se 1 (by rfl) ⟨615947, by rfl⟩ : syracuseStep 821263 = 1231895) B1231895
theorem B6228029 : Blo 726324 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B2328695 : Blo 726324 2328695 := bstep (se 1 (by rfl) ⟨1746521, by rfl⟩ : syracuseStep 2328695 = 3493043) B3493043
theorem B3508343 : Blo 726324 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B1968275 : Blo 726324 1968275 := bstep (se 1 (by rfl) ⟨1476206, by rfl⟩ : syracuseStep 1968275 = 2952413) B2952413
theorem B919927 : Blo 726324 919927 := bstep (se 1 (by rfl) ⟨689945, by rfl⟩ : syracuseStep 919927 = 1379891) B1379891
theorem B4426283 : Blo 726324 4426283 := bstep (se 1 (by rfl) ⟨3319712, by rfl⟩ : syracuseStep 4426283 = 6639425) B6639425
theorem B1641095 : Blo 726324 1641095 := bstep (se 1 (by rfl) ⟨1230821, by rfl⟩ : syracuseStep 1641095 = 2461643) B2461643
theorem B920251 : Blo 726324 920251 := bstep (se 1 (by rfl) ⟨690188, by rfl⟩ : syracuseStep 920251 = 1380377) B1380377
theorem B1641275 : Blo 726324 1641275 := bstep (se 1 (by rfl) ⟨1230956, by rfl⟩ : syracuseStep 1641275 = 2461913) B2461913
theorem B1379207 : Blo 726324 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B2460563 : Blo 726324 2460563 := bstep (se 1 (by rfl) ⟨1845422, by rfl⟩ : syracuseStep 2460563 = 3690845) B3690845
theorem B1641401 : Blo 726324 1641401 := bstep (se 2 (by rfl) ⟨615525, by rfl⟩ : syracuseStep 1641401 = 1231051) B1231051
theorem B986041 : Blo 726324 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B2624555 : Blo 726324 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B17697923 : Blo 726324 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B920747 : Blo 726324 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B4656365 : Blo 726324 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B1641743 : Blo 726324 1641743 := bstep (se 1 (by rfl) ⟨1231307, by rfl⟩ : syracuseStep 1641743 = 2462615) B2462615
theorem B1641761 : Blo 726324 1641761 := bstep (se 2 (by rfl) ⟨615660, by rfl⟩ : syracuseStep 1641761 = 1231321) B1231321
theorem B1642103 : Blo 726324 1642103 := bstep (se 1 (by rfl) ⟨1231577, by rfl⟩ : syracuseStep 1642103 = 2463155) B2463155
theorem B921223 : Blo 726324 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B1642283 : Blo 726324 1642283 := bstep (se 1 (by rfl) ⟨1231712, by rfl⟩ : syracuseStep 1642283 = 2463425) B2463425
theorem B1183547 : Blo 726324 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B1838963 : Blo 726324 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B1838983 : Blo 726324 1838983 := bstep (se 1 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 1838983 = 2758475) B2758475
theorem B3117143 : Blo 726324 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B921719 : Blo 726324 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B1642643 : Blo 726324 1642643 := bstep (se 1 (by rfl) ⟨1231982, by rfl⟩ : syracuseStep 1642643 = 2463965) B2463965
theorem B1839257 : Blo 726324 1839257 := bstep (se 2 (by rfl) ⟨689721, by rfl⟩ : syracuseStep 1839257 = 1379443) B1379443
theorem B4788397 : Blo 726324 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B1642697 : Blo 726324 1642697 := bstep (se 2 (by rfl) ⟨616011, by rfl⟩ : syracuseStep 1642697 = 1232023) B1232023
theorem B921871 : Blo 726324 921871 := bstep (se 1 (by rfl) ⟨691403, by rfl⟩ : syracuseStep 921871 = 1382807) B1382807
theorem B2461967 : Blo 726324 2461967 := bstep (se 1 (by rfl) ⟨1846475, by rfl⟩ : syracuseStep 2461967 = 3692951) B3692951
theorem B1577249 : Blo 726324 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1839419 : Blo 726324 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B6984083 : Blo 726324 6984083 := bstep (se 1 (by rfl) ⟨5238062, by rfl⟩ : syracuseStep 6984083 = 10476125) B10476125
theorem B1315219 : Blo 726324 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B922043 : Blo 726324 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B2068993 : Blo 726324 2068993 := bstep (se 2 (by rfl) ⟨775872, by rfl⟩ : syracuseStep 2068993 = 1551745) B1551745
theorem B1839631 : Blo 726324 1839631 := bstep (se 1 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 1839631 = 2759447) B2759447
theorem B2462237 : Blo 726324 2462237 := bstep (se 3 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 2462237 = 923339) B923339
theorem B3937025 : Blo 726324 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B1839905 : Blo 726324 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B2069563 : Blo 726324 2069563 := bstep (se 1 (by rfl) ⟨1552172, by rfl⟩ : syracuseStep 2069563 = 3104345) B3104345
theorem B2495777 : Blo 726324 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B726331 : Blo 726324 726331 := bstep (se 1 (by rfl) ⟨544748, by rfl⟩ : syracuseStep 726331 = 1089497) B1089497
theorem B1381691 : Blo 726324 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B7968131 : Blo 726324 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B726407 : Blo 726324 726407 := bstep (se 1 (by rfl) ⟨544805, by rfl⟩ : syracuseStep 726407 = 1089611) B1089611
theorem B923015 : Blo 726324 923015 := bstep (se 1 (by rfl) ⟨692261, by rfl⟩ : syracuseStep 923015 = 1384523) B1384523
theorem B726415 : Blo 726324 726415 := bstep (se 1 (by rfl) ⟨544811, by rfl⟩ : syracuseStep 726415 = 1089623) B1089623
theorem B5543315 : Blo 726324 5543315 := bstep (se 1 (by rfl) ⟨4157486, by rfl⟩ : syracuseStep 5543315 = 8314973) B8314973
theorem B1185209 : Blo 726324 1185209 := bstep (se 2 (by rfl) ⟨444453, by rfl⟩ : syracuseStep 1185209 = 888907) B888907
theorem B726459 : Blo 726324 726459 := bstep (se 1 (by rfl) ⟨544844, by rfl⟩ : syracuseStep 726459 = 1089689) B1089689
theorem B726535 : Blo 726324 726535 := bstep (se 1 (by rfl) ⟨544901, by rfl⟩ : syracuseStep 726535 = 1089803) B1089803
theorem B726543 : Blo 726324 726543 := bstep (se 1 (by rfl) ⟨544907, by rfl⟩ : syracuseStep 726543 = 1089815) B1089815
theorem B726587 : Blo 726324 726587 := bstep (se 1 (by rfl) ⟨544940, by rfl⟩ : syracuseStep 726587 = 1089881) B1089881
theorem B16782947 : Blo 726324 16782947 := bstep (se 1 (by rfl) ⟨12587210, by rfl⟩ : syracuseStep 16782947 = 25174421) B25174421
theorem B8001125 : Blo 726324 8001125 := bstep (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) B1500211
theorem B726663 : Blo 726324 726663 := bstep (se 1 (by rfl) ⟨544997, by rfl⟩ : syracuseStep 726663 = 1089995) B1089995
theorem B726671 : Blo 726324 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B726715 : Blo 726324 726715 := bstep (se 1 (by rfl) ⟨545036, by rfl⟩ : syracuseStep 726715 = 1090073) B1090073
theorem B4429541 : Blo 726324 4429541 := bstep (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) B830539
theorem B4200173 : Blo 726324 4200173 := bstep (se 3 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 4200173 = 1575065) B1575065
theorem B726791 : Blo 726324 726791 := bstep (se 1 (by rfl) ⟨545093, by rfl⟩ : syracuseStep 726791 = 1090187) B1090187
theorem B1840907 : Blo 726324 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B726799 : Blo 726324 726799 := bstep (se 1 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 726799 = 1090199) B1090199
theorem B1382177 : Blo 726324 1382177 := bstep (se 2 (by rfl) ⟨518316, by rfl⟩ : syracuseStep 1382177 = 1036633) B1036633
theorem B2955041 : Blo 726324 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B726843 : Blo 726324 726843 := bstep (se 1 (by rfl) ⟨545132, by rfl⟩ : syracuseStep 726843 = 1090265) B1090265
theorem B726919 : Blo 726324 726919 := bstep (se 1 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 726919 = 1090379) B1090379
theorem B726927 : Blo 726324 726927 := bstep (se 1 (by rfl) ⟨545195, by rfl⟩ : syracuseStep 726927 = 1090391) B1090391
theorem B2987929 : Blo 726324 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B2463641 : Blo 726324 2463641 := bstep (se 2 (by rfl) ⟨923865, by rfl⟩ : syracuseStep 2463641 = 1847731) B1847731
theorem B726971 : Blo 726324 726971 := bstep (se 1 (by rfl) ⟨545228, by rfl⟩ : syracuseStep 726971 = 1090457) B1090457
theorem B3119057 : Blo 726324 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B727047 : Blo 726324 727047 := bstep (se 1 (by rfl) ⟨545285, by rfl⟩ : syracuseStep 727047 = 1090571) B1090571
theorem B727055 : Blo 726324 727055 := bstep (se 1 (by rfl) ⟨545291, by rfl⟩ : syracuseStep 727055 = 1090583) B1090583
theorem B923663 : Blo 726324 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B727099 : Blo 726324 727099 := bstep (se 1 (by rfl) ⟨545324, by rfl⟩ : syracuseStep 727099 = 1090649) B1090649
theorem B6658109 : Blo 726324 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B727175 : Blo 726324 727175 := bstep (se 1 (by rfl) ⟨545381, by rfl⟩ : syracuseStep 727175 = 1090763) B1090763
theorem B727183 : Blo 726324 727183 := bstep (se 1 (by rfl) ⟨545387, by rfl⟩ : syracuseStep 727183 = 1090775) B1090775
theorem B727227 : Blo 726324 727227 := bstep (se 1 (by rfl) ⟨545420, by rfl⟩ : syracuseStep 727227 = 1090841) B1090841
theorem B727303 : Blo 726324 727303 := bstep (se 1 (by rfl) ⟨545477, by rfl⟩ : syracuseStep 727303 = 1090955) B1090955
theorem B727311 : Blo 726324 727311 := bstep (se 1 (by rfl) ⟨545483, by rfl⟩ : syracuseStep 727311 = 1090967) B1090967
theorem B727355 : Blo 726324 727355 := bstep (se 1 (by rfl) ⟨545516, by rfl⟩ : syracuseStep 727355 = 1091033) B1091033
theorem B727431 : Blo 726324 727431 := bstep (se 1 (by rfl) ⟨545573, by rfl⟩ : syracuseStep 727431 = 1091147) B1091147
theorem B727439 : Blo 726324 727439 := bstep (se 1 (by rfl) ⟨545579, by rfl⟩ : syracuseStep 727439 = 1091159) B1091159
theorem B1841555 : Blo 726324 1841555 := bstep (se 1 (by rfl) ⟨1381166, by rfl⟩ : syracuseStep 1841555 = 2762333) B2762333
theorem B727483 : Blo 726324 727483 := bstep (se 1 (by rfl) ⟨545612, by rfl⟩ : syracuseStep 727483 = 1091225) B1091225
theorem B727559 : Blo 726324 727559 := bstep (se 1 (by rfl) ⟨545669, by rfl⟩ : syracuseStep 727559 = 1091339) B1091339
theorem B727567 : Blo 726324 727567 := bstep (se 1 (by rfl) ⟨545675, by rfl⟩ : syracuseStep 727567 = 1091351) B1091351
theorem B727611 : Blo 726324 727611 := bstep (se 1 (by rfl) ⟨545708, by rfl⟩ : syracuseStep 727611 = 1091417) B1091417
theorem B2333245 : Blo 726324 2333245 := bstep (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) B874967
theorem B2464343 : Blo 726324 2464343 := bstep (se 1 (by rfl) ⟨1848257, by rfl⟩ : syracuseStep 2464343 = 3696515) B3696515
theorem B727687 : Blo 726324 727687 := bstep (se 1 (by rfl) ⟨545765, by rfl⟩ : syracuseStep 727687 = 1091531) B1091531
theorem B727695 : Blo 726324 727695 := bstep (se 1 (by rfl) ⟨545771, by rfl⟩ : syracuseStep 727695 = 1091543) B1091543
theorem B1841849 : Blo 726324 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B727739 : Blo 726324 727739 := bstep (se 1 (by rfl) ⟨545804, by rfl⟩ : syracuseStep 727739 = 1091609) B1091609
theorem B727815 : Blo 726324 727815 := bstep (se 1 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 727815 = 1091723) B1091723
theorem B727823 : Blo 726324 727823 := bstep (se 1 (by rfl) ⟨545867, by rfl⟩ : syracuseStep 727823 = 1091735) B1091735
theorem B727867 : Blo 726324 727867 := bstep (se 1 (by rfl) ⟨545900, by rfl⟩ : syracuseStep 727867 = 1091801) B1091801
theorem B727943 : Blo 726324 727943 := bstep (se 1 (by rfl) ⟨545957, by rfl⟩ : syracuseStep 727943 = 1091915) B1091915
theorem B727951 : Blo 726324 727951 := bstep (se 1 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 727951 = 1091927) B1091927
theorem B3677075 : Blo 726324 3677075 := bstep (se 1 (by rfl) ⟨2757806, by rfl⟩ : syracuseStep 3677075 = 5515613) B5515613
theorem B727995 : Blo 726324 727995 := bstep (se 1 (by rfl) ⟨545996, by rfl⟩ : syracuseStep 727995 = 1091993) B1091993
theorem B8297477 : Blo 726324 8297477 := bstep (se 4 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 8297477 = 1555777) B1555777
theorem B728071 : Blo 726324 728071 := bstep (se 1 (by rfl) ⟨546053, by rfl⟩ : syracuseStep 728071 = 1092107) B1092107
theorem B728079 : Blo 726324 728079 := bstep (se 1 (by rfl) ⟨546059, by rfl⟩ : syracuseStep 728079 = 1092119) B1092119
theorem B728123 : Blo 726324 728123 := bstep (se 1 (by rfl) ⟨546092, by rfl⟩ : syracuseStep 728123 = 1092185) B1092185
theorem B2464829 : Blo 726324 2464829 := bstep (se 3 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 2464829 = 924311) B924311
theorem B728199 : Blo 726324 728199 := bstep (se 1 (by rfl) ⟨546149, by rfl⟩ : syracuseStep 728199 = 1092299) B1092299
theorem B728207 : Blo 726324 728207 := bstep (se 1 (by rfl) ⟨546155, by rfl⟩ : syracuseStep 728207 = 1092311) B1092311
theorem B728251 : Blo 726324 728251 := bstep (se 1 (by rfl) ⟨546188, by rfl⟩ : syracuseStep 728251 = 1092377) B1092377
theorem B2628865 : Blo 726324 2628865 := bstep (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) B1971649
theorem B728327 : Blo 726324 728327 := bstep (se 1 (by rfl) ⟨546245, by rfl⟩ : syracuseStep 728327 = 1092491) B1092491
theorem B728335 : Blo 726324 728335 := bstep (se 1 (by rfl) ⟨546251, by rfl⟩ : syracuseStep 728335 = 1092503) B1092503
theorem B728379 : Blo 726324 728379 := bstep (se 1 (by rfl) ⟨546284, by rfl⟩ : syracuseStep 728379 = 1092569) B1092569
theorem B1842547 : Blo 726324 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B728455 : Blo 726324 728455 := bstep (se 1 (by rfl) ⟨546341, by rfl⟩ : syracuseStep 728455 = 1092683) B1092683
theorem B728463 : Blo 726324 728463 := bstep (se 1 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 728463 = 1092695) B1092695
theorem B2071955 : Blo 726324 2071955 := bstep (se 1 (by rfl) ⟨1553966, by rfl⟩ : syracuseStep 2071955 = 3107933) B3107933
theorem B728507 : Blo 726324 728507 := bstep (se 1 (by rfl) ⟨546380, by rfl⟩ : syracuseStep 728507 = 1092761) B1092761
theorem B1842689 : Blo 726324 1842689 := bstep (se 2 (by rfl) ⟨691008, by rfl⟩ : syracuseStep 1842689 = 1382017) B1382017
theorem B728583 : Blo 726324 728583 := bstep (se 1 (by rfl) ⟨546437, by rfl⟩ : syracuseStep 728583 = 1092875) B1092875
theorem B728591 : Blo 726324 728591 := bstep (se 1 (by rfl) ⟨546443, by rfl⟩ : syracuseStep 728591 = 1092887) B1092887
theorem B728635 : Blo 726324 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B2629181 : Blo 726324 2629181 := bstep (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) B985943
theorem B17997389 : Blo 726324 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B1973875 : Blo 726324 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B728711 : Blo 726324 728711 := bstep (se 1 (by rfl) ⟨546533, by rfl⟩ : syracuseStep 728711 = 1093067) B1093067
theorem B728719 : Blo 726324 728719 := bstep (se 1 (by rfl) ⟨546539, by rfl⟩ : syracuseStep 728719 = 1093079) B1093079
theorem B1384121 : Blo 726324 1384121 := bstep (se 2 (by rfl) ⟨519045, by rfl⟩ : syracuseStep 1384121 = 1038091) B1038091
theorem B728763 : Blo 726324 728763 := bstep (se 1 (by rfl) ⟨546572, by rfl⟩ : syracuseStep 728763 = 1093145) B1093145
theorem B728839 : Blo 726324 728839 := bstep (se 1 (by rfl) ⟨546629, by rfl⟩ : syracuseStep 728839 = 1093259) B1093259
theorem B728847 : Blo 726324 728847 := bstep (se 1 (by rfl) ⟨546635, by rfl⟩ : syracuseStep 728847 = 1093271) B1093271
theorem B4038437 : Blo 726324 4038437 := bstep (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) B757207
theorem B728891 : Blo 726324 728891 := bstep (se 1 (by rfl) ⟨546668, by rfl⟩ : syracuseStep 728891 = 1093337) B1093337
theorem B728967 : Blo 726324 728967 := bstep (se 1 (by rfl) ⟨546725, by rfl⟩ : syracuseStep 728967 = 1093451) B1093451
theorem B728975 : Blo 726324 728975 := bstep (se 1 (by rfl) ⟨546731, by rfl⟩ : syracuseStep 728975 = 1093463) B1093463
theorem B2760601 : Blo 726324 2760601 := bstep (se 2 (by rfl) ⟨1035225, by rfl⟩ : syracuseStep 2760601 = 2070451) B2070451
theorem B729019 : Blo 726324 729019 := bstep (se 1 (by rfl) ⟨546764, by rfl⟩ : syracuseStep 729019 = 1093529) B1093529
theorem B1843145 : Blo 726324 1843145 := bstep (se 2 (by rfl) ⟨691179, by rfl⟩ : syracuseStep 1843145 = 1382359) B1382359
theorem B1089527 : Blo 726324 1089527 := bstep (se 1 (by rfl) ⟨817145, by rfl⟩ : syracuseStep 1089527 = 1634291) B1634291
theorem B729095 : Blo 726324 729095 := bstep (se 1 (by rfl) ⟨546821, by rfl⟩ : syracuseStep 729095 = 1093643) B1093643
theorem B1089551 : Blo 726324 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B729103 : Blo 726324 729103 := bstep (se 1 (by rfl) ⟨546827, by rfl⟩ : syracuseStep 729103 = 1093655) B1093655
theorem B1089593 : Blo 726324 1089593 := bstep (se 2 (by rfl) ⟨408597, by rfl⟩ : syracuseStep 1089593 = 817195) B817195
theorem B729147 : Blo 726324 729147 := bstep (se 1 (by rfl) ⟨546860, by rfl⟩ : syracuseStep 729147 = 1093721) B1093721
theorem B1089671 : Blo 726324 1089671 := bstep (se 1 (by rfl) ⟨817253, by rfl⟩ : syracuseStep 1089671 = 1634507) B1634507
theorem B729223 : Blo 726324 729223 := bstep (se 1 (by rfl) ⟨546917, by rfl⟩ : syracuseStep 729223 = 1093835) B1093835
theorem B729231 : Blo 726324 729231 := bstep (se 1 (by rfl) ⟨546923, by rfl⟩ : syracuseStep 729231 = 1093847) B1093847
theorem B2072729 : Blo 726324 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B1089707 : Blo 726324 1089707 := bstep (se 1 (by rfl) ⟨817280, by rfl⟩ : syracuseStep 1089707 = 1634561) B1634561
theorem B729275 : Blo 726324 729275 := bstep (se 1 (by rfl) ⟨546956, by rfl⟩ : syracuseStep 729275 = 1093913) B1093913
theorem B1089737 : Blo 726324 1089737 := bstep (se 2 (by rfl) ⟨408651, by rfl⟩ : syracuseStep 1089737 = 817303) B817303
theorem B2760905 : Blo 726324 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B729351 : Blo 726324 729351 := bstep (se 1 (by rfl) ⟨547013, by rfl⟩ : syracuseStep 729351 = 1094027) B1094027
theorem B729359 : Blo 726324 729359 := bstep (se 1 (by rfl) ⟨547019, by rfl⟩ : syracuseStep 729359 = 1094039) B1094039
theorem B1843499 : Blo 726324 1843499 := bstep (se 1 (by rfl) ⟨1382624, by rfl⟩ : syracuseStep 1843499 = 2765249) B2765249
theorem B1089851 : Blo 726324 1089851 := bstep (se 1 (by rfl) ⟨817388, by rfl⟩ : syracuseStep 1089851 = 1634777) B1634777
theorem B729403 : Blo 726324 729403 := bstep (se 1 (by rfl) ⟨547052, by rfl⟩ : syracuseStep 729403 = 1094105) B1094105
theorem B1089911 : Blo 726324 1089911 := bstep (se 1 (by rfl) ⟨817433, by rfl⟩ : syracuseStep 1089911 = 1634867) B1634867
theorem B729479 : Blo 726324 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B1089935 : Blo 726324 1089935 := bstep (se 1 (by rfl) ⟨817451, by rfl⟩ : syracuseStep 1089935 = 1634903) B1634903
theorem B729487 : Blo 726324 729487 := bstep (se 1 (by rfl) ⟨547115, by rfl⟩ : syracuseStep 729487 = 1094231) B1094231
theorem B1089977 : Blo 726324 1089977 := bstep (se 2 (by rfl) ⟨408741, by rfl⟩ : syracuseStep 1089977 = 817483) B817483
theorem B729531 : Blo 726324 729531 := bstep (se 1 (by rfl) ⟨547148, by rfl⟩ : syracuseStep 729531 = 1094297) B1094297
theorem B1090055 : Blo 726324 1090055 := bstep (se 1 (by rfl) ⟨817541, by rfl⟩ : syracuseStep 1090055 = 1635083) B1635083
theorem B729607 : Blo 726324 729607 := bstep (se 1 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 729607 = 1094411) B1094411
theorem B729615 : Blo 726324 729615 := bstep (se 1 (by rfl) ⟨547211, by rfl⟩ : syracuseStep 729615 = 1094423) B1094423
theorem B1090091 : Blo 726324 1090091 := bstep (se 1 (by rfl) ⟨817568, by rfl⟩ : syracuseStep 1090091 = 1635137) B1635137
theorem B729659 : Blo 726324 729659 := bstep (se 1 (by rfl) ⟨547244, by rfl⟩ : syracuseStep 729659 = 1094489) B1094489
theorem B6988355 : Blo 726324 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B1090121 : Blo 726324 1090121 := bstep (se 2 (by rfl) ⟨408795, by rfl⟩ : syracuseStep 1090121 = 817591) B817591
theorem B729735 : Blo 726324 729735 := bstep (se 1 (by rfl) ⟨547301, by rfl⟩ : syracuseStep 729735 = 1094603) B1094603
theorem B729743 : Blo 726324 729743 := bstep (se 1 (by rfl) ⟨547307, by rfl⟩ : syracuseStep 729743 = 1094615) B1094615
theorem B1090235 : Blo 726324 1090235 := bstep (se 1 (by rfl) ⟨817676, by rfl⟩ : syracuseStep 1090235 = 1635353) B1635353
theorem B729787 : Blo 726324 729787 := bstep (se 1 (by rfl) ⟨547340, by rfl⟩ : syracuseStep 729787 = 1094681) B1094681
theorem B3318509 : Blo 726324 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1090295 : Blo 726324 1090295 := bstep (se 1 (by rfl) ⟨817721, by rfl⟩ : syracuseStep 1090295 = 1635443) B1635443
theorem B729863 : Blo 726324 729863 := bstep (se 1 (by rfl) ⟨547397, by rfl⟩ : syracuseStep 729863 = 1094795) B1094795
theorem B1090319 : Blo 726324 1090319 := bstep (se 1 (by rfl) ⟨817739, by rfl⟩ : syracuseStep 1090319 = 1635479) B1635479
theorem B729871 : Blo 726324 729871 := bstep (se 1 (by rfl) ⟨547403, by rfl⟩ : syracuseStep 729871 = 1094807) B1094807
theorem B5251877 : Blo 726324 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B1090361 : Blo 726324 1090361 := bstep (se 2 (by rfl) ⟨408885, by rfl⟩ : syracuseStep 1090361 = 817771) B817771
theorem B1385275 : Blo 726324 1385275 := bstep (se 1 (by rfl) ⟨1038956, by rfl⟩ : syracuseStep 1385275 = 2077913) B2077913
theorem B729915 : Blo 726324 729915 := bstep (se 1 (by rfl) ⟨547436, by rfl⟩ : syracuseStep 729915 = 1094873) B1094873
theorem B7873355 : Blo 726324 7873355 := bstep (se 1 (by rfl) ⟨5905016, by rfl⟩ : syracuseStep 7873355 = 11810033) B11810033
theorem B1090439 : Blo 726324 1090439 := bstep (se 1 (by rfl) ⟨817829, by rfl⟩ : syracuseStep 1090439 = 1635659) B1635659
theorem B729991 : Blo 726324 729991 := bstep (se 1 (by rfl) ⟨547493, by rfl⟩ : syracuseStep 729991 = 1094987) B1094987
theorem B729999 : Blo 726324 729999 := bstep (se 1 (by rfl) ⟨547499, by rfl⟩ : syracuseStep 729999 = 1094999) B1094999
theorem B1090475 : Blo 726324 1090475 := bstep (se 1 (by rfl) ⟨817856, by rfl⟩ : syracuseStep 1090475 = 1635713) B1635713
theorem B730043 : Blo 726324 730043 := bstep (se 1 (by rfl) ⟨547532, by rfl⟩ : syracuseStep 730043 = 1095065) B1095065
theorem B1090505 : Blo 726324 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B730119 : Blo 726324 730119 := bstep (se 1 (by rfl) ⟨547589, by rfl⟩ : syracuseStep 730119 = 1095179) B1095179
theorem B730127 : Blo 726324 730127 := bstep (se 1 (by rfl) ⟨547595, by rfl⟩ : syracuseStep 730127 = 1095191) B1095191
theorem B1090619 : Blo 726324 1090619 := bstep (se 1 (by rfl) ⟨817964, by rfl⟩ : syracuseStep 1090619 = 1635929) B1635929
theorem B730171 : Blo 726324 730171 := bstep (se 1 (by rfl) ⟨547628, by rfl⟩ : syracuseStep 730171 = 1095257) B1095257
theorem B1090679 : Blo 726324 1090679 := bstep (se 1 (by rfl) ⟨818009, by rfl⟩ : syracuseStep 1090679 = 1636019) B1636019
theorem B2761847 : Blo 726324 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B730247 : Blo 726324 730247 := bstep (se 1 (by rfl) ⟨547685, by rfl⟩ : syracuseStep 730247 = 1095371) B1095371
theorem B1090703 : Blo 726324 1090703 := bstep (se 1 (by rfl) ⟨818027, by rfl⟩ : syracuseStep 1090703 = 1636055) B1636055
theorem B730255 : Blo 726324 730255 := bstep (se 1 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 730255 = 1095383) B1095383
theorem B1090745 : Blo 726324 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B730299 : Blo 726324 730299 := bstep (se 1 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 730299 = 1095449) B1095449
theorem B1090823 : Blo 726324 1090823 := bstep (se 1 (by rfl) ⟨818117, by rfl⟩ : syracuseStep 1090823 = 1636235) B1636235
theorem B1844491 : Blo 726324 1844491 := bstep (se 1 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 1844491 = 2766737) B2766737
theorem B1385761 : Blo 726324 1385761 := bstep (se 2 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 1385761 = 1039321) B1039321
theorem B1090859 : Blo 726324 1090859 := bstep (se 1 (by rfl) ⟨818144, by rfl⟩ : syracuseStep 1090859 = 1636289) B1636289
theorem B1090889 : Blo 726324 1090889 := bstep (se 2 (by rfl) ⟨409083, by rfl⟩ : syracuseStep 1090889 = 818167) B818167
theorem B1844633 : Blo 726324 1844633 := bstep (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) B1383475
theorem B1091003 : Blo 726324 1091003 := bstep (se 1 (by rfl) ⟨818252, by rfl⟩ : syracuseStep 1091003 = 1636505) B1636505
theorem B1091063 : Blo 726324 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B1091087 : Blo 726324 1091087 := bstep (se 1 (by rfl) ⟨818315, by rfl⟩ : syracuseStep 1091087 = 1636631) B1636631
theorem B1091129 : Blo 726324 1091129 := bstep (se 2 (by rfl) ⟨409173, by rfl⟩ : syracuseStep 1091129 = 818347) B818347
theorem B1844795 : Blo 726324 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B1091207 : Blo 726324 1091207 := bstep (se 1 (by rfl) ⟨818405, by rfl⟩ : syracuseStep 1091207 = 1636811) B1636811
theorem B1091243 : Blo 726324 1091243 := bstep (se 1 (by rfl) ⟨818432, by rfl⟩ : syracuseStep 1091243 = 1636865) B1636865
theorem B1091273 : Blo 726324 1091273 := bstep (se 2 (by rfl) ⟨409227, by rfl⟩ : syracuseStep 1091273 = 818455) B818455
theorem B1091387 : Blo 726324 1091387 := bstep (se 1 (by rfl) ⟨818540, by rfl⟩ : syracuseStep 1091387 = 1637081) B1637081
theorem B17737541 : Blo 726324 17737541 := bstep (se 4 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 17737541 = 3325789) B3325789
theorem B4663129 : Blo 726324 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B2336627 : Blo 726324 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1091447 : Blo 726324 1091447 := bstep (se 1 (by rfl) ⟨818585, by rfl⟩ : syracuseStep 1091447 = 1637171) B1637171
theorem B1091471 : Blo 726324 1091471 := bstep (se 1 (by rfl) ⟨818603, by rfl⟩ : syracuseStep 1091471 = 1637207) B1637207
theorem B4138897 : Blo 726324 4138897 := bstep (se 2 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 4138897 = 3104173) B3104173
theorem B1845139 : Blo 726324 1845139 := bstep (se 1 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 1845139 = 2767709) B2767709
theorem B3680153 : Blo 726324 3680153 := bstep (se 2 (by rfl) ⟨1380057, by rfl⟩ : syracuseStep 3680153 = 2760115) B2760115
theorem B1091513 : Blo 726324 1091513 := bstep (se 2 (by rfl) ⟨409317, by rfl⟩ : syracuseStep 1091513 = 818635) B818635
theorem B1091591 : Blo 726324 1091591 := bstep (se 1 (by rfl) ⟨818693, by rfl⟩ : syracuseStep 1091591 = 1637387) B1637387
theorem B1845281 : Blo 726324 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B1091627 : Blo 726324 1091627 := bstep (se 1 (by rfl) ⟨818720, by rfl⟩ : syracuseStep 1091627 = 1637441) B1637441
theorem B2762819 : Blo 726324 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B1091657 : Blo 726324 1091657 := bstep (se 2 (by rfl) ⟨409371, by rfl⟩ : syracuseStep 1091657 = 818743) B818743
theorem B6400133 : Blo 726324 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B1091771 : Blo 726324 1091771 := bstep (se 1 (by rfl) ⟨818828, by rfl⟩ : syracuseStep 1091771 = 1637657) B1637657
theorem B2074825 : Blo 726324 2074825 := bstep (se 2 (by rfl) ⟨778059, by rfl⟩ : syracuseStep 2074825 = 1556119) B1556119
theorem B1091831 : Blo 726324 1091831 := bstep (se 1 (by rfl) ⟨818873, by rfl⟩ : syracuseStep 1091831 = 1637747) B1637747
theorem B1091855 : Blo 726324 1091855 := bstep (se 1 (by rfl) ⟨818891, by rfl⟩ : syracuseStep 1091855 = 1637783) B1637783
theorem B1091897 : Blo 726324 1091897 := bstep (se 2 (by rfl) ⟨409461, by rfl⟩ : syracuseStep 1091897 = 818923) B818923
theorem B1091975 : Blo 726324 1091975 := bstep (se 1 (by rfl) ⟨818981, by rfl⟩ : syracuseStep 1091975 = 1637963) B1637963
theorem B1092011 : Blo 726324 1092011 := bstep (se 1 (by rfl) ⟨819008, by rfl⟩ : syracuseStep 1092011 = 1638017) B1638017
theorem B829883 : Blo 726324 829883 := bstep (se 1 (by rfl) ⟨622412, by rfl⟩ : syracuseStep 829883 = 1244825) B1244825
theorem B1092041 : Blo 726324 1092041 := bstep (se 2 (by rfl) ⟨409515, by rfl⟩ : syracuseStep 1092041 = 819031) B819031
theorem B2075179 : Blo 726324 2075179 := bstep (se 1 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 2075179 = 3112769) B3112769
theorem B1092155 : Blo 726324 1092155 := bstep (se 1 (by rfl) ⟨819116, by rfl⟩ : syracuseStep 1092155 = 1638233) B1638233
theorem B1092215 : Blo 726324 1092215 := bstep (se 1 (by rfl) ⟨819161, by rfl⟩ : syracuseStep 1092215 = 1638323) B1638323
theorem B1092239 : Blo 726324 1092239 := bstep (se 1 (by rfl) ⟨819179, by rfl⟩ : syracuseStep 1092239 = 1638359) B1638359
theorem B1092281 : Blo 726324 1092281 := bstep (se 2 (by rfl) ⟨409605, by rfl⟩ : syracuseStep 1092281 = 819211) B819211
theorem B1092359 : Blo 726324 1092359 := bstep (se 1 (by rfl) ⟨819269, by rfl⟩ : syracuseStep 1092359 = 1638539) B1638539
theorem B1092395 : Blo 726324 1092395 := bstep (se 1 (by rfl) ⟨819296, by rfl⟩ : syracuseStep 1092395 = 1638593) B1638593
theorem B2075453 : Blo 726324 2075453 := bstep (se 3 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 2075453 = 778295) B778295
theorem B1092425 : Blo 726324 1092425 := bstep (se 2 (by rfl) ⟨409659, by rfl⟩ : syracuseStep 1092425 = 819319) B819319
theorem B1092539 : Blo 726324 1092539 := bstep (se 1 (by rfl) ⟨819404, by rfl⟩ : syracuseStep 1092539 = 1638809) B1638809
theorem B4205533 : Blo 726324 4205533 := bstep (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) B1577075
theorem B1092599 : Blo 726324 1092599 := bstep (se 1 (by rfl) ⟨819449, by rfl⟩ : syracuseStep 1092599 = 1638899) B1638899
theorem B1846273 : Blo 726324 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B1092623 : Blo 726324 1092623 := bstep (se 1 (by rfl) ⟨819467, by rfl⟩ : syracuseStep 1092623 = 1638935) B1638935
theorem B1551403 : Blo 726324 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B1092665 : Blo 726324 1092665 := bstep (se 2 (by rfl) ⟨409749, by rfl⟩ : syracuseStep 1092665 = 819499) B819499
theorem B9972823 : Blo 726324 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B1092743 : Blo 726324 1092743 := bstep (se 1 (by rfl) ⟨819557, by rfl⟩ : syracuseStep 1092743 = 1639115) B1639115
theorem B1092779 : Blo 726324 1092779 := bstep (se 1 (by rfl) ⟨819584, by rfl⟩ : syracuseStep 1092779 = 1639169) B1639169
theorem B1092809 : Blo 726324 1092809 := bstep (se 2 (by rfl) ⟨409803, by rfl⟩ : syracuseStep 1092809 = 819607) B819607
theorem B1092923 : Blo 726324 1092923 := bstep (se 1 (by rfl) ⟨819692, by rfl⟩ : syracuseStep 1092923 = 1639385) B1639385
theorem B1092983 : Blo 726324 1092983 := bstep (se 1 (by rfl) ⟨819737, by rfl⟩ : syracuseStep 1092983 = 1639475) B1639475
theorem B1093007 : Blo 726324 1093007 := bstep (se 1 (by rfl) ⟨819755, by rfl⟩ : syracuseStep 1093007 = 1639511) B1639511
theorem B1093049 : Blo 726324 1093049 := bstep (se 2 (by rfl) ⟨409893, by rfl⟩ : syracuseStep 1093049 = 819787) B819787
theorem B1093127 : Blo 726324 1093127 := bstep (se 1 (by rfl) ⟨819845, by rfl⟩ : syracuseStep 1093127 = 1639691) B1639691
theorem B1093163 : Blo 726324 1093163 := bstep (se 1 (by rfl) ⟨819872, by rfl⟩ : syracuseStep 1093163 = 1639745) B1639745
theorem B1093193 : Blo 726324 1093193 := bstep (se 2 (by rfl) ⟨409947, by rfl⟩ : syracuseStep 1093193 = 819895) B819895
theorem B1846871 : Blo 726324 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B1093307 : Blo 726324 1093307 := bstep (se 1 (by rfl) ⟨819980, by rfl⟩ : syracuseStep 1093307 = 1639961) B1639961
theorem B2764489 : Blo 726324 2764489 := bstep (se 2 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 2764489 = 2073367) B2073367
theorem B1093367 : Blo 726324 1093367 := bstep (se 1 (by rfl) ⟨820025, by rfl⟩ : syracuseStep 1093367 = 1640051) B1640051
theorem B5517071 : Blo 726324 5517071 := bstep (se 1 (by rfl) ⟨4137803, by rfl⟩ : syracuseStep 5517071 = 8275607) B8275607
theorem B1093391 : Blo 726324 1093391 := bstep (se 1 (by rfl) ⟨820043, by rfl⟩ : syracuseStep 1093391 = 1640087) B1640087
theorem B1847083 : Blo 726324 1847083 := bstep (se 1 (by rfl) ⟨1385312, by rfl⟩ : syracuseStep 1847083 = 2770625) B2770625
theorem B1093433 : Blo 726324 1093433 := bstep (se 2 (by rfl) ⟨410037, by rfl⟩ : syracuseStep 1093433 = 820075) B820075
theorem B1093511 : Blo 726324 1093511 := bstep (se 1 (by rfl) ⟨820133, by rfl⟩ : syracuseStep 1093511 = 1640267) B1640267
theorem B9351065 : Blo 726324 9351065 := bstep (se 2 (by rfl) ⟨3506649, by rfl⟩ : syracuseStep 9351065 = 7013299) B7013299
theorem B1093547 : Blo 726324 1093547 := bstep (se 1 (by rfl) ⟨820160, by rfl⟩ : syracuseStep 1093547 = 1640321) B1640321
theorem B1847225 : Blo 726324 1847225 := bstep (se 2 (by rfl) ⟨692709, by rfl⟩ : syracuseStep 1847225 = 1385419) B1385419
theorem B1093577 : Blo 726324 1093577 := bstep (se 2 (by rfl) ⟨410091, by rfl⟩ : syracuseStep 1093577 = 820183) B820183
theorem B1093691 : Blo 726324 1093691 := bstep (se 1 (by rfl) ⟨820268, by rfl⟩ : syracuseStep 1093691 = 1640537) B1640537
theorem B1093751 : Blo 726324 1093751 := bstep (se 1 (by rfl) ⟨820313, by rfl⟩ : syracuseStep 1093751 = 1640627) B1640627
theorem B1093775 : Blo 726324 1093775 := bstep (se 1 (by rfl) ⟨820331, by rfl⟩ : syracuseStep 1093775 = 1640663) B1640663
theorem B1093817 : Blo 726324 1093817 := bstep (se 2 (by rfl) ⟨410181, by rfl⟩ : syracuseStep 1093817 = 820363) B820363
theorem B4141313 : Blo 726324 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B1093895 : Blo 726324 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B2240779 : Blo 726324 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B1093931 : Blo 726324 1093931 := bstep (se 1 (by rfl) ⟨820448, by rfl⟩ : syracuseStep 1093931 = 1640897) B1640897
theorem B1093961 : Blo 726324 1093961 := bstep (se 2 (by rfl) ⟨410235, by rfl⟩ : syracuseStep 1093961 = 820471) B820471
theorem B1749395 : Blo 726324 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B3682745 : Blo 726324 3682745 := bstep (se 2 (by rfl) ⟨1381029, by rfl⟩ : syracuseStep 3682745 = 2762059) B2762059
theorem B1094075 : Blo 726324 1094075 := bstep (se 1 (by rfl) ⟨820556, by rfl⟩ : syracuseStep 1094075 = 1641113) B1641113
theorem B1094135 : Blo 726324 1094135 := bstep (se 1 (by rfl) ⟨820601, by rfl⟩ : syracuseStep 1094135 = 1641203) B1641203
theorem B1094159 : Blo 726324 1094159 := bstep (se 1 (by rfl) ⟨820619, by rfl⟩ : syracuseStep 1094159 = 1641239) B1641239
theorem B1094201 : Blo 726324 1094201 := bstep (se 2 (by rfl) ⟨410325, by rfl⟩ : syracuseStep 1094201 = 820651) B820651
theorem B16822849 : Blo 726324 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B1094279 : Blo 726324 1094279 := bstep (se 1 (by rfl) ⟨820709, by rfl⟩ : syracuseStep 1094279 = 1641419) B1641419
theorem B1094315 : Blo 726324 1094315 := bstep (se 1 (by rfl) ⟨820736, by rfl⟩ : syracuseStep 1094315 = 1641473) B1641473
theorem B1094345 : Blo 726324 1094345 := bstep (se 2 (by rfl) ⟨410379, by rfl⟩ : syracuseStep 1094345 = 820759) B820759
theorem B1094459 : Blo 726324 1094459 := bstep (se 1 (by rfl) ⟨820844, by rfl⟩ : syracuseStep 1094459 = 1641689) B1641689
theorem B2077559 : Blo 726324 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B1094519 : Blo 726324 1094519 := bstep (se 1 (by rfl) ⟨820889, by rfl⟩ : syracuseStep 1094519 = 1641779) B1641779
theorem B1094543 : Blo 726324 1094543 := bstep (se 1 (by rfl) ⟨820907, by rfl⟩ : syracuseStep 1094543 = 1641815) B1641815
theorem B1848217 : Blo 726324 1848217 := bstep (se 2 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 1848217 = 1386163) B1386163
theorem B1094585 : Blo 726324 1094585 := bstep (se 2 (by rfl) ⟨410469, by rfl⟩ : syracuseStep 1094585 = 820939) B820939
theorem B1094663 : Blo 726324 1094663 := bstep (se 1 (by rfl) ⟨820997, by rfl⟩ : syracuseStep 1094663 = 1641995) B1641995
theorem B1094699 : Blo 726324 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B1848379 : Blo 726324 1848379 := bstep (se 1 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 1848379 = 2772569) B2772569
theorem B1094729 : Blo 726324 1094729 := bstep (se 2 (by rfl) ⟨410523, by rfl⟩ : syracuseStep 1094729 = 821047) B821047
theorem B1225847 : Blo 726324 1225847 := bstep (se 1 (by rfl) ⟨919385, by rfl⟩ : syracuseStep 1225847 = 1838771) B1838771
theorem B1094843 : Blo 726324 1094843 := bstep (se 1 (by rfl) ⟨821132, by rfl⟩ : syracuseStep 1094843 = 1642265) B1642265
theorem B3945673 : Blo 726324 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B1848521 : Blo 726324 1848521 := bstep (se 2 (by rfl) ⟨693195, by rfl⟩ : syracuseStep 1848521 = 1386391) B1386391
theorem B1094903 : Blo 726324 1094903 := bstep (se 1 (by rfl) ⟨821177, by rfl⟩ : syracuseStep 1094903 = 1642355) B1642355
theorem B1094927 : Blo 726324 1094927 := bstep (se 1 (by rfl) ⟨821195, by rfl⟩ : syracuseStep 1094927 = 1642391) B1642391
theorem B1094969 : Blo 726324 1094969 := bstep (se 2 (by rfl) ⟨410613, by rfl⟩ : syracuseStep 1094969 = 821227) B821227
theorem B1095047 : Blo 726324 1095047 := bstep (se 1 (by rfl) ⟨821285, by rfl⟩ : syracuseStep 1095047 = 1642571) B1642571
theorem B1095083 : Blo 726324 1095083 := bstep (se 1 (by rfl) ⟨821312, by rfl⟩ : syracuseStep 1095083 = 1642625) B1642625
theorem B1095113 : Blo 726324 1095113 := bstep (se 2 (by rfl) ⟨410667, by rfl⟩ : syracuseStep 1095113 = 821335) B821335
theorem B1226299 : Blo 726324 1226299 := bstep (se 1 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 1226299 = 1839449) B1839449
theorem B1095227 : Blo 726324 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B1095287 : Blo 726324 1095287 := bstep (se 1 (by rfl) ⟨821465, by rfl⟩ : syracuseStep 1095287 = 1642931) B1642931
theorem B1095311 : Blo 726324 1095311 := bstep (se 1 (by rfl) ⟨821483, by rfl⟩ : syracuseStep 1095311 = 1642967) B1642967
theorem B1095353 : Blo 726324 1095353 := bstep (se 2 (by rfl) ⟨410757, by rfl⟩ : syracuseStep 1095353 = 821515) B821515
theorem B3847873 : Blo 726324 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1226441 : Blo 726324 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B3684041 : Blo 726324 3684041 := bstep (se 2 (by rfl) ⟨1381515, by rfl⟩ : syracuseStep 3684041 = 2763031) B2763031
theorem B1095431 : Blo 726324 1095431 := bstep (se 1 (by rfl) ⟨821573, by rfl⟩ : syracuseStep 1095431 = 1643147) B1643147
theorem B1095467 : Blo 726324 1095467 := bstep (se 1 (by rfl) ⟨821600, by rfl⟩ : syracuseStep 1095467 = 1643201) B1643201
theorem B2766707 : Blo 726324 2766707 := bstep (se 1 (by rfl) ⟨2075030, by rfl⟩ : syracuseStep 2766707 = 4150061) B4150061
theorem B1227143 : Blo 726324 1227143 := bstep (se 1 (by rfl) ⟨920357, by rfl⟩ : syracuseStep 1227143 = 1840715) B1840715
theorem B4143545 : Blo 726324 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B1554889 : Blo 726324 1554889 := bstep (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) B1166167
theorem B2243513 : Blo 726324 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B11811851 : Blo 726324 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B1227791 : Blo 726324 1227791 := bstep (se 1 (by rfl) ⟨920843, by rfl⟩ : syracuseStep 1227791 = 1841687) B1841687
theorem B15777155 : Blo 726324 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B1228331 : Blo 726324 1228331 := bstep (se 1 (by rfl) ⟨921248, by rfl⟩ : syracuseStep 1228331 = 1842497) B1842497
theorem B999055 : Blo 726324 999055 := bstep (se 1 (by rfl) ⟨749291, by rfl⟩ : syracuseStep 999055 = 1498583) B1498583
theorem B1228729 : Blo 726324 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B2768849 : Blo 726324 2768849 := bstep (se 2 (by rfl) ⟨1038318, by rfl⟩ : syracuseStep 2768849 = 2076637) B2076637
theorem B8503319 : Blo 726324 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B2769167 : Blo 726324 2769167 := bstep (se 1 (by rfl) ⟨2076875, by rfl⟩ : syracuseStep 2769167 = 4153751) B4153751
theorem B1556795 : Blo 726324 1556795 := bstep (se 1 (by rfl) ⟨1167596, by rfl⟩ : syracuseStep 1556795 = 2335193) B2335193
theorem B4145687 : Blo 726324 4145687 := bstep (se 1 (by rfl) ⟨3109265, by rfl⟩ : syracuseStep 4145687 = 6218531) B6218531
theorem B22364707 : Blo 726324 22364707 := bstep (se 1 (by rfl) ⟨16773530, by rfl⟩ : syracuseStep 22364707 = 33547061) B33547061
theorem B3490391 : Blo 726324 3490391 := bstep (se 1 (by rfl) ⟨2617793, by rfl⟩ : syracuseStep 3490391 = 5235587) B5235587
theorem B1229431 : Blo 726324 1229431 := bstep (se 1 (by rfl) ⟨922073, by rfl⟩ : syracuseStep 1229431 = 1844147) B1844147
theorem B1557281 : Blo 726324 1557281 := bstep (se 2 (by rfl) ⟨583980, by rfl⟩ : syracuseStep 1557281 = 1167961) B1167961
theorem B1229627 : Blo 726324 1229627 := bstep (se 1 (by rfl) ⟨922220, by rfl⟩ : syracuseStep 1229627 = 1844441) B1844441
theorem B4146187 : Blo 726324 4146187 := bstep (se 1 (by rfl) ⟨3109640, by rfl⟩ : syracuseStep 4146187 = 6219281) B6219281
theorem B1557623 : Blo 726324 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1230025 : Blo 726324 1230025 := bstep (se 2 (by rfl) ⟨461259, by rfl⟩ : syracuseStep 1230025 = 922519) B922519
theorem B3556723 : Blo 726324 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B13321907 : Blo 726324 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B1230727 : Blo 726324 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B28067957 : Blo 726324 28067957 := bstep (se 5 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 28067957 = 2631371) B2631371
theorem B1034383 : Blo 726324 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B1231375 : Blo 726324 1231375 := bstep (se 1 (by rfl) ⟨923531, by rfl⟩ : syracuseStep 1231375 = 1847063) B1847063
theorem B6212173 : Blo 726324 6212173 := bstep (se 3 (by rfl) ⟨1164782, by rfl⟩ : syracuseStep 6212173 = 2329565) B2329565
theorem B99830485 : Blo 726324 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B4148171 : Blo 726324 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B3984349 : Blo 726324 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B1035271 : Blo 726324 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B1231915 : Blo 726324 1231915 := bstep (se 1 (by rfl) ⟨923936, by rfl⟩ : syracuseStep 1231915 = 1847873) B1847873
theorem B1232057 : Blo 726324 1232057 := bstep (se 2 (by rfl) ⟨462021, by rfl⟩ : syracuseStep 1232057 = 924043) B924043
theorem B3689873 : Blo 726324 3689873 := bstep (se 2 (by rfl) ⟨1383702, by rfl⟩ : syracuseStep 3689873 = 2767405) B2767405
theorem B1035767 : Blo 726324 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B2772737 : Blo 726324 2772737 := bstep (se 2 (by rfl) ⟨1039776, by rfl⟩ : syracuseStep 2772737 = 2079553) B2079553
theorem B2772751 : Blo 726324 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B7491365 : Blo 726324 7491365 := bstep (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) B1404631
theorem B1658809 : Blo 726324 1658809 := bstep (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) B1244107
theorem B4673483 : Blo 726324 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B5525819 : Blo 726324 5525819 := bstep (se 1 (by rfl) ⟨4144364, by rfl⟩ : syracuseStep 5525819 = 8288729) B8288729
theorem B1036729 : Blo 726324 1036729 := bstep (se 2 (by rfl) ⟨388773, by rfl⟩ : syracuseStep 1036729 = 777547) B777547
theorem B7000769 : Blo 726324 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B1037071 : Blo 726324 1037071 := bstep (se 1 (by rfl) ⟨777803, by rfl⟩ : syracuseStep 1037071 = 1555607) B1555607
theorem B1332001 : Blo 726324 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B11195171 : Blo 726324 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B2806643 : Blo 726324 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B1168519 : Blo 726324 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B4150561 : Blo 726324 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B3691979 : Blo 726324 3691979 := bstep (se 1 (by rfl) ⟨2768984, by rfl⟩ : syracuseStep 3691979 = 5537969) B5537969
theorem B23025329 : Blo 726324 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B3692303 : Blo 726324 3692303 := bstep (se 1 (by rfl) ⟨2769227, by rfl⟩ : syracuseStep 3692303 = 5538455) B5538455
theorem B1038199 : Blo 726324 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B2873411 : Blo 726324 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B6641837 : Blo 726324 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B4151837 : Blo 726324 4151837 := bstep (se 3 (by rfl) ⟨778469, by rfl⟩ : syracuseStep 4151837 = 1556939) B1556939
theorem B4742003 : Blo 726324 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B3497003 : Blo 726324 3497003 := bstep (se 1 (by rfl) ⟨2622752, by rfl⟩ : syracuseStep 3497003 = 5245505) B5245505
theorem B3693761 : Blo 726324 3693761 := bstep (se 2 (by rfl) ⟨1385160, by rfl⟩ : syracuseStep 3693761 = 2770321) B2770321
theorem B14179643 : Blo 726324 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B3792413 : Blo 726324 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B778555 : Blo 726324 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B3695057 : Blo 726324 3695057 := bstep (se 2 (by rfl) ⟨1385646, by rfl⟩ : syracuseStep 3695057 = 2771293) B2771293
theorem B3727901 : Blo 726324 3727901 := bstep (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) B1397963
theorem B4154435 : Blo 726324 4154435 := bstep (se 1 (by rfl) ⟨3115826, by rfl⟩ : syracuseStep 4154435 = 6231653) B6231653
theorem B5531165 : Blo 726324 5531165 := bstep (se 3 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 5531165 = 2074187) B2074187
theorem B3106619 : Blo 726324 3106619 := bstep (se 1 (by rfl) ⟨2329964, by rfl⟩ : syracuseStep 3106619 = 4659929) B4659929
theorem B4418059 : Blo 726324 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B3697163 : Blo 726324 3697163 := bstep (se 1 (by rfl) ⟨2772872, by rfl⟩ : syracuseStep 3697163 = 5545745) B5545745
theorem B4156211 : Blo 726324 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B12479321 : Blo 726324 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B2452409 : Blo 726324 2452409 := bstep (se 2 (by rfl) ⟨919653, by rfl⟩ : syracuseStep 2452409 = 1839307) B1839307
theorem B17493347 : Blo 726324 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B2453003 : Blo 726324 2453003 := bstep (se 1 (by rfl) ⟨1839752, by rfl⟩ : syracuseStep 2453003 = 3679505) B3679505
theorem B3108395 : Blo 726324 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B20967011 : Blo 726324 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B2453111 : Blo 726324 2453111 := bstep (se 1 (by rfl) ⟨1839833, by rfl⟩ : syracuseStep 2453111 = 3679667) B3679667
theorem B1437385 : Blo 726324 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B3501883 : Blo 726324 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B1109819 : Blo 726324 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B3927943 : Blo 726324 3927943 := bstep (se 1 (by rfl) ⟨2945957, by rfl⟩ : syracuseStep 3927943 = 5891915) B5891915
theorem B1634363 : Blo 726324 1634363 := bstep (se 1 (by rfl) ⟨1225772, by rfl⟩ : syracuseStep 1634363 = 2451545) B2451545
theorem B1634489 : Blo 726324 1634489 := bstep (se 2 (by rfl) ⟨612933, by rfl⟩ : syracuseStep 1634489 = 1225867) B1225867
theorem B2453705 : Blo 726324 2453705 := bstep (se 2 (by rfl) ⟨920139, by rfl⟩ : syracuseStep 2453705 = 1840279) B1840279
theorem B4157669 : Blo 726324 4157669 := bstep (se 4 (by rfl) ⟨389781, by rfl⟩ : syracuseStep 4157669 = 779563) B779563
theorem B1995155 : Blo 726324 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B1634831 : Blo 726324 1634831 := bstep (se 1 (by rfl) ⟨1226123, by rfl⟩ : syracuseStep 1634831 = 2452247) B2452247
theorem B1634849 : Blo 726324 1634849 := bstep (se 2 (by rfl) ⟨613068, by rfl⟩ : syracuseStep 1634849 = 1226137) B1226137
theorem B4158125 : Blo 726324 4158125 := bstep (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) B1559297
theorem B1635191 : Blo 726324 1635191 := bstep (se 1 (by rfl) ⟨1226393, by rfl⟩ : syracuseStep 1635191 = 2452787) B2452787
theorem B2454407 : Blo 726324 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B1635371 : Blo 726324 1635371 := bstep (se 1 (by rfl) ⟨1226528, by rfl⟩ : syracuseStep 1635371 = 2453057) B2453057
theorem B1995977 : Blo 726324 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B2454785 : Blo 726324 2454785 := bstep (se 2 (by rfl) ⟨920544, by rfl⟩ : syracuseStep 2454785 = 1841089) B1841089
theorem B4158809 : Blo 726324 4158809 := bstep (se 2 (by rfl) ⟨1559553, by rfl⟩ : syracuseStep 4158809 = 3119107) B3119107
theorem B1635731 : Blo 726324 1635731 := bstep (se 1 (by rfl) ⟨1226798, by rfl⟩ : syracuseStep 1635731 = 2453597) B2453597
theorem B1635785 : Blo 726324 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B3929629 : Blo 726324 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B2488009 : Blo 726324 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B6649573 : Blo 726324 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B5535539 : Blo 726324 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B3504019 : Blo 726324 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B817159 : Blo 726324 817159 := bstep (se 1 (by rfl) ⟨612869, by rfl⟩ : syracuseStep 817159 = 1225739) B1225739
theorem B7993367 : Blo 726324 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B2455595 : Blo 726324 2455595 := bstep (se 1 (by rfl) ⟨1841696, by rfl⟩ : syracuseStep 2455595 = 3683393) B3683393
theorem B1636487 : Blo 726324 1636487 := bstep (se 1 (by rfl) ⟨1227365, by rfl⟩ : syracuseStep 1636487 = 2454731) B2454731
theorem B817339 : Blo 726324 817339 := bstep (se 1 (by rfl) ⟨613004, by rfl⟩ : syracuseStep 817339 = 1226009) B1226009
theorem B1636667 : Blo 726324 1636667 := bstep (se 1 (by rfl) ⟨1227500, by rfl⟩ : syracuseStep 1636667 = 2455001) B2455001
theorem B1636793 : Blo 726324 1636793 := bstep (se 2 (by rfl) ⟨613797, by rfl⟩ : syracuseStep 1636793 = 1227595) B1227595
theorem B7469597 : Blo 726324 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B817807 : Blo 726324 817807 := bstep (se 1 (by rfl) ⟨613355, by rfl⟩ : syracuseStep 817807 = 1226711) B1226711
theorem B1637135 : Blo 726324 1637135 := bstep (se 1 (by rfl) ⟨1227851, by rfl⟩ : syracuseStep 1637135 = 2455703) B2455703
theorem B1637153 : Blo 726324 1637153 := bstep (se 2 (by rfl) ⟨613932, by rfl⟩ : syracuseStep 1637153 = 1227865) B1227865
theorem B7863155 : Blo 726324 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B3111965 : Blo 726324 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B9337943 : Blo 726324 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B1637495 : Blo 726324 1637495 := bstep (se 1 (by rfl) ⟨1228121, by rfl⟩ : syracuseStep 1637495 = 2456243) B2456243
theorem B818311 : Blo 726324 818311 := bstep (se 1 (by rfl) ⟨613733, by rfl⟩ : syracuseStep 818311 = 1227467) B1227467
theorem B1637675 : Blo 726324 1637675 := bstep (se 1 (by rfl) ⟨1228256, by rfl⟩ : syracuseStep 1637675 = 2456513) B2456513
theorem B818491 : Blo 726324 818491 := bstep (se 1 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 818491 = 1227737) B1227737
theorem B2456891 : Blo 726324 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B3112307 : Blo 726324 3112307 := bstep (se 1 (by rfl) ⟨2334230, by rfl⟩ : syracuseStep 3112307 = 4668461) B4668461
theorem B1473977 : Blo 726324 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B5242445 : Blo 726324 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B7011917 : Blo 726324 7011917 := bstep (se 3 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 7011917 = 2629469) B2629469
theorem B1638035 : Blo 726324 1638035 := bstep (se 1 (by rfl) ⟨1228526, by rfl⟩ : syracuseStep 1638035 = 2457053) B2457053
theorem B1638089 : Blo 726324 1638089 := bstep (se 2 (by rfl) ⟨614283, by rfl⟩ : syracuseStep 1638089 = 1228567) B1228567
theorem B2621165 : Blo 726324 2621165 := bstep (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) B982937
theorem B9961217 : Blo 726324 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B818959 : Blo 726324 818959 := bstep (se 1 (by rfl) ⟨614219, by rfl⟩ : syracuseStep 818959 = 1228439) B1228439
theorem B2457377 : Blo 726324 2457377 := bstep (se 2 (by rfl) ⟨921516, by rfl⟩ : syracuseStep 2457377 = 1843033) B1843033
theorem B5668879 : Blo 726324 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B1310843 : Blo 726324 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B1638647 : Blo 726324 1638647 := bstep (se 1 (by rfl) ⟨1228985, by rfl⟩ : syracuseStep 1638647 = 2457971) B2457971
theorem B2457917 : Blo 726324 2457917 := bstep (se 3 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 2457917 = 921719) B921719
theorem B2326927 : Blo 726324 2326927 := bstep (se 1 (by rfl) ⟨1745195, by rfl⟩ : syracuseStep 2326927 = 3490391) B3490391
theorem B1245659 : Blo 726324 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B3146249 : Blo 726324 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B819751 : Blo 726324 819751 := bstep (se 1 (by rfl) ⟨614813, by rfl⟩ : syracuseStep 819751 = 1229627) B1229627
theorem B29819609 : Blo 726324 29819609 := bstep (se 2 (by rfl) ⟨11182353, by rfl⟩ : syracuseStep 29819609 = 22364707) B22364707
theorem B1639241 : Blo 726324 1639241 := bstep (se 2 (by rfl) ⟨614715, by rfl⟩ : syracuseStep 1639241 = 1229431) B1229431
theorem B1246247 : Blo 726324 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B8881271 : Blo 726324 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B2458781 : Blo 726324 2458781 := bstep (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) B922043
theorem B18711971 : Blo 726324 18711971 := bstep (se 1 (by rfl) ⟨14033978, by rfl⟩ : syracuseStep 18711971 = 28067957) B28067957
theorem B1312183 : Blo 726324 1312183 := bstep (se 1 (by rfl) ⟨984137, by rfl⟩ : syracuseStep 1312183 = 1968275) B1968275
theorem B1640033 : Blo 726324 1640033 := bstep (se 2 (by rfl) ⟨615012, by rfl⟩ : syracuseStep 1640033 = 1230025) B1230025
theorem B2459321 : Blo 726324 2459321 := bstep (se 2 (by rfl) ⟨922245, by rfl⟩ : syracuseStep 2459321 = 1844491) B1844491
theorem B1640375 : Blo 726324 1640375 := bstep (se 1 (by rfl) ⟨1230281, by rfl⟩ : syracuseStep 1640375 = 2460563) B2460563
theorem B11798615 : Blo 726324 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B821371 : Blo 726324 821371 := bstep (se 1 (by rfl) ⟨616028, by rfl⟩ : syracuseStep 821371 = 1232057) B1232057
theorem B2459915 : Blo 726324 2459915 := bstep (se 1 (by rfl) ⟨1844936, by rfl⟩ : syracuseStep 2459915 = 3689873) B3689873
theorem B1640969 : Blo 726324 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B2460185 : Blo 726324 2460185 := bstep (se 2 (by rfl) ⟨922569, by rfl⟩ : syracuseStep 2460185 = 1845139) B1845139
theorem B789031 : Blo 726324 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B3115655 : Blo 726324 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B1641311 : Blo 726324 1641311 := bstep (se 1 (by rfl) ⟨1230983, by rfl⟩ : syracuseStep 1641311 = 2461967) B2461967
theorem B1379177 : Blo 726324 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B1051499 : Blo 726324 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B4656055 : Blo 726324 4656055 := bstep (se 1 (by rfl) ⟨3492041, by rfl⟩ : syracuseStep 4656055 = 6984083) B6984083
theorem B1641491 : Blo 726324 1641491 := bstep (se 1 (by rfl) ⟨1231118, by rfl⟩ : syracuseStep 1641491 = 2462237) B2462237
theorem B2624683 : Blo 726324 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B1871095 : Blo 726324 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B1641833 : Blo 726324 1641833 := bstep (se 2 (by rfl) ⟨615687, by rfl⟩ : syracuseStep 1641833 = 1231375) B1231375
theorem B921127 : Blo 726324 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B5312087 : Blo 726324 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B133107313 : Blo 726324 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B790139 : Blo 726324 790139 := bstep (se 1 (by rfl) ⟨592604, by rfl⟩ : syracuseStep 790139 = 1185209) B1185209
theorem B2461319 : Blo 726324 2461319 := bstep (se 1 (by rfl) ⟨1845989, by rfl⟩ : syracuseStep 2461319 = 3691979) B3691979
theorem B2461373 : Blo 726324 2461373 := bstep (se 3 (by rfl) ⟨461507, by rfl⟩ : syracuseStep 2461373 = 923015) B923015
theorem B2953027 : Blo 726324 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B2461535 : Blo 726324 2461535 := bstep (se 1 (by rfl) ⟨1846151, by rfl⟩ : syracuseStep 2461535 = 3692303) B3692303
theorem B921451 : Blo 726324 921451 := bstep (se 1 (by rfl) ⟨691088, by rfl⟩ : syracuseStep 921451 = 1382177) B1382177
theorem B1970027 : Blo 726324 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B1314721 : Blo 726324 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1642427 : Blo 726324 1642427 := bstep (se 1 (by rfl) ⟨1231820, by rfl⟩ : syracuseStep 1642427 = 2463641) B2463641
theorem B5312465 : Blo 726324 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B5607377 : Blo 726324 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B2461697 : Blo 726324 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B1642553 : Blo 726324 1642553 := bstep (se 2 (by rfl) ⟨615957, by rfl⟩ : syracuseStep 1642553 = 1231915) B1231915
theorem B4427891 : Blo 726324 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B1642895 : Blo 726324 1642895 := bstep (se 1 (by rfl) ⟨1232171, by rfl⟩ : syracuseStep 1642895 = 2464343) B2464343
theorem B2331335 : Blo 726324 2331335 := bstep (se 1 (by rfl) ⟨1748501, by rfl⟩ : syracuseStep 2331335 = 3497003) B3497003
theorem B1643219 : Blo 726324 1643219 := bstep (se 1 (by rfl) ⟨1232414, by rfl⟩ : syracuseStep 1643219 = 2464829) B2464829
theorem B2462507 : Blo 726324 2462507 := bstep (se 1 (by rfl) ⟨1846880, by rfl⟩ : syracuseStep 2462507 = 3693761) B3693761
theorem B1381303 : Blo 726324 1381303 := bstep (se 1 (by rfl) ⟨1035977, by rfl⟩ : syracuseStep 1381303 = 2071955) B2071955
theorem B6231005 : Blo 726324 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B2528275 : Blo 726324 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B11998259 : Blo 726324 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B2462777 : Blo 726324 2462777 := bstep (se 2 (by rfl) ⟨923541, by rfl⟩ : syracuseStep 2462777 = 1847083) B1847083
theorem B922747 : Blo 726324 922747 := bstep (se 1 (by rfl) ⟨692060, by rfl⟩ : syracuseStep 922747 = 1384121) B1384121
theorem B726351 : Blo 726324 726351 := bstep (se 1 (by rfl) ⟨544763, by rfl⟩ : syracuseStep 726351 = 1089527) B1089527
theorem B726367 : Blo 726324 726367 := bstep (se 1 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 726367 = 1089551) B1089551
theorem B726395 : Blo 726324 726395 := bstep (se 1 (by rfl) ⟨544796, by rfl⟩ : syracuseStep 726395 = 1089593) B1089593
theorem B2463101 : Blo 726324 2463101 := bstep (se 3 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 2463101 = 923663) B923663
theorem B726447 : Blo 726324 726447 := bstep (se 1 (by rfl) ⟨544835, by rfl⟩ : syracuseStep 726447 = 1089671) B1089671
theorem B726471 : Blo 726324 726471 := bstep (se 1 (by rfl) ⟨544853, by rfl⟩ : syracuseStep 726471 = 1089707) B1089707
theorem B726491 : Blo 726324 726491 := bstep (se 1 (by rfl) ⟨544868, by rfl⟩ : syracuseStep 726491 = 1089737) B1089737
theorem B1840603 : Blo 726324 1840603 := bstep (se 1 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 1840603 = 2760905) B2760905
theorem B726567 : Blo 726324 726567 := bstep (se 1 (by rfl) ⟨544925, by rfl⟩ : syracuseStep 726567 = 1089851) B1089851
theorem B726607 : Blo 726324 726607 := bstep (se 1 (by rfl) ⟨544955, by rfl⟩ : syracuseStep 726607 = 1089911) B1089911
theorem B726623 : Blo 726324 726623 := bstep (se 1 (by rfl) ⟨544967, by rfl⟩ : syracuseStep 726623 = 1089935) B1089935
theorem B726651 : Blo 726324 726651 := bstep (se 1 (by rfl) ⟨544988, by rfl⟩ : syracuseStep 726651 = 1089977) B1089977
theorem B2463371 : Blo 726324 2463371 := bstep (se 1 (by rfl) ⟨1847528, by rfl⟩ : syracuseStep 2463371 = 3695057) B3695057
theorem B726703 : Blo 726324 726703 := bstep (se 1 (by rfl) ⟨545027, by rfl⟩ : syracuseStep 726703 = 1090055) B1090055
theorem B2987705 : Blo 726324 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B726727 : Blo 726324 726727 := bstep (se 1 (by rfl) ⟨545045, by rfl⟩ : syracuseStep 726727 = 1090091) B1090091
theorem B4658903 : Blo 726324 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B726747 : Blo 726324 726747 := bstep (se 1 (by rfl) ⟨545060, by rfl⟩ : syracuseStep 726747 = 1090121) B1090121
theorem B726823 : Blo 726324 726823 := bstep (se 1 (by rfl) ⟨545117, by rfl⟩ : syracuseStep 726823 = 1090235) B1090235
theorem B726863 : Blo 726324 726863 := bstep (se 1 (by rfl) ⟨545147, by rfl⟩ : syracuseStep 726863 = 1090295) B1090295
theorem B726879 : Blo 726324 726879 := bstep (se 1 (by rfl) ⟨545159, by rfl⟩ : syracuseStep 726879 = 1090319) B1090319
theorem B726907 : Blo 726324 726907 := bstep (se 1 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 726907 = 1090361) B1090361
theorem B5248903 : Blo 726324 5248903 := bstep (se 1 (by rfl) ⟨3936677, by rfl⟩ : syracuseStep 5248903 = 7873355) B7873355
theorem B726959 : Blo 726324 726959 := bstep (se 1 (by rfl) ⟨545219, by rfl⟩ : syracuseStep 726959 = 1090439) B1090439
theorem B726983 : Blo 726324 726983 := bstep (se 1 (by rfl) ⟨545237, by rfl⟩ : syracuseStep 726983 = 1090475) B1090475
theorem B727003 : Blo 726324 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B2758657 : Blo 726324 2758657 := bstep (se 2 (by rfl) ⟨1034496, by rfl⟩ : syracuseStep 2758657 = 2068993) B2068993
theorem B727079 : Blo 726324 727079 := bstep (se 1 (by rfl) ⟨545309, by rfl⟩ : syracuseStep 727079 = 1090619) B1090619
theorem B727119 : Blo 726324 727119 := bstep (se 1 (by rfl) ⟨545339, by rfl⟩ : syracuseStep 727119 = 1090679) B1090679
theorem B1841231 : Blo 726324 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B727135 : Blo 726324 727135 := bstep (se 1 (by rfl) ⟨545351, by rfl⟩ : syracuseStep 727135 = 1090703) B1090703
theorem B727163 : Blo 726324 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B727215 : Blo 726324 727215 := bstep (se 1 (by rfl) ⟨545411, by rfl⟩ : syracuseStep 727215 = 1090823) B1090823
theorem B727239 : Blo 726324 727239 := bstep (se 1 (by rfl) ⟨545429, by rfl⟩ : syracuseStep 727239 = 1090859) B1090859
theorem B727259 : Blo 726324 727259 := bstep (se 1 (by rfl) ⟨545444, by rfl⟩ : syracuseStep 727259 = 1090889) B1090889
theorem B727335 : Blo 726324 727335 := bstep (se 1 (by rfl) ⟨545501, by rfl⟩ : syracuseStep 727335 = 1091003) B1091003
theorem B727375 : Blo 726324 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B727391 : Blo 726324 727391 := bstep (se 1 (by rfl) ⟨545543, by rfl⟩ : syracuseStep 727391 = 1091087) B1091087
theorem B1382761 : Blo 726324 1382761 := bstep (se 2 (by rfl) ⟨518535, by rfl⟩ : syracuseStep 1382761 = 1037071) B1037071
theorem B727419 : Blo 726324 727419 := bstep (se 1 (by rfl) ⟨545564, by rfl⟩ : syracuseStep 727419 = 1091129) B1091129
theorem B1776001 : Blo 726324 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B727471 : Blo 726324 727471 := bstep (se 1 (by rfl) ⟨545603, by rfl⟩ : syracuseStep 727471 = 1091207) B1091207
theorem B727495 : Blo 726324 727495 := bstep (se 1 (by rfl) ⟨545621, by rfl⟩ : syracuseStep 727495 = 1091243) B1091243
theorem B727515 : Blo 726324 727515 := bstep (se 1 (by rfl) ⟨545636, by rfl⟩ : syracuseStep 727515 = 1091273) B1091273
theorem B2464289 : Blo 726324 2464289 := bstep (se 2 (by rfl) ⟨924108, by rfl⟩ : syracuseStep 2464289 = 1848217) B1848217
theorem B2071079 : Blo 726324 2071079 := bstep (se 1 (by rfl) ⟨1553309, by rfl⟩ : syracuseStep 2071079 = 3106619) B3106619
theorem B727591 : Blo 726324 727591 := bstep (se 1 (by rfl) ⟨545693, by rfl⟩ : syracuseStep 727591 = 1091387) B1091387
theorem B727631 : Blo 726324 727631 := bstep (se 1 (by rfl) ⟨545723, by rfl⟩ : syracuseStep 727631 = 1091447) B1091447
theorem B727647 : Blo 726324 727647 := bstep (se 1 (by rfl) ⟨545735, by rfl⟩ : syracuseStep 727647 = 1091471) B1091471
theorem B727675 : Blo 726324 727675 := bstep (se 1 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 727675 = 1091513) B1091513
theorem B727727 : Blo 726324 727727 := bstep (se 1 (by rfl) ⟨545795, by rfl⟩ : syracuseStep 727727 = 1091591) B1091591
theorem B727751 : Blo 726324 727751 := bstep (se 1 (by rfl) ⟨545813, by rfl⟩ : syracuseStep 727751 = 1091627) B1091627
theorem B1841879 : Blo 726324 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B727771 : Blo 726324 727771 := bstep (se 1 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 727771 = 1091657) B1091657
theorem B2759417 : Blo 726324 2759417 := bstep (se 2 (by rfl) ⟨1034781, by rfl⟩ : syracuseStep 2759417 = 2069563) B2069563
theorem B2464505 : Blo 726324 2464505 := bstep (se 2 (by rfl) ⟨924189, by rfl⟩ : syracuseStep 2464505 = 1848379) B1848379
theorem B4266755 : Blo 726324 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B11803421 : Blo 726324 11803421 := bstep (se 3 (by rfl) ⟨2213141, by rfl⟩ : syracuseStep 11803421 = 4426283) B4426283
theorem B727847 : Blo 726324 727847 := bstep (se 1 (by rfl) ⟨545885, by rfl⟩ : syracuseStep 727847 = 1091771) B1091771
theorem B727887 : Blo 726324 727887 := bstep (se 1 (by rfl) ⟨545915, by rfl⟩ : syracuseStep 727887 = 1091831) B1091831
theorem B727903 : Blo 726324 727903 := bstep (se 1 (by rfl) ⟨545927, by rfl⟩ : syracuseStep 727903 = 1091855) B1091855
theorem B727931 : Blo 726324 727931 := bstep (se 1 (by rfl) ⟨545948, by rfl⟩ : syracuseStep 727931 = 1091897) B1091897
theorem B727983 : Blo 726324 727983 := bstep (se 1 (by rfl) ⟨545987, by rfl⟩ : syracuseStep 727983 = 1091975) B1091975
theorem B728007 : Blo 726324 728007 := bstep (se 1 (by rfl) ⟨546005, by rfl⟩ : syracuseStep 728007 = 1092011) B1092011
theorem B728027 : Blo 726324 728027 := bstep (se 1 (by rfl) ⟨546020, by rfl⟩ : syracuseStep 728027 = 1092041) B1092041
theorem B2464775 : Blo 726324 2464775 := bstep (se 1 (by rfl) ⟨1848581, by rfl⟩ : syracuseStep 2464775 = 3697163) B3697163
theorem B728103 : Blo 726324 728103 := bstep (se 1 (by rfl) ⟨546077, by rfl⟩ : syracuseStep 728103 = 1092155) B1092155
theorem B728143 : Blo 726324 728143 := bstep (se 1 (by rfl) ⟨546107, by rfl⟩ : syracuseStep 728143 = 1092215) B1092215
theorem B728159 : Blo 726324 728159 := bstep (se 1 (by rfl) ⟨546119, by rfl⟩ : syracuseStep 728159 = 1092239) B1092239
theorem B728187 : Blo 726324 728187 := bstep (se 1 (by rfl) ⟨546140, by rfl⟩ : syracuseStep 728187 = 1092281) B1092281
theorem B728239 : Blo 726324 728239 := bstep (se 1 (by rfl) ⟨546179, by rfl⟩ : syracuseStep 728239 = 1092359) B1092359
theorem B728263 : Blo 726324 728263 := bstep (se 1 (by rfl) ⟨546197, by rfl⟩ : syracuseStep 728263 = 1092395) B1092395
theorem B1383635 : Blo 726324 1383635 := bstep (se 1 (by rfl) ⟨1037726, by rfl⟩ : syracuseStep 1383635 = 2075453) B2075453
theorem B728283 : Blo 726324 728283 := bstep (se 1 (by rfl) ⟨546212, by rfl⟩ : syracuseStep 728283 = 1092425) B1092425
theorem B728359 : Blo 726324 728359 := bstep (se 1 (by rfl) ⟨546269, by rfl⟩ : syracuseStep 728359 = 1092539) B1092539
theorem B728399 : Blo 726324 728399 := bstep (se 1 (by rfl) ⟨546299, by rfl⟩ : syracuseStep 728399 = 1092599) B1092599
theorem B728415 : Blo 726324 728415 := bstep (se 1 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 728415 = 1092623) B1092623
theorem B728443 : Blo 726324 728443 := bstep (se 1 (by rfl) ⟨546332, by rfl⟩ : syracuseStep 728443 = 1092665) B1092665
theorem B728495 : Blo 726324 728495 := bstep (se 1 (by rfl) ⟨546371, by rfl⟩ : syracuseStep 728495 = 1092743) B1092743
theorem B728519 : Blo 726324 728519 := bstep (se 1 (by rfl) ⟨546389, by rfl⟩ : syracuseStep 728519 = 1092779) B1092779
theorem B728539 : Blo 726324 728539 := bstep (se 1 (by rfl) ⟨546404, by rfl⟩ : syracuseStep 728539 = 1092809) B1092809
theorem B728615 : Blo 726324 728615 := bstep (se 1 (by rfl) ⟨546461, by rfl⟩ : syracuseStep 728615 = 1092923) B1092923
theorem B728655 : Blo 726324 728655 := bstep (se 1 (by rfl) ⟨546491, by rfl⟩ : syracuseStep 728655 = 1092983) B1092983
theorem B728671 : Blo 726324 728671 := bstep (se 1 (by rfl) ⟨546503, by rfl⟩ : syracuseStep 728671 = 1093007) B1093007
theorem B3317345 : Blo 726324 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B728699 : Blo 726324 728699 := bstep (se 1 (by rfl) ⟨546524, by rfl⟩ : syracuseStep 728699 = 1093049) B1093049
theorem B728751 : Blo 726324 728751 := bstep (se 1 (by rfl) ⟨546563, by rfl⟩ : syracuseStep 728751 = 1093127) B1093127
theorem B3677885 : Blo 726324 3677885 := bstep (se 3 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 3677885 = 1379207) B1379207
theorem B2072263 : Blo 726324 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B728775 : Blo 726324 728775 := bstep (se 1 (by rfl) ⟨546581, by rfl⟩ : syracuseStep 728775 = 1093163) B1093163
theorem B728795 : Blo 726324 728795 := bstep (se 1 (by rfl) ⟨546596, by rfl⟩ : syracuseStep 728795 = 1093193) B1093193
theorem B728871 : Blo 726324 728871 := bstep (se 1 (by rfl) ⟨546653, by rfl⟩ : syracuseStep 728871 = 1093307) B1093307
theorem B1384265 : Blo 726324 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B728911 : Blo 726324 728911 := bstep (se 1 (by rfl) ⟨546683, by rfl⟩ : syracuseStep 728911 = 1093367) B1093367
theorem B3678047 : Blo 726324 3678047 := bstep (se 1 (by rfl) ⟨2758535, by rfl⟩ : syracuseStep 3678047 = 5517071) B5517071
theorem B728927 : Blo 726324 728927 := bstep (se 1 (by rfl) ⟨546695, by rfl⟩ : syracuseStep 728927 = 1093391) B1093391
theorem B728955 : Blo 726324 728955 := bstep (se 1 (by rfl) ⟨546716, by rfl⟩ : syracuseStep 728955 = 1093433) B1093433
theorem B729007 : Blo 726324 729007 := bstep (se 1 (by rfl) ⟨546755, by rfl⟩ : syracuseStep 729007 = 1093511) B1093511
theorem B6234043 : Blo 726324 6234043 := bstep (se 1 (by rfl) ⟨4675532, by rfl⟩ : syracuseStep 6234043 = 9351065) B9351065
theorem B729031 : Blo 726324 729031 := bstep (se 1 (by rfl) ⟨546773, by rfl⟩ : syracuseStep 729031 = 1093547) B1093547
theorem B729051 : Blo 726324 729051 := bstep (se 1 (by rfl) ⟨546788, by rfl⟩ : syracuseStep 729051 = 1093577) B1093577
theorem B1089545 : Blo 726324 1089545 := bstep (se 2 (by rfl) ⟨408579, by rfl⟩ : syracuseStep 1089545 = 817159) B817159
theorem B1089575 : Blo 726324 1089575 := bstep (se 1 (by rfl) ⟨817181, by rfl⟩ : syracuseStep 1089575 = 1634363) B1634363
theorem B729127 : Blo 726324 729127 := bstep (se 1 (by rfl) ⟨546845, by rfl⟩ : syracuseStep 729127 = 1093691) B1093691
theorem B729167 : Blo 726324 729167 := bstep (se 1 (by rfl) ⟨546875, by rfl⟩ : syracuseStep 729167 = 1093751) B1093751
theorem B729183 : Blo 726324 729183 := bstep (se 1 (by rfl) ⟨546887, by rfl⟩ : syracuseStep 729183 = 1093775) B1093775
theorem B1089659 : Blo 726324 1089659 := bstep (se 1 (by rfl) ⟨817244, by rfl⟩ : syracuseStep 1089659 = 1634489) B1634489
theorem B729211 : Blo 726324 729211 := bstep (se 1 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 729211 = 1093817) B1093817
theorem B2760875 : Blo 726324 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B729263 : Blo 726324 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B729287 : Blo 726324 729287 := bstep (se 1 (by rfl) ⟨546965, by rfl⟩ : syracuseStep 729287 = 1093931) B1093931
theorem B729307 : Blo 726324 729307 := bstep (se 1 (by rfl) ⟨546980, by rfl⟩ : syracuseStep 729307 = 1093961) B1093961
theorem B1089785 : Blo 726324 1089785 := bstep (se 2 (by rfl) ⟨408669, by rfl⟩ : syracuseStep 1089785 = 817339) B817339
theorem B729383 : Blo 726324 729383 := bstep (se 1 (by rfl) ⟨547037, by rfl⟩ : syracuseStep 729383 = 1094075) B1094075
theorem B729423 : Blo 726324 729423 := bstep (se 1 (by rfl) ⟨547067, by rfl⟩ : syracuseStep 729423 = 1094135) B1094135
theorem B1089887 : Blo 726324 1089887 := bstep (se 1 (by rfl) ⟨817415, by rfl⟩ : syracuseStep 1089887 = 1634831) B1634831
theorem B729439 : Blo 726324 729439 := bstep (se 1 (by rfl) ⟨547079, by rfl⟩ : syracuseStep 729439 = 1094159) B1094159
theorem B1089899 : Blo 726324 1089899 := bstep (se 1 (by rfl) ⟨817424, by rfl⟩ : syracuseStep 1089899 = 1634849) B1634849
theorem B729467 : Blo 726324 729467 := bstep (se 1 (by rfl) ⟨547100, by rfl⟩ : syracuseStep 729467 = 1094201) B1094201
theorem B729519 : Blo 726324 729519 := bstep (se 1 (by rfl) ⟨547139, by rfl⟩ : syracuseStep 729519 = 1094279) B1094279
theorem B729543 : Blo 726324 729543 := bstep (se 1 (by rfl) ⟨547157, by rfl⟩ : syracuseStep 729543 = 1094315) B1094315
theorem B729563 : Blo 726324 729563 := bstep (se 1 (by rfl) ⟨547172, by rfl⟩ : syracuseStep 729563 = 1094345) B1094345
theorem B729639 : Blo 726324 729639 := bstep (se 1 (by rfl) ⟨547229, by rfl⟩ : syracuseStep 729639 = 1094459) B1094459
theorem B1090127 : Blo 726324 1090127 := bstep (se 1 (by rfl) ⟨817595, by rfl⟩ : syracuseStep 1090127 = 1635191) B1635191
theorem B1385039 : Blo 726324 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B729679 : Blo 726324 729679 := bstep (se 1 (by rfl) ⟨547259, by rfl⟩ : syracuseStep 729679 = 1094519) B1094519
theorem B729695 : Blo 726324 729695 := bstep (se 1 (by rfl) ⟨547271, by rfl⟩ : syracuseStep 729695 = 1094543) B1094543
theorem B2073185 : Blo 726324 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B729723 : Blo 726324 729723 := bstep (se 1 (by rfl) ⟨547292, by rfl⟩ : syracuseStep 729723 = 1094585) B1094585
theorem B729775 : Blo 726324 729775 := bstep (se 1 (by rfl) ⟨547331, by rfl⟩ : syracuseStep 729775 = 1094663) B1094663
theorem B1090247 : Blo 726324 1090247 := bstep (se 1 (by rfl) ⟨817685, by rfl⟩ : syracuseStep 1090247 = 1635371) B1635371
theorem B729799 : Blo 726324 729799 := bstep (se 1 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 729799 = 1094699) B1094699
theorem B729819 : Blo 726324 729819 := bstep (se 1 (by rfl) ⟨547364, by rfl⟩ : syracuseStep 729819 = 1094729) B1094729
theorem B729895 : Blo 726324 729895 := bstep (se 1 (by rfl) ⟨547421, by rfl⟩ : syracuseStep 729895 = 1094843) B1094843
theorem B729935 : Blo 726324 729935 := bstep (se 1 (by rfl) ⟨547451, by rfl⟩ : syracuseStep 729935 = 1094903) B1094903
theorem B729951 : Blo 726324 729951 := bstep (se 1 (by rfl) ⟨547463, by rfl⟩ : syracuseStep 729951 = 1094927) B1094927
theorem B1090409 : Blo 726324 1090409 := bstep (se 2 (by rfl) ⟨408903, by rfl⟩ : syracuseStep 1090409 = 817807) B817807
theorem B729979 : Blo 726324 729979 := bstep (se 1 (by rfl) ⟨547484, by rfl⟩ : syracuseStep 729979 = 1094969) B1094969
theorem B730031 : Blo 726324 730031 := bstep (se 1 (by rfl) ⟨547523, by rfl⟩ : syracuseStep 730031 = 1095047) B1095047
theorem B1090487 : Blo 726324 1090487 := bstep (se 1 (by rfl) ⟨817865, by rfl⟩ : syracuseStep 1090487 = 1635731) B1635731
theorem B730055 : Blo 726324 730055 := bstep (se 1 (by rfl) ⟨547541, by rfl⟩ : syracuseStep 730055 = 1095083) B1095083
theorem B1090523 : Blo 726324 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B730075 : Blo 726324 730075 := bstep (se 1 (by rfl) ⟨547556, by rfl⟩ : syracuseStep 730075 = 1095113) B1095113
theorem B730151 : Blo 726324 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B730191 : Blo 726324 730191 := bstep (se 1 (by rfl) ⟨547643, by rfl⟩ : syracuseStep 730191 = 1095287) B1095287
theorem B730207 : Blo 726324 730207 := bstep (se 1 (by rfl) ⟨547655, by rfl⟩ : syracuseStep 730207 = 1095311) B1095311
theorem B730235 : Blo 726324 730235 := bstep (se 1 (by rfl) ⟨547676, by rfl⟩ : syracuseStep 730235 = 1095353) B1095353
theorem B730287 : Blo 726324 730287 := bstep (se 1 (by rfl) ⟨547715, by rfl⟩ : syracuseStep 730287 = 1095431) B1095431
theorem B730311 : Blo 726324 730311 := bstep (se 1 (by rfl) ⟨547733, by rfl⟩ : syracuseStep 730311 = 1095467) B1095467
theorem B1844471 : Blo 726324 1844471 := bstep (se 1 (by rfl) ⟨1383353, by rfl⟩ : syracuseStep 1844471 = 2766707) B2766707
theorem B2762045 : Blo 726324 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1090991 : Blo 726324 1090991 := bstep (se 1 (by rfl) ⟨818243, by rfl⟩ : syracuseStep 1090991 = 1636487) B1636487
theorem B1091081 : Blo 726324 1091081 := bstep (se 2 (by rfl) ⟨409155, by rfl⟩ : syracuseStep 1091081 = 818311) B818311
theorem B1091111 : Blo 726324 1091111 := bstep (se 1 (by rfl) ⟨818333, by rfl⟩ : syracuseStep 1091111 = 1636667) B1636667
theorem B1091195 : Blo 726324 1091195 := bstep (se 1 (by rfl) ⟨818396, by rfl⟩ : syracuseStep 1091195 = 1636793) B1636793
theorem B2762363 : Blo 726324 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B1091321 : Blo 726324 1091321 := bstep (se 2 (by rfl) ⟨409245, by rfl⟩ : syracuseStep 1091321 = 818491) B818491
theorem B1091423 : Blo 726324 1091423 := bstep (se 1 (by rfl) ⟨818567, by rfl⟩ : syracuseStep 1091423 = 1637135) B1637135
theorem B1091435 : Blo 726324 1091435 := bstep (se 1 (by rfl) ⟨818576, by rfl⟩ : syracuseStep 1091435 = 1637153) B1637153
theorem B6989773 : Blo 726324 6989773 := bstep (se 3 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 6989773 = 2621165) B2621165
theorem B7874567 : Blo 726324 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B2074643 : Blo 726324 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B1091663 : Blo 726324 1091663 := bstep (se 1 (by rfl) ⟨818747, by rfl⟩ : syracuseStep 1091663 = 1637495) B1637495
theorem B2631833 : Blo 726324 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B2959517 : Blo 726324 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B1091783 : Blo 726324 1091783 := bstep (se 1 (by rfl) ⟨818837, by rfl⟩ : syracuseStep 1091783 = 1637675) B1637675
theorem B2074871 : Blo 726324 2074871 := bstep (se 1 (by rfl) ⟨1556153, by rfl⟩ : syracuseStep 2074871 = 3112307) B3112307
theorem B1091945 : Blo 726324 1091945 := bstep (se 2 (by rfl) ⟨409479, by rfl⟩ : syracuseStep 1091945 = 818959) B818959
theorem B1092023 : Blo 726324 1092023 := bstep (se 1 (by rfl) ⟨819017, by rfl⟩ : syracuseStep 1092023 = 1638035) B1638035
theorem B1092059 : Blo 726324 1092059 := bstep (se 1 (by rfl) ⟨819044, by rfl⟩ : syracuseStep 1092059 = 1638089) B1638089
theorem B3680801 : Blo 726324 3680801 := bstep (se 2 (by rfl) ⟨1380300, by rfl⟩ : syracuseStep 3680801 = 2760601) B2760601
theorem B1845899 : Blo 726324 1845899 := bstep (se 1 (by rfl) ⟨1384424, by rfl⟩ : syracuseStep 1845899 = 2768849) B2768849
theorem B1846111 : Blo 726324 1846111 := bstep (se 1 (by rfl) ⟨1384583, by rfl⟩ : syracuseStep 1846111 = 2769167) B2769167
theorem B1092527 : Blo 726324 1092527 := bstep (se 1 (by rfl) ⟨819395, by rfl⟩ : syracuseStep 1092527 = 1638791) B1638791
theorem B1092617 : Blo 726324 1092617 := bstep (se 2 (by rfl) ⟨409731, by rfl⟩ : syracuseStep 1092617 = 819463) B819463
theorem B2763791 : Blo 726324 2763791 := bstep (se 1 (by rfl) ⟨2072843, by rfl⟩ : syracuseStep 2763791 = 4145687) B4145687
theorem B1616915 : Blo 726324 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1092647 : Blo 726324 1092647 := bstep (se 1 (by rfl) ⟨819485, by rfl⟩ : syracuseStep 1092647 = 1638971) B1638971
theorem B1092731 : Blo 726324 1092731 := bstep (se 1 (by rfl) ⟨819548, by rfl⟩ : syracuseStep 1092731 = 1639097) B1639097
theorem B1092857 : Blo 726324 1092857 := bstep (se 2 (by rfl) ⟨409821, by rfl⟩ : syracuseStep 1092857 = 819643) B819643
theorem B1092959 : Blo 726324 1092959 := bstep (se 1 (by rfl) ⟨819719, by rfl⟩ : syracuseStep 1092959 = 1639439) B1639439
theorem B1092971 : Blo 726324 1092971 := bstep (se 1 (by rfl) ⟨819728, by rfl⟩ : syracuseStep 1092971 = 1639457) B1639457
theorem B1093199 : Blo 726324 1093199 := bstep (se 1 (by rfl) ⟨819899, by rfl⟩ : syracuseStep 1093199 = 1639799) B1639799
theorem B2076283 : Blo 726324 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B1093319 : Blo 726324 1093319 := bstep (se 1 (by rfl) ⟨819989, by rfl⟩ : syracuseStep 1093319 = 1639979) B1639979
theorem B2797267 : Blo 726324 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B4665053 : Blo 726324 4665053 := bstep (se 3 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 4665053 = 1749395) B1749395
theorem B1847033 : Blo 726324 1847033 := bstep (se 2 (by rfl) ⟨692637, by rfl⟩ : syracuseStep 1847033 = 1385275) B1385275
theorem B2076511 : Blo 726324 2076511 := bstep (se 1 (by rfl) ⟨1557383, by rfl⟩ : syracuseStep 2076511 = 3114767) B3114767
theorem B1093481 : Blo 726324 1093481 := bstep (se 2 (by rfl) ⟨410055, by rfl⟩ : syracuseStep 1093481 = 820111) B820111
theorem B3321719 : Blo 726324 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B1093559 : Blo 726324 1093559 := bstep (se 1 (by rfl) ⟨820169, by rfl⟩ : syracuseStep 1093559 = 1640339) B1640339
theorem B1093595 : Blo 726324 1093595 := bstep (se 1 (by rfl) ⟨820196, by rfl⟩ : syracuseStep 1093595 = 1640393) B1640393
theorem B9941069 : Blo 726324 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B1552463 : Blo 726324 1552463 := bstep (se 1 (by rfl) ⟨1164347, by rfl⟩ : syracuseStep 1552463 = 2328695) B2328695
theorem B2338895 : Blo 726324 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B1847681 : Blo 726324 1847681 := bstep (se 2 (by rfl) ⟨692880, by rfl⟩ : syracuseStep 1847681 = 1385761) B1385761
theorem B1094063 : Blo 726324 1094063 := bstep (se 1 (by rfl) ⟨820547, by rfl⟩ : syracuseStep 1094063 = 1641095) B1641095
theorem B1094153 : Blo 726324 1094153 := bstep (se 2 (by rfl) ⟨410307, by rfl⟩ : syracuseStep 1094153 = 820615) B820615
theorem B1094183 : Blo 726324 1094183 := bstep (se 1 (by rfl) ⟨820637, by rfl⟩ : syracuseStep 1094183 = 1641275) B1641275
theorem B1094267 : Blo 726324 1094267 := bstep (se 1 (by rfl) ⟨820700, by rfl⟩ : syracuseStep 1094267 = 1641401) B1641401
theorem B2765447 : Blo 726324 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B1749703 : Blo 726324 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B1094393 : Blo 726324 1094393 := bstep (se 2 (by rfl) ⟨410397, by rfl⟩ : syracuseStep 1094393 = 820795) B820795
theorem B1094495 : Blo 726324 1094495 := bstep (se 1 (by rfl) ⟨820871, by rfl⟩ : syracuseStep 1094495 = 1641743) B1641743
theorem B1094507 : Blo 726324 1094507 := bstep (se 1 (by rfl) ⟨820880, by rfl⟩ : syracuseStep 1094507 = 1641761) B1641761
theorem B1094735 : Blo 726324 1094735 := bstep (se 1 (by rfl) ⟨821051, by rfl⟩ : syracuseStep 1094735 = 1642103) B1642103
theorem B1848491 : Blo 726324 1848491 := bstep (se 1 (by rfl) ⟨1386368, by rfl⟩ : syracuseStep 1848491 = 2772737) B2772737
theorem B5518529 : Blo 726324 5518529 := bstep (se 2 (by rfl) ⟨2069448, by rfl⟩ : syracuseStep 5518529 = 4138897) B4138897
theorem B4994243 : Blo 726324 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B1094855 : Blo 726324 1094855 := bstep (se 1 (by rfl) ⟨821141, by rfl⟩ : syracuseStep 1094855 = 1642283) B1642283
theorem B1225975 : Blo 726324 1225975 := bstep (se 1 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 1225975 = 1838963) B1838963
theorem B1095017 : Blo 726324 1095017 := bstep (se 2 (by rfl) ⟨410631, by rfl⟩ : syracuseStep 1095017 = 821263) B821263
theorem B2078095 : Blo 726324 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B1095095 : Blo 726324 1095095 := bstep (se 1 (by rfl) ⟨821321, by rfl⟩ : syracuseStep 1095095 = 1642643) B1642643
theorem B1226171 : Blo 726324 1226171 := bstep (se 1 (by rfl) ⟨919628, by rfl⟩ : syracuseStep 1226171 = 1839257) B1839257
theorem B1095131 : Blo 726324 1095131 := bstep (se 1 (by rfl) ⟨821348, by rfl⟩ : syracuseStep 1095131 = 1642697) B1642697
theorem B1226279 : Blo 726324 1226279 := bstep (se 1 (by rfl) ⟨919709, by rfl⟩ : syracuseStep 1226279 = 1839419) B1839419
theorem B3683879 : Blo 726324 3683879 := bstep (se 1 (by rfl) ⟨2762909, by rfl⟩ : syracuseStep 3683879 = 5525819) B5525819
theorem B2766433 : Blo 726324 2766433 := bstep (se 2 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 2766433 = 2074825) B2074825
theorem B26621621 : Blo 726324 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B4667179 : Blo 726324 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B1226569 : Blo 726324 1226569 := bstep (se 2 (by rfl) ⟨459963, by rfl⟩ : syracuseStep 1226569 = 919927) B919927
theorem B1226603 : Blo 726324 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B9353069 : Blo 726324 9353069 := bstep (se 3 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 9353069 = 3507401) B3507401
theorem B2766905 : Blo 726324 2766905 := bstep (se 2 (by rfl) ⟨1037589, by rfl⟩ : syracuseStep 2766905 = 2075179) B2075179
theorem B1227001 : Blo 726324 1227001 := bstep (se 2 (by rfl) ⟨460125, by rfl⟩ : syracuseStep 1227001 = 920251) B920251
theorem B11188631 : Blo 726324 11188631 := bstep (se 1 (by rfl) ⟨8391473, by rfl⟩ : syracuseStep 11188631 = 16782947) B16782947
theorem B15350219 : Blo 726324 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B2800115 : Blo 726324 2800115 := bstep (se 1 (by rfl) ⟨2100086, by rfl⟩ : syracuseStep 2800115 = 4200173) B4200173
theorem B1227271 : Blo 726324 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B2079371 : Blo 726324 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B4438739 : Blo 726324 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B1915607 : Blo 726324 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B1227703 : Blo 726324 1227703 := bstep (se 1 (by rfl) ⟨920777, by rfl⟩ : syracuseStep 1227703 = 1841555) B1841555
theorem B2767891 : Blo 726324 2767891 := bstep (se 1 (by rfl) ⟨2075918, by rfl⟩ : syracuseStep 2767891 = 4151837) B4151837
theorem B1227899 : Blo 726324 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1228297 : Blo 726324 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B9453095 : Blo 726324 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1916513 : Blo 726324 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B3685985 : Blo 726324 3685985 := bstep (se 2 (by rfl) ⟨1382244, by rfl⟩ : syracuseStep 3685985 = 2764489) B2764489
theorem B1228459 : Blo 726324 1228459 := bstep (se 1 (by rfl) ⟨921344, by rfl⟩ : syracuseStep 1228459 = 1842689) B1842689
theorem B1752787 : Blo 726324 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B4669177 : Blo 726324 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B2211745 : Blo 726324 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B1228763 : Blo 726324 1228763 := bstep (se 1 (by rfl) ⟨921572, by rfl⟩ : syracuseStep 1228763 = 1843145) B1843145
theorem B5521445 : Blo 726324 5521445 := bstep (se 4 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 5521445 = 1035271) B1035271
theorem B1228999 : Blo 726324 1228999 := bstep (se 1 (by rfl) ⟨921749, by rfl⟩ : syracuseStep 1228999 = 1843499) B1843499
theorem B8274149 : Blo 726324 8274149 := bstep (se 4 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 8274149 = 1551403) B1551403
theorem B1229161 : Blo 726324 1229161 := bstep (se 2 (by rfl) ⟨460935, by rfl⟩ : syracuseStep 1229161 = 921871) B921871
theorem B2212339 : Blo 726324 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1753625 : Blo 726324 1753625 := bstep (se 2 (by rfl) ⟨657609, by rfl⟩ : syracuseStep 1753625 = 1315219) B1315219
theorem B2769623 : Blo 726324 2769623 := bstep (se 1 (by rfl) ⟨2077217, by rfl⟩ : syracuseStep 2769623 = 4154435) B4154435
theorem B22430465 : Blo 726324 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B1229755 : Blo 726324 1229755 := bstep (se 1 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 1229755 = 1844633) B1844633
theorem B3687443 : Blo 726324 3687443 := bstep (se 1 (by rfl) ⟨2765582, by rfl⟩ : syracuseStep 3687443 = 5531165) B5531165
theorem B1229863 : Blo 726324 1229863 := bstep (se 1 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 1229863 = 1844795) B1844795
theorem B2213021 : Blo 726324 2213021 := bstep (se 3 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 2213021 = 829883) B829883
theorem B1230187 : Blo 726324 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B1558025 : Blo 726324 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B5260897 : Blo 726324 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B2770807 : Blo 726324 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B5130497 : Blo 726324 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B8866097 : Blo 726324 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B1231247 : Blo 726324 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B13978007 : Blo 726324 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B4672025 : Blo 726324 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B3983905 : Blo 726324 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B1231483 : Blo 726324 1231483 := bstep (se 1 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 1231483 = 1847225) B1847225
theorem B2771779 : Blo 726324 2771779 := bstep (se 1 (by rfl) ⟨2078834, by rfl⟩ : syracuseStep 2771779 = 4157669) B4157669
theorem B1330103 : Blo 726324 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B2772083 : Blo 726324 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B5328293 : Blo 726324 5328293 := bstep (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) B999055
theorem B1330651 : Blo 726324 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B1232347 : Blo 726324 1232347 := bstep (se 1 (by rfl) ⟨924260, by rfl⟩ : syracuseStep 1232347 = 1848521) B1848521
theorem B2772539 : Blo 726324 2772539 := bstep (se 1 (by rfl) ⟨2079404, by rfl⟩ : syracuseStep 2772539 = 4158809) B4158809
theorem B3690359 : Blo 726324 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B5328911 : Blo 726324 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B1495675 : Blo 726324 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B10769165 : Blo 726324 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B3494963 : Blo 726324 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B4674611 : Blo 726324 4674611 := bstep (se 1 (by rfl) ⟨3505958, by rfl⟩ : syracuseStep 4674611 = 7011917) B7011917
theorem B6640811 : Blo 726324 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B1037863 : Blo 726324 1037863 := bstep (se 1 (by rfl) ⟨778397, by rfl⟩ : syracuseStep 1037863 = 1556795) B1556795
theorem B5527277 : Blo 726324 5527277 := bstep (se 3 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 5527277 = 2072729) B2072729
theorem B10639163 : Blo 726324 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B1038187 : Blo 726324 1038187 := bstep (se 1 (by rfl) ⟨778640, by rfl⟩ : syracuseStep 1038187 = 1557281) B1557281
theorem B1038415 : Blo 726324 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B9984647 : Blo 726324 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B5528249 : Blo 726324 5528249 := bstep (se 2 (by rfl) ⟨2073093, by rfl⟩ : syracuseStep 5528249 = 4146187) B4146187
theorem B4152019 : Blo 726324 4152019 := bstep (se 1 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 4152019 = 6228029) B6228029
theorem B3496733 : Blo 726324 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B4152293 : Blo 726324 4152293 := bstep (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) B778555
theorem B4742297 : Blo 726324 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B3104243 : Blo 726324 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B5529221 : Blo 726324 5529221 := bstep (se 4 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 5529221 = 1036729) B1036729
theorem B4152977 : Blo 726324 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B6217505 : Blo 726324 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B7463447 : Blo 726324 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B5890745 : Blo 726324 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B8282897 : Blo 726324 8282897 := bstep (se 2 (by rfl) ⟨3106086, by rfl⟩ : syracuseStep 8282897 = 6212173) B6212173
theorem B3695543 : Blo 726324 3695543 := bstep (se 1 (by rfl) ⟨2771657, by rfl⟩ : syracuseStep 3695543 = 5543315) B5543315
theorem B5334083 : Blo 726324 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B13297097 : Blo 726324 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B2451383 : Blo 726324 2451383 := bstep (se 1 (by rfl) ⟨1838537, by rfl⟩ : syracuseStep 2451383 = 3677075) B3677075
theorem B5531651 : Blo 726324 5531651 := bstep (se 1 (by rfl) ⟨4148738, by rfl⟩ : syracuseStep 5531651 = 8297477) B8297477
theorem B3697001 : Blo 726324 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B2451977 : Blo 726324 2451977 := bstep (se 2 (by rfl) ⟨919491, by rfl⟩ : syracuseStep 2451977 = 1838983) B1838983
theorem B5237257 : Blo 726324 5237257 := bstep (se 2 (by rfl) ⟨1963971, by rfl⟩ : syracuseStep 5237257 = 3927943) B3927943
theorem B6384529 : Blo 726324 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B3501251 : Blo 726324 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B2452841 : Blo 726324 2452841 := bstep (se 2 (by rfl) ⟨919815, by rfl⟩ : syracuseStep 2452841 = 1839631) B1839631
theorem B11825027 : Blo 726324 11825027 := bstep (se 1 (by rfl) ⟨8868770, by rfl⟩ : syracuseStep 11825027 = 17737541) B17737541
theorem B2453435 : Blo 726324 2453435 := bstep (se 1 (by rfl) ⟨1840076, by rfl⟩ : syracuseStep 2453435 = 3680153) B3680153
theorem B5534081 : Blo 726324 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B8319547 : Blo 726324 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B1634939 : Blo 726324 1634939 := bstep (se 1 (by rfl) ⟨1226204, by rfl⟩ : syracuseStep 1634939 = 2452409) B2452409
theorem B5239505 : Blo 726324 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B1635065 : Blo 726324 1635065 := bstep (se 2 (by rfl) ⟨613149, by rfl⟩ : syracuseStep 1635065 = 1226299) B1226299
theorem B11662231 : Blo 726324 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B12645341 : Blo 726324 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B1635335 : Blo 726324 1635335 := bstep (se 1 (by rfl) ⟨1226501, by rfl⟩ : syracuseStep 1635335 = 2453003) B2453003
theorem B1635407 : Blo 726324 1635407 := bstep (se 1 (by rfl) ⟨1226555, by rfl⟩ : syracuseStep 1635407 = 2453111) B2453111
theorem B1635803 : Blo 726324 1635803 := bstep (se 1 (by rfl) ⟨1226852, by rfl⟩ : syracuseStep 1635803 = 2453705) B2453705
theorem B2455163 : Blo 726324 2455163 := bstep (se 1 (by rfl) ⟨1841372, by rfl⟩ : syracuseStep 2455163 = 3682745) B3682745
theorem B2455325 : Blo 726324 2455325 := bstep (se 3 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 2455325 = 920747) B920747
theorem B1636271 : Blo 726324 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B817231 : Blo 726324 817231 := bstep (se 1 (by rfl) ⟨612923, by rfl⟩ : syracuseStep 817231 = 1225847) B1225847
theorem B3110993 : Blo 726324 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B1636523 : Blo 726324 1636523 := bstep (se 1 (by rfl) ⟨1227392, by rfl⟩ : syracuseStep 1636523 = 2454785) B2454785
theorem B817627 : Blo 726324 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B2456027 : Blo 726324 2456027 := bstep (se 1 (by rfl) ⟨1842020, by rfl⟩ : syracuseStep 2456027 = 3684041) B3684041
theorem B3930605 : Blo 726324 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B1637063 : Blo 726324 1637063 := bstep (se 1 (by rfl) ⟨1227797, by rfl⟩ : syracuseStep 1637063 = 2455595) B2455595
theorem B818095 : Blo 726324 818095 := bstep (se 1 (by rfl) ⟨613571, by rfl⟩ : syracuseStep 818095 = 1227143) B1227143
theorem B3505153 : Blo 726324 3505153 := bstep (se 2 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 3505153 = 2628865) B2628865
theorem B4979731 : Blo 726324 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B2456729 : Blo 726324 2456729 := bstep (se 2 (by rfl) ⟨921273, by rfl⟩ : syracuseStep 2456729 = 1842547) B1842547
theorem B5242103 : Blo 726324 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B818527 : Blo 726324 818527 := bstep (se 1 (by rfl) ⟨613895, by rfl⟩ : syracuseStep 818527 = 1227791) B1227791
theorem B6225295 : Blo 726324 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B1637927 : Blo 726324 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B10518103 : Blo 726324 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B818887 : Blo 726324 818887 := bstep (se 1 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 818887 = 1228331) B1228331
theorem B1638251 : Blo 726324 1638251 := bstep (se 1 (by rfl) ⟨1228688, by rfl⟩ : syracuseStep 1638251 = 2457377) B2457377
theorem B1638305 : Blo 726324 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B26509517 : Blo 726324 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B1638611 : Blo 726324 1638611 := bstep (se 1 (by rfl) ⟨1228958, by rfl⟩ : syracuseStep 1638611 = 2457917) B2457917
theorem B1638665 : Blo 726324 1638665 := bstep (se 2 (by rfl) ⟨614499, by rfl⟩ : syracuseStep 1638665 = 1228999) B1228999
theorem B2097499 : Blo 726324 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B1638881 : Blo 726324 1638881 := bstep (se 2 (by rfl) ⟨614580, by rfl⟩ : syracuseStep 1638881 = 1229161) B1229161
theorem B2949785 : Blo 726324 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B2458295 : Blo 726324 2458295 := bstep (se 1 (by rfl) ⟨1843721, by rfl⟩ : syracuseStep 2458295 = 3687443) B3687443
theorem B1475347 : Blo 726324 1475347 := bstep (se 1 (by rfl) ⟨1106510, by rfl⟩ : syracuseStep 1475347 = 2213021) B2213021
theorem B1639187 : Blo 726324 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B1639547 : Blo 726324 1639547 := bstep (se 1 (by rfl) ⟨1229660, by rfl⟩ : syracuseStep 1639547 = 2459321) B2459321
theorem B1639673 : Blo 726324 1639673 := bstep (se 2 (by rfl) ⟨614877, by rfl⟩ : syracuseStep 1639673 = 1229755) B1229755
theorem B1639817 : Blo 726324 1639817 := bstep (se 2 (by rfl) ⟨614931, by rfl⟩ : syracuseStep 1639817 = 1229863) B1229863
theorem B7865743 : Blo 726324 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B1639943 : Blo 726324 1639943 := bstep (se 1 (by rfl) ⟨1229957, by rfl⟩ : syracuseStep 1639943 = 2459915) B2459915
theorem B820831 : Blo 726324 820831 := bstep (se 1 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 820831 = 1231247) B1231247
theorem B1640123 : Blo 726324 1640123 := bstep (se 1 (by rfl) ⟨1230092, by rfl⟩ : syracuseStep 1640123 = 2460185) B2460185
theorem B3114683 : Blo 726324 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B1640249 : Blo 726324 1640249 := bstep (se 2 (by rfl) ⟨615093, by rfl⟩ : syracuseStep 1640249 = 1230187) B1230187
theorem B919451 : Blo 726324 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B886735 : Blo 726324 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B7014529 : Blo 726324 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B3541391 : Blo 726324 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B1640879 : Blo 726324 1640879 := bstep (se 1 (by rfl) ⟨1230659, by rfl⟩ : syracuseStep 1640879 = 2461319) B2461319
theorem B1640915 : Blo 726324 1640915 := bstep (se 1 (by rfl) ⟨1230686, by rfl⟩ : syracuseStep 1640915 = 2461373) B2461373
theorem B1641023 : Blo 726324 1641023 := bstep (se 1 (by rfl) ⟨1230767, by rfl⟩ : syracuseStep 1641023 = 2461535) B2461535
theorem B1313351 : Blo 726324 1313351 := bstep (se 1 (by rfl) ⟨985013, by rfl⟩ : syracuseStep 1313351 = 1970027) B1970027
theorem B2460239 : Blo 726324 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B3541643 : Blo 726324 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B3738251 : Blo 726324 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B1641131 : Blo 726324 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B2951927 : Blo 726324 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B7179443 : Blo 726324 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B1641671 : Blo 726324 1641671 := bstep (se 1 (by rfl) ⟨1231253, by rfl⟩ : syracuseStep 1641671 = 2462507) B2462507
theorem B6983009 : Blo 726324 6983009 := bstep (se 2 (by rfl) ⟨2618628, by rfl⟩ : syracuseStep 6983009 = 5237257) B5237257
theorem B2329975 : Blo 726324 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B3116407 : Blo 726324 3116407 := bstep (se 1 (by rfl) ⟨2337305, by rfl⟩ : syracuseStep 3116407 = 4674611) B4674611
theorem B7998839 : Blo 726324 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B1641851 : Blo 726324 1641851 := bstep (se 1 (by rfl) ⟨1231388, by rfl⟩ : syracuseStep 1641851 = 2462777) B2462777
theorem B5311873 : Blo 726324 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B1052041 : Blo 726324 1052041 := bstep (se 2 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 1052041 = 789031) B789031
theorem B4427207 : Blo 726324 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B1641977 : Blo 726324 1641977 := bstep (se 2 (by rfl) ⟨615741, by rfl⟩ : syracuseStep 1641977 = 1231483) B1231483
theorem B1642067 : Blo 726324 1642067 := bstep (se 1 (by rfl) ⟨1231550, by rfl⟩ : syracuseStep 1642067 = 2463101) B2463101
theorem B1642247 : Blo 726324 1642247 := bstep (se 1 (by rfl) ⟨1231685, by rfl⟩ : syracuseStep 1642247 = 2463371) B2463371
theorem B2461481 : Blo 726324 2461481 := bstep (se 2 (by rfl) ⟨923055, by rfl⟩ : syracuseStep 2461481 = 1846111) B1846111
theorem B2494793 : Blo 726324 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B1642859 : Blo 726324 1642859 := bstep (se 1 (by rfl) ⟨1232144, by rfl⟩ : syracuseStep 1642859 = 2464289) B2464289
theorem B1380719 : Blo 726324 1380719 := bstep (se 1 (by rfl) ⟨1035539, by rfl⟩ : syracuseStep 1380719 = 2071079) B2071079
theorem B6656431 : Blo 726324 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B1839611 : Blo 726324 1839611 := bstep (se 1 (by rfl) ⟨1379708, by rfl⟩ : syracuseStep 1839611 = 2759417) B2759417
theorem B1643003 : Blo 726324 1643003 := bstep (se 1 (by rfl) ⟨1232252, by rfl⟩ : syracuseStep 1643003 = 2464505) B2464505
theorem B2331155 : Blo 726324 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B7868947 : Blo 726324 7868947 := bstep (se 1 (by rfl) ⟨5901710, by rfl⟩ : syracuseStep 7868947 = 11803421) B11803421
theorem B1643129 : Blo 726324 1643129 := bstep (se 2 (by rfl) ⟨616173, by rfl⟩ : syracuseStep 1643129 = 1232347) B1232347
theorem B1643183 : Blo 726324 1643183 := bstep (se 1 (by rfl) ⟨1232387, by rfl⟩ : syracuseStep 1643183 = 2464775) B2464775
theorem B922423 : Blo 726324 922423 := bstep (se 1 (by rfl) ⟨691817, by rfl⟩ : syracuseStep 922423 = 1383635) B1383635
theorem B177476417 : Blo 726324 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B2069495 : Blo 726324 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B922843 : Blo 726324 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B726363 : Blo 726324 726363 := bstep (se 1 (by rfl) ⟨544772, by rfl⟩ : syracuseStep 726363 = 1089545) B1089545
theorem B726383 : Blo 726324 726383 := bstep (se 1 (by rfl) ⟨544787, by rfl⟩ : syracuseStep 726383 = 1089575) B1089575
theorem B726439 : Blo 726324 726439 := bstep (se 1 (by rfl) ⟨544829, by rfl⟩ : syracuseStep 726439 = 1089659) B1089659
theorem B1840583 : Blo 726324 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B726523 : Blo 726324 726523 := bstep (se 1 (by rfl) ⟨544892, by rfl⟩ : syracuseStep 726523 = 1089785) B1089785
theorem B726591 : Blo 726324 726591 := bstep (se 1 (by rfl) ⟨544943, by rfl⟩ : syracuseStep 726591 = 1089887) B1089887
theorem B726599 : Blo 726324 726599 := bstep (se 1 (by rfl) ⟨544949, by rfl⟩ : syracuseStep 726599 = 1089899) B1089899
theorem B726751 : Blo 726324 726751 := bstep (se 1 (by rfl) ⟨545063, by rfl⟩ : syracuseStep 726751 = 1090127) B1090127
theorem B1382123 : Blo 726324 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B726831 : Blo 726324 726831 := bstep (se 1 (by rfl) ⟨545123, by rfl⟩ : syracuseStep 726831 = 1090247) B1090247
theorem B726939 : Blo 726324 726939 := bstep (se 1 (by rfl) ⟨545204, by rfl⟩ : syracuseStep 726939 = 1090409) B1090409
theorem B726991 : Blo 726324 726991 := bstep (se 1 (by rfl) ⟨545243, by rfl⟩ : syracuseStep 726991 = 1090487) B1090487
theorem B2463695 : Blo 726324 2463695 := bstep (se 1 (by rfl) ⟨1847771, by rfl⟩ : syracuseStep 2463695 = 3695543) B3695543
theorem B727015 : Blo 726324 727015 := bstep (se 1 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 727015 = 1090523) B1090523
theorem B1841363 : Blo 726324 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B2332937 : Blo 726324 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B727327 : Blo 726324 727327 := bstep (se 1 (by rfl) ⟨545495, by rfl⟩ : syracuseStep 727327 = 1090991) B1090991
theorem B727387 : Blo 726324 727387 := bstep (se 1 (by rfl) ⟨545540, by rfl⟩ : syracuseStep 727387 = 1091081) B1091081
theorem B727407 : Blo 726324 727407 := bstep (se 1 (by rfl) ⟨545555, by rfl⟩ : syracuseStep 727407 = 1091111) B1091111
theorem B727463 : Blo 726324 727463 := bstep (se 1 (by rfl) ⟨545597, by rfl⟩ : syracuseStep 727463 = 1091195) B1091195
theorem B1841575 : Blo 726324 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B727547 : Blo 726324 727547 := bstep (se 1 (by rfl) ⟨545660, by rfl⟩ : syracuseStep 727547 = 1091321) B1091321
theorem B727615 : Blo 726324 727615 := bstep (se 1 (by rfl) ⟨545711, by rfl⟩ : syracuseStep 727615 = 1091423) B1091423
theorem B727623 : Blo 726324 727623 := bstep (se 1 (by rfl) ⟨545717, by rfl⟩ : syracuseStep 727623 = 1091435) B1091435
theorem B1841737 : Blo 726324 1841737 := bstep (se 2 (by rfl) ⟨690651, by rfl⟩ : syracuseStep 1841737 = 1381303) B1381303
theorem B5249711 : Blo 726324 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B1383095 : Blo 726324 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B727775 : Blo 726324 727775 := bstep (se 1 (by rfl) ⟨545831, by rfl⟩ : syracuseStep 727775 = 1091663) B1091663
theorem B1973011 : Blo 726324 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B727855 : Blo 726324 727855 := bstep (se 1 (by rfl) ⟨545891, by rfl⟩ : syracuseStep 727855 = 1091783) B1091783
theorem B1383247 : Blo 726324 1383247 := bstep (se 1 (by rfl) ⟨1037435, by rfl⟩ : syracuseStep 1383247 = 2074871) B2074871
theorem B727963 : Blo 726324 727963 := bstep (se 1 (by rfl) ⟨545972, by rfl⟩ : syracuseStep 727963 = 1091945) B1091945
theorem B2464667 : Blo 726324 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B728015 : Blo 726324 728015 := bstep (se 1 (by rfl) ⟨546011, by rfl⟩ : syracuseStep 728015 = 1092023) B1092023
theorem B728039 : Blo 726324 728039 := bstep (se 1 (by rfl) ⟨546029, by rfl⟩ : syracuseStep 728039 = 1092059) B1092059
theorem B11836637 : Blo 726324 11836637 := bstep (se 3 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 11836637 = 4438739) B4438739
theorem B728351 : Blo 726324 728351 := bstep (se 1 (by rfl) ⟨546263, by rfl⟩ : syracuseStep 728351 = 1092527) B1092527
theorem B728411 : Blo 726324 728411 := bstep (se 1 (by rfl) ⟨546308, by rfl⟩ : syracuseStep 728411 = 1092617) B1092617
theorem B1842527 : Blo 726324 1842527 := bstep (se 1 (by rfl) ⟨1381895, by rfl⟩ : syracuseStep 1842527 = 2763791) B2763791
theorem B728431 : Blo 726324 728431 := bstep (se 1 (by rfl) ⟨546323, by rfl⟩ : syracuseStep 728431 = 1092647) B1092647
theorem B1383817 : Blo 726324 1383817 := bstep (se 2 (by rfl) ⟨518931, by rfl⟩ : syracuseStep 1383817 = 1037863) B1037863
theorem B728487 : Blo 726324 728487 := bstep (se 1 (by rfl) ⟨546365, by rfl⟩ : syracuseStep 728487 = 1092731) B1092731
theorem B2334167 : Blo 726324 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B728571 : Blo 726324 728571 := bstep (se 1 (by rfl) ⟨546428, by rfl⟩ : syracuseStep 728571 = 1092857) B1092857
theorem B728639 : Blo 726324 728639 := bstep (se 1 (by rfl) ⟨546479, by rfl⟩ : syracuseStep 728639 = 1092959) B1092959
theorem B728647 : Blo 726324 728647 := bstep (se 1 (by rfl) ⟨546485, by rfl⟩ : syracuseStep 728647 = 1092971) B1092971
theorem B728799 : Blo 726324 728799 := bstep (se 1 (by rfl) ⟨546599, by rfl⟩ : syracuseStep 728799 = 1093199) B1093199
theorem B728879 : Blo 726324 728879 := bstep (se 1 (by rfl) ⟨546659, by rfl⟩ : syracuseStep 728879 = 1093319) B1093319
theorem B728987 : Blo 726324 728987 := bstep (se 1 (by rfl) ⟨546740, by rfl⟩ : syracuseStep 728987 = 1093481) B1093481
theorem B729039 : Blo 726324 729039 := bstep (se 1 (by rfl) ⟨546779, by rfl⟩ : syracuseStep 729039 = 1093559) B1093559
theorem B729063 : Blo 726324 729063 := bstep (se 1 (by rfl) ⟨546797, by rfl⟩ : syracuseStep 729063 = 1093595) B1093595
theorem B3678209 : Blo 726324 3678209 := bstep (se 2 (by rfl) ⟨1379328, by rfl⟩ : syracuseStep 3678209 = 2758657) B2758657
theorem B1089641 : Blo 726324 1089641 := bstep (se 2 (by rfl) ⟨408615, by rfl⟩ : syracuseStep 1089641 = 817231) B817231
theorem B1384553 : Blo 726324 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B729375 : Blo 726324 729375 := bstep (se 1 (by rfl) ⟨547031, by rfl⟩ : syracuseStep 729375 = 1094063) B1094063
theorem B729435 : Blo 726324 729435 := bstep (se 1 (by rfl) ⟨547076, by rfl⟩ : syracuseStep 729435 = 1094153) B1094153
theorem B729455 : Blo 726324 729455 := bstep (se 1 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 729455 = 1094183) B1094183
theorem B1089959 : Blo 726324 1089959 := bstep (se 1 (by rfl) ⟨817469, by rfl⟩ : syracuseStep 1089959 = 1634939) B1634939
theorem B729511 : Blo 726324 729511 := bstep (se 1 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 729511 = 1094267) B1094267
theorem B1843631 : Blo 726324 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B1843681 : Blo 726324 1843681 := bstep (se 2 (by rfl) ⟨691380, by rfl⟩ : syracuseStep 1843681 = 1382761) B1382761
theorem B1090043 : Blo 726324 1090043 := bstep (se 1 (by rfl) ⟨817532, by rfl⟩ : syracuseStep 1090043 = 1635065) B1635065
theorem B729595 : Blo 726324 729595 := bstep (se 1 (by rfl) ⟨547196, by rfl⟩ : syracuseStep 729595 = 1094393) B1094393
theorem B2368001 : Blo 726324 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B729663 : Blo 726324 729663 := bstep (se 1 (by rfl) ⟨547247, by rfl⟩ : syracuseStep 729663 = 1094495) B1094495
theorem B729671 : Blo 726324 729671 := bstep (se 1 (by rfl) ⟨547253, by rfl⟩ : syracuseStep 729671 = 1094507) B1094507
theorem B1090169 : Blo 726324 1090169 := bstep (se 2 (by rfl) ⟨408813, by rfl⟩ : syracuseStep 1090169 = 817627) B817627
theorem B8430227 : Blo 726324 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B1090223 : Blo 726324 1090223 := bstep (se 1 (by rfl) ⟨817667, by rfl⟩ : syracuseStep 1090223 = 1635335) B1635335
theorem B1090271 : Blo 726324 1090271 := bstep (se 1 (by rfl) ⟨817703, by rfl⟩ : syracuseStep 1090271 = 1635407) B1635407
theorem B729823 : Blo 726324 729823 := bstep (se 1 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 729823 = 1094735) B1094735
theorem B3679019 : Blo 726324 3679019 := bstep (se 1 (by rfl) ⟨2759264, by rfl⟩ : syracuseStep 3679019 = 5518529) B5518529
theorem B729903 : Blo 726324 729903 := bstep (se 1 (by rfl) ⟨547427, by rfl⟩ : syracuseStep 729903 = 1094855) B1094855
theorem B730011 : Blo 726324 730011 := bstep (se 1 (by rfl) ⟨547508, by rfl⟩ : syracuseStep 730011 = 1095017) B1095017
theorem B730063 : Blo 726324 730063 := bstep (se 1 (by rfl) ⟨547547, by rfl⟩ : syracuseStep 730063 = 1095095) B1095095
theorem B1090535 : Blo 726324 1090535 := bstep (se 1 (by rfl) ⟨817901, by rfl⟩ : syracuseStep 1090535 = 1635803) B1635803
theorem B730087 : Blo 726324 730087 := bstep (se 1 (by rfl) ⟨547565, by rfl⟩ : syracuseStep 730087 = 1095131) B1095131
theorem B1090793 : Blo 726324 1090793 := bstep (se 2 (by rfl) ⟨409047, by rfl⟩ : syracuseStep 1090793 = 818095) B818095
theorem B6235379 : Blo 726324 6235379 := bstep (se 1 (by rfl) ⟨4676534, by rfl⟩ : syracuseStep 6235379 = 9353069) B9353069
theorem B1090847 : Blo 726324 1090847 := bstep (se 1 (by rfl) ⟨818135, by rfl⟩ : syracuseStep 1090847 = 1636271) B1636271
theorem B1844603 : Blo 726324 1844603 := bstep (se 1 (by rfl) ⟨1383452, by rfl⟩ : syracuseStep 1844603 = 2766905) B2766905
theorem B2073995 : Blo 726324 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B1091015 : Blo 726324 1091015 := bstep (se 1 (by rfl) ⟨818261, by rfl⟩ : syracuseStep 1091015 = 1636523) B1636523
theorem B10233479 : Blo 726324 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B2107037 : Blo 726324 2107037 := bstep (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) B790139
theorem B1386247 : Blo 726324 1386247 := bstep (se 1 (by rfl) ⟨1039685, by rfl⟩ : syracuseStep 1386247 = 2079371) B2079371
theorem B1091369 : Blo 726324 1091369 := bstep (se 2 (by rfl) ⟨409263, by rfl⟩ : syracuseStep 1091369 = 818527) B818527
theorem B1091375 : Blo 726324 1091375 := bstep (se 1 (by rfl) ⟨818531, by rfl⟩ : syracuseStep 1091375 = 1637063) B1637063
theorem B8300393 : Blo 726324 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B2763017 : Blo 726324 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B1091849 : Blo 726324 1091849 := bstep (se 2 (by rfl) ⟨409443, by rfl⟩ : syracuseStep 1091849 = 818887) B818887
theorem B2337049 : Blo 726324 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B6302063 : Blo 726324 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B1091951 : Blo 726324 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B1092167 : Blo 726324 1092167 := bstep (se 1 (by rfl) ⟨819125, by rfl⟩ : syracuseStep 1092167 = 1638251) B1638251
theorem B1092203 : Blo 726324 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B3680963 : Blo 726324 3680963 := bstep (se 1 (by rfl) ⟨2760722, by rfl⟩ : syracuseStep 3680963 = 5521445) B5521445
theorem B5516099 : Blo 726324 5516099 := bstep (se 1 (by rfl) ⟨4137074, by rfl⟩ : syracuseStep 5516099 = 8274149) B8274149
theorem B1092431 : Blo 726324 1092431 := bstep (se 1 (by rfl) ⟨819323, by rfl⟩ : syracuseStep 1092431 = 1638647) B1638647
theorem B1846415 : Blo 726324 1846415 := bstep (se 1 (by rfl) ⟨1384811, by rfl⟩ : syracuseStep 1846415 = 2769623) B2769623
theorem B14953643 : Blo 726324 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B1092827 : Blo 726324 1092827 := bstep (se 1 (by rfl) ⟨819620, by rfl⟩ : syracuseStep 1092827 = 1639241) B1639241
theorem B830831 : Blo 726324 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B1093001 : Blo 726324 1093001 := bstep (se 2 (by rfl) ⟨409875, by rfl⟩ : syracuseStep 1093001 = 819751) B819751
theorem B1093355 : Blo 726324 1093355 := bstep (se 1 (by rfl) ⟨820016, by rfl⟩ : syracuseStep 1093355 = 1640033) B1640033
theorem B3321757 : Blo 726324 3321757 := bstep (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) B1245659
theorem B1093583 : Blo 726324 1093583 := bstep (se 1 (by rfl) ⟨820187, by rfl⟩ : syracuseStep 1093583 = 1640375) B1640375
theorem B5910731 : Blo 726324 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B9318671 : Blo 726324 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B1093979 : Blo 726324 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B2077103 : Blo 726324 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B15708653 : Blo 726324 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B13972013 : Blo 726324 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B1094207 : Blo 726324 1094207 := bstep (se 1 (by rfl) ⟨820655, by rfl⟩ : syracuseStep 1094207 = 1641311) B1641311
theorem B1094327 : Blo 726324 1094327 := bstep (se 1 (by rfl) ⟨820745, by rfl⟩ : syracuseStep 1094327 = 1641491) B1641491
theorem B1848055 : Blo 726324 1848055 := bstep (se 1 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 1848055 = 2772083) B2772083
theorem B1094555 : Blo 726324 1094555 := bstep (se 1 (by rfl) ⟨820916, by rfl⟩ : syracuseStep 1094555 = 1641833) B1641833
theorem B1848359 : Blo 726324 1848359 := bstep (se 1 (by rfl) ⟨1386269, by rfl⟩ : syracuseStep 1848359 = 2772539) B2772539
theorem B9319697 : Blo 726324 9319697 := bstep (se 2 (by rfl) ⟨3494886, by rfl⟩ : syracuseStep 9319697 = 6989773) B6989773
theorem B1094951 : Blo 726324 1094951 := bstep (se 1 (by rfl) ⟨821213, by rfl⟩ : syracuseStep 1094951 = 1642427) B1642427
theorem B3552607 : Blo 726324 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B1095035 : Blo 726324 1095035 := bstep (se 1 (by rfl) ⟨821276, by rfl⟩ : syracuseStep 1095035 = 1642553) B1642553
theorem B1095161 : Blo 726324 1095161 := bstep (se 2 (by rfl) ⟨410685, by rfl⟩ : syracuseStep 1095161 = 821371) B821371
theorem B1095263 : Blo 726324 1095263 := bstep (se 1 (by rfl) ⟨821447, by rfl⟩ : syracuseStep 1095263 = 1642895) B1642895
theorem B1554223 : Blo 726324 1554223 := bstep (se 1 (by rfl) ⟨1165667, by rfl⟩ : syracuseStep 1554223 = 2331335) B2331335
theorem B1095479 : Blo 726324 1095479 := bstep (se 1 (by rfl) ⟨821609, by rfl⟩ : syracuseStep 1095479 = 1643219) B1643219
theorem B3684851 : Blo 726324 3684851 := bstep (se 1 (by rfl) ⟨2763638, by rfl⟩ : syracuseStep 3684851 = 5527277) B5527277
theorem B7092775 : Blo 726324 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B6208073 : Blo 726324 6208073 := bstep (se 2 (by rfl) ⟨2328027, by rfl⟩ : syracuseStep 6208073 = 4656055) B4656055
theorem B1227487 : Blo 726324 1227487 := bstep (se 1 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 1227487 = 1841231) B1841231
theorem B56835125 : Blo 726324 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B3685499 : Blo 726324 3685499 := bstep (se 1 (by rfl) ⟨2764124, by rfl⟩ : syracuseStep 3685499 = 5528249) B5528249
theorem B1227919 : Blo 726324 1227919 := bstep (se 1 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 1227919 = 1841879) B1841879
theorem B2768195 : Blo 726324 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B1228169 : Blo 726324 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B3161531 : Blo 726324 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B2768377 : Blo 726324 2768377 := bstep (se 2 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 2768377 = 2076283) B2076283
theorem B2211563 : Blo 726324 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B3686147 : Blo 726324 3686147 := bstep (se 1 (by rfl) ⟨2764610, by rfl⟩ : syracuseStep 3686147 = 5529221) B5529221
theorem B2768651 : Blo 726324 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B2768681 : Blo 726324 2768681 := bstep (se 2 (by rfl) ⟨1038255, by rfl⟩ : syracuseStep 2768681 = 2076511) B2076511
theorem B1228601 : Blo 726324 1228601 := bstep (se 2 (by rfl) ⟨460725, by rfl⟩ : syracuseStep 1228601 = 921451) B921451
theorem B4145003 : Blo 726324 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B1752961 : Blo 726324 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B5521931 : Blo 726324 5521931 := bstep (se 1 (by rfl) ⟨4141448, by rfl⟩ : syracuseStep 5521931 = 8282897) B8282897
theorem B13681325 : Blo 726324 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B3556055 : Blo 726324 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B11092729 : Blo 726324 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B1229647 : Blo 726324 1229647 := bstep (se 1 (by rfl) ⟨922235, by rfl⟩ : syracuseStep 1229647 = 1844471) B1844471
theorem B8864731 : Blo 726324 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B15549641 : Blo 726324 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B3687767 : Blo 726324 3687767 := bstep (se 1 (by rfl) ⟨2765825, by rfl⟩ : syracuseStep 3687767 = 5531651) B5531651
theorem B1754555 : Blo 726324 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B1230329 : Blo 726324 1230329 := bstep (se 2 (by rfl) ⟨461373, by rfl⟩ : syracuseStep 1230329 = 922747) B922747
theorem B1230599 : Blo 726324 1230599 := bstep (se 1 (by rfl) ⟨922949, by rfl⟩ : syracuseStep 1230599 = 1845899) B1845899
theorem B2770793 : Blo 726324 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B3688577 : Blo 726324 3688577 := bstep (se 2 (by rfl) ⟨1383216, by rfl⟩ : syracuseStep 3688577 = 2766433) B2766433
theorem B2803997 : Blo 726324 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B6998309 : Blo 726324 6998309 := bstep (se 4 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 6998309 = 1312183) B1312183
theorem B7096805 : Blo 726324 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B1231355 : Blo 726324 1231355 := bstep (se 1 (by rfl) ⟨923516, by rfl⟩ : syracuseStep 1231355 = 1847033) B1847033
theorem B6998537 : Blo 726324 6998537 := bstep (se 2 (by rfl) ⟨2624451, by rfl⟩ : syracuseStep 6998537 = 5248903) B5248903
theorem B2214479 : Blo 726324 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B7883351 : Blo 726324 7883351 := bstep (se 1 (by rfl) ⟨5912513, by rfl⟩ : syracuseStep 7883351 = 11825027) B11825027
theorem B1034975 : Blo 726324 1034975 := bstep (se 1 (by rfl) ⟨776231, by rfl⟩ : syracuseStep 1034975 = 1552463) B1552463
theorem B1559263 : Blo 726324 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B3689387 : Blo 726324 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B1231787 : Blo 726324 1231787 := bstep (se 1 (by rfl) ⟨923840, by rfl⟩ : syracuseStep 1231787 = 1847681) B1847681
theorem B1232327 : Blo 726324 1232327 := bstep (se 1 (by rfl) ⟨924245, by rfl⟩ : syracuseStep 1232327 = 1848491) B1848491
theorem B3329495 : Blo 726324 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B17747747 : Blo 726324 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B4673537 : Blo 726324 4673537 := bstep (se 2 (by rfl) ⟨1752576, by rfl⟩ : syracuseStep 4673537 = 3505153) B3505153
theorem B6639641 : Blo 726324 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B3690521 : Blo 726324 3690521 := bstep (se 2 (by rfl) ⟨1383945, by rfl⟩ : syracuseStep 3690521 = 2767891) B2767891
theorem B7459087 : Blo 726324 7459087 := bstep (se 1 (by rfl) ⟨5594315, by rfl⟩ : syracuseStep 7459087 = 11188631) B11188631
theorem B15749477 : Blo 726324 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B3494735 : Blo 726324 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B8312057 : Blo 726324 8312057 := bstep (se 2 (by rfl) ⟨3117021, by rfl⟩ : syracuseStep 8312057 = 6234043) B6234043
theorem B7558505 : Blo 726324 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B873895 : Blo 726324 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B1169083 : Blo 726324 1169083 := bstep (se 1 (by rfl) ⟨876812, by rfl⟩ : syracuseStep 1169083 = 1753625) B1753625
theorem B19879739 : Blo 726324 19879739 := bstep (se 1 (by rfl) ⟨14909804, by rfl⟩ : syracuseStep 19879739 = 29819609) B29819609
theorem B3102569 : Blo 726324 3102569 := bstep (se 2 (by rfl) ⟨1163463, by rfl⟩ : syracuseStep 3102569 = 2326927) B2326927
theorem B5920847 : Blo 726324 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B12474647 : Blo 726324 12474647 := bstep (se 1 (by rfl) ⟨9355985, by rfl⟩ : syracuseStep 12474647 = 18711971) B18711971
theorem B1038683 : Blo 726324 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B3693437 : Blo 726324 3693437 := bstep (se 3 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 3693437 = 1385039) B1385039
theorem B3694409 : Blo 726324 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B4154003 : Blo 726324 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B3695705 : Blo 726324 3695705 := bstep (se 2 (by rfl) ⟨1385889, by rfl⟩ : syracuseStep 3695705 = 2771779) B2771779
theorem B1991803 : Blo 726324 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B3105935 : Blo 726324 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B8512705 : Blo 726324 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B3499577 : Blo 726324 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B2844503 : Blo 726324 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B3729689 : Blo 726324 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B2451923 : Blo 726324 2451923 := bstep (se 1 (by rfl) ⟨1838942, by rfl⟩ : syracuseStep 2451923 = 3677885) B3677885
theorem B2452031 : Blo 726324 2452031 := bstep (se 1 (by rfl) ⟨1839023, by rfl⟩ : syracuseStep 2452031 = 3678047) B3678047
theorem B4975631 : Blo 726324 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B1994233 : Blo 726324 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B1634255 : Blo 726324 1634255 := bstep (se 1 (by rfl) ⟨1225691, by rfl⟩ : syracuseStep 1634255 = 2451383) B2451383
theorem B3371033 : Blo 726324 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B1634633 : Blo 726324 1634633 := bstep (se 2 (by rfl) ⟨612987, by rfl⟩ : syracuseStep 1634633 = 1225975) B1225975
theorem B1634651 : Blo 726324 1634651 := bstep (se 1 (by rfl) ⟨1225988, by rfl⟩ : syracuseStep 1634651 = 2451977) B2451977
theorem B2453867 : Blo 726324 2453867 := bstep (se 1 (by rfl) ⟨1840400, by rfl⟩ : syracuseStep 2453867 = 3680801) B3680801
theorem B5108285 : Blo 726324 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B2454137 : Blo 726324 2454137 := bstep (se 2 (by rfl) ⟨920301, by rfl⟩ : syracuseStep 2454137 = 1840603) B1840603
theorem B1077943 : Blo 726324 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B1635227 : Blo 726324 1635227 := bstep (se 1 (by rfl) ⟨1226420, by rfl⟩ : syracuseStep 1635227 = 2452841) B2452841
theorem B6222905 : Blo 726324 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B1635425 : Blo 726324 1635425 := bstep (se 2 (by rfl) ⟨613284, by rfl⟩ : syracuseStep 1635425 = 1226569) B1226569
theorem B3110035 : Blo 726324 3110035 := bstep (se 1 (by rfl) ⟨2332526, by rfl⟩ : syracuseStep 3110035 = 4665053) B4665053
theorem B1635623 : Blo 726324 1635623 := bstep (se 1 (by rfl) ⟨1226717, by rfl⟩ : syracuseStep 1635623 = 2453435) B2453435
theorem B1636001 : Blo 726324 1636001 := bstep (se 2 (by rfl) ⟨613500, by rfl⟩ : syracuseStep 1636001 = 1227001) B1227001
theorem B1636361 : Blo 726324 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B5536025 : Blo 726324 5536025 := bstep (se 2 (by rfl) ⟨2076009, by rfl⟩ : syracuseStep 5536025 = 4152019) B4152019
theorem B817447 : Blo 726324 817447 := bstep (se 1 (by rfl) ⟨613085, by rfl⟩ : syracuseStep 817447 = 1226171) B1226171
theorem B817519 : Blo 726324 817519 := bstep (se 1 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 817519 = 1226279) B1226279
theorem B2455919 : Blo 726324 2455919 := bstep (se 1 (by rfl) ⟨1841939, by rfl⟩ : syracuseStep 2455919 = 3683879) B3683879
theorem B1636775 : Blo 726324 1636775 := bstep (se 1 (by rfl) ⟨1227581, by rfl⟩ : syracuseStep 1636775 = 2455163) B2455163
theorem B1636883 : Blo 726324 1636883 := bstep (se 1 (by rfl) ⟨1227662, by rfl⟩ : syracuseStep 1636883 = 2455325) B2455325
theorem B817735 : Blo 726324 817735 := bstep (se 1 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 817735 = 1226603) B1226603
theorem B1636937 : Blo 726324 1636937 := bstep (se 2 (by rfl) ⟨613851, by rfl⟩ : syracuseStep 1636937 = 1227703) B1227703
theorem B1637351 : Blo 726324 1637351 := bstep (se 1 (by rfl) ⟨1228013, by rfl⟩ : syracuseStep 1637351 = 2456027) B2456027
theorem B2620403 : Blo 726324 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B1866743 : Blo 726324 1866743 := bstep (se 1 (by rfl) ⟨1400057, by rfl⟩ : syracuseStep 1866743 = 2800115) B2800115
theorem B5536997 : Blo 726324 5536997 := bstep (se 4 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 5536997 = 1038187) B1038187
theorem B1637729 : Blo 726324 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B818599 : Blo 726324 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B1637819 : Blo 726324 1637819 := bstep (se 1 (by rfl) ⟨1228364, by rfl⟩ : syracuseStep 1637819 = 2456729) B2456729
theorem B14024137 : Blo 726324 14024137 := bstep (se 2 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 14024137 = 10518103) B10518103
theorem B1637945 : Blo 726324 1637945 := bstep (se 2 (by rfl) ⟨614229, by rfl⟩ : syracuseStep 1637945 = 1228459) B1228459
theorem B6225569 : Blo 726324 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B1277675 : Blo 726324 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B2457323 : Blo 726324 2457323 := bstep (se 1 (by rfl) ⟨1842992, by rfl⟩ : syracuseStep 2457323 = 3685985) B3685985
theorem B2948993 : Blo 726324 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B819175 : Blo 726324 819175 := bstep (se 1 (by rfl) ⟨614381, by rfl⟩ : syracuseStep 819175 = 1228763) B1228763
theorem B1966523 : Blo 726324 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1638863 : Blo 726324 1638863 := bstep (se 1 (by rfl) ⟨1229147, by rfl⟩ : syracuseStep 1638863 = 2458295) B2458295
theorem B2458241 : Blo 726324 2458241 := bstep (se 2 (by rfl) ⟨921840, by rfl⟩ : syracuseStep 2458241 = 1843681) B1843681
theorem B2458511 : Blo 726324 2458511 := bstep (se 1 (by rfl) ⟨1843883, by rfl⟩ : syracuseStep 2458511 = 3687767) B3687767
theorem B820219 : Blo 726324 820219 := bstep (se 1 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 820219 = 1230329) B1230329
theorem B1967129 : Blo 726324 1967129 := bstep (se 2 (by rfl) ⟨737673, by rfl⟩ : syracuseStep 1967129 = 1475347) B1475347
theorem B1639529 : Blo 726324 1639529 := bstep (se 2 (by rfl) ⟨614823, by rfl⟩ : syracuseStep 1639529 = 1229647) B1229647
theorem B5538941 : Blo 726324 5538941 := bstep (se 3 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 5538941 = 2077103) B2077103
theorem B820399 : Blo 726324 820399 := bstep (se 1 (by rfl) ⟨615299, by rfl⟩ : syracuseStep 820399 = 1230599) B1230599
theorem B2459051 : Blo 726324 2459051 := bstep (se 1 (by rfl) ⟨1844288, by rfl⟩ : syracuseStep 2459051 = 3688577) B3688577
theorem B2655737 : Blo 726324 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1869331 : Blo 726324 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B2360927 : Blo 726324 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B820903 : Blo 726324 820903 := bstep (se 1 (by rfl) ⟨615677, by rfl⟩ : syracuseStep 820903 = 1231355) B1231355
theorem B1640159 : Blo 726324 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B2361095 : Blo 726324 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B2492167 : Blo 726324 2492167 := bstep (se 1 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 2492167 = 3738251) B3738251
theorem B1967951 : Blo 726324 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B10487657 : Blo 726324 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B2459591 : Blo 726324 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B821191 : Blo 726324 821191 := bstep (se 1 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 821191 = 1231787) B1231787
theorem B4786295 : Blo 726324 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B4655339 : Blo 726324 4655339 := bstep (se 1 (by rfl) ⟨3491504, by rfl⟩ : syracuseStep 4655339 = 6983009) B6983009
theorem B2951471 : Blo 726324 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B821551 : Blo 726324 821551 := bstep (se 1 (by rfl) ⟨616163, by rfl⟩ : syracuseStep 821551 = 1232327) B1232327
theorem B11831831 : Blo 726324 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B1640987 : Blo 726324 1640987 := bstep (se 1 (by rfl) ⟨1230740, by rfl⟩ : syracuseStep 1640987 = 2461481) B2461481
theorem B1182313 : Blo 726324 1182313 := bstep (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) B886735
theorem B3115691 : Blo 726324 3115691 := bstep (se 1 (by rfl) ⟨2336768, by rfl⟩ : syracuseStep 3115691 = 4673537) B4673537
theorem B4426427 : Blo 726324 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B2460347 : Blo 726324 2460347 := bstep (se 1 (by rfl) ⟨1845260, by rfl⟩ : syracuseStep 2460347 = 3690521) B3690521
theorem B920479 : Blo 726324 920479 := bstep (se 1 (by rfl) ⟨690359, by rfl⟩ : syracuseStep 920479 = 1380719) B1380719
theorem B3116065 : Blo 726324 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B2329823 : Blo 726324 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1379663 : Blo 726324 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B5541371 : Blo 726324 5541371 := bstep (se 1 (by rfl) ⟨4156028, by rfl⟩ : syracuseStep 5541371 = 8312057) B8312057
theorem B2068379 : Blo 726324 2068379 := bstep (se 1 (by rfl) ⟨1551284, by rfl⟩ : syracuseStep 2068379 = 3102569) B3102569
theorem B1642463 : Blo 726324 1642463 := bstep (se 1 (by rfl) ⟨1231847, by rfl⟩ : syracuseStep 1642463 = 2463695) B2463695
theorem B7082497 : Blo 726324 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B2462291 : Blo 726324 2462291 := bstep (se 1 (by rfl) ⟨1846718, by rfl⟩ : syracuseStep 2462291 = 3693437) B3693437
theorem B1643111 : Blo 726324 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B2658977 : Blo 726324 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B4429009 : Blo 726324 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B2462939 : Blo 726324 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B726427 : Blo 726324 726427 := bstep (se 1 (by rfl) ⟨544820, by rfl⟩ : syracuseStep 726427 = 1089641) B1089641
theorem B726639 : Blo 726324 726639 := bstep (se 1 (by rfl) ⟨544979, by rfl⟩ : syracuseStep 726639 = 1089959) B1089959
theorem B726695 : Blo 726324 726695 := bstep (se 1 (by rfl) ⟨545021, by rfl⟩ : syracuseStep 726695 = 1090043) B1090043
theorem B726779 : Blo 726324 726779 := bstep (se 1 (by rfl) ⟨545084, by rfl⟩ : syracuseStep 726779 = 1090169) B1090169
theorem B726815 : Blo 726324 726815 := bstep (se 1 (by rfl) ⟨545111, by rfl⟩ : syracuseStep 726815 = 1090223) B1090223
theorem B726847 : Blo 726324 726847 := bstep (se 1 (by rfl) ⟨545135, by rfl⟩ : syracuseStep 726847 = 1090271) B1090271
theorem B727023 : Blo 726324 727023 := bstep (se 1 (by rfl) ⟨545267, by rfl⟩ : syracuseStep 727023 = 1090535) B1090535
theorem B10491929 : Blo 726324 10491929 := bstep (se 2 (by rfl) ⟨3934473, by rfl⟩ : syracuseStep 10491929 = 7868947) B7868947
theorem B2463803 : Blo 726324 2463803 := bstep (se 1 (by rfl) ⟨1847852, by rfl⟩ : syracuseStep 2463803 = 3695705) B3695705
theorem B2070623 : Blo 726324 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B727195 : Blo 726324 727195 := bstep (se 1 (by rfl) ⟨545396, by rfl⟩ : syracuseStep 727195 = 1090793) B1090793
theorem B727231 : Blo 726324 727231 := bstep (se 1 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 727231 = 1090847) B1090847
theorem B1382663 : Blo 726324 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B727343 : Blo 726324 727343 := bstep (se 1 (by rfl) ⟨545507, by rfl⟩ : syracuseStep 727343 = 1091015) B1091015
theorem B2464073 : Blo 726324 2464073 := bstep (se 2 (by rfl) ⟨924027, by rfl⟩ : syracuseStep 2464073 = 1848055) B1848055
theorem B2333051 : Blo 726324 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B6822319 : Blo 726324 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B727579 : Blo 726324 727579 := bstep (se 1 (by rfl) ⟨545684, by rfl⟩ : syracuseStep 727579 = 1091369) B1091369
theorem B727583 : Blo 726324 727583 := bstep (se 1 (by rfl) ⟨545687, by rfl⟩ : syracuseStep 727583 = 1091375) B1091375
theorem B1842011 : Blo 726324 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B727899 : Blo 726324 727899 := bstep (se 1 (by rfl) ⟨545924, by rfl⟩ : syracuseStep 727899 = 1091849) B1091849
theorem B5905277 : Blo 726324 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B727967 : Blo 726324 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B728111 : Blo 726324 728111 := bstep (se 1 (by rfl) ⟨546083, by rfl⟩ : syracuseStep 728111 = 1092167) B1092167
theorem B728135 : Blo 726324 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B13999229 : Blo 726324 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B3677399 : Blo 726324 3677399 := bstep (se 1 (by rfl) ⟨2758049, by rfl⟩ : syracuseStep 3677399 = 5516099) B5516099
theorem B728287 : Blo 726324 728287 := bstep (se 1 (by rfl) ⟨546215, by rfl⟩ : syracuseStep 728287 = 1092431) B1092431
theorem B2759933 : Blo 726324 2759933 := bstep (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) B1034975
theorem B12426533 : Blo 726324 12426533 := bstep (se 4 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 12426533 = 2329975) B2329975
theorem B3317087 : Blo 726324 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B9969095 : Blo 726324 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B728551 : Blo 726324 728551 := bstep (se 1 (by rfl) ⟨546413, by rfl⟩ : syracuseStep 728551 = 1092827) B1092827
theorem B728667 : Blo 726324 728667 := bstep (se 1 (by rfl) ⟨546500, by rfl⟩ : syracuseStep 728667 = 1093001) B1093001
theorem B2072297 : Blo 726324 2072297 := bstep (se 2 (by rfl) ⟨777111, by rfl⟩ : syracuseStep 2072297 = 1554223) B1554223
theorem B728903 : Blo 726324 728903 := bstep (se 1 (by rfl) ⟨546677, by rfl⟩ : syracuseStep 728903 = 1093355) B1093355
theorem B1089503 : Blo 726324 1089503 := bstep (se 1 (by rfl) ⟨817127, by rfl⟩ : syracuseStep 1089503 = 1634255) B1634255
theorem B729055 : Blo 726324 729055 := bstep (se 1 (by rfl) ⟨546791, by rfl⟩ : syracuseStep 729055 = 1093583) B1093583
theorem B3940487 : Blo 726324 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B1089755 : Blo 726324 1089755 := bstep (se 1 (by rfl) ⟨817316, by rfl⟩ : syracuseStep 1089755 = 1634633) B1634633
theorem B1089767 : Blo 726324 1089767 := bstep (se 1 (by rfl) ⟨817325, by rfl⟩ : syracuseStep 1089767 = 1634651) B1634651
theorem B729319 : Blo 726324 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B9314675 : Blo 726324 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B729471 : Blo 726324 729471 := bstep (se 1 (by rfl) ⟨547103, by rfl⟩ : syracuseStep 729471 = 1094207) B1094207
theorem B1089929 : Blo 726324 1089929 := bstep (se 2 (by rfl) ⟨408723, by rfl⟩ : syracuseStep 1089929 = 817447) B817447
theorem B729551 : Blo 726324 729551 := bstep (se 1 (by rfl) ⟨547163, by rfl⟩ : syracuseStep 729551 = 1094327) B1094327
theorem B1090025 : Blo 726324 1090025 := bstep (se 2 (by rfl) ⟨408759, by rfl⟩ : syracuseStep 1090025 = 817519) B817519
theorem B1090151 : Blo 726324 1090151 := bstep (se 1 (by rfl) ⟨817613, by rfl⟩ : syracuseStep 1090151 = 1635227) B1635227
theorem B729703 : Blo 726324 729703 := bstep (se 1 (by rfl) ⟨547277, by rfl⟩ : syracuseStep 729703 = 1094555) B1094555
theorem B1090283 : Blo 726324 1090283 := bstep (se 1 (by rfl) ⟨817712, by rfl⟩ : syracuseStep 1090283 = 1635425) B1635425
theorem B1090313 : Blo 726324 1090313 := bstep (se 2 (by rfl) ⟨408867, by rfl⟩ : syracuseStep 1090313 = 817735) B817735
theorem B1090415 : Blo 726324 1090415 := bstep (se 1 (by rfl) ⟨817811, by rfl⟩ : syracuseStep 1090415 = 1635623) B1635623
theorem B729967 : Blo 726324 729967 := bstep (se 1 (by rfl) ⟨547475, by rfl⟩ : syracuseStep 729967 = 1094951) B1094951
theorem B730023 : Blo 726324 730023 := bstep (se 1 (by rfl) ⟨547517, by rfl⟩ : syracuseStep 730023 = 1095035) B1095035
theorem B730107 : Blo 726324 730107 := bstep (se 1 (by rfl) ⟨547580, by rfl⟩ : syracuseStep 730107 = 1095161) B1095161
theorem B2630681 : Blo 726324 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B730175 : Blo 726324 730175 := bstep (se 1 (by rfl) ⟨547631, by rfl⟩ : syracuseStep 730175 = 1095263) B1095263
theorem B1844329 : Blo 726324 1844329 := bstep (se 2 (by rfl) ⟨691623, by rfl⟩ : syracuseStep 1844329 = 1383247) B1383247
theorem B1090667 : Blo 726324 1090667 := bstep (se 1 (by rfl) ⟨818000, by rfl⟩ : syracuseStep 1090667 = 1636001) B1636001
theorem B8430749 : Blo 726324 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B730319 : Blo 726324 730319 := bstep (se 1 (by rfl) ⟨547739, by rfl⟩ : syracuseStep 730319 = 1095479) B1095479
theorem B1090907 : Blo 726324 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B1091183 : Blo 726324 1091183 := bstep (se 1 (by rfl) ⟨818387, by rfl⟩ : syracuseStep 1091183 = 1636775) B1636775
theorem B1091255 : Blo 726324 1091255 := bstep (se 1 (by rfl) ⟨818441, by rfl⟩ : syracuseStep 1091255 = 1636883) B1636883
theorem B4138715 : Blo 726324 4138715 := bstep (se 1 (by rfl) ⟨3104036, by rfl⟩ : syracuseStep 4138715 = 6208073) B6208073
theorem B1091291 : Blo 726324 1091291 := bstep (se 1 (by rfl) ⟨818468, by rfl⟩ : syracuseStep 1091291 = 1636937) B1636937
theorem B1845089 : Blo 726324 1845089 := bstep (se 2 (by rfl) ⟨691908, by rfl⟩ : syracuseStep 1845089 = 1383817) B1383817
theorem B1091465 : Blo 726324 1091465 := bstep (se 2 (by rfl) ⟨409299, by rfl⟩ : syracuseStep 1091465 = 818599) B818599
theorem B1091567 : Blo 726324 1091567 := bstep (se 1 (by rfl) ⟨818675, by rfl⟩ : syracuseStep 1091567 = 1637351) B1637351
theorem B1746935 : Blo 726324 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B37890083 : Blo 726324 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B1845463 : Blo 726324 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B1091819 : Blo 726324 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B1091879 : Blo 726324 1091879 := bstep (se 1 (by rfl) ⟨818909, by rfl⟩ : syracuseStep 1091879 = 1637819) B1637819
theorem B1091963 : Blo 726324 1091963 := bstep (se 1 (by rfl) ⟨818972, by rfl⟩ : syracuseStep 1091963 = 1637945) B1637945
theorem B2337281 : Blo 726324 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B1845767 : Blo 726324 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B1845787 : Blo 726324 1845787 := bstep (se 1 (by rfl) ⟨1384340, by rfl⟩ : syracuseStep 1845787 = 2768681) B2768681
theorem B2763335 : Blo 726324 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B1092233 : Blo 726324 1092233 := bstep (se 2 (by rfl) ⟨409587, by rfl⟩ : syracuseStep 1092233 = 819175) B819175
theorem B17673011 : Blo 726324 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B1092407 : Blo 726324 1092407 := bstep (se 1 (by rfl) ⟨819305, by rfl⟩ : syracuseStep 1092407 = 1638611) B1638611
theorem B1092443 : Blo 726324 1092443 := bstep (se 1 (by rfl) ⟨819332, by rfl⟩ : syracuseStep 1092443 = 1638665) B1638665
theorem B1092587 : Blo 726324 1092587 := bstep (se 1 (by rfl) ⟨819440, by rfl⟩ : syracuseStep 1092587 = 1638881) B1638881
theorem B3681287 : Blo 726324 3681287 := bstep (se 1 (by rfl) ⟨2760965, by rfl⟩ : syracuseStep 3681287 = 5521931) B5521931
theorem B9120883 : Blo 726324 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2796665 : Blo 726324 2796665 := bstep (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) B2097499
theorem B2370703 : Blo 726324 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B1092791 : Blo 726324 1092791 := bstep (se 1 (by rfl) ⟨819593, by rfl⟩ : syracuseStep 1092791 = 1639187) B1639187
theorem B1093031 : Blo 726324 1093031 := bstep (se 1 (by rfl) ⟨819773, by rfl⟩ : syracuseStep 1093031 = 1639547) B1639547
theorem B10366427 : Blo 726324 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B1093115 : Blo 726324 1093115 := bstep (se 1 (by rfl) ⟨819836, by rfl⟩ : syracuseStep 1093115 = 1639673) B1639673
theorem B1093211 : Blo 726324 1093211 := bstep (se 1 (by rfl) ⟨819908, by rfl⟩ : syracuseStep 1093211 = 1639817) B1639817
theorem B14790305 : Blo 726324 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B1093295 : Blo 726324 1093295 := bstep (se 1 (by rfl) ⟨819971, by rfl⟩ : syracuseStep 1093295 = 1639943) B1639943
theorem B1093415 : Blo 726324 1093415 := bstep (se 1 (by rfl) ⟨820061, by rfl⟩ : syracuseStep 1093415 = 1640123) B1640123
theorem B2076455 : Blo 726324 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B1093499 : Blo 726324 1093499 := bstep (se 1 (by rfl) ⟨820124, by rfl⟩ : syracuseStep 1093499 = 1640249) B1640249
theorem B1847195 : Blo 726324 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B4665539 : Blo 726324 4665539 := bstep (se 1 (by rfl) ⟨3499154, by rfl⟩ : syracuseStep 4665539 = 6998309) B6998309
theorem B11350273 : Blo 726324 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B1093919 : Blo 726324 1093919 := bstep (se 1 (by rfl) ⟨820439, by rfl⟩ : syracuseStep 1093919 = 1640879) B1640879
theorem B1093943 : Blo 726324 1093943 := bstep (se 1 (by rfl) ⟨820457, by rfl⟩ : syracuseStep 1093943 = 1640915) B1640915
theorem B4731203 : Blo 726324 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B4665691 : Blo 726324 4665691 := bstep (se 1 (by rfl) ⟨3499268, by rfl⟩ : syracuseStep 4665691 = 6998537) B6998537
theorem B1094015 : Blo 726324 1094015 := bstep (se 1 (by rfl) ⟨820511, by rfl⟩ : syracuseStep 1094015 = 1641023) B1641023
theorem B5255567 : Blo 726324 5255567 := bstep (se 1 (by rfl) ⟨3941675, by rfl⟩ : syracuseStep 5255567 = 7883351) B7883351
theorem B1094087 : Blo 726324 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B1094441 : Blo 726324 1094441 := bstep (se 2 (by rfl) ⟨410415, by rfl⟩ : syracuseStep 1094441 = 820831) B820831
theorem B1094447 : Blo 726324 1094447 := bstep (se 1 (by rfl) ⟨820835, by rfl⟩ : syracuseStep 1094447 = 1641671) B1641671
theorem B1094567 : Blo 726324 1094567 := bstep (se 1 (by rfl) ⟨820925, by rfl⟩ : syracuseStep 1094567 = 1641851) B1641851
theorem B1094651 : Blo 726324 1094651 := bstep (se 1 (by rfl) ⟨820988, by rfl⟩ : syracuseStep 1094651 = 1641977) B1641977
theorem B1848329 : Blo 726324 1848329 := bstep (se 2 (by rfl) ⟨693123, by rfl⟩ : syracuseStep 1848329 = 1386247) B1386247
theorem B1094711 : Blo 726324 1094711 := bstep (se 1 (by rfl) ⟨821033, by rfl⟩ : syracuseStep 1094711 = 1642067) B1642067
theorem B1094831 : Blo 726324 1094831 := bstep (se 1 (by rfl) ⟨821123, by rfl⟩ : syracuseStep 1094831 = 1642247) B1642247
theorem B9352705 : Blo 726324 9352705 := bstep (se 2 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 9352705 = 7014529) B7014529
theorem B10499651 : Blo 726324 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B1095239 : Blo 726324 1095239 := bstep (se 1 (by rfl) ⟨821429, by rfl⟩ : syracuseStep 1095239 = 1642859) B1642859
theorem B1226407 : Blo 726324 1226407 := bstep (se 1 (by rfl) ⟨919805, by rfl⟩ : syracuseStep 1226407 = 1839611) B1839611
theorem B1095335 : Blo 726324 1095335 := bstep (se 1 (by rfl) ⟨821501, by rfl⟩ : syracuseStep 1095335 = 1643003) B1643003
theorem B1554103 : Blo 726324 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B1095419 : Blo 726324 1095419 := bstep (se 1 (by rfl) ⟨821564, by rfl⟩ : syracuseStep 1095419 = 1643129) B1643129
theorem B1095455 : Blo 726324 1095455 := bstep (se 1 (by rfl) ⟨821591, by rfl⟩ : syracuseStep 1095455 = 1643183) B1643183
theorem B2079017 : Blo 726324 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B1227055 : Blo 726324 1227055 := bstep (se 1 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 1227055 = 1840583) B1840583
theorem B13253159 : Blo 726324 13253159 := bstep (se 1 (by rfl) ⟨9939869, by rfl⟩ : syracuseStep 13253159 = 19879739) B19879739
theorem B3947231 : Blo 726324 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B1227575 : Blo 726324 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B1555291 : Blo 726324 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B3685661 : Blo 726324 3685661 := bstep (se 3 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 3685661 = 1382123) B1382123
theorem B1228351 : Blo 726324 1228351 := bstep (se 1 (by rfl) ⟨921263, by rfl⟩ : syracuseStep 1228351 = 1842527) B1842527
theorem B1556111 : Blo 726324 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1229087 : Blo 726324 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B9945449 : Blo 726324 9945449 := bstep (se 2 (by rfl) ⟨3729543, by rfl⟩ : syracuseStep 9945449 = 7459087) B7459087
theorem B2769335 : Blo 726324 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B5620151 : Blo 726324 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B2769821 : Blo 726324 2769821 := bstep (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) B1038683
theorem B1229735 : Blo 726324 1229735 := bstep (se 1 (by rfl) ⟨922301, by rfl⟩ : syracuseStep 1229735 = 1844603) B1844603
theorem B1229897 : Blo 726324 1229897 := bstep (se 2 (by rfl) ⟨461211, by rfl⟩ : syracuseStep 1229897 = 922423) B922423
theorem B4146713 : Blo 726324 4146713 := bstep (se 2 (by rfl) ⟨1555017, by rfl⟩ : syracuseStep 4146713 = 3110035) B3110035
theorem B1230457 : Blo 726324 1230457 := bstep (se 2 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 1230457 = 922843) B922843
theorem B4736809 : Blo 726324 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B3688253 : Blo 726324 3688253 := bstep (se 3 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 3688253 = 1383095) B1383095
theorem B1165193 : Blo 726324 1165193 := bstep (se 2 (by rfl) ⟨436947, by rfl⟩ : syracuseStep 1165193 = 873895) B873895
theorem B1230943 : Blo 726324 1230943 := bstep (se 1 (by rfl) ⟨923207, by rfl⟩ : syracuseStep 1230943 = 1846415) B1846415
theorem B1558777 : Blo 726324 1558777 := bstep (se 2 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 1558777 = 1169083) B1169083
theorem B2247355 : Blo 726324 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B6212447 : Blo 726324 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B10472435 : Blo 726324 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B1232239 : Blo 726324 1232239 := bstep (se 1 (by rfl) ⟨924179, by rfl⟩ : syracuseStep 1232239 = 1848359) B1848359
theorem B4148603 : Blo 726324 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B9457033 : Blo 726324 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B6213131 : Blo 726324 6213131 := bstep (se 1 (by rfl) ⟨4659848, by rfl⟩ : syracuseStep 6213131 = 9319697) B9319697
theorem B2215549 : Blo 726324 2215549 := bstep (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) B830831
theorem B3690683 : Blo 726324 3690683 := bstep (se 1 (by rfl) ⟨2768012, by rfl⟩ : syracuseStep 3690683 = 5536025) B5536025
theorem B54514133 : Blo 726324 54514133 := bstep (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) B1277675
theorem B18698849 : Blo 726324 18698849 := bstep (se 2 (by rfl) ⟨7012068, by rfl⟩ : syracuseStep 18698849 = 14024137) B14024137
theorem B3691169 : Blo 726324 3691169 := bstep (se 2 (by rfl) ⟨1384188, by rfl⟩ : syracuseStep 3691169 = 2768377) B2768377
theorem B3691331 : Blo 726324 3691331 := bstep (se 1 (by rfl) ⟨2768498, by rfl⟩ : syracuseStep 3691331 = 5536997) B5536997
theorem B4150379 : Blo 726324 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B3692141 : Blo 726324 3692141 := bstep (se 3 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 3692141 = 1384553) B1384553
theorem B11819641 : Blo 726324 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B6314669 : Blo 726324 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B875567 : Blo 726324 875567 := bstep (se 1 (by rfl) ⟨656675, by rfl⟩ : syracuseStep 875567 = 1313351) B1313351
theorem B5332559 : Blo 726324 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B2219663 : Blo 726324 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B1663195 : Blo 726324 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B118317611 : Blo 726324 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B5039003 : Blo 726324 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B4678813 : Blo 726324 4678813 := bstep (se 3 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 4678813 = 1754555) B1754555
theorem B8316431 : Blo 726324 8316431 := bstep (se 1 (by rfl) ⟨6237323, by rfl⟩ : syracuseStep 8316431 = 12474647) B12474647
theorem B4155209 : Blo 726324 4155209 := bstep (se 2 (by rfl) ⟨1558203, by rfl⟩ : syracuseStep 4155209 = 3116407) B3116407
theorem B1402721 : Blo 726324 1402721 := bstep (se 2 (by rfl) ⟨526020, by rfl⟩ : syracuseStep 1402721 = 1052041) B1052041
theorem B7891091 : Blo 726324 7891091 := bstep (se 1 (by rfl) ⟨5918318, by rfl⟩ : syracuseStep 7891091 = 11836637) B11836637
theorem B2451869 : Blo 726324 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B2452139 : Blo 726324 2452139 := bstep (se 1 (by rfl) ⟨1839104, by rfl⟩ : syracuseStep 2452139 = 3678209) B3678209
theorem B2452679 : Blo 726324 2452679 := bstep (se 1 (by rfl) ⟨1839509, by rfl⟩ : syracuseStep 2452679 = 3679019) B3679019
theorem B8875241 : Blo 726324 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B4156919 : Blo 726324 4156919 := bstep (se 1 (by rfl) ⟨3117689, by rfl⟩ : syracuseStep 4156919 = 6235379) B6235379
theorem B1437257 : Blo 726324 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B16805501 : Blo 726324 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B1404691 : Blo 726324 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B1896335 : Blo 726324 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B5533595 : Blo 726324 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B2486459 : Blo 726324 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B1634615 : Blo 726324 1634615 := bstep (se 1 (by rfl) ⟨1225961, by rfl⟩ : syracuseStep 1634615 = 2451923) B2451923
theorem B1634687 : Blo 726324 1634687 := bstep (se 1 (by rfl) ⟨1226015, by rfl⟩ : syracuseStep 1634687 = 2452031) B2452031
theorem B2453975 : Blo 726324 2453975 := bstep (se 1 (by rfl) ⟨1840481, by rfl⟩ : syracuseStep 2453975 = 3680963) B3680963
theorem B1635911 : Blo 726324 1635911 := bstep (se 1 (by rfl) ⟨1226933, by rfl⟩ : syracuseStep 1635911 = 2453867) B2453867
theorem B3405523 : Blo 726324 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B1636091 : Blo 726324 1636091 := bstep (se 1 (by rfl) ⟨1227068, by rfl⟩ : syracuseStep 1636091 = 2454137) B2454137
theorem B2455433 : Blo 726324 2455433 := bstep (se 2 (by rfl) ⟨920787, by rfl⟩ : syracuseStep 2455433 = 1841575) B1841575
theorem B2455649 : Blo 726324 2455649 := bstep (se 2 (by rfl) ⟨920868, by rfl⟩ : syracuseStep 2455649 = 1841737) B1841737
theorem B1636649 : Blo 726324 1636649 := bstep (se 2 (by rfl) ⟨613743, by rfl⟩ : syracuseStep 1636649 = 1227487) B1227487
theorem B1637225 : Blo 726324 1637225 := bstep (se 2 (by rfl) ⟨613959, by rfl⟩ : syracuseStep 1637225 = 1227919) B1227919
theorem B1637279 : Blo 726324 1637279 := bstep (se 1 (by rfl) ⟨1227959, by rfl⟩ : syracuseStep 1637279 = 2455919) B2455919
theorem B2456567 : Blo 726324 2456567 := bstep (se 1 (by rfl) ⟨1842425, by rfl⟩ : syracuseStep 2456567 = 3684851) B3684851
theorem B1244495 : Blo 726324 1244495 := bstep (se 1 (by rfl) ⟨933371, by rfl⟩ : syracuseStep 1244495 = 1866743) B1866743
theorem B2456999 : Blo 726324 2456999 := bstep (se 1 (by rfl) ⟨1842749, by rfl⟩ : syracuseStep 2456999 = 3685499) B3685499
theorem B818779 : Blo 726324 818779 := bstep (se 1 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 818779 = 1228169) B1228169
theorem B1474375 : Blo 726324 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B1638215 : Blo 726324 1638215 := bstep (se 1 (by rfl) ⟨1228661, by rfl⟩ : syracuseStep 1638215 = 2457323) B2457323
theorem B2457431 : Blo 726324 2457431 := bstep (se 1 (by rfl) ⟨1843073, by rfl⟩ : syracuseStep 2457431 = 3686147) B3686147
theorem B819067 : Blo 726324 819067 := bstep (se 1 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 819067 = 1228601) B1228601
theorem B1965995 : Blo 726324 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B819391 : Blo 726324 819391 := bstep (se 1 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 819391 = 1229087) B1229087
theorem B1638827 : Blo 726324 1638827 := bstep (se 1 (by rfl) ⟨1229120, by rfl⟩ : syracuseStep 1638827 = 2458241) B2458241
theorem B1639007 : Blo 726324 1639007 := bstep (se 1 (by rfl) ⟨1229255, by rfl⟩ : syracuseStep 1639007 = 2458511) B2458511
theorem B819823 : Blo 726324 819823 := bstep (se 1 (by rfl) ⟨614867, by rfl⟩ : syracuseStep 819823 = 1229735) B1229735
theorem B1311419 : Blo 726324 1311419 := bstep (se 1 (by rfl) ⟨983564, by rfl⟩ : syracuseStep 1311419 = 1967129) B1967129
theorem B819931 : Blo 726324 819931 := bstep (se 1 (by rfl) ⟨614948, by rfl⟩ : syracuseStep 819931 = 1229897) B1229897
theorem B1639367 : Blo 726324 1639367 := bstep (se 1 (by rfl) ⟨1229525, by rfl⟩ : syracuseStep 1639367 = 2459051) B2459051
theorem B1770491 : Blo 726324 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B5244061 : Blo 726324 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B1574063 : Blo 726324 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B2458835 : Blo 726324 2458835 := bstep (se 1 (by rfl) ⟨1844126, by rfl⟩ : syracuseStep 2458835 = 3688253) B3688253
theorem B1311967 : Blo 726324 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B1639727 : Blo 726324 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B2459105 : Blo 726324 2459105 := bstep (se 2 (by rfl) ⟨922164, by rfl⟩ : syracuseStep 2459105 = 1844329) B1844329
theorem B1967647 : Blo 726324 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B1640231 : Blo 726324 1640231 := bstep (se 1 (by rfl) ⟨1230173, by rfl⟩ : syracuseStep 1640231 = 2460347) B2460347
theorem B6981623 : Blo 726324 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B2492441 : Blo 726324 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B1640609 : Blo 726324 1640609 := bstep (se 2 (by rfl) ⟨615228, by rfl⟩ : syracuseStep 1640609 = 1230457) B1230457
theorem B919775 : Blo 726324 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B1378919 : Blo 726324 1378919 := bstep (se 1 (by rfl) ⟨1034189, by rfl⟩ : syracuseStep 1378919 = 2068379) B2068379
theorem B2460455 : Blo 726324 2460455 := bstep (se 1 (by rfl) ⟨1845341, by rfl⟩ : syracuseStep 2460455 = 3690683) B3690683
theorem B1641257 : Blo 726324 1641257 := bstep (se 2 (by rfl) ⟨615471, by rfl⟩ : syracuseStep 1641257 = 1230943) B1230943
theorem B2460617 : Blo 726324 2460617 := bstep (se 2 (by rfl) ⟨922731, by rfl⟩ : syracuseStep 2460617 = 1845463) B1845463
theorem B36342755 : Blo 726324 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B1641527 : Blo 726324 1641527 := bstep (se 1 (by rfl) ⟨1231145, by rfl⟩ : syracuseStep 1641527 = 2462291) B2462291
theorem B1772651 : Blo 726324 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B2460779 : Blo 726324 2460779 := bstep (se 1 (by rfl) ⟨1845584, by rfl⟩ : syracuseStep 2460779 = 3691169) B3691169
theorem B2460887 : Blo 726324 2460887 := bstep (se 1 (by rfl) ⟨1845665, by rfl⟩ : syracuseStep 2460887 = 3691331) B3691331
theorem B2461049 : Blo 726324 2461049 := bstep (se 2 (by rfl) ⟨922893, by rfl⟩ : syracuseStep 2461049 = 1845787) B1845787
theorem B1576417 : Blo 726324 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B1641959 : Blo 726324 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B2461427 : Blo 726324 2461427 := bstep (se 1 (by rfl) ⟨1846070, by rfl⟩ : syracuseStep 2461427 = 3692141) B3692141
theorem B1642535 : Blo 726324 1642535 := bstep (se 1 (by rfl) ⟨1231901, by rfl⟩ : syracuseStep 1642535 = 2463803) B2463803
theorem B1380415 : Blo 726324 1380415 := bstep (se 1 (by rfl) ⟨1035311, by rfl⟩ : syracuseStep 1380415 = 2070623) B2070623
theorem B12161177 : Blo 726324 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B921775 : Blo 726324 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B1642715 : Blo 726324 1642715 := bstep (se 1 (by rfl) ⟨1232036, by rfl⟩ : syracuseStep 1642715 = 2464073) B2464073
theorem B6295805 : Blo 726324 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B1642985 : Blo 726324 1642985 := bstep (se 2 (by rfl) ⟨616119, by rfl⟩ : syracuseStep 1642985 = 1232239) B1232239
theorem B3936851 : Blo 726324 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B2954065 : Blo 726324 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B1839955 : Blo 726324 1839955 := bstep (se 1 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 1839955 = 2759933) B2759933
theorem B1381531 : Blo 726324 1381531 := bstep (se 1 (by rfl) ⟨1036148, by rfl⟩ : syracuseStep 1381531 = 2072297) B2072297
theorem B726335 : Blo 726324 726335 := bstep (se 1 (by rfl) ⟨544751, by rfl⟩ : syracuseStep 726335 = 1089503) B1089503
theorem B2626991 : Blo 726324 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B726503 : Blo 726324 726503 := bstep (se 1 (by rfl) ⟨544877, by rfl⟩ : syracuseStep 726503 = 1089755) B1089755
theorem B726511 : Blo 726324 726511 := bstep (se 1 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 726511 = 1089767) B1089767
theorem B726619 : Blo 726324 726619 := bstep (se 1 (by rfl) ⟨544964, by rfl⟩ : syracuseStep 726619 = 1089929) B1089929
theorem B726683 : Blo 726324 726683 := bstep (se 1 (by rfl) ⟨545012, by rfl⟩ : syracuseStep 726683 = 1090025) B1090025
theorem B78878407 : Blo 726324 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B726767 : Blo 726324 726767 := bstep (se 1 (by rfl) ⟨545075, by rfl⟩ : syracuseStep 726767 = 1090151) B1090151
theorem B726855 : Blo 726324 726855 := bstep (se 1 (by rfl) ⟨545141, by rfl⟩ : syracuseStep 726855 = 1090283) B1090283
theorem B726875 : Blo 726324 726875 := bstep (se 1 (by rfl) ⟨545156, by rfl⟩ : syracuseStep 726875 = 1090313) B1090313
theorem B726943 : Blo 726324 726943 := bstep (se 1 (by rfl) ⟨545207, by rfl⟩ : syracuseStep 726943 = 1090415) B1090415
theorem B727111 : Blo 726324 727111 := bstep (se 1 (by rfl) ⟨545333, by rfl⟩ : syracuseStep 727111 = 1090667) B1090667
theorem B727271 : Blo 726324 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B5544287 : Blo 726324 5544287 := bstep (se 1 (by rfl) ⟨4158215, by rfl⟩ : syracuseStep 5544287 = 8316431) B8316431
theorem B727455 : Blo 726324 727455 := bstep (se 1 (by rfl) ⟨545591, by rfl⟩ : syracuseStep 727455 = 1091183) B1091183
theorem B727503 : Blo 726324 727503 := bstep (se 1 (by rfl) ⟨545627, by rfl⟩ : syracuseStep 727503 = 1091255) B1091255
theorem B2759143 : Blo 726324 2759143 := bstep (se 1 (by rfl) ⟨2069357, by rfl⟩ : syracuseStep 2759143 = 4138715) B4138715
theorem B727527 : Blo 726324 727527 := bstep (se 1 (by rfl) ⟨545645, by rfl⟩ : syracuseStep 727527 = 1091291) B1091291
theorem B727643 : Blo 726324 727643 := bstep (se 1 (by rfl) ⟨545732, by rfl⟩ : syracuseStep 727643 = 1091465) B1091465
theorem B727711 : Blo 726324 727711 := bstep (se 1 (by rfl) ⟨545783, by rfl⟩ : syracuseStep 727711 = 1091567) B1091567
theorem B727879 : Blo 726324 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B727919 : Blo 726324 727919 := bstep (se 1 (by rfl) ⟨545939, by rfl⟩ : syracuseStep 727919 = 1091879) B1091879
theorem B727975 : Blo 726324 727975 := bstep (se 1 (by rfl) ⟨545981, by rfl⟩ : syracuseStep 727975 = 1091963) B1091963
theorem B5905345 : Blo 726324 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B1842223 : Blo 726324 1842223 := bstep (se 1 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 1842223 = 2763335) B2763335
theorem B728155 : Blo 726324 728155 := bstep (se 1 (by rfl) ⟨546116, by rfl⟩ : syracuseStep 728155 = 1092233) B1092233
theorem B11803805 : Blo 726324 11803805 := bstep (se 3 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 11803805 = 4426427) B4426427
theorem B728271 : Blo 726324 728271 := bstep (se 1 (by rfl) ⟨546203, by rfl⟩ : syracuseStep 728271 = 1092407) B1092407
theorem B728295 : Blo 726324 728295 := bstep (se 1 (by rfl) ⟨546221, by rfl⟩ : syracuseStep 728295 = 1092443) B1092443
theorem B10525949 : Blo 726324 10525949 := bstep (se 3 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 10525949 = 3947231) B3947231
theorem B728391 : Blo 726324 728391 := bstep (se 1 (by rfl) ⟨546293, by rfl⟩ : syracuseStep 728391 = 1092587) B1092587
theorem B728527 : Blo 726324 728527 := bstep (se 1 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 728527 = 1092791) B1092791
theorem B2072137 : Blo 726324 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B728687 : Blo 726324 728687 := bstep (se 1 (by rfl) ⟨546515, by rfl⟩ : syracuseStep 728687 = 1093031) B1093031
theorem B728743 : Blo 726324 728743 := bstep (se 1 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 728743 = 1093115) B1093115
theorem B958171 : Blo 726324 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B728807 : Blo 726324 728807 := bstep (se 1 (by rfl) ⟨546605, by rfl⟩ : syracuseStep 728807 = 1093211) B1093211
theorem B728863 : Blo 726324 728863 := bstep (se 1 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 728863 = 1093295) B1093295
theorem B728943 : Blo 726324 728943 := bstep (se 1 (by rfl) ⟨546707, by rfl⟩ : syracuseStep 728943 = 1093415) B1093415
theorem B1384303 : Blo 726324 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B728999 : Blo 726324 728999 := bstep (se 1 (by rfl) ⟨546749, by rfl⟩ : syracuseStep 728999 = 1093499) B1093499
theorem B2334845 : Blo 726324 2334845 := bstep (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) B875567
theorem B729279 : Blo 726324 729279 := bstep (se 1 (by rfl) ⟨546959, by rfl⟩ : syracuseStep 729279 = 1093919) B1093919
theorem B1089743 : Blo 726324 1089743 := bstep (se 1 (by rfl) ⟨817307, by rfl⟩ : syracuseStep 1089743 = 1634615) B1634615
theorem B729295 : Blo 726324 729295 := bstep (se 1 (by rfl) ⟨546971, by rfl⟩ : syracuseStep 729295 = 1093943) B1093943
theorem B3154135 : Blo 726324 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B1089791 : Blo 726324 1089791 := bstep (se 1 (by rfl) ⟨817343, by rfl⟩ : syracuseStep 1089791 = 1634687) B1634687
theorem B729343 : Blo 726324 729343 := bstep (se 1 (by rfl) ⟨547007, by rfl⟩ : syracuseStep 729343 = 1094015) B1094015
theorem B729391 : Blo 726324 729391 := bstep (se 1 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 729391 = 1094087) B1094087
theorem B729627 : Blo 726324 729627 := bstep (se 1 (by rfl) ⟨547220, by rfl⟩ : syracuseStep 729627 = 1094441) B1094441
theorem B729631 : Blo 726324 729631 := bstep (se 1 (by rfl) ⟨547223, by rfl⟩ : syracuseStep 729631 = 1094447) B1094447
theorem B729711 : Blo 726324 729711 := bstep (se 1 (by rfl) ⟨547283, by rfl⟩ : syracuseStep 729711 = 1094567) B1094567
theorem B729767 : Blo 726324 729767 := bstep (se 1 (by rfl) ⟨547325, by rfl⟩ : syracuseStep 729767 = 1094651) B1094651
theorem B729807 : Blo 726324 729807 := bstep (se 1 (by rfl) ⟨547355, by rfl⟩ : syracuseStep 729807 = 1094711) B1094711
theorem B729887 : Blo 726324 729887 := bstep (se 1 (by rfl) ⟨547415, by rfl⟩ : syracuseStep 729887 = 1094831) B1094831
theorem B3318653 : Blo 726324 3318653 := bstep (se 3 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 3318653 = 1244495) B1244495
theorem B1090607 : Blo 726324 1090607 := bstep (se 1 (by rfl) ⟨817955, by rfl⟩ : syracuseStep 1090607 = 1635911) B1635911
theorem B730159 : Blo 726324 730159 := bstep (se 1 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 730159 = 1095239) B1095239
theorem B730223 : Blo 726324 730223 := bstep (se 1 (by rfl) ⟨547667, by rfl⟩ : syracuseStep 730223 = 1095335) B1095335
theorem B2073721 : Blo 726324 2073721 := bstep (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) B1555291
theorem B1090727 : Blo 726324 1090727 := bstep (se 1 (by rfl) ⟨818045, by rfl⟩ : syracuseStep 1090727 = 1636091) B1636091
theorem B730279 : Blo 726324 730279 := bstep (se 1 (by rfl) ⟨547709, by rfl⟩ : syracuseStep 730279 = 1095419) B1095419
theorem B730303 : Blo 726324 730303 := bstep (se 1 (by rfl) ⟨547727, by rfl⟩ : syracuseStep 730303 = 1095455) B1095455
theorem B1091099 : Blo 726324 1091099 := bstep (se 1 (by rfl) ⟨818324, by rfl⟩ : syracuseStep 1091099 = 1636649) B1636649
theorem B1386011 : Blo 726324 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B1091483 : Blo 726324 1091483 := bstep (se 1 (by rfl) ⟨818612, by rfl⟩ : syracuseStep 1091483 = 1637225) B1637225
theorem B1091519 : Blo 726324 1091519 := bstep (se 1 (by rfl) ⟨818639, by rfl⟩ : syracuseStep 1091519 = 1637279) B1637279
theorem B1091705 : Blo 726324 1091705 := bstep (se 2 (by rfl) ⟨409389, by rfl⟩ : syracuseStep 1091705 = 818779) B818779
theorem B1092089 : Blo 726324 1092089 := bstep (se 2 (by rfl) ⟨409533, by rfl⟩ : syracuseStep 1092089 = 819067) B819067
theorem B1092143 : Blo 726324 1092143 := bstep (se 1 (by rfl) ⟨819107, by rfl⟩ : syracuseStep 1092143 = 1638215) B1638215
theorem B6630299 : Blo 726324 6630299 := bstep (se 1 (by rfl) ⟨4972724, by rfl⟩ : syracuseStep 6630299 = 9945449) B9945449
theorem B1846223 : Blo 726324 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B3746767 : Blo 726324 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B1092575 : Blo 726324 1092575 := bstep (se 1 (by rfl) ⟨819431, by rfl⟩ : syracuseStep 1092575 = 1638863) B1638863
theorem B6630557 : Blo 726324 6630557 := bstep (se 3 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 6630557 = 2486459) B2486459
theorem B1846547 : Blo 726324 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B1093019 : Blo 726324 1093019 := bstep (se 1 (by rfl) ⟨819764, by rfl⟩ : syracuseStep 1093019 = 1639529) B1639529
theorem B2764475 : Blo 726324 2764475 := bstep (se 1 (by rfl) ⟨2073356, by rfl⟩ : syracuseStep 2764475 = 4146713) B4146713
theorem B1093439 : Blo 726324 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B6991771 : Blo 726324 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B1093625 : Blo 726324 1093625 := bstep (se 2 (by rfl) ⟨410109, by rfl⟩ : syracuseStep 1093625 = 820219) B820219
theorem B6238417 : Blo 726324 6238417 := bstep (se 2 (by rfl) ⟨2339406, by rfl⟩ : syracuseStep 6238417 = 4678813) B4678813
theorem B1093865 : Blo 726324 1093865 := bstep (se 2 (by rfl) ⟨410199, by rfl⟩ : syracuseStep 1093865 = 820399) B820399
theorem B1093991 : Blo 726324 1093991 := bstep (se 1 (by rfl) ⟨820493, by rfl⟩ : syracuseStep 1093991 = 1640987) B1640987
theorem B2077127 : Blo 726324 2077127 := bstep (se 1 (by rfl) ⟨1557845, by rfl⟩ : syracuseStep 2077127 = 3115691) B3115691
theorem B4141631 : Blo 726324 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B1553215 : Blo 726324 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B1094537 : Blo 726324 1094537 := bstep (se 2 (by rfl) ⟨410451, by rfl⟩ : syracuseStep 1094537 = 820903) B820903
theorem B2765735 : Blo 726324 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B4142087 : Blo 726324 4142087 := bstep (se 1 (by rfl) ⟨3106565, by rfl⟩ : syracuseStep 4142087 = 6213131) B6213131
theorem B3322889 : Blo 726324 3322889 := bstep (se 2 (by rfl) ⟨1246083, by rfl⟩ : syracuseStep 3322889 = 2492167) B2492167
theorem B1094921 : Blo 726324 1094921 := bstep (se 2 (by rfl) ⟨410595, by rfl⟩ : syracuseStep 1094921 = 821191) B821191
theorem B1094975 : Blo 726324 1094975 := bstep (se 1 (by rfl) ⟨821231, by rfl⟩ : syracuseStep 1094975 = 1642463) B1642463
theorem B2078369 : Blo 726324 2078369 := bstep (se 2 (by rfl) ⟨779388, by rfl⟩ : syracuseStep 2078369 = 1558777) B1558777
theorem B1095401 : Blo 726324 1095401 := bstep (se 2 (by rfl) ⟨410775, by rfl⟩ : syracuseStep 1095401 = 821551) B821551
theorem B12465899 : Blo 726324 12465899 := bstep (se 1 (by rfl) ⟨9349424, by rfl⟩ : syracuseStep 12465899 = 18698849) B18698849
theorem B1095407 : Blo 726324 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B2766919 : Blo 726324 2766919 := bstep (se 1 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 2766919 = 4150379) B4150379
theorem B1227305 : Blo 726324 1227305 := bstep (se 2 (by rfl) ⟨460239, by rfl⟩ : syracuseStep 1227305 = 920479) B920479
theorem B6994619 : Blo 726324 6994619 := bstep (se 1 (by rfl) ⟨5245964, by rfl⟩ : syracuseStep 6994619 = 10491929) B10491929
theorem B3160937 : Blo 726324 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B1555367 : Blo 726324 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B4209779 : Blo 726324 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1228007 : Blo 726324 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B2211391 : Blo 726324 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B6209783 : Blo 726324 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B12763453 : Blo 726324 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B3359335 : Blo 726324 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1753787 : Blo 726324 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B5620499 : Blo 726324 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B2770139 : Blo 726324 2770139 := bstep (se 1 (by rfl) ⟨2077604, by rfl⟩ : syracuseStep 2770139 = 4155209) B4155209
theorem B1230059 : Blo 726324 1230059 := bstep (se 1 (by rfl) ⟨922544, by rfl⟩ : syracuseStep 1230059 = 1845089) B1845089
theorem B935147 : Blo 726324 935147 := bstep (se 1 (by rfl) ⟨701360, by rfl⟩ : syracuseStep 935147 = 1402721) B1402721
theorem B1164623 : Blo 726324 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B5260727 : Blo 726324 5260727 := bstep (se 1 (by rfl) ⟨3945545, by rfl⟩ : syracuseStep 5260727 = 7891091) B7891091
theorem B1558187 : Blo 726324 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B1230511 : Blo 726324 1230511 := bstep (se 1 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 1230511 = 1845767) B1845767
theorem B11782007 : Blo 726324 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B12470273 : Blo 726324 12470273 := bstep (se 2 (by rfl) ⟨4676352, by rfl⟩ : syracuseStep 12470273 = 9352705) B9352705
theorem B5916827 : Blo 726324 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B4540697 : Blo 726324 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B2771279 : Blo 726324 2771279 := bstep (se 1 (by rfl) ⟨2078459, by rfl⟩ : syracuseStep 2771279 = 4156919) B4156919
theorem B1264223 : Blo 726324 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B3689063 : Blo 726324 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B1231463 : Blo 726324 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B7457773 : Blo 726324 7457773 := bstep (se 3 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 7457773 = 2796665) B2796665
theorem B9096425 : Blo 726324 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1232219 : Blo 726324 1232219 := bstep (se 1 (by rfl) ⟨924164, by rfl⟩ : syracuseStep 1232219 = 1848329) B1848329
theorem B6999767 : Blo 726324 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B7491685 : Blo 726324 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B8835439 : Blo 726324 8835439 := bstep (se 1 (by rfl) ⟨6626579, by rfl⟩ : syracuseStep 8835439 = 13253159) B13253159
theorem B4149629 : Blo 726324 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B5919101 : Blo 726324 5919101 := bstep (se 3 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 5919101 = 2219663) B2219663
theorem B2217593 : Blo 726324 2217593 := bstep (se 2 (by rfl) ⟨831597, by rfl⟩ : syracuseStep 2217593 = 1663195) B1663195
theorem B3692627 : Blo 726324 3692627 := bstep (se 1 (by rfl) ⟨2769470, by rfl⟩ : syracuseStep 3692627 = 5538941) B5538941
theorem B776795 : Blo 726324 776795 := bstep (se 1 (by rfl) ⟨582596, by rfl⟩ : syracuseStep 776795 = 1165193) B1165193
theorem B3103559 : Blo 726324 3103559 := bstep (se 1 (by rfl) ⟨2327669, by rfl⟩ : syracuseStep 3103559 = 4655339) B4655339
theorem B7887887 : Blo 726324 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B3694247 : Blo 726324 3694247 := bstep (se 1 (by rfl) ⟨2770685, by rfl⟩ : syracuseStep 3694247 = 5541371) B5541371
theorem B6315745 : Blo 726324 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B37773317 : Blo 726324 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B11985893 : Blo 726324 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B4154753 : Blo 726324 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B12609377 : Blo 726324 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B9332819 : Blo 726324 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B2451599 : Blo 726324 2451599 := bstep (se 1 (by rfl) ⟨1838699, by rfl⟩ : syracuseStep 2451599 = 3677399) B3677399
theorem B8284355 : Blo 726324 8284355 := bstep (se 1 (by rfl) ⟨6213266, by rfl⟩ : syracuseStep 8284355 = 12426533) B12426533
theorem B6646063 : Blo 726324 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B15133697 : Blo 726324 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B6220921 : Blo 726324 6220921 := bstep (se 2 (by rfl) ⟨2332845, by rfl⟩ : syracuseStep 6220921 = 4665691) B4665691
theorem B25260055 : Blo 726324 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B1634579 : Blo 726324 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B1634759 : Blo 726324 1634759 := bstep (se 1 (by rfl) ⟨1226069, by rfl⟩ : syracuseStep 1634759 = 2452139) B2452139
theorem B2454191 : Blo 726324 2454191 := bstep (se 1 (by rfl) ⟨1840643, by rfl⟩ : syracuseStep 2454191 = 3681287) B3681287
theorem B1635119 : Blo 726324 1635119 := bstep (se 1 (by rfl) ⟨1226339, by rfl⟩ : syracuseStep 1635119 = 2452679) B2452679
theorem B1635209 : Blo 726324 1635209 := bstep (se 2 (by rfl) ⟨613203, by rfl⟩ : syracuseStep 1635209 = 1226407) B1226407
theorem B6910951 : Blo 726324 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B11203667 : Blo 726324 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B9860203 : Blo 726324 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B3110359 : Blo 726324 3110359 := bstep (se 1 (by rfl) ⟨2332769, by rfl⟩ : syracuseStep 3110359 = 4665539) B4665539
theorem B3503711 : Blo 726324 3503711 := bstep (se 1 (by rfl) ⟨2627783, by rfl⟩ : syracuseStep 3503711 = 5255567) B5255567
theorem B1635983 : Blo 726324 1635983 := bstep (se 1 (by rfl) ⟨1226987, by rfl⟩ : syracuseStep 1635983 = 2453975) B2453975
theorem B1636073 : Blo 726324 1636073 := bstep (se 2 (by rfl) ⟨613527, by rfl⟩ : syracuseStep 1636073 = 1227055) B1227055
theorem B15759521 : Blo 726324 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B1636955 : Blo 726324 1636955 := bstep (se 1 (by rfl) ⟨1227716, by rfl⟩ : syracuseStep 1636955 = 2455433) B2455433
theorem B1637099 : Blo 726324 1637099 := bstep (se 1 (by rfl) ⟨1227824, by rfl⟩ : syracuseStep 1637099 = 2455649) B2455649
theorem B14220157 : Blo 726324 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B818383 : Blo 726324 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1637711 : Blo 726324 1637711 := bstep (se 1 (by rfl) ⟨1228283, by rfl⟩ : syracuseStep 1637711 = 2456567) B2456567
theorem B1637801 : Blo 726324 1637801 := bstep (se 2 (by rfl) ⟨614175, by rfl⟩ : syracuseStep 1637801 = 1228351) B1228351
theorem B2457107 : Blo 726324 2457107 := bstep (se 1 (by rfl) ⟨1842830, by rfl⟩ : syracuseStep 2457107 = 3685661) B3685661
theorem B1637999 : Blo 726324 1637999 := bstep (se 1 (by rfl) ⟨1228499, by rfl⟩ : syracuseStep 1637999 = 2456999) B2456999
theorem B1965833 : Blo 726324 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B1638287 : Blo 726324 1638287 := bstep (se 1 (by rfl) ⟨1228715, by rfl⟩ : syracuseStep 1638287 = 2457431) B2457431
theorem B1310663 : Blo 726324 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B6226253 : Blo 726324 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B1180327 : Blo 726324 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B1049375 : Blo 726324 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B1639223 : Blo 726324 1639223 := bstep (se 1 (by rfl) ⟨1229417, by rfl⟩ : syracuseStep 1639223 = 2458835) B2458835
theorem B820039 : Blo 726324 820039 := bstep (se 1 (by rfl) ⟨615029, by rfl⟩ : syracuseStep 820039 = 1230059) B1230059
theorem B3507151 : Blo 726324 3507151 := bstep (se 1 (by rfl) ⟨2630363, by rfl⟩ : syracuseStep 3507151 = 5260727) B5260727
theorem B1639403 : Blo 726324 1639403 := bstep (se 1 (by rfl) ⟨1229552, by rfl⟩ : syracuseStep 1639403 = 2459105) B2459105
theorem B4654415 : Blo 726324 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B919279 : Blo 726324 919279 := bstep (se 1 (by rfl) ⟨689459, by rfl⟩ : syracuseStep 919279 = 1378919) B1378919
theorem B2459375 : Blo 726324 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B820975 : Blo 726324 820975 := bstep (se 1 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 820975 = 1231463) B1231463
theorem B1640303 : Blo 726324 1640303 := bstep (se 1 (by rfl) ⟨1230227, by rfl⟩ : syracuseStep 1640303 = 2460455) B2460455
theorem B1640411 : Blo 726324 1640411 := bstep (se 1 (by rfl) ⟨1230308, by rfl⟩ : syracuseStep 1640411 = 2460617) B2460617
theorem B2623529 : Blo 726324 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B1640519 : Blo 726324 1640519 := bstep (se 1 (by rfl) ⟨1230389, by rfl⟩ : syracuseStep 1640519 = 2460779) B2460779
theorem B1640591 : Blo 726324 1640591 := bstep (se 1 (by rfl) ⟨1230443, by rfl⟩ : syracuseStep 1640591 = 2460887) B2460887
theorem B6064283 : Blo 726324 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B821479 : Blo 726324 821479 := bstep (se 1 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 821479 = 1232219) B1232219
theorem B1640681 : Blo 726324 1640681 := bstep (se 2 (by rfl) ⟨615255, by rfl⟩ : syracuseStep 1640681 = 1230511) B1230511
theorem B1640699 : Blo 726324 1640699 := bstep (se 1 (by rfl) ⟨1230524, by rfl⟩ : syracuseStep 1640699 = 2461049) B2461049
theorem B1640951 : Blo 726324 1640951 := bstep (se 1 (by rfl) ⟨1230713, by rfl⟩ : syracuseStep 1640951 = 2461427) B2461427
theorem B4197203 : Blo 726324 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B2624567 : Blo 726324 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B2493725 : Blo 726324 2493725 := bstep (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) B935147
theorem B1478395 : Blo 726324 1478395 := bstep (se 1 (by rfl) ⟨1108796, by rfl⟩ : syracuseStep 1478395 = 2217593) B2217593
theorem B2461751 : Blo 726324 2461751 := bstep (se 1 (by rfl) ⟨1846313, by rfl⟩ : syracuseStep 2461751 = 3692627) B3692627
theorem B8294561 : Blo 726324 8294561 := bstep (se 2 (by rfl) ⟨3110460, by rfl⟩ : syracuseStep 8294561 = 6220921) B6220921
theorem B2069039 : Blo 726324 2069039 := bstep (se 1 (by rfl) ⟨1551779, by rfl⟩ : syracuseStep 2069039 = 3103559) B3103559
theorem B2101889 : Blo 726324 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B7869203 : Blo 726324 7869203 := bstep (se 1 (by rfl) ⟨5901902, by rfl⟩ : syracuseStep 7869203 = 11803805) B11803805
theorem B7017299 : Blo 726324 7017299 := bstep (se 1 (by rfl) ⟨5262974, by rfl⟩ : syracuseStep 7017299 = 10525949) B10525949
theorem B2462831 : Blo 726324 2462831 := bstep (se 1 (by rfl) ⟨1847123, by rfl⟩ : syracuseStep 2462831 = 3694247) B3694247
theorem B1840553 : Blo 726324 1840553 := bstep (se 2 (by rfl) ⟨690207, by rfl⟩ : syracuseStep 1840553 = 1380415) B1380415
theorem B726495 : Blo 726324 726495 := bstep (se 1 (by rfl) ⟨544871, by rfl⟩ : syracuseStep 726495 = 1089743) B1089743
theorem B726527 : Blo 726324 726527 := bstep (se 1 (by rfl) ⟨544895, by rfl⟩ : syracuseStep 726527 = 1089791) B1089791
theorem B727071 : Blo 726324 727071 := bstep (se 1 (by rfl) ⟨545303, by rfl⟩ : syracuseStep 727071 = 1090607) B1090607
theorem B727151 : Blo 726324 727151 := bstep (se 1 (by rfl) ⟨545363, by rfl⟩ : syracuseStep 727151 = 1090727) B1090727
theorem B727399 : Blo 726324 727399 := bstep (se 1 (by rfl) ⟨545549, by rfl⟩ : syracuseStep 727399 = 1091099) B1091099
theorem B2070953 : Blo 726324 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B3938753 : Blo 726324 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B727655 : Blo 726324 727655 := bstep (se 1 (by rfl) ⟨545741, by rfl⟩ : syracuseStep 727655 = 1091483) B1091483
theorem B727679 : Blo 726324 727679 := bstep (se 1 (by rfl) ⟨545759, by rfl⟩ : syracuseStep 727679 = 1091519) B1091519
theorem B727803 : Blo 726324 727803 := bstep (se 1 (by rfl) ⟨545852, by rfl⟩ : syracuseStep 727803 = 1091705) B1091705
theorem B13146937 : Blo 726324 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B1842041 : Blo 726324 1842041 := bstep (se 2 (by rfl) ⟨690765, by rfl⟩ : syracuseStep 1842041 = 1381531) B1381531
theorem B728059 : Blo 726324 728059 := bstep (se 1 (by rfl) ⟨546044, by rfl⟩ : syracuseStep 728059 = 1092089) B1092089
theorem B728095 : Blo 726324 728095 := bstep (se 1 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 728095 = 1092143) B1092143
theorem B728383 : Blo 726324 728383 := bstep (se 1 (by rfl) ⟨546287, by rfl⟩ : syracuseStep 728383 = 1092575) B1092575
theorem B728679 : Blo 726324 728679 := bstep (se 1 (by rfl) ⟨546509, by rfl⟩ : syracuseStep 728679 = 1093019) B1093019
theorem B1842983 : Blo 726324 1842983 := bstep (se 1 (by rfl) ⟨1382237, by rfl⟩ : syracuseStep 1842983 = 2764475) B2764475
theorem B728959 : Blo 726324 728959 := bstep (se 1 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 728959 = 1093439) B1093439
theorem B729083 : Blo 726324 729083 := bstep (se 1 (by rfl) ⟨546812, by rfl⟩ : syracuseStep 729083 = 1093625) B1093625
theorem B729243 : Blo 726324 729243 := bstep (se 1 (by rfl) ⟨546932, by rfl⟩ : syracuseStep 729243 = 1093865) B1093865
theorem B1089719 : Blo 726324 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B729327 : Blo 726324 729327 := bstep (se 1 (by rfl) ⟨546995, by rfl⟩ : syracuseStep 729327 = 1093991) B1093991
theorem B4727069 : Blo 726324 4727069 := bstep (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) B1772651
theorem B1089839 : Blo 726324 1089839 := bstep (se 1 (by rfl) ⟨817379, by rfl⟩ : syracuseStep 1089839 = 1634759) B1634759
theorem B1384751 : Blo 726324 1384751 := bstep (se 1 (by rfl) ⟨1038563, by rfl⟩ : syracuseStep 1384751 = 2077127) B2077127
theorem B2761087 : Blo 726324 2761087 := bstep (se 1 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 2761087 = 4141631) B4141631
theorem B1090079 : Blo 726324 1090079 := bstep (se 1 (by rfl) ⟨817559, by rfl⟩ : syracuseStep 1090079 = 1635119) B1635119
theorem B1090139 : Blo 726324 1090139 := bstep (se 1 (by rfl) ⟨817604, by rfl⟩ : syracuseStep 1090139 = 1635209) B1635209
theorem B729691 : Blo 726324 729691 := bstep (se 1 (by rfl) ⟨547268, by rfl⟩ : syracuseStep 729691 = 1094537) B1094537
theorem B1843823 : Blo 726324 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B3678857 : Blo 726324 3678857 := bstep (se 2 (by rfl) ⟨1379571, by rfl⟩ : syracuseStep 3678857 = 2759143) B2759143
theorem B2761391 : Blo 726324 2761391 := bstep (se 1 (by rfl) ⟨2071043, by rfl⟩ : syracuseStep 2761391 = 4142087) B4142087
theorem B729947 : Blo 726324 729947 := bstep (se 1 (by rfl) ⟨547460, by rfl⟩ : syracuseStep 729947 = 1094921) B1094921
theorem B729983 : Blo 726324 729983 := bstep (se 1 (by rfl) ⟨547487, by rfl⟩ : syracuseStep 729983 = 1094975) B1094975
theorem B2335807 : Blo 726324 2335807 := bstep (se 1 (by rfl) ⟨1751855, by rfl⟩ : syracuseStep 2335807 = 3503711) B3503711
theorem B1090655 : Blo 726324 1090655 := bstep (se 1 (by rfl) ⟨817991, by rfl⟩ : syracuseStep 1090655 = 1635983) B1635983
theorem B1385579 : Blo 726324 1385579 := bstep (se 1 (by rfl) ⟨1039184, by rfl⟩ : syracuseStep 1385579 = 2078369) B2078369
theorem B1090715 : Blo 726324 1090715 := bstep (se 1 (by rfl) ⟨818036, by rfl⟩ : syracuseStep 1090715 = 1636073) B1636073
theorem B730267 : Blo 726324 730267 := bstep (se 1 (by rfl) ⟨547700, by rfl⟩ : syracuseStep 730267 = 1095401) B1095401
theorem B730271 : Blo 726324 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B7873793 : Blo 726324 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B1091177 : Blo 726324 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B1091303 : Blo 726324 1091303 := bstep (se 1 (by rfl) ⟨818477, by rfl⟩ : syracuseStep 1091303 = 1636955) B1636955
theorem B4663079 : Blo 726324 4663079 := bstep (se 1 (by rfl) ⟨3497309, by rfl⟩ : syracuseStep 4663079 = 6994619) B6994619
theorem B1091399 : Blo 726324 1091399 := bstep (se 1 (by rfl) ⟨818549, by rfl⟩ : syracuseStep 1091399 = 1637099) B1637099
theorem B2107291 : Blo 726324 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B2762849 : Blo 726324 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B147433621 : Blo 726324 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B1091807 : Blo 726324 1091807 := bstep (se 1 (by rfl) ⟨818855, by rfl⟩ : syracuseStep 1091807 = 1637711) B1637711
theorem B1091867 : Blo 726324 1091867 := bstep (se 1 (by rfl) ⟨818900, by rfl⟩ : syracuseStep 1091867 = 1637801) B1637801
theorem B1091999 : Blo 726324 1091999 := bstep (se 1 (by rfl) ⟨818999, by rfl⟩ : syracuseStep 1091999 = 1637999) B1637999
theorem B1845737 : Blo 726324 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B1092191 : Blo 726324 1092191 := bstep (se 1 (by rfl) ⟨819143, by rfl⟩ : syracuseStep 1092191 = 1638287) B1638287
theorem B134720293 : Blo 726324 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B4139855 : Blo 726324 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B1092521 : Blo 726324 1092521 := bstep (se 2 (by rfl) ⟨409695, by rfl⟩ : syracuseStep 1092521 = 819391) B819391
theorem B1092551 : Blo 726324 1092551 := bstep (se 1 (by rfl) ⟨819413, by rfl⟩ : syracuseStep 1092551 = 1638827) B1638827
theorem B4205513 : Blo 726324 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B1092671 : Blo 726324 1092671 := bstep (se 1 (by rfl) ⟨819503, by rfl⟩ : syracuseStep 1092671 = 1639007) B1639007
theorem B17017937 : Blo 726324 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B3746999 : Blo 726324 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B1092911 : Blo 726324 1092911 := bstep (se 1 (by rfl) ⟨819683, by rfl⟩ : syracuseStep 1092911 = 1639367) B1639367
theorem B1846759 : Blo 726324 1846759 := bstep (se 1 (by rfl) ⟨1385069, by rfl⟩ : syracuseStep 1846759 = 2770139) B2770139
theorem B1093097 : Blo 726324 1093097 := bstep (se 2 (by rfl) ⟨409911, by rfl⟩ : syracuseStep 1093097 = 819823) B819823
theorem B1093151 : Blo 726324 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B1093241 : Blo 726324 1093241 := bstep (se 2 (by rfl) ⟨409965, by rfl⟩ : syracuseStep 1093241 = 819931) B819931
theorem B1093487 : Blo 726324 1093487 := bstep (se 1 (by rfl) ⟨820115, by rfl⟩ : syracuseStep 1093487 = 1640231) B1640231
theorem B3944551 : Blo 726324 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B1093739 : Blo 726324 1093739 := bstep (se 1 (by rfl) ⟨820304, by rfl⟩ : syracuseStep 1093739 = 1640609) B1640609
theorem B2764961 : Blo 726324 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B3027131 : Blo 726324 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B6992081 : Blo 726324 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1847519 : Blo 726324 1847519 := bstep (se 1 (by rfl) ⟨1385639, by rfl⟩ : syracuseStep 1847519 = 2771279) B2771279
theorem B1749289 : Blo 726324 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B1094171 : Blo 726324 1094171 := bstep (se 1 (by rfl) ⟨820628, by rfl⟩ : syracuseStep 1094171 = 1641257) B1641257
theorem B24228503 : Blo 726324 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B1094351 : Blo 726324 1094351 := bstep (se 1 (by rfl) ⟨820763, by rfl⟩ : syracuseStep 1094351 = 1641527) B1641527
theorem B1094639 : Blo 726324 1094639 := bstep (se 1 (by rfl) ⟨820979, by rfl⟩ : syracuseStep 1094639 = 1641959) B1641959
theorem B4666511 : Blo 726324 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B1095023 : Blo 726324 1095023 := bstep (se 1 (by rfl) ⟨821267, by rfl⟩ : syracuseStep 1095023 = 1642535) B1642535
theorem B8107451 : Blo 726324 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B1095143 : Blo 726324 1095143 := bstep (se 1 (by rfl) ⟨821357, by rfl⟩ : syracuseStep 1095143 = 1642715) B1642715
theorem B2766419 : Blo 726324 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B3946067 : Blo 726324 3946067 := bstep (se 1 (by rfl) ⟨2959550, by rfl⟩ : syracuseStep 3946067 = 5919101) B5919101
theorem B1095323 : Blo 726324 1095323 := bstep (se 1 (by rfl) ⟨821492, by rfl⟩ : syracuseStep 1095323 = 1642985) B1642985
theorem B8861417 : Blo 726324 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B1751327 : Blo 726324 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B4995689 : Blo 726324 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B9943697 : Blo 726324 9943697 := bstep (se 2 (by rfl) ⟨3728886, by rfl⟩ : syracuseStep 9943697 = 7457773) B7457773
theorem B5258591 : Blo 726324 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B9322361 : Blo 726324 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B25182211 : Blo 726324 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B1229033 : Blo 726324 1229033 := bstep (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) B921775
theorem B11780585 : Blo 726324 11780585 := bstep (se 2 (by rfl) ⟨4417719, by rfl⟩ : syracuseStep 11780585 = 8835439) B8835439
theorem B2212435 : Blo 726324 2212435 := bstep (se 1 (by rfl) ⟨1659326, by rfl⟩ : syracuseStep 2212435 = 3318653) B3318653
theorem B2769835 : Blo 726324 2769835 := bstep (se 1 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 2769835 = 4154753) B4154753
theorem B8406251 : Blo 726324 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B5522903 : Blo 726324 5522903 := bstep (se 1 (by rfl) ⟨4142177, by rfl⟩ : syracuseStep 5522903 = 8284355) B8284355
theorem B4147145 : Blo 726324 4147145 := bstep (se 2 (by rfl) ⟨1555179, by rfl⟩ : syracuseStep 4147145 = 3110359) B3110359
theorem B1230815 : Blo 726324 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B1231031 : Blo 726324 1231031 := bstep (se 1 (by rfl) ⟨923273, by rfl⟩ : syracuseStep 1231031 = 1846547) B1846547
theorem B105171209 : Blo 726324 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B4147645 : Blo 726324 4147645 := bstep (se 3 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 4147645 = 1555367) B1555367
theorem B3689225 : Blo 726324 3689225 := bstep (se 2 (by rfl) ⟨1383459, by rfl⟩ : syracuseStep 3689225 = 2766919) B2766919
theorem B11226077 : Blo 726324 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B17681485 : Blo 726324 17681485 := bstep (se 3 (by rfl) ⟨3315278, by rfl⟩ : syracuseStep 17681485 = 6630557) B6630557
theorem B2215259 : Blo 726324 2215259 := bstep (se 1 (by rfl) ⟨1661444, by rfl⟩ : syracuseStep 2215259 = 3322889) B3322889
theorem B8310599 : Blo 726324 8310599 := bstep (se 1 (by rfl) ⟨6232949, by rfl⟩ : syracuseStep 8310599 = 12465899) B12465899
theorem B18960209 : Blo 726324 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B10506347 : Blo 726324 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B873775 : Blo 726324 873775 := bstep (se 1 (by rfl) ⟨655331, by rfl⟩ : syracuseStep 873775 = 1310663) B1310663
theorem B874279 : Blo 726324 874279 := bstep (se 1 (by rfl) ⟨655709, by rfl⟩ : syracuseStep 874279 = 1311419) B1311419
theorem B1169191 : Blo 726324 1169191 := bstep (se 1 (by rfl) ⟨876893, by rfl⟩ : syracuseStep 1169191 = 1753787) B1753787
theorem B4479113 : Blo 726324 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B1038791 : Blo 726324 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B7854671 : Blo 726324 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B8313515 : Blo 726324 8313515 := bstep (se 1 (by rfl) ⟨6235136, by rfl⟩ : syracuseStep 8313515 = 12470273) B12470273
theorem B1661627 : Blo 726324 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B842815 : Blo 726324 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B3105661 : Blo 726324 3105661 := bstep (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) B1164623
theorem B3696029 : Blo 726324 3696029 := bstep (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) B1386011
theorem B3696191 : Blo 726324 3696191 := bstep (se 1 (by rfl) ⟨2772143, by rfl⟩ : syracuseStep 3696191 = 5544287) B5544287
theorem B9988913 : Blo 726324 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B8317889 : Blo 726324 8317889 := bstep (se 2 (by rfl) ⟨3119208, by rfl⟩ : syracuseStep 8317889 = 6238417) B6238417
theorem B2452733 : Blo 726324 2452733 := bstep (se 3 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 2452733 = 919775) B919775
theorem B7990595 : Blo 726324 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B8285813 : Blo 726324 8285813 := bstep (se 5 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 8285813 = 776795) B776795
theorem B2453273 : Blo 726324 2453273 := bstep (se 2 (by rfl) ⟨919977, by rfl⟩ : syracuseStep 2453273 = 1839955) B1839955
theorem B6221879 : Blo 726324 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B1634399 : Blo 726324 1634399 := bstep (se 1 (by rfl) ⟨1225799, by rfl⟩ : syracuseStep 1634399 = 2451599) B2451599
theorem B4420199 : Blo 726324 4420199 := bstep (se 1 (by rfl) ⟨3315149, by rfl⟩ : syracuseStep 4420199 = 6630299) B6630299
theorem B10089131 : Blo 726324 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B1636127 : Blo 726324 1636127 := bstep (se 1 (by rfl) ⟨1227095, by rfl⟩ : syracuseStep 1636127 = 2454191) B2454191
theorem B7469111 : Blo 726324 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B2456297 : Blo 726324 2456297 := bstep (se 2 (by rfl) ⟨921111, by rfl⟩ : syracuseStep 2456297 = 1842223) B1842223
theorem B818203 : Blo 726324 818203 := bstep (se 1 (by rfl) ⟨613652, by rfl⟩ : syracuseStep 818203 = 1227305) B1227305
theorem B2948521 : Blo 726324 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B818671 : Blo 726324 818671 := bstep (se 1 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 818671 = 1228007) B1228007
theorem B1277561 : Blo 726324 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B8420993 : Blo 726324 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B1638071 : Blo 726324 1638071 := bstep (se 1 (by rfl) ⟨1228553, by rfl⟩ : syracuseStep 1638071 = 2457107) B2457107
theorem B1310555 : Blo 726324 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B819355 : Blo 726324 819355 := bstep (se 1 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 819355 = 1229033) B1229033
theorem B2949913 : Blo 726324 2949913 := bstep (se 2 (by rfl) ⟨1106217, by rfl⟩ : syracuseStep 2949913 = 2212435) B2212435
theorem B5604167 : Blo 726324 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B1573769 : Blo 726324 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B1639583 : Blo 726324 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B820543 : Blo 726324 820543 := bstep (se 1 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 820543 = 1230815) B1230815
theorem B3114409 : Blo 726324 3114409 := bstep (se 2 (by rfl) ⟨1167903, by rfl⟩ : syracuseStep 3114409 = 2335807) B2335807
theorem B820687 : Blo 726324 820687 := bstep (se 1 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 820687 = 1231031) B1231031
theorem B5605037 : Blo 726324 5605037 := bstep (se 3 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 5605037 = 2101889) B2101889
theorem B26904349 : Blo 726324 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B2459483 : Blo 726324 2459483 := bstep (se 1 (by rfl) ⟨1844612, by rfl⟩ : syracuseStep 2459483 = 3689225) B3689225
theorem B1476839 : Blo 726324 1476839 := bstep (se 1 (by rfl) ⟨1107629, by rfl⟩ : syracuseStep 1476839 = 2215259) B2215259
theorem B5540399 : Blo 726324 5540399 := bstep (se 1 (by rfl) ⟨4155299, by rfl⟩ : syracuseStep 5540399 = 8310599) B8310599
theorem B1641167 : Blo 726324 1641167 := bstep (se 1 (by rfl) ⟨1230875, by rfl⟩ : syracuseStep 1641167 = 2461751) B2461751
theorem B196578161 : Blo 726324 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B1379359 : Blo 726324 1379359 := bstep (se 1 (by rfl) ⟨1034519, by rfl⟩ : syracuseStep 1379359 = 2069039) B2069039
theorem B5246135 : Blo 726324 5246135 := bstep (se 1 (by rfl) ⟨3934601, by rfl⟩ : syracuseStep 5246135 = 7869203) B7869203
theorem B1641887 : Blo 726324 1641887 := bstep (se 1 (by rfl) ⟨1231415, by rfl⟩ : syracuseStep 1641887 = 2462831) B2462831
theorem B2986075 : Blo 726324 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B1380635 : Blo 726324 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B5542343 : Blo 726324 5542343 := bstep (se 1 (by rfl) ⟨4156757, by rfl⟩ : syracuseStep 5542343 = 8313515) B8313515
theorem B2462345 : Blo 726324 2462345 := bstep (se 2 (by rfl) ⟨923379, by rfl⟩ : syracuseStep 2462345 = 1846759) B1846759
theorem B726479 : Blo 726324 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B3151379 : Blo 726324 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B726559 : Blo 726324 726559 := bstep (se 1 (by rfl) ⟨544919, by rfl⟩ : syracuseStep 726559 = 1089839) B1089839
theorem B923167 : Blo 726324 923167 := bstep (se 1 (by rfl) ⟨692375, by rfl⟩ : syracuseStep 923167 = 1384751) B1384751
theorem B4495013 : Blo 726324 4495013 := bstep (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) B842815
theorem B726719 : Blo 726324 726719 := bstep (se 1 (by rfl) ⟨545039, by rfl⟩ : syracuseStep 726719 = 1090079) B1090079
theorem B2332385 : Blo 726324 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B726759 : Blo 726324 726759 := bstep (se 1 (by rfl) ⟨545069, by rfl⟩ : syracuseStep 726759 = 1090139) B1090139
theorem B1840927 : Blo 726324 1840927 := bstep (se 1 (by rfl) ⟨1380695, by rfl⟩ : syracuseStep 1840927 = 2761391) B2761391
theorem B727103 : Blo 726324 727103 := bstep (se 1 (by rfl) ⟨545327, by rfl⟩ : syracuseStep 727103 = 1090655) B1090655
theorem B923719 : Blo 726324 923719 := bstep (se 1 (by rfl) ⟨692789, by rfl⟩ : syracuseStep 923719 = 1385579) B1385579
theorem B727143 : Blo 726324 727143 := bstep (se 1 (by rfl) ⟨545357, by rfl⟩ : syracuseStep 727143 = 1090715) B1090715
theorem B5249195 : Blo 726324 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B2464019 : Blo 726324 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B2464127 : Blo 726324 2464127 := bstep (se 1 (by rfl) ⟨1848095, by rfl⟩ : syracuseStep 2464127 = 3696191) B3696191
theorem B727451 : Blo 726324 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B727535 : Blo 726324 727535 := bstep (se 1 (by rfl) ⟨545651, by rfl⟩ : syracuseStep 727535 = 1091303) B1091303
theorem B727599 : Blo 726324 727599 := bstep (se 1 (by rfl) ⟨545699, by rfl⟩ : syracuseStep 727599 = 1091399) B1091399
theorem B1841899 : Blo 726324 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B727871 : Blo 726324 727871 := bstep (se 1 (by rfl) ⟨545903, by rfl⟩ : syracuseStep 727871 = 1091807) B1091807
theorem B727911 : Blo 726324 727911 := bstep (se 1 (by rfl) ⟨545933, by rfl⟩ : syracuseStep 727911 = 1091867) B1091867
theorem B20945789 : Blo 726324 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B727999 : Blo 726324 727999 := bstep (se 1 (by rfl) ⟨545999, by rfl⟩ : syracuseStep 727999 = 1091999) B1091999
theorem B728127 : Blo 726324 728127 := bstep (se 1 (by rfl) ⟨546095, by rfl⟩ : syracuseStep 728127 = 1092191) B1092191
theorem B6659275 : Blo 726324 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B2759903 : Blo 726324 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B728347 : Blo 726324 728347 := bstep (se 1 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 728347 = 1092521) B1092521
theorem B5545259 : Blo 726324 5545259 := bstep (se 1 (by rfl) ⟨4158944, by rfl⟩ : syracuseStep 5545259 = 8317889) B8317889
theorem B728367 : Blo 726324 728367 := bstep (se 1 (by rfl) ⟨546275, by rfl⟩ : syracuseStep 728367 = 1092551) B1092551
theorem B728447 : Blo 726324 728447 := bstep (se 1 (by rfl) ⟨546335, by rfl⟩ : syracuseStep 728447 = 1092671) B1092671
theorem B11345291 : Blo 726324 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B2497999 : Blo 726324 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B728607 : Blo 726324 728607 := bstep (se 1 (by rfl) ⟨546455, by rfl⟩ : syracuseStep 728607 = 1092911) B1092911
theorem B728731 : Blo 726324 728731 := bstep (se 1 (by rfl) ⟨546548, by rfl⟩ : syracuseStep 728731 = 1093097) B1093097
theorem B728767 : Blo 726324 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B728827 : Blo 726324 728827 := bstep (se 1 (by rfl) ⟨546620, by rfl⟩ : syracuseStep 728827 = 1093241) B1093241
theorem B728991 : Blo 726324 728991 := bstep (se 1 (by rfl) ⟨546743, by rfl⟩ : syracuseStep 728991 = 1093487) B1093487
theorem B1089599 : Blo 726324 1089599 := bstep (se 1 (by rfl) ⟨817199, by rfl⟩ : syracuseStep 1089599 = 1634399) B1634399
theorem B729159 : Blo 726324 729159 := bstep (se 1 (by rfl) ⟨546869, by rfl⟩ : syracuseStep 729159 = 1093739) B1093739
theorem B1843307 : Blo 726324 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B4661387 : Blo 726324 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B729447 : Blo 726324 729447 := bstep (se 1 (by rfl) ⟨547085, by rfl⟩ : syracuseStep 729447 = 1094171) B1094171
theorem B729567 : Blo 726324 729567 := bstep (se 1 (by rfl) ⟨547175, by rfl⟩ : syracuseStep 729567 = 1094351) B1094351
theorem B729759 : Blo 726324 729759 := bstep (se 1 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 729759 = 1094639) B1094639
theorem B730015 : Blo 726324 730015 := bstep (se 1 (by rfl) ⟨547511, by rfl⟩ : syracuseStep 730015 = 1095023) B1095023
theorem B730095 : Blo 726324 730095 := bstep (se 1 (by rfl) ⟨547571, by rfl⟩ : syracuseStep 730095 = 1095143) B1095143
theorem B1844279 : Blo 726324 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B2630711 : Blo 726324 2630711 := bstep (se 1 (by rfl) ⟨1973033, by rfl⟩ : syracuseStep 2630711 = 3946067) B3946067
theorem B730215 : Blo 726324 730215 := bstep (se 1 (by rfl) ⟨547661, by rfl⟩ : syracuseStep 730215 = 1095323) B1095323
theorem B5907611 : Blo 726324 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B1090751 : Blo 726324 1090751 := bstep (se 1 (by rfl) ⟨818063, by rfl⟩ : syracuseStep 1090751 = 1636127) B1636127
theorem B1090937 : Blo 726324 1090937 := bstep (se 2 (by rfl) ⟨409101, by rfl⟩ : syracuseStep 1090937 = 818203) B818203
theorem B4662821 : Blo 726324 4662821 := bstep (se 4 (by rfl) ⟨437139, by rfl⟩ : syracuseStep 4662821 = 874279) B874279
theorem B6629131 : Blo 726324 6629131 := bstep (se 1 (by rfl) ⟨4971848, by rfl⟩ : syracuseStep 6629131 = 9943697) B9943697
theorem B1091561 : Blo 726324 1091561 := bstep (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) B818671
theorem B5613995 : Blo 726324 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B1092047 : Blo 726324 1092047 := bstep (se 1 (by rfl) ⟨819035, by rfl⟩ : syracuseStep 1092047 = 1638071) B1638071
theorem B3681449 : Blo 726324 3681449 := bstep (se 2 (by rfl) ⟨1380543, by rfl⟩ : syracuseStep 3681449 = 2761087) B2761087
theorem B1092815 : Blo 726324 1092815 := bstep (se 1 (by rfl) ⟨819611, by rfl⟩ : syracuseStep 1092815 = 1639223) B1639223
theorem B1092935 : Blo 726324 1092935 := bstep (se 1 (by rfl) ⟨819701, by rfl⟩ : syracuseStep 1092935 = 1639403) B1639403
theorem B3681935 : Blo 726324 3681935 := bstep (se 1 (by rfl) ⟨2761451, by rfl⟩ : syracuseStep 3681935 = 5522903) B5522903
theorem B1093385 : Blo 726324 1093385 := bstep (se 2 (by rfl) ⟨410019, by rfl⟩ : syracuseStep 1093385 = 820039) B820039
theorem B4140881 : Blo 726324 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B1093535 : Blo 726324 1093535 := bstep (se 1 (by rfl) ⟨820151, by rfl⟩ : syracuseStep 1093535 = 1640303) B1640303
theorem B2764763 : Blo 726324 2764763 := bstep (se 1 (by rfl) ⟨2073572, by rfl⟩ : syracuseStep 2764763 = 4147145) B4147145
theorem B1093607 : Blo 726324 1093607 := bstep (se 1 (by rfl) ⟨820205, by rfl⟩ : syracuseStep 1093607 = 1640411) B1640411
theorem B1093679 : Blo 726324 1093679 := bstep (se 1 (by rfl) ⟨820259, by rfl⟩ : syracuseStep 1093679 = 1640519) B1640519
theorem B1093727 : Blo 726324 1093727 := bstep (se 1 (by rfl) ⟨820295, by rfl⟩ : syracuseStep 1093727 = 1640591) B1640591
theorem B4042855 : Blo 726324 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1093787 : Blo 726324 1093787 := bstep (se 1 (by rfl) ⟨820340, by rfl⟩ : syracuseStep 1093787 = 1640681) B1640681
theorem B1093799 : Blo 726324 1093799 := bstep (se 1 (by rfl) ⟨820349, by rfl⟩ : syracuseStep 1093799 = 1640699) B1640699
theorem B1093967 : Blo 726324 1093967 := bstep (se 1 (by rfl) ⟨820475, by rfl⟩ : syracuseStep 1093967 = 1640951) B1640951
theorem B2798135 : Blo 726324 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B7484051 : Blo 726324 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B2798333 : Blo 726324 2798333 := bstep (se 3 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 2798333 = 1049375) B1049375
theorem B1225705 : Blo 726324 1225705 := bstep (se 2 (by rfl) ⟨459639, by rfl⟩ : syracuseStep 1225705 = 919279) B919279
theorem B1094633 : Blo 726324 1094633 := bstep (se 2 (by rfl) ⟨410487, by rfl⟩ : syracuseStep 1094633 = 820975) B820975
theorem B1095305 : Blo 726324 1095305 := bstep (se 2 (by rfl) ⟨410739, by rfl⟩ : syracuseStep 1095305 = 821479) B821479
theorem B1227035 : Blo 726324 1227035 := bstep (se 1 (by rfl) ⟨920276, by rfl⟩ : syracuseStep 1227035 = 1840553) B1840553
theorem B23575313 : Blo 726324 23575313 := bstep (se 2 (by rfl) ⟨8840742, by rfl⟩ : syracuseStep 23575313 = 17681485) B17681485
theorem B1228027 : Blo 726324 1228027 := bstep (se 1 (by rfl) ⟨921020, by rfl⟩ : syracuseStep 1228027 = 1842041) B1842041
theorem B1228655 : Blo 726324 1228655 := bstep (se 1 (by rfl) ⟨921491, by rfl⟩ : syracuseStep 1228655 = 1842983) B1842983
theorem B6996077 : Blo 726324 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B5259401 : Blo 726324 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B1229215 : Blo 726324 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B10503341 : Blo 726324 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B2770109 : Blo 726324 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B13321837 : Blo 726324 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B1230491 : Blo 726324 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B1165033 : Blo 726324 1165033 := bstep (se 2 (by rfl) ⟨436887, by rfl⟩ : syracuseStep 1165033 = 873775) B873775
theorem B2803675 : Blo 726324 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B5327063 : Blo 726324 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B1558921 : Blo 726324 1558921 := bstep (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) B1169191
theorem B5523875 : Blo 726324 5523875 := bstep (se 1 (by rfl) ⟨4142906, by rfl⟩ : syracuseStep 5523875 = 8285813) B8285813
theorem B4147919 : Blo 726324 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B2018087 : Blo 726324 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B6998845 : Blo 726324 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B1231679 : Blo 726324 1231679 := bstep (se 1 (by rfl) ⟨923759, by rfl⟩ : syracuseStep 1231679 = 1847519) B1847519
theorem B7884773 : Blo 726324 7884773 := bstep (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) B1478395
theorem B1167551 : Blo 726324 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B873703 : Blo 726324 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B6214907 : Blo 726324 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B33576281 : Blo 726324 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B4150835 : Blo 726324 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B7853723 : Blo 726324 7853723 := bstep (se 1 (by rfl) ⟨5890292, by rfl⟩ : syracuseStep 7853723 = 11780585) B11780585
theorem B3102943 : Blo 726324 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B3693113 : Blo 726324 3693113 := bstep (se 2 (by rfl) ⟨1384917, by rfl⟩ : syracuseStep 3693113 = 2769835) B2769835
theorem B4676201 : Blo 726324 4676201 := bstep (se 2 (by rfl) ⟨1753575, by rfl⟩ : syracuseStep 4676201 = 3507151) B3507151
theorem B70114139 : Blo 726324 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B2809721 : Blo 726324 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B12640139 : Blo 726324 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B7004231 : Blo 726324 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B5529707 : Blo 726324 5529707 := bstep (se 1 (by rfl) ⟨4147280, by rfl⟩ : syracuseStep 5529707 = 8294561) B8294561
theorem B12444029 : Blo 726324 12444029 := bstep (se 3 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 12444029 = 4666511) B4666511
theorem B4678199 : Blo 726324 4678199 := bstep (se 1 (by rfl) ⟨3508649, by rfl⟩ : syracuseStep 4678199 = 7017299) B7017299
theorem B5530193 : Blo 726324 5530193 := bstep (se 2 (by rfl) ⟨2073822, by rfl⟩ : syracuseStep 5530193 = 4147645) B4147645
theorem B179627057 : Blo 726324 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B70116997 : Blo 726324 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B1107751 : Blo 726324 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B2452571 : Blo 726324 2452571 := bstep (se 1 (by rfl) ⟨1839428, by rfl⟩ : syracuseStep 2452571 = 3678857) B3678857
theorem B3108719 : Blo 726324 3108719 := bstep (se 1 (by rfl) ⟨2331539, by rfl⟩ : syracuseStep 3108719 = 4663079) B4663079
theorem B1635155 : Blo 726324 1635155 := bstep (se 1 (by rfl) ⟨1226366, by rfl⟩ : syracuseStep 1635155 = 2452733) B2452733
theorem B1635515 : Blo 726324 1635515 := bstep (se 1 (by rfl) ⟨1226636, by rfl⟩ : syracuseStep 1635515 = 2453273) B2453273
theorem B2946799 : Blo 726324 2946799 := bstep (se 1 (by rfl) ⟨2210099, by rfl⟩ : syracuseStep 2946799 = 4420199) B4420199
theorem B16152335 : Blo 726324 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B6649933 : Blo 726324 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B5404967 : Blo 726324 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B4979407 : Blo 726324 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B1637531 : Blo 726324 1637531 := bstep (se 1 (by rfl) ⟨1228148, by rfl⟩ : syracuseStep 1637531 = 2456297) B2456297
theorem B3931361 : Blo 726324 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B3505727 : Blo 726324 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B851707 : Blo 726324 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B3506267 : Blo 726324 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B15925733 : Blo 726324 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B1638953 : Blo 726324 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B3736111 : Blo 726324 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B3933217 : Blo 726324 3933217 := bstep (se 2 (by rfl) ⟨1474956, by rfl⟩ : syracuseStep 3933217 = 2949913) B2949913
theorem B820327 : Blo 726324 820327 := bstep (se 1 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 820327 = 1230491) B1230491
theorem B3736691 : Blo 726324 3736691 := bstep (se 1 (by rfl) ⟨2802518, by rfl⟩ : syracuseStep 3736691 = 5605037) B5605037
theorem B1639655 : Blo 726324 1639655 := bstep (se 1 (by rfl) ⟨1229741, by rfl⟩ : syracuseStep 1639655 = 2459483) B2459483
theorem B984559 : Blo 726324 984559 := bstep (se 1 (by rfl) ⟨738419, by rfl⟩ : syracuseStep 984559 = 1476839) B1476839
theorem B1345391 : Blo 726324 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B821119 : Blo 726324 821119 := bstep (se 1 (by rfl) ⟨615839, by rfl⟩ : syracuseStep 821119 = 1231679) B1231679
theorem B17762449 : Blo 726324 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B93489329 : Blo 726324 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B4196717 : Blo 726324 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B1477001 : Blo 726324 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B3738233 : Blo 726324 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B920423 : Blo 726324 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B1641563 : Blo 726324 1641563 := bstep (se 1 (by rfl) ⟨1231172, by rfl⟩ : syracuseStep 1641563 = 2462345) B2462345
theorem B22384187 : Blo 726324 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B2100919 : Blo 726324 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B1839145 : Blo 726324 1839145 := bstep (se 2 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 1839145 = 1379359) B1379359
theorem B1642679 : Blo 726324 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B1642751 : Blo 726324 1642751 := bstep (se 1 (by rfl) ⟨1232063, by rfl⟩ : syracuseStep 1642751 = 2464127) B2464127
theorem B2462075 : Blo 726324 2462075 := bstep (se 1 (by rfl) ⟨1846556, by rfl⟩ : syracuseStep 2462075 = 3693113) B3693113
theorem B3117467 : Blo 726324 3117467 := bstep (se 1 (by rfl) ⟨2338100, by rfl⟩ : syracuseStep 3117467 = 4676201) B4676201
theorem B13963859 : Blo 726324 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B1839935 : Blo 726324 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B1873147 : Blo 726324 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B8426759 : Blo 726324 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B726399 : Blo 726324 726399 := bstep (se 1 (by rfl) ⟨544799, by rfl⟩ : syracuseStep 726399 = 1089599) B1089599
theorem B8296019 : Blo 726324 8296019 := bstep (se 1 (by rfl) ⟨6222014, by rfl⟩ : syracuseStep 8296019 = 12444029) B12444029
theorem B3118799 : Blo 726324 3118799 := bstep (se 1 (by rfl) ⟨2339099, by rfl⟩ : syracuseStep 3118799 = 4678199) B4678199
theorem B727167 : Blo 726324 727167 := bstep (se 1 (by rfl) ⟨545375, by rfl⟩ : syracuseStep 727167 = 1090751) B1090751
theorem B727291 : Blo 726324 727291 := bstep (se 1 (by rfl) ⟨545468, by rfl⟩ : syracuseStep 727291 = 1090937) B1090937
theorem B727707 : Blo 726324 727707 := bstep (se 1 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 727707 = 1091561) B1091561
theorem B728031 : Blo 726324 728031 := bstep (se 1 (by rfl) ⟨546023, by rfl⟩ : syracuseStep 728031 = 1092047) B1092047
theorem B728543 : Blo 726324 728543 := bstep (se 1 (by rfl) ⟨546407, by rfl⟩ : syracuseStep 728543 = 1092815) B1092815
theorem B728623 : Blo 726324 728623 := bstep (se 1 (by rfl) ⟨546467, by rfl⟩ : syracuseStep 728623 = 1092935) B1092935
theorem B728923 : Blo 726324 728923 := bstep (se 1 (by rfl) ⟨546692, by rfl⟩ : syracuseStep 728923 = 1093385) B1093385
theorem B2760587 : Blo 726324 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B2072479 : Blo 726324 2072479 := bstep (se 1 (by rfl) ⟨1554359, by rfl⟩ : syracuseStep 2072479 = 3108719) B3108719
theorem B729023 : Blo 726324 729023 := bstep (se 1 (by rfl) ⟨546767, by rfl⟩ : syracuseStep 729023 = 1093535) B1093535
theorem B1843175 : Blo 726324 1843175 := bstep (se 1 (by rfl) ⟨1382381, by rfl⟩ : syracuseStep 1843175 = 2764763) B2764763
theorem B729071 : Blo 726324 729071 := bstep (se 1 (by rfl) ⟨546803, by rfl⟩ : syracuseStep 729071 = 1093607) B1093607
theorem B729119 : Blo 726324 729119 := bstep (se 1 (by rfl) ⟨546839, by rfl⟩ : syracuseStep 729119 = 1093679) B1093679
theorem B729151 : Blo 726324 729151 := bstep (se 1 (by rfl) ⟨546863, by rfl⟩ : syracuseStep 729151 = 1093727) B1093727
theorem B729191 : Blo 726324 729191 := bstep (se 1 (by rfl) ⟨546893, by rfl⟩ : syracuseStep 729191 = 1093787) B1093787
theorem B729199 : Blo 726324 729199 := bstep (se 1 (by rfl) ⟨546899, by rfl⟩ : syracuseStep 729199 = 1093799) B1093799
theorem B729311 : Blo 726324 729311 := bstep (se 1 (by rfl) ⟨546983, by rfl⟩ : syracuseStep 729311 = 1093967) B1093967
theorem B4137257 : Blo 726324 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B4989367 : Blo 726324 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B1090103 : Blo 726324 1090103 := bstep (se 1 (by rfl) ⟨817577, by rfl⟩ : syracuseStep 1090103 = 1635155) B1635155
theorem B729755 : Blo 726324 729755 := bstep (se 1 (by rfl) ⟨547316, by rfl⟩ : syracuseStep 729755 = 1094633) B1094633
theorem B1090343 : Blo 726324 1090343 := bstep (se 1 (by rfl) ⟨817757, by rfl⟩ : syracuseStep 1090343 = 1635515) B1635515
theorem B730203 : Blo 726324 730203 := bstep (se 1 (by rfl) ⟨547652, by rfl⟩ : syracuseStep 730203 = 1095305) B1095305
theorem B9348605 : Blo 726324 9348605 := bstep (se 3 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 9348605 = 3505727) B3505727
theorem B1091687 : Blo 726324 1091687 := bstep (se 1 (by rfl) ⟨818765, by rfl⟩ : syracuseStep 1091687 = 1637531) B1637531
theorem B4664051 : Blo 726324 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B1092473 : Blo 726324 1092473 := bstep (se 2 (by rfl) ⟨409677, by rfl⟩ : syracuseStep 1092473 = 819355) B819355
theorem B1093055 : Blo 726324 1093055 := bstep (se 1 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 1093055 = 1639583) B1639583
theorem B1846739 : Blo 726324 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B3551375 : Blo 726324 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B3682583 : Blo 726324 3682583 := bstep (se 1 (by rfl) ⟨2761937, by rfl⟩ : syracuseStep 3682583 = 5523875) B5523875
theorem B1094057 : Blo 726324 1094057 := bstep (se 2 (by rfl) ⟨410271, by rfl⟩ : syracuseStep 1094057 = 820543) B820543
theorem B2765279 : Blo 726324 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B1094111 : Blo 726324 1094111 := bstep (se 1 (by rfl) ⟨820583, by rfl⟩ : syracuseStep 1094111 = 1641167) B1641167
theorem B131052107 : Blo 726324 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B1094249 : Blo 726324 1094249 := bstep (se 2 (by rfl) ⟨410343, by rfl⟩ : syracuseStep 1094249 = 820687) B820687
theorem B1094591 : Blo 726324 1094591 := bstep (se 1 (by rfl) ⟨820943, by rfl⟩ : syracuseStep 1094591 = 1641887) B1641887
theorem B5256515 : Blo 726324 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B2078561 : Blo 726324 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B4143271 : Blo 726324 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B2767223 : Blo 726324 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B2996675 : Blo 726324 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B1554923 : Blo 726324 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B46742759 : Blo 726324 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B4669487 : Blo 726324 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B3686471 : Blo 726324 3686471 := bstep (se 1 (by rfl) ⟨2764853, by rfl⟩ : syracuseStep 3686471 = 5529707) B5529707
theorem B1228871 : Blo 726324 1228871 := bstep (se 1 (by rfl) ⟨921653, by rfl⟩ : syracuseStep 1228871 = 1843307) B1843307
theorem B5390473 : Blo 726324 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B3686795 : Blo 726324 3686795 := bstep (se 1 (by rfl) ⟨2765096, by rfl⟩ : syracuseStep 3686795 = 5530193) B5530193
theorem B119751371 : Blo 726324 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B1229519 : Blo 726324 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B1753807 : Blo 726324 1753807 := bstep (se 1 (by rfl) ⟨1315355, by rfl⟩ : syracuseStep 1753807 = 2630711) B2630711
theorem B1164937 : Blo 726324 1164937 := bstep (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) B873703
theorem B1230889 : Blo 726324 1230889 := bstep (se 2 (by rfl) ⟨461583, by rfl⟩ : syracuseStep 1230889 = 923167) B923167
theorem B1231625 : Blo 726324 1231625 := bstep (se 2 (by rfl) ⟨461859, by rfl⟩ : syracuseStep 1231625 = 923719) B923719
theorem B8866577 : Blo 726324 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B6639209 : Blo 726324 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B10768223 : Blo 726324 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B6213509 : Blo 726324 6213509 := bstep (se 4 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 6213509 = 1165033) B1165033
theorem B15716261 : Blo 726324 15716261 := bstep (se 4 (by rfl) ⟨1473399, by rfl⟩ : syracuseStep 15716261 = 2946799) B2946799
theorem B4542437 : Blo 726324 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B15716875 : Blo 726324 15716875 := bstep (se 1 (by rfl) ⟨11787656, by rfl⟩ : syracuseStep 15716875 = 23575313) B23575313
theorem B3330665 : Blo 726324 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B7002227 : Blo 726324 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B3693599 : Blo 726324 3693599 := bstep (se 1 (by rfl) ⟨2770199, by rfl⟩ : syracuseStep 3693599 = 5540399) B5540399
theorem B4152545 : Blo 726324 4152545 := bstep (se 2 (by rfl) ⟨1557204, by rfl⟩ : syracuseStep 4152545 = 3114409) B3114409
theorem B3497423 : Blo 726324 3497423 := bstep (se 1 (by rfl) ⟨2623067, by rfl⟩ : syracuseStep 3497423 = 5246135) B5246135
theorem B8838841 : Blo 726324 8838841 := bstep (se 2 (by rfl) ⟨3314565, by rfl⟩ : syracuseStep 8838841 = 6629131) B6629131
theorem B35872465 : Blo 726324 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B778367 : Blo 726324 778367 := bstep (se 1 (by rfl) ⟨583775, by rfl⟩ : syracuseStep 778367 = 1167551) B1167551
theorem B3694895 : Blo 726324 3694895 := bstep (se 1 (by rfl) ⟨2771171, by rfl⟩ : syracuseStep 3694895 = 5542343) B5542343
theorem B15753629 : Blo 726324 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B9331793 : Blo 726324 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B5235815 : Blo 726324 5235815 := bstep (se 1 (by rfl) ⟨3926861, by rfl⟩ : syracuseStep 5235815 = 7853723) B7853723
theorem B3499463 : Blo 726324 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B3696839 : Blo 726324 3696839 := bstep (se 1 (by rfl) ⟨2772629, by rfl⟩ : syracuseStep 3696839 = 5545259) B5545259
theorem B7563527 : Blo 726324 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B3107591 : Blo 726324 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B3108547 : Blo 726324 3108547 := bstep (se 1 (by rfl) ⟨2331410, by rfl⟩ : syracuseStep 3108547 = 4662821) B4662821
theorem B14970653 : Blo 726324 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B1634273 : Blo 726324 1634273 := bstep (se 2 (by rfl) ⟨612852, by rfl⟩ : syracuseStep 1634273 = 1225705) B1225705
theorem B1635047 : Blo 726324 1635047 := bstep (se 1 (by rfl) ⟨1226285, by rfl⟩ : syracuseStep 1635047 = 2452571) B2452571
theorem B2454299 : Blo 726324 2454299 := bstep (se 1 (by rfl) ⟨1840724, by rfl⟩ : syracuseStep 2454299 = 3681449) B3681449
theorem B2454569 : Blo 726324 2454569 := bstep (se 2 (by rfl) ⟨920463, by rfl⟩ : syracuseStep 2454569 = 1840927) B1840927
theorem B2454623 : Blo 726324 2454623 := bstep (se 1 (by rfl) ⟨1840967, by rfl⟩ : syracuseStep 2454623 = 3681935) B3681935
theorem B1865423 : Blo 726324 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1865555 : Blo 726324 1865555 := bstep (se 1 (by rfl) ⟨1399166, by rfl⟩ : syracuseStep 1865555 = 2798333) B2798333
theorem B2455865 : Blo 726324 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B818023 : Blo 726324 818023 := bstep (se 1 (by rfl) ⟨613517, by rfl⟩ : syracuseStep 818023 = 1227035) B1227035
theorem B3603311 : Blo 726324 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B8879033 : Blo 726324 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B1637369 : Blo 726324 1637369 := bstep (se 2 (by rfl) ⟨614013, by rfl⟩ : syracuseStep 1637369 = 1228027) B1228027
theorem B2620907 : Blo 726324 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B819103 : Blo 726324 819103 := bstep (se 1 (by rfl) ⟨614327, by rfl⟩ : syracuseStep 819103 = 1228655) B1228655
theorem B3112991 : Blo 726324 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B2457647 : Blo 726324 2457647 := bstep (se 1 (by rfl) ⟨1843235, by rfl⟩ : syracuseStep 2457647 = 3686471) B3686471
theorem B819247 : Blo 726324 819247 := bstep (se 1 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 819247 = 1228871) B1228871
theorem B2457863 : Blo 726324 2457863 := bstep (se 1 (by rfl) ⟨1843397, by rfl⟩ : syracuseStep 2457863 = 3686795) B3686795
theorem B10617155 : Blo 726324 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B9470333 : Blo 726324 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B819679 : Blo 726324 819679 := bstep (se 1 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 819679 = 1229519) B1229519
theorem B6652489 : Blo 726324 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B4981481 : Blo 726324 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B2491127 : Blo 726324 2491127 := bstep (se 1 (by rfl) ⟨1868345, by rfl⟩ : syracuseStep 2491127 = 3736691) B3736691
theorem B62326219 : Blo 726324 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B2492155 : Blo 726324 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B821083 : Blo 726324 821083 := bstep (se 1 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 821083 = 1231625) B1231625
theorem B1312745 : Blo 726324 1312745 := bstep (se 2 (by rfl) ⟨492279, by rfl⟩ : syracuseStep 1312745 = 984559) B984559
theorem B4426139 : Blo 726324 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B7178815 : Blo 726324 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B1641185 : Blo 726324 1641185 := bstep (se 2 (by rfl) ⟨615444, by rfl⟩ : syracuseStep 1641185 = 1230889) B1230889
theorem B1641383 : Blo 726324 1641383 := bstep (se 1 (by rfl) ⟨1231037, by rfl⟩ : syracuseStep 1641383 = 2462075) B2462075
theorem B9309239 : Blo 726324 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B2462399 : Blo 726324 2462399 := bstep (se 1 (by rfl) ⟨1846799, by rfl⟩ : syracuseStep 2462399 = 3693599) B3693599
theorem B5542829 : Blo 726324 5542829 := bstep (se 3 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 5542829 = 2078561) B2078561
theorem B1840391 : Blo 726324 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B20977157 : Blo 726324 20977157 := bstep (se 4 (by rfl) ⟨1966608, by rfl⟩ : syracuseStep 20977157 = 3933217) B3933217
theorem B2758171 : Blo 726324 2758171 := bstep (se 1 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 2758171 = 4137257) B4137257
theorem B2463263 : Blo 726324 2463263 := bstep (se 1 (by rfl) ⟨1847447, by rfl⟩ : syracuseStep 2463263 = 3694895) B3694895
theorem B726735 : Blo 726324 726735 := bstep (se 1 (by rfl) ⟨545051, by rfl⟩ : syracuseStep 726735 = 1090103) B1090103
theorem B726895 : Blo 726324 726895 := bstep (se 1 (by rfl) ⟨545171, by rfl⟩ : syracuseStep 726895 = 1090343) B1090343
theorem B2332975 : Blo 726324 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B6232403 : Blo 726324 6232403 := bstep (se 1 (by rfl) ⟨4674302, by rfl⟩ : syracuseStep 6232403 = 9348605) B9348605
theorem B3938669 : Blo 726324 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B727791 : Blo 726324 727791 := bstep (se 1 (by rfl) ⟨545843, by rfl⟩ : syracuseStep 727791 = 1091687) B1091687
theorem B2464559 : Blo 726324 2464559 := bstep (se 1 (by rfl) ⟨1848419, by rfl⟩ : syracuseStep 2464559 = 3696839) B3696839
theorem B2497529 : Blo 726324 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B2071727 : Blo 726324 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B728315 : Blo 726324 728315 := bstep (se 1 (by rfl) ⟨546236, by rfl⟩ : syracuseStep 728315 = 1092473) B1092473
theorem B728703 : Blo 726324 728703 := bstep (se 1 (by rfl) ⟨546527, by rfl⟩ : syracuseStep 728703 = 1093055) B1093055
theorem B1089515 : Blo 726324 1089515 := bstep (se 1 (by rfl) ⟨817136, by rfl⟩ : syracuseStep 1089515 = 1634273) B1634273
theorem B729371 : Blo 726324 729371 := bstep (se 1 (by rfl) ⟨547028, by rfl⟩ : syracuseStep 729371 = 1094057) B1094057
theorem B1843519 : Blo 726324 1843519 := bstep (se 1 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 1843519 = 2765279) B2765279
theorem B729407 : Blo 726324 729407 := bstep (se 1 (by rfl) ⟨547055, by rfl⟩ : syracuseStep 729407 = 1094111) B1094111
theorem B87368071 : Blo 726324 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B729499 : Blo 726324 729499 := bstep (se 1 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 729499 = 1094249) B1094249
theorem B1090031 : Blo 726324 1090031 := bstep (se 1 (by rfl) ⟨817523, by rfl⟩ : syracuseStep 1090031 = 1635047) B1635047
theorem B729727 : Blo 726324 729727 := bstep (se 1 (by rfl) ⟨547295, by rfl⟩ : syracuseStep 729727 = 1094591) B1094591
theorem B1090697 : Blo 726324 1090697 := bstep (se 2 (by rfl) ⟨409011, by rfl⟩ : syracuseStep 1090697 = 818023) B818023
theorem B1844815 : Blo 726324 1844815 := bstep (se 1 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 1844815 = 2767223) B2767223
theorem B2402207 : Blo 726324 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B1091579 : Blo 726324 1091579 := bstep (se 1 (by rfl) ⟨818684, by rfl⟩ : syracuseStep 1091579 = 1637369) B1637369
theorem B1747271 : Blo 726324 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B2763305 : Blo 726324 2763305 := bstep (se 2 (by rfl) ⟨1036239, by rfl⟩ : syracuseStep 2763305 = 2072479) B2072479
theorem B1092137 : Blo 726324 1092137 := bstep (se 2 (by rfl) ⟨409551, by rfl⟩ : syracuseStep 1092137 = 819103) B819103
theorem B2337511 : Blo 726324 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B7187297 : Blo 726324 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B2075645 : Blo 726324 2075645 := bstep (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) B778367
theorem B1092635 : Blo 726324 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B79834247 : Blo 726324 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B1093103 : Blo 726324 1093103 := bstep (se 1 (by rfl) ⟨819827, by rfl⟩ : syracuseStep 1093103 = 1639655) B1639655
theorem B2338409 : Blo 726324 2338409 := bstep (se 2 (by rfl) ⟨876903, by rfl⟩ : syracuseStep 2338409 = 1753807) B1753807
theorem B896927 : Blo 726324 896927 := bstep (se 1 (by rfl) ⟨672695, by rfl⟩ : syracuseStep 896927 = 1345391) B1345391
theorem B1093769 : Blo 726324 1093769 := bstep (se 2 (by rfl) ⟨410163, by rfl⟩ : syracuseStep 1093769 = 820327) B820327
theorem B2797811 : Blo 726324 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B5911051 : Blo 726324 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B1094375 : Blo 726324 1094375 := bstep (se 1 (by rfl) ⟨820781, by rfl⟩ : syracuseStep 1094375 = 1641563) B1641563
theorem B1553249 : Blo 726324 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B14922791 : Blo 726324 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B1094825 : Blo 726324 1094825 := bstep (se 2 (by rfl) ⟨410559, by rfl⟩ : syracuseStep 1094825 = 821119) B821119
theorem B4142339 : Blo 726324 4142339 := bstep (se 1 (by rfl) ⟨3106754, by rfl⟩ : syracuseStep 4142339 = 6213509) B6213509
theorem B3028291 : Blo 726324 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1095119 : Blo 726324 1095119 := bstep (se 1 (by rfl) ⟨821339, by rfl⟩ : syracuseStep 1095119 = 1642679) B1642679
theorem B1095167 : Blo 726324 1095167 := bstep (se 1 (by rfl) ⟨821375, by rfl⟩ : syracuseStep 1095167 = 1642751) B1642751
theorem B2078311 : Blo 726324 2078311 := bstep (se 1 (by rfl) ⟨1558733, by rfl⟩ : syracuseStep 2078311 = 3117467) B3117467
theorem B1226623 : Blo 726324 1226623 := bstep (se 1 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 1226623 = 1839935) B1839935
theorem B2079199 : Blo 726324 2079199 := bstep (se 1 (by rfl) ⟨1559399, by rfl⟩ : syracuseStep 2079199 = 3118799) B3118799
theorem B2768363 : Blo 726324 2768363 := bstep (se 1 (by rfl) ⟨2076272, by rfl⟩ : syracuseStep 2768363 = 4152545) B4152545
theorem B2801225 : Blo 726324 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B4144729 : Blo 726324 4144729 := bstep (se 2 (by rfl) ⟨1554273, by rfl⟩ : syracuseStep 4144729 = 3108547) B3108547
theorem B1228783 : Blo 726324 1228783 := bstep (se 1 (by rfl) ⟨921587, by rfl⟩ : syracuseStep 1228783 = 1843175) B1843175
theorem B10502419 : Blo 726324 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B20955833 : Blo 726324 20955833 := bstep (se 2 (by rfl) ⟨7858437, by rfl⟩ : syracuseStep 20955833 = 15716875) B15716875
theorem B3490543 : Blo 726324 3490543 := bstep (se 1 (by rfl) ⟨2617907, by rfl⟩ : syracuseStep 3490543 = 5235815) B5235815
theorem B4146461 : Blo 726324 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B1231159 : Blo 726324 1231159 := bstep (se 1 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 1231159 = 1846739) B1846739
theorem B9980435 : Blo 726324 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B5524361 : Blo 726324 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B9326461 : Blo 726324 9326461 := bstep (se 3 (by rfl) ⟨1748711, by rfl⟩ : syracuseStep 9326461 = 3497423) B3497423
theorem B5919355 : Blo 726324 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B11785121 : Blo 726324 11785121 := bstep (se 2 (by rfl) ⟨4419420, by rfl⟩ : syracuseStep 11785121 = 8838841) B8838841
theorem B47829953 : Blo 726324 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B10477507 : Blo 726324 10477507 := bstep (se 1 (by rfl) ⟨7858130, by rfl⟩ : syracuseStep 10477507 = 15716261) B15716261
theorem B23683265 : Blo 726324 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B2220443 : Blo 726324 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B22471357 : Blo 726324 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B14017373 : Blo 726324 14017373 := bstep (se 3 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 14017373 = 5256515) B5256515
theorem B5530679 : Blo 726324 5530679 := bstep (se 1 (by rfl) ⟨4148009, by rfl⟩ : syracuseStep 5530679 = 8296019) B8296019
theorem B2452193 : Blo 726324 2452193 := bstep (se 2 (by rfl) ⟨919572, by rfl⟩ : syracuseStep 2452193 = 1839145) B1839145
theorem B18672605 : Blo 726324 18672605 := bstep (se 3 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 18672605 = 7002227) B7002227
theorem B6221195 : Blo 726324 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B5042351 : Blo 726324 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B3109367 : Blo 726324 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B2454461 : Blo 726324 2454461 := bstep (se 3 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 2454461 = 920423) B920423
theorem B2455055 : Blo 726324 2455055 := bstep (se 1 (by rfl) ⟨1841291, by rfl⟩ : syracuseStep 2455055 = 3682583) B3682583
theorem B1636199 : Blo 726324 1636199 := bstep (se 1 (by rfl) ⟨1227149, by rfl⟩ : syracuseStep 1636199 = 2454299) B2454299
theorem B1636379 : Blo 726324 1636379 := bstep (se 1 (by rfl) ⟨1227284, by rfl⟩ : syracuseStep 1636379 = 2454569) B2454569
theorem B1636415 : Blo 726324 1636415 := bstep (se 1 (by rfl) ⟨1227311, by rfl⟩ : syracuseStep 1636415 = 2454623) B2454623
theorem B1243615 : Blo 726324 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B1243703 : Blo 726324 1243703 := bstep (se 1 (by rfl) ⟨932777, by rfl⟩ : syracuseStep 1243703 = 1865555) B1865555
theorem B1637243 : Blo 726324 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B1997783 : Blo 726324 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B31161839 : Blo 726324 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B1638431 : Blo 726324 1638431 := bstep (se 1 (by rfl) ⟨1228823, by rfl⟩ : syracuseStep 1638431 = 2457647) B2457647
theorem B1638575 : Blo 726324 1638575 := bstep (se 1 (by rfl) ⟨1228931, by rfl⟩ : syracuseStep 1638575 = 2457863) B2457863
theorem B7078103 : Blo 726324 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B2458025 : Blo 726324 2458025 := bstep (se 2 (by rfl) ⟨921759, by rfl⟩ : syracuseStep 2458025 = 1843519) B1843519
theorem B116490761 : Blo 726324 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B4654057 : Blo 726324 4654057 := bstep (se 2 (by rfl) ⟨1745271, by rfl⟩ : syracuseStep 4654057 = 3490543) B3490543
theorem B8291645 : Blo 726324 8291645 := bstep (se 3 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 8291645 = 3109367) B3109367
theorem B2950759 : Blo 726324 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B83101625 : Blo 726324 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B2459753 : Blo 726324 2459753 := bstep (se 2 (by rfl) ⟨922407, by rfl⟩ : syracuseStep 2459753 = 1844815) B1844815
theorem B1641545 : Blo 726324 1641545 := bstep (se 2 (by rfl) ⟨615579, by rfl⟩ : syracuseStep 1641545 = 1231159) B1231159
theorem B1641599 : Blo 726324 1641599 := bstep (se 1 (by rfl) ⟨1231199, by rfl⟩ : syracuseStep 1641599 = 2462399) B2462399
theorem B31886635 : Blo 726324 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B9571753 : Blo 726324 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B3116681 : Blo 726324 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B1642175 : Blo 726324 1642175 := bstep (se 1 (by rfl) ⟨1231631, by rfl⟩ : syracuseStep 1642175 = 2463263) B2463263
theorem B2625779 : Blo 726324 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B1643039 : Blo 726324 1643039 := bstep (se 1 (by rfl) ⟨1232279, by rfl⟩ : syracuseStep 1643039 = 2464559) B2464559
theorem B1381151 : Blo 726324 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B726343 : Blo 726324 726343 := bstep (se 1 (by rfl) ⟨544757, by rfl⟩ : syracuseStep 726343 = 1089515) B1089515
theorem B1480295 : Blo 726324 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B726687 : Blo 726324 726687 := bstep (se 1 (by rfl) ⟨545015, by rfl⟩ : syracuseStep 726687 = 1090031) B1090031
theorem B9344915 : Blo 726324 9344915 := bstep (se 1 (by rfl) ⟨7008686, by rfl⟩ : syracuseStep 9344915 = 14017373) B14017373
theorem B727131 : Blo 726324 727131 := bstep (se 1 (by rfl) ⟨545348, by rfl⟩ : syracuseStep 727131 = 1090697) B1090697
theorem B4659389 : Blo 726324 4659389 := bstep (se 3 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 4659389 = 1747271) B1747271
theorem B727719 : Blo 726324 727719 := bstep (se 1 (by rfl) ⟨545789, by rfl⟩ : syracuseStep 727719 = 1091579) B1091579
theorem B26614493 : Blo 726324 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B1842203 : Blo 726324 1842203 := bstep (se 1 (by rfl) ⟨1381652, by rfl⟩ : syracuseStep 1842203 = 2763305) B2763305
theorem B728091 : Blo 726324 728091 := bstep (se 1 (by rfl) ⟨546068, by rfl⟩ : syracuseStep 728091 = 1092137) B1092137
theorem B728423 : Blo 726324 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B3677561 : Blo 726324 3677561 := bstep (se 2 (by rfl) ⟨1379085, by rfl⟩ : syracuseStep 3677561 = 2758171) B2758171
theorem B53222831 : Blo 726324 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B728735 : Blo 726324 728735 := bstep (se 1 (by rfl) ⟨546551, by rfl⟩ : syracuseStep 728735 = 1093103) B1093103
theorem B729179 : Blo 726324 729179 := bstep (se 1 (by rfl) ⟨546884, by rfl⟩ : syracuseStep 729179 = 1093769) B1093769
theorem B729583 : Blo 726324 729583 := bstep (se 1 (by rfl) ⟨547187, by rfl⟩ : syracuseStep 729583 = 1094375) B1094375
theorem B729883 : Blo 726324 729883 := bstep (se 1 (by rfl) ⟨547412, by rfl⟩ : syracuseStep 729883 = 1094825) B1094825
theorem B2761559 : Blo 726324 2761559 := bstep (se 1 (by rfl) ⟨2071169, by rfl⟩ : syracuseStep 2761559 = 4142339) B4142339
theorem B730079 : Blo 726324 730079 := bstep (se 1 (by rfl) ⟨547559, by rfl⟩ : syracuseStep 730079 = 1095119) B1095119
theorem B730111 : Blo 726324 730111 := bstep (se 1 (by rfl) ⟨547583, by rfl⟩ : syracuseStep 730111 = 1095167) B1095167
theorem B1090799 : Blo 726324 1090799 := bstep (se 1 (by rfl) ⟨818099, by rfl⟩ : syracuseStep 1090799 = 1636199) B1636199
theorem B1090919 : Blo 726324 1090919 := bstep (se 1 (by rfl) ⟨818189, by rfl⟩ : syracuseStep 1090919 = 1636379) B1636379
theorem B1090943 : Blo 726324 1090943 := bstep (se 1 (by rfl) ⟨818207, by rfl⟩ : syracuseStep 1090943 = 1636415) B1636415
theorem B829135 : Blo 726324 829135 := bstep (se 1 (by rfl) ⟨621851, by rfl⟩ : syracuseStep 829135 = 1243703) B1243703
theorem B1091495 : Blo 726324 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B1845575 : Blo 726324 1845575 := bstep (se 1 (by rfl) ⟨1384181, by rfl⟩ : syracuseStep 1845575 = 2768363) B2768363
theorem B13970009 : Blo 726324 13970009 := bstep (se 2 (by rfl) ⟨5238753, by rfl⟩ : syracuseStep 13970009 = 10477507) B10477507
theorem B2075327 : Blo 726324 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B1092329 : Blo 726324 1092329 := bstep (se 2 (by rfl) ⟨409623, by rfl⟩ : syracuseStep 1092329 = 819247) B819247
theorem B14003225 : Blo 726324 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B13970555 : Blo 726324 13970555 := bstep (se 1 (by rfl) ⟨10477916, by rfl⟩ : syracuseStep 13970555 = 20955833) B20955833
theorem B13446269 : Blo 726324 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B1092905 : Blo 726324 1092905 := bstep (se 2 (by rfl) ⟨409839, by rfl⟩ : syracuseStep 1092905 = 819679) B819679
theorem B2764307 : Blo 726324 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B29961809 : Blo 726324 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B1094123 : Blo 726324 1094123 := bstep (se 1 (by rfl) ⟨820592, by rfl⟩ : syracuseStep 1094123 = 1641185) B1641185
theorem B3682907 : Blo 726324 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B1094255 : Blo 726324 1094255 := bstep (se 1 (by rfl) ⟨820691, by rfl⟩ : syracuseStep 1094255 = 1641383) B1641383
theorem B6206159 : Blo 726324 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B3322873 : Blo 726324 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B1094777 : Blo 726324 1094777 := bstep (se 2 (by rfl) ⟨410541, by rfl⟩ : syracuseStep 1094777 = 821083) B821083
theorem B1226927 : Blo 726324 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B12435281 : Blo 726324 12435281 := bstep (se 2 (by rfl) ⟨4663230, by rfl⟩ : syracuseStep 12435281 = 9326461) B9326461
theorem B7881401 : Blo 726324 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B3687119 : Blo 726324 3687119 := bstep (se 1 (by rfl) ⟨2765339, by rfl⟩ : syracuseStep 3687119 = 5530679) B5530679
theorem B64603541 : Blo 726324 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B2771081 : Blo 726324 2771081 := bstep (se 2 (by rfl) ⟨1039155, by rfl⟩ : syracuseStep 2771081 = 2078311) B2078311
theorem B4147463 : Blo 726324 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B1558939 : Blo 726324 1558939 := bstep (se 1 (by rfl) ⟨1169204, by rfl⟩ : syracuseStep 1558939 = 2338409) B2338409
theorem B53135797 : Blo 726324 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B1035499 : Blo 726324 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B1658153 : Blo 726324 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B2772265 : Blo 726324 2772265 := bstep (se 2 (by rfl) ⟨1039599, by rfl⟩ : syracuseStep 2772265 = 2079199) B2079199
theorem B9948527 : Blo 726324 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B76664501 : Blo 726324 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B1331855 : Blo 726324 1331855 := bstep (se 1 (by rfl) ⟨998891, by rfl⟩ : syracuseStep 1331855 = 1997783) B1997783
theorem B5526305 : Blo 726324 5526305 := bstep (se 2 (by rfl) ⟨2072364, by rfl⟩ : syracuseStep 5526305 = 4144729) B4144729
theorem B6313555 : Blo 726324 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B1660751 : Blo 726324 1660751 := bstep (se 1 (by rfl) ⟨1245563, by rfl⟩ : syracuseStep 1660751 = 2491127) B2491127
theorem B8869985 : Blo 726324 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B7856747 : Blo 726324 7856747 := bstep (se 1 (by rfl) ⟨5892560, by rfl⟩ : syracuseStep 7856747 = 11785121) B11785121
theorem B3695219 : Blo 726324 3695219 := bstep (se 1 (by rfl) ⟨2771414, by rfl⟩ : syracuseStep 3695219 = 5542829) B5542829
theorem B13984771 : Blo 726324 13984771 := bstep (se 1 (by rfl) ⟨10488578, by rfl⟩ : syracuseStep 13984771 = 20977157) B20977157
theorem B4154935 : Blo 726324 4154935 := bstep (se 1 (by rfl) ⟨3116201, by rfl⟩ : syracuseStep 4154935 = 6232403) B6232403
theorem B1665019 : Blo 726324 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B3500653 : Blo 726324 3500653 := bstep (se 3 (by rfl) ⟨656372, by rfl⟩ : syracuseStep 3500653 = 1312745) B1312745
theorem B15788843 : Blo 726324 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B7892473 : Blo 726324 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B1601471 : Blo 726324 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B1634795 : Blo 726324 1634795 := bstep (se 1 (by rfl) ⟨1226096, by rfl⟩ : syracuseStep 1634795 = 2452193) B2452193
theorem B12448403 : Blo 726324 12448403 := bstep (se 1 (by rfl) ⟨9336302, by rfl⟩ : syracuseStep 12448403 = 18672605) B18672605
theorem B1635497 : Blo 726324 1635497 := bstep (se 2 (by rfl) ⟨613311, by rfl⟩ : syracuseStep 1635497 = 1226623) B1226623
theorem B5535053 : Blo 726324 5535053 := bstep (se 3 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 5535053 = 2075645) B2075645
theorem B1865207 : Blo 726324 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B3110633 : Blo 726324 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B1636307 : Blo 726324 1636307 := bstep (se 1 (by rfl) ⟨1227230, by rfl⟩ : syracuseStep 1636307 = 2454461) B2454461
theorem B1636703 : Blo 726324 1636703 := bstep (se 1 (by rfl) ⟨1227527, by rfl⟩ : syracuseStep 1636703 = 2455055) B2455055
theorem B83098237 : Blo 726324 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B1867483 : Blo 726324 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B2391805 : Blo 726324 2391805 := bstep (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) B896927
theorem B1638377 : Blo 726324 1638377 := bstep (se 2 (by rfl) ⟨614391, by rfl⟩ : syracuseStep 1638377 = 1228783) B1228783
theorem B4718735 : Blo 726324 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B1638683 : Blo 726324 1638683 := bstep (se 1 (by rfl) ⟨1229012, by rfl⟩ : syracuseStep 1638683 = 2458025) B2458025
theorem B77660507 : Blo 726324 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B2458079 : Blo 726324 2458079 := bstep (se 1 (by rfl) ⟨1843559, by rfl⟩ : syracuseStep 2458079 = 3687119) B3687119
theorem B18646361 : Blo 726324 18646361 := bstep (se 2 (by rfl) ⟨6992385, by rfl⟩ : syracuseStep 18646361 = 13984771) B13984771
theorem B1639835 : Blo 726324 1639835 := bstep (se 1 (by rfl) ⟨1229876, by rfl⟩ : syracuseStep 1639835 = 2459753) B2459753
theorem B5539913 : Blo 726324 5539913 := bstep (se 2 (by rfl) ⟨2077467, by rfl⟩ : syracuseStep 5539913 = 4154935) B4154935
theorem B3934345 : Blo 726324 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B887903 : Blo 726324 887903 := bstep (se 1 (by rfl) ⟨665927, by rfl⟩ : syracuseStep 887903 = 1331855) B1331855
theorem B70847729 : Blo 726324 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B6229943 : Blo 726324 6229943 := bstep (se 1 (by rfl) ⟨4672457, by rfl⟩ : syracuseStep 6229943 = 9344915) B9344915
theorem B1380665 : Blo 726324 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B10523297 : Blo 726324 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B2463479 : Blo 726324 2463479 := bstep (se 1 (by rfl) ⟨1847609, by rfl⟩ : syracuseStep 2463479 = 3695219) B3695219
theorem B1841039 : Blo 726324 1841039 := bstep (se 1 (by rfl) ⟨1380779, by rfl⟩ : syracuseStep 1841039 = 2761559) B2761559
theorem B727199 : Blo 726324 727199 := bstep (se 1 (by rfl) ⟨545399, by rfl⟩ : syracuseStep 727199 = 1090799) B1090799
theorem B727279 : Blo 726324 727279 := bstep (se 1 (by rfl) ⟨545459, by rfl⟩ : syracuseStep 727279 = 1090919) B1090919
theorem B727295 : Blo 726324 727295 := bstep (se 1 (by rfl) ⟨545471, by rfl⟩ : syracuseStep 727295 = 1090943) B1090943
theorem B727663 : Blo 726324 727663 := bstep (se 1 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 727663 = 1091495) B1091495
theorem B4430497 : Blo 726324 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B9313339 : Blo 726324 9313339 := bstep (se 1 (by rfl) ⟨6985004, by rfl⟩ : syracuseStep 9313339 = 13970009) B13970009
theorem B1383551 : Blo 726324 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B728219 : Blo 726324 728219 := bstep (se 1 (by rfl) ⟨546164, by rfl⟩ : syracuseStep 728219 = 1092329) B1092329
theorem B10525895 : Blo 726324 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B9313703 : Blo 726324 9313703 := bstep (se 1 (by rfl) ⟨6985277, by rfl⟩ : syracuseStep 9313703 = 13970555) B13970555
theorem B728603 : Blo 726324 728603 := bstep (se 1 (by rfl) ⟨546452, by rfl⟩ : syracuseStep 728603 = 1092905) B1092905
theorem B1842871 : Blo 726324 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B1089863 : Blo 726324 1089863 := bstep (se 1 (by rfl) ⟨817397, by rfl⟩ : syracuseStep 1089863 = 1634795) B1634795
theorem B729415 : Blo 726324 729415 := bstep (se 1 (by rfl) ⟨547061, by rfl⟩ : syracuseStep 729415 = 1094123) B1094123
theorem B729503 : Blo 726324 729503 := bstep (se 1 (by rfl) ⟨547127, by rfl⟩ : syracuseStep 729503 = 1094255) B1094255
theorem B8298935 : Blo 726324 8298935 := bstep (se 1 (by rfl) ⟨6224201, by rfl⟩ : syracuseStep 8298935 = 12448403) B12448403
theorem B4137439 : Blo 726324 4137439 := bstep (se 1 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 4137439 = 6206159) B6206159
theorem B729851 : Blo 726324 729851 := bstep (se 1 (by rfl) ⟨547388, by rfl⟩ : syracuseStep 729851 = 1094777) B1094777
theorem B1090331 : Blo 726324 1090331 := bstep (se 1 (by rfl) ⟨817748, by rfl⟩ : syracuseStep 1090331 = 1635497) B1635497
theorem B110797649 : Blo 726324 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B2073755 : Blo 726324 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B1090871 : Blo 726324 1090871 := bstep (se 1 (by rfl) ⟨818153, by rfl⟩ : syracuseStep 1090871 = 1636307) B1636307
theorem B1091135 : Blo 726324 1091135 := bstep (se 1 (by rfl) ⟨818351, by rfl⟩ : syracuseStep 1091135 = 1636703) B1636703
theorem B3189073 : Blo 726324 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B4270589 : Blo 726324 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B1092251 : Blo 726324 1092251 := bstep (se 1 (by rfl) ⟨819188, by rfl⟩ : syracuseStep 1092251 = 1638377) B1638377
theorem B1092287 : Blo 726324 1092287 := bstep (se 1 (by rfl) ⟨819215, by rfl⟩ : syracuseStep 1092287 = 1638431) B1638431
theorem B1092383 : Blo 726324 1092383 := bstep (se 1 (by rfl) ⟨819287, by rfl⟩ : syracuseStep 1092383 = 1638575) B1638575
theorem B43069027 : Blo 726324 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B6205409 : Blo 726324 6205409 := bstep (se 2 (by rfl) ⟨2327028, by rfl⟩ : syracuseStep 6205409 = 4654057) B4654057
theorem B1847387 : Blo 726324 1847387 := bstep (se 1 (by rfl) ⟨1385540, by rfl⟩ : syracuseStep 1847387 = 2771081) B2771081
theorem B2764975 : Blo 726324 2764975 := bstep (se 1 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 2764975 = 4147463) B4147463
theorem B21017069 : Blo 726324 21017069 := bstep (se 3 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 21017069 = 7881401) B7881401
theorem B1094363 : Blo 726324 1094363 := bstep (se 1 (by rfl) ⟨820772, by rfl⟩ : syracuseStep 1094363 = 1641545) B1641545
theorem B3683069 : Blo 726324 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B1094399 : Blo 726324 1094399 := bstep (se 1 (by rfl) ⟨820799, by rfl⟩ : syracuseStep 1094399 = 1641599) B1641599
theorem B6632351 : Blo 726324 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B2077787 : Blo 726324 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B1094783 : Blo 726324 1094783 := bstep (se 1 (by rfl) ⟨821087, by rfl⟩ : syracuseStep 1094783 = 1642175) B1642175
theorem B1750519 : Blo 726324 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B1095359 : Blo 726324 1095359 := bstep (se 1 (by rfl) ⟨821519, by rfl⟩ : syracuseStep 1095359 = 1643039) B1643039
theorem B3684203 : Blo 726324 3684203 := bstep (se 1 (by rfl) ⟨2763152, by rfl⟩ : syracuseStep 3684203 = 5526305) B5526305
theorem B2078585 : Blo 726324 2078585 := bstep (se 2 (by rfl) ⟨779469, by rfl⟩ : syracuseStep 2078585 = 1558939) B1558939
theorem B4667537 : Blo 726324 4667537 := bstep (se 2 (by rfl) ⟨1750326, by rfl⟩ : syracuseStep 4667537 = 3500653) B3500653
theorem B5913323 : Blo 726324 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B3947453 : Blo 726324 3947453 := bstep (se 3 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 3947453 = 1480295) B1480295
theorem B42515513 : Blo 726324 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B17742995 : Blo 726324 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B1228135 : Blo 726324 1228135 := bstep (se 1 (by rfl) ⟨921101, by rfl⟩ : syracuseStep 1228135 = 1842203) B1842203
theorem B1230383 : Blo 726324 1230383 := bstep (se 1 (by rfl) ⟨922787, by rfl⟩ : syracuseStep 1230383 = 1845575) B1845575
theorem B8964179 : Blo 726324 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B19974539 : Blo 726324 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B3690035 : Blo 726324 3690035 := bstep (se 1 (by rfl) ⟨2767526, by rfl⟩ : syracuseStep 3690035 = 5535053) B5535053
theorem B5527763 : Blo 726324 5527763 := bstep (se 1 (by rfl) ⟨4145822, by rfl⟩ : syracuseStep 5527763 = 8291645) B8291645
theorem B55401083 : Blo 726324 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B1105435 : Blo 726324 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B51109667 : Blo 726324 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B1107167 : Blo 726324 1107167 := bstep (se 1 (by rfl) ⟨830375, by rfl⟩ : syracuseStep 1107167 = 1660751) B1660751
theorem B3106259 : Blo 726324 3106259 := bstep (se 1 (by rfl) ⟨2329694, by rfl⟩ : syracuseStep 3106259 = 4659389) B4659389
theorem B3696353 : Blo 726324 3696353 := bstep (se 2 (by rfl) ⟨1386132, by rfl⟩ : syracuseStep 3696353 = 2772265) B2772265
theorem B2451707 : Blo 726324 2451707 := bstep (se 1 (by rfl) ⟨1838780, by rfl⟩ : syracuseStep 2451707 = 3677561) B3677561
theorem B35481887 : Blo 726324 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B5237831 : Blo 726324 5237831 := bstep (se 1 (by rfl) ⟨3928373, by rfl⟩ : syracuseStep 5237831 = 7856747) B7856747
theorem B9335483 : Blo 726324 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B8418073 : Blo 726324 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B51049349 : Blo 726324 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B2455271 : Blo 726324 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B1243471 : Blo 726324 1243471 := bstep (se 1 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 1243471 = 1865207) B1865207
theorem B4422053 : Blo 726324 4422053 := bstep (se 4 (by rfl) ⟨414567, by rfl⟩ : syracuseStep 4422053 = 829135) B829135
theorem B817951 : Blo 726324 817951 := bstep (se 1 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 817951 = 1226927) B1226927
theorem B2489977 : Blo 726324 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B8290187 : Blo 726324 8290187 := bstep (se 1 (by rfl) ⟨6217640, by rfl⟩ : syracuseStep 8290187 = 12435281) B12435281
theorem B8880101 : Blo 726324 8880101 := bstep (se 4 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 8880101 = 1665019) B1665019
theorem B3145823 : Blo 726324 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B51773671 : Blo 726324 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B1638719 : Blo 726324 1638719 := bstep (se 1 (by rfl) ⟨1229039, by rfl⟩ : syracuseStep 1638719 = 2458079) B2458079
theorem B9470965 : Blo 726324 9470965 := bstep (se 5 (by rfl) ⟨443951, by rfl⟩ : syracuseStep 9470965 = 887903) B887903
theorem B820255 : Blo 726324 820255 := bstep (se 1 (by rfl) ⟨615191, by rfl⟩ : syracuseStep 820255 = 1230383) B1230383
theorem B2460023 : Blo 726324 2460023 := bstep (se 1 (by rfl) ⟨1845017, by rfl⟩ : syracuseStep 2460023 = 3690035) B3690035
theorem B5245793 : Blo 726324 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B7015531 : Blo 726324 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B2952445 : Blo 726324 2952445 := bstep (se 3 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 2952445 = 1107167) B1107167
theorem B1642319 : Blo 726324 1642319 := bstep (se 1 (by rfl) ⟨1231739, by rfl⟩ : syracuseStep 1642319 = 2463479) B2463479
theorem B36934055 : Blo 726324 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B922367 : Blo 726324 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B7017263 : Blo 726324 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B726575 : Blo 726324 726575 := bstep (se 1 (by rfl) ⟨544931, by rfl⟩ : syracuseStep 726575 = 1089863) B1089863
theorem B726887 : Blo 726324 726887 := bstep (se 1 (by rfl) ⟨545165, by rfl⟩ : syracuseStep 726887 = 1090331) B1090331
theorem B73865099 : Blo 726324 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B1382503 : Blo 726324 1382503 := bstep (se 1 (by rfl) ⟨1036877, by rfl⟩ : syracuseStep 1382503 = 2073755) B2073755
theorem B727247 : Blo 726324 727247 := bstep (se 1 (by rfl) ⟨545435, by rfl⟩ : syracuseStep 727247 = 1090871) B1090871
theorem B2070839 : Blo 726324 2070839 := bstep (se 1 (by rfl) ⟨1553129, by rfl⟩ : syracuseStep 2070839 = 3106259) B3106259
theorem B727423 : Blo 726324 727423 := bstep (se 1 (by rfl) ⟨545567, by rfl⟩ : syracuseStep 727423 = 1091135) B1091135
theorem B2464235 : Blo 726324 2464235 := bstep (se 1 (by rfl) ⟨1848176, by rfl⟩ : syracuseStep 2464235 = 3696353) B3696353
theorem B728167 : Blo 726324 728167 := bstep (se 1 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 728167 = 1092251) B1092251
theorem B728191 : Blo 726324 728191 := bstep (se 1 (by rfl) ⟨546143, by rfl⟩ : syracuseStep 728191 = 1092287) B1092287
theorem B728255 : Blo 726324 728255 := bstep (se 1 (by rfl) ⟨546191, by rfl⟩ : syracuseStep 728255 = 1092383) B1092383
theorem B2334025 : Blo 726324 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B4136939 : Blo 726324 4136939 := bstep (se 1 (by rfl) ⟨3102704, by rfl⟩ : syracuseStep 4136939 = 6205409) B6205409
theorem B13967549 : Blo 726324 13967549 := bstep (se 3 (by rfl) ⟨2618915, by rfl⟩ : syracuseStep 13967549 = 5237831) B5237831
theorem B729575 : Blo 726324 729575 := bstep (se 1 (by rfl) ⟨547181, by rfl⟩ : syracuseStep 729575 = 1094363) B1094363
theorem B729599 : Blo 726324 729599 := bstep (se 1 (by rfl) ⟨547199, by rfl⟩ : syracuseStep 729599 = 1094399) B1094399
theorem B1385191 : Blo 726324 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B729855 : Blo 726324 729855 := bstep (se 1 (by rfl) ⟨547391, by rfl⟩ : syracuseStep 729855 = 1094783) B1094783
theorem B5907329 : Blo 726324 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B1090601 : Blo 726324 1090601 := bstep (se 2 (by rfl) ⟨408975, by rfl⟩ : syracuseStep 1090601 = 817951) B817951
theorem B730239 : Blo 726324 730239 := bstep (se 1 (by rfl) ⟨547679, by rfl⟩ : syracuseStep 730239 = 1095359) B1095359
theorem B1385723 : Blo 726324 1385723 := bstep (se 1 (by rfl) ⟨1039292, by rfl⟩ : syracuseStep 1385723 = 2078585) B2078585
theorem B3942215 : Blo 726324 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B2631635 : Blo 726324 2631635 := bstep (se 1 (by rfl) ⟨1973726, by rfl⟩ : syracuseStep 2631635 = 3947453) B3947453
theorem B3319969 : Blo 726324 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B1092455 : Blo 726324 1092455 := bstep (se 1 (by rfl) ⟨819341, by rfl⟩ : syracuseStep 1092455 = 1638683) B1638683
theorem B5516585 : Blo 726324 5516585 := bstep (se 2 (by rfl) ⟨2068719, by rfl⟩ : syracuseStep 5516585 = 4137439) B4137439
theorem B3681773 : Blo 726324 3681773 := bstep (se 3 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 3681773 = 1380665) B1380665
theorem B12430907 : Blo 726324 12430907 := bstep (se 1 (by rfl) ⟨9323180, by rfl⟩ : syracuseStep 12430907 = 18646361) B18646361
theorem B1093223 : Blo 726324 1093223 := bstep (se 1 (by rfl) ⟨819917, by rfl⟩ : syracuseStep 1093223 = 1639835) B1639835
theorem B5976119 : Blo 726324 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B13316359 : Blo 726324 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B47231819 : Blo 726324 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B1227359 : Blo 726324 1227359 := bstep (se 1 (by rfl) ⟨920519, by rfl⟩ : syracuseStep 1227359 = 1841039) B1841039
theorem B3685175 : Blo 726324 3685175 := bstep (se 1 (by rfl) ⟨2763881, by rfl⟩ : syracuseStep 3685175 = 5527763) B5527763
theorem B57425369 : Blo 726324 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B6209135 : Blo 726324 6209135 := bstep (se 1 (by rfl) ⟨4656851, by rfl⟩ : syracuseStep 6209135 = 9313703) B9313703
theorem B3686633 : Blo 726324 3686633 := bstep (se 2 (by rfl) ⟨1382487, by rfl⟩ : syracuseStep 3686633 = 2764975) B2764975
theorem B11224097 : Blo 726324 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B1231591 : Blo 726324 1231591 := bstep (se 1 (by rfl) ⟨923693, by rfl⟩ : syracuseStep 1231591 = 1847387) B1847387
theorem B14011379 : Blo 726324 14011379 := bstep (se 1 (by rfl) ⟨10508534, by rfl⟩ : syracuseStep 14011379 = 21017069) B21017069
theorem B1657961 : Blo 726324 1657961 := bstep (se 2 (by rfl) ⟨621735, by rfl⟩ : syracuseStep 1657961 = 1243471) B1243471
theorem B34032899 : Blo 726324 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B5526791 : Blo 726324 5526791 := bstep (se 1 (by rfl) ⟨4145093, by rfl⟩ : syracuseStep 5526791 = 8290187) B8290187
theorem B5920067 : Blo 726324 5920067 := bstep (se 1 (by rfl) ⟨4440050, by rfl⟩ : syracuseStep 5920067 = 8880101) B8880101
theorem B3693275 : Blo 726324 3693275 := bstep (se 1 (by rfl) ⟨2769956, by rfl⟩ : syracuseStep 3693275 = 5539913) B5539913
theorem B4153295 : Blo 726324 4153295 := bstep (se 1 (by rfl) ⟨3114971, by rfl⟩ : syracuseStep 4153295 = 6229943) B6229943
theorem B4252097 : Blo 726324 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B34073111 : Blo 726324 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B5532623 : Blo 726324 5532623 := bstep (se 1 (by rfl) ⟨4149467, by rfl⟩ : syracuseStep 5532623 = 8298935) B8298935
theorem B1634471 : Blo 726324 1634471 := bstep (se 1 (by rfl) ⟨1225853, by rfl⟩ : syracuseStep 1634471 = 2451707) B2451707
theorem B23654591 : Blo 726324 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B2847059 : Blo 726324 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B6223655 : Blo 726324 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B2455379 : Blo 726324 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B4421567 : Blo 726324 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1636847 : Blo 726324 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B2456135 : Blo 726324 2456135 := bstep (se 1 (by rfl) ⟨1842101, by rfl⟩ : syracuseStep 2456135 = 3684203) B3684203
theorem B12417785 : Blo 726324 12417785 := bstep (se 2 (by rfl) ⟨4656669, by rfl⟩ : syracuseStep 12417785 = 9313339) B9313339
theorem B3111691 : Blo 726324 3111691 := bstep (se 1 (by rfl) ⟨2333768, by rfl⟩ : syracuseStep 3111691 = 4667537) B4667537
theorem B2948035 : Blo 726324 2948035 := bstep (se 1 (by rfl) ⟨2211026, by rfl⟩ : syracuseStep 2948035 = 4422053) B4422053
theorem B1637513 : Blo 726324 1637513 := bstep (se 2 (by rfl) ⟨614067, by rfl⟩ : syracuseStep 1637513 = 1228135) B1228135
theorem B1473913 : Blo 726324 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B28343675 : Blo 726324 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B11828663 : Blo 726324 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B2457161 : Blo 726324 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B2097215 : Blo 726324 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B2457755 : Blo 726324 2457755 := bstep (se 1 (by rfl) ⟨1843316, by rfl⟩ : syracuseStep 2457755 = 3686633) B3686633
theorem B1640015 : Blo 726324 1640015 := bstep (se 1 (by rfl) ⟨1230011, by rfl⟩ : syracuseStep 1640015 = 2460023) B2460023
theorem B9340919 : Blo 726324 9340919 := bstep (se 1 (by rfl) ⟨7005689, by rfl⟩ : syracuseStep 9340919 = 14011379) B14011379
theorem B2459645 : Blo 726324 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B4426625 : Blo 726324 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B1642121 : Blo 726324 1642121 := bstep (se 2 (by rfl) ⟨615795, by rfl⟩ : syracuseStep 1642121 = 1231591) B1231591
theorem B1380559 : Blo 726324 1380559 := bstep (se 1 (by rfl) ⟨1035419, by rfl⟩ : syracuseStep 1380559 = 2070839) B2070839
theorem B1642823 : Blo 726324 1642823 := bstep (se 1 (by rfl) ⟨1232117, by rfl⟩ : syracuseStep 1642823 = 2464235) B2464235
theorem B3936593 : Blo 726324 3936593 := bstep (se 2 (by rfl) ⟨1476222, by rfl⟩ : syracuseStep 3936593 = 2952445) B2952445
theorem B2462183 : Blo 726324 2462183 := bstep (se 1 (by rfl) ⟨1846637, by rfl⟩ : syracuseStep 2462183 = 3693275) B3693275
theorem B2757959 : Blo 726324 2757959 := bstep (se 1 (by rfl) ⟨2068469, by rfl⟩ : syracuseStep 2757959 = 4136939) B4136939
theorem B9311699 : Blo 726324 9311699 := bstep (se 1 (by rfl) ⟨6983774, by rfl⟩ : syracuseStep 9311699 = 13967549) B13967549
theorem B3938219 : Blo 726324 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B727067 : Blo 726324 727067 := bstep (se 1 (by rfl) ⟨545300, by rfl⟩ : syracuseStep 727067 = 1090601) B1090601
theorem B923815 : Blo 726324 923815 := bstep (se 1 (by rfl) ⟨692861, by rfl⟩ : syracuseStep 923815 = 1385723) B1385723
theorem B2628143 : Blo 726324 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B22715407 : Blo 726324 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B728303 : Blo 726324 728303 := bstep (se 1 (by rfl) ⟨546227, by rfl⟩ : syracuseStep 728303 = 1092455) B1092455
theorem B3677723 : Blo 726324 3677723 := bstep (se 1 (by rfl) ⟨2758292, by rfl⟩ : syracuseStep 3677723 = 5516585) B5516585
theorem B728815 : Blo 726324 728815 := bstep (se 1 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 728815 = 1093223) B1093223
theorem B1089647 : Blo 726324 1089647 := bstep (se 1 (by rfl) ⟨817235, by rfl⟩ : syracuseStep 1089647 = 1634471) B1634471
theorem B15769727 : Blo 726324 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B1843337 : Blo 726324 1843337 := bstep (se 2 (by rfl) ⟨691251, by rfl⟩ : syracuseStep 1843337 = 1382503) B1382503
theorem B153134317 : Blo 726324 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B1091231 : Blo 726324 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B1091675 : Blo 726324 1091675 := bstep (se 1 (by rfl) ⟨818756, by rfl⟩ : syracuseStep 1091675 = 1637513) B1637513
theorem B4139423 : Blo 726324 4139423 := bstep (se 1 (by rfl) ⟨3104567, by rfl⟩ : syracuseStep 4139423 = 6209135) B6209135
theorem B1092479 : Blo 726324 1092479 := bstep (se 1 (by rfl) ⟨819359, by rfl⟩ : syracuseStep 1092479 = 1638719) B1638719
theorem B7482731 : Blo 726324 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B1846921 : Blo 726324 1846921 := bstep (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) B1385191
theorem B12627953 : Blo 726324 12627953 := bstep (se 2 (by rfl) ⟨4735482, by rfl⟩ : syracuseStep 12627953 = 9470965) B9470965
theorem B1093673 : Blo 726324 1093673 := bstep (se 2 (by rfl) ⟨410127, by rfl⟩ : syracuseStep 1093673 = 820255) B820255
theorem B22688599 : Blo 726324 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B1094879 : Blo 726324 1094879 := bstep (se 1 (by rfl) ⟨821159, by rfl⟩ : syracuseStep 1094879 = 1642319) B1642319
theorem B24622703 : Blo 726324 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B3684527 : Blo 726324 3684527 := bstep (se 1 (by rfl) ⟨2763395, by rfl⟩ : syracuseStep 3684527 = 5526791) B5526791
theorem B9354041 : Blo 726324 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B2768863 : Blo 726324 2768863 := bstep (se 1 (by rfl) ⟨2076647, by rfl⟩ : syracuseStep 2768863 = 4153295) B4153295
theorem B2834731 : Blo 726324 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B1754423 : Blo 726324 1754423 := bstep (se 1 (by rfl) ⟨1315817, by rfl⟩ : syracuseStep 1754423 = 2631635) B2631635
theorem B3688415 : Blo 726324 3688415 := bstep (se 1 (by rfl) ⟨2766311, by rfl⟩ : syracuseStep 3688415 = 5532623) B5532623
theorem B3984079 : Blo 726324 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B4148921 : Blo 726324 4148921 := bstep (se 2 (by rfl) ⟨1555845, by rfl⟩ : syracuseStep 4148921 = 3111691) B3111691
theorem B4149103 : Blo 726324 4149103 := bstep (se 1 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 4149103 = 6223655) B6223655
theorem B8278523 : Blo 726324 8278523 := bstep (se 1 (by rfl) ⟨6208892, by rfl⟩ : syracuseStep 8278523 = 12417785) B12417785
theorem B18895783 : Blo 726324 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B7885775 : Blo 726324 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B69031561 : Blo 726324 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B3497195 : Blo 726324 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B1105307 : Blo 726324 1105307 := bstep (se 1 (by rfl) ⟨828980, by rfl⟩ : syracuseStep 1105307 = 1657961) B1657961
theorem B4678175 : Blo 726324 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B15786845 : Blo 726324 15786845 := bstep (se 3 (by rfl) ⟨2960033, by rfl⟩ : syracuseStep 15786845 = 5920067) B5920067
theorem B49243399 : Blo 726324 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B17755145 : Blo 726324 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B2454515 : Blo 726324 2454515 := bstep (se 1 (by rfl) ⟨1840886, by rfl⟩ : syracuseStep 2454515 = 3681773) B3681773
theorem B8287271 : Blo 726324 8287271 := bstep (se 1 (by rfl) ⟨6215453, by rfl⟩ : syracuseStep 8287271 = 12430907) B12430907
theorem B1898039 : Blo 726324 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B31487879 : Blo 726324 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B1636919 : Blo 726324 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B3930713 : Blo 726324 3930713 := bstep (se 2 (by rfl) ⟨1474017, by rfl⟩ : syracuseStep 3930713 = 2948035) B2948035
theorem B2947711 : Blo 726324 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B1637423 : Blo 726324 1637423 := bstep (se 1 (by rfl) ⟨1228067, by rfl⟩ : syracuseStep 1637423 = 2456135) B2456135
theorem B818239 : Blo 726324 818239 := bstep (se 1 (by rfl) ⟨613679, by rfl⟩ : syracuseStep 818239 = 1227359) B1227359
theorem B3112033 : Blo 726324 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B1965217 : Blo 726324 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B2456783 : Blo 726324 2456783 := bstep (se 1 (by rfl) ⟨1842587, by rfl⟩ : syracuseStep 2456783 = 3685175) B3685175
theorem B1638107 : Blo 726324 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B1638503 : Blo 726324 1638503 := bstep (se 1 (by rfl) ⟨1228877, by rfl⟩ : syracuseStep 1638503 = 2457755) B2457755
theorem B2458943 : Blo 726324 2458943 := bstep (se 1 (by rfl) ⟨1844207, by rfl⟩ : syracuseStep 2458943 = 3688415) B3688415
theorem B6227279 : Blo 726324 6227279 := bstep (se 1 (by rfl) ⟨4670459, by rfl⟩ : syracuseStep 6227279 = 9340919) B9340919
theorem B1639763 : Blo 726324 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B2951083 : Blo 726324 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B2624395 : Blo 726324 2624395 := bstep (se 1 (by rfl) ⟨1968296, by rfl⟩ : syracuseStep 2624395 = 3936593) B3936593
theorem B1641455 : Blo 726324 1641455 := bstep (se 1 (by rfl) ⟨1231091, by rfl⟩ : syracuseStep 1641455 = 2462183) B2462183
theorem B1838639 : Blo 726324 1838639 := bstep (se 1 (by rfl) ⟨1378979, by rfl⟩ : syracuseStep 1838639 = 2757959) B2757959
theorem B5312105 : Blo 726324 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B2625479 : Blo 726324 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B2331463 : Blo 726324 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B2462561 : Blo 726324 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B726431 : Blo 726324 726431 := bstep (se 1 (by rfl) ⟨544823, by rfl⟩ : syracuseStep 726431 = 1089647) B1089647
theorem B1840745 : Blo 726324 1840745 := bstep (se 2 (by rfl) ⟨690279, by rfl⟩ : syracuseStep 1840745 = 1380559) B1380559
theorem B3118783 : Blo 726324 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B10524563 : Blo 726324 10524563 := bstep (se 1 (by rfl) ⟨7893422, by rfl⟩ : syracuseStep 10524563 = 15786845) B15786845
theorem B727487 : Blo 726324 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B30251465 : Blo 726324 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B816716357 : Blo 726324 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B727783 : Blo 726324 727783 := bstep (se 1 (by rfl) ⟨545837, by rfl⟩ : syracuseStep 727783 = 1091675) B1091675
theorem B2759615 : Blo 726324 2759615 := bstep (se 1 (by rfl) ⟨2069711, by rfl⟩ : syracuseStep 2759615 = 4139423) B4139423
theorem B728319 : Blo 726324 728319 := bstep (se 1 (by rfl) ⟨546239, by rfl⟩ : syracuseStep 728319 = 1092479) B1092479
theorem B11836763 : Blo 726324 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B729115 : Blo 726324 729115 := bstep (se 1 (by rfl) ⟨546836, by rfl⟩ : syracuseStep 729115 = 1093673) B1093673
theorem B729919 : Blo 726324 729919 := bstep (se 1 (by rfl) ⟨547439, by rfl⟩ : syracuseStep 729919 = 1094879) B1094879
theorem B30287209 : Blo 726324 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1090985 : Blo 726324 1090985 := bstep (se 2 (by rfl) ⟨409119, by rfl⟩ : syracuseStep 1090985 = 818239) B818239
theorem B1091279 : Blo 726324 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B6236027 : Blo 726324 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B1091615 : Blo 726324 1091615 := bstep (se 1 (by rfl) ⟨818711, by rfl⟩ : syracuseStep 1091615 = 1637423) B1637423
theorem B1092071 : Blo 726324 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B3779641 : Blo 726324 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B1093343 : Blo 726324 1093343 := bstep (se 1 (by rfl) ⟨820007, by rfl⟩ : syracuseStep 1093343 = 1640015) B1640015
theorem B1094747 : Blo 726324 1094747 := bstep (se 1 (by rfl) ⟨821060, by rfl⟩ : syracuseStep 1094747 = 1642121) B1642121
theorem B2765947 : Blo 726324 2765947 := bstep (se 1 (by rfl) ⟨2074460, by rfl⟩ : syracuseStep 2765947 = 4148921) B4148921
theorem B1095215 : Blo 726324 1095215 := bstep (se 1 (by rfl) ⟨821411, by rfl⟩ : syracuseStep 1095215 = 1642823) B1642823
theorem B5519015 : Blo 726324 5519015 := bstep (se 1 (by rfl) ⟨4139261, by rfl⟩ : syracuseStep 5519015 = 8278523) B8278523
theorem B5257183 : Blo 726324 5257183 := bstep (se 1 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 5257183 = 7885775) B7885775
theorem B6207799 : Blo 726324 6207799 := bstep (se 1 (by rfl) ⟨4655849, by rfl⟩ : syracuseStep 6207799 = 9311699) B9311699
theorem B5061437 : Blo 726324 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B1752095 : Blo 726324 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B736871 : Blo 726324 736871 := bstep (se 1 (by rfl) ⟨552653, by rfl⟩ : syracuseStep 736871 = 1105307) B1105307
theorem B1228891 : Blo 726324 1228891 := bstep (se 1 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 1228891 = 1843337) B1843337
theorem B1050525845 : Blo 726324 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B1231753 : Blo 726324 1231753 := bstep (se 2 (by rfl) ⟨461907, by rfl⟩ : syracuseStep 1231753 = 923815) B923815
theorem B5524847 : Blo 726324 5524847 := bstep (se 1 (by rfl) ⟨4143635, by rfl⟩ : syracuseStep 5524847 = 8287271) B8287271
theorem B20991919 : Blo 726324 20991919 := bstep (se 1 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 20991919 = 31487879) B31487879
theorem B4149377 : Blo 726324 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B3691817 : Blo 726324 3691817 := bstep (se 2 (by rfl) ⟨1384431, by rfl⟩ : syracuseStep 3691817 = 2768863) B2768863
theorem B1398143 : Blo 726324 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B1169615 : Blo 726324 1169615 := bstep (se 1 (by rfl) ⟨877211, by rfl⟩ : syracuseStep 1169615 = 1754423) B1754423
theorem B2451815 : Blo 726324 2451815 := bstep (se 1 (by rfl) ⟨1838861, by rfl⟩ : syracuseStep 2451815 = 3677723) B3677723
theorem B5532137 : Blo 726324 5532137 := bstep (se 2 (by rfl) ⟨2074551, by rfl⟩ : syracuseStep 5532137 = 4149103) B4149103
theorem B10513151 : Blo 726324 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B25194377 : Blo 726324 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B92042081 : Blo 726324 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B8418635 : Blo 726324 8418635 := bstep (se 1 (by rfl) ⟨6313976, by rfl⟩ : syracuseStep 8418635 = 12627953) B12627953
theorem B1636343 : Blo 726324 1636343 := bstep (se 1 (by rfl) ⟨1227257, by rfl⟩ : syracuseStep 1636343 = 2454515) B2454515
theorem B3930281 : Blo 726324 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B19953949 : Blo 726324 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B16415135 : Blo 726324 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B2456351 : Blo 726324 2456351 := bstep (se 1 (by rfl) ⟨1842263, by rfl⟩ : syracuseStep 2456351 = 3684527) B3684527
theorem B2620289 : Blo 726324 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B2620475 : Blo 726324 2620475 := bstep (se 1 (by rfl) ⟨1965356, by rfl⟩ : syracuseStep 2620475 = 3930713) B3930713
theorem B1637855 : Blo 726324 1637855 := bstep (se 1 (by rfl) ⟨1228391, by rfl⟩ : syracuseStep 1637855 = 2456783) B2456783
theorem B700350563 : Blo 726324 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B1638521 : Blo 726324 1638521 := bstep (se 2 (by rfl) ⟨614445, by rfl⟩ : syracuseStep 1638521 = 1228891) B1228891
theorem B1639295 : Blo 726324 1639295 := bstep (se 1 (by rfl) ⟨1229471, by rfl⟩ : syracuseStep 1639295 = 2458943) B2458943
theorem B3541403 : Blo 726324 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B3934777 : Blo 726324 3934777 := bstep (se 2 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 3934777 = 2951083) B2951083
theorem B1641707 : Blo 726324 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B2461211 : Blo 726324 2461211 := bstep (se 1 (by rfl) ⟨1845908, by rfl⟩ : syracuseStep 2461211 = 3691817) B3691817
theorem B1642337 : Blo 726324 1642337 := bstep (se 2 (by rfl) ⟨615876, by rfl⟩ : syracuseStep 1642337 = 1231753) B1231753
theorem B7016375 : Blo 726324 7016375 := bstep (se 1 (by rfl) ⟨5262281, by rfl⟩ : syracuseStep 7016375 = 10524563) B10524563
theorem B544477571 : Blo 726324 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B1839743 : Blo 726324 1839743 := bstep (se 1 (by rfl) ⟨1379807, by rfl⟩ : syracuseStep 1839743 = 2759615) B2759615
theorem B27989225 : Blo 726324 27989225 := bstep (se 2 (by rfl) ⟨10495959, by rfl⟩ : syracuseStep 27989225 = 20991919) B20991919
theorem B20158085 : Blo 726324 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B727323 : Blo 726324 727323 := bstep (se 1 (by rfl) ⟨545492, by rfl⟩ : syracuseStep 727323 = 1090985) B1090985
theorem B727519 : Blo 726324 727519 := bstep (se 1 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 727519 = 1091279) B1091279
theorem B727743 : Blo 726324 727743 := bstep (se 1 (by rfl) ⟨545807, by rfl⟩ : syracuseStep 727743 = 1091615) B1091615
theorem B728047 : Blo 726324 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B728895 : Blo 726324 728895 := bstep (se 1 (by rfl) ⟨546671, by rfl⟩ : syracuseStep 728895 = 1093343) B1093343
theorem B729831 : Blo 726324 729831 := bstep (se 1 (by rfl) ⟨547373, by rfl⟩ : syracuseStep 729831 = 1094747) B1094747
theorem B5612423 : Blo 726324 5612423 := bstep (se 1 (by rfl) ⟨4209317, by rfl⟩ : syracuseStep 5612423 = 8418635) B8418635
theorem B730143 : Blo 726324 730143 := bstep (se 1 (by rfl) ⟨547607, by rfl⟩ : syracuseStep 730143 = 1095215) B1095215
theorem B3679343 : Blo 726324 3679343 := bstep (se 1 (by rfl) ⟨2759507, by rfl⟩ : syracuseStep 3679343 = 5519015) B5519015
theorem B1090895 : Blo 726324 1090895 := bstep (se 1 (by rfl) ⟨818171, by rfl⟩ : syracuseStep 1090895 = 1636343) B1636343
theorem B1746859 : Blo 726324 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B1746983 : Blo 726324 1746983 := bstep (se 1 (by rfl) ⟨1310237, by rfl⟩ : syracuseStep 1746983 = 2620475) B2620475
theorem B1091903 : Blo 726324 1091903 := bstep (se 1 (by rfl) ⟨818927, by rfl⟩ : syracuseStep 1091903 = 1637855) B1637855
theorem B1092335 : Blo 726324 1092335 := bstep (se 1 (by rfl) ⟨819251, by rfl⟩ : syracuseStep 1092335 = 1638503) B1638503
theorem B1093175 : Blo 726324 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B40382945 : Blo 726324 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1094303 : Blo 726324 1094303 := bstep (se 1 (by rfl) ⟨820727, by rfl⟩ : syracuseStep 1094303 = 1641455) B1641455
theorem B3683231 : Blo 726324 3683231 := bstep (se 1 (by rfl) ⟨2762423, by rfl⟩ : syracuseStep 3683231 = 5524847) B5524847
theorem B1225759 : Blo 726324 1225759 := bstep (se 1 (by rfl) ⟨919319, by rfl⟩ : syracuseStep 1225759 = 1838639) B1838639
theorem B1750319 : Blo 726324 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B2766251 : Blo 726324 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B932095 : Blo 726324 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B1227163 : Blo 726324 1227163 := bstep (se 1 (by rfl) ⟨920372, by rfl⟩ : syracuseStep 1227163 = 1840745) B1840745
theorem B20167643 : Blo 726324 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B3687929 : Blo 726324 3687929 := bstep (se 2 (by rfl) ⟨1382973, by rfl⟩ : syracuseStep 3687929 = 2765947) B2765947
theorem B3688091 : Blo 726324 3688091 := bstep (se 1 (by rfl) ⟨2766068, by rfl⟩ : syracuseStep 3688091 = 5532137) B5532137
theorem B16796251 : Blo 726324 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B8277065 : Blo 726324 8277065 := bstep (se 2 (by rfl) ⟨3103899, by rfl⟩ : syracuseStep 8277065 = 6207799) B6207799
theorem B61361387 : Blo 726324 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B1168063 : Blo 726324 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B4151519 : Blo 726324 4151519 := bstep (se 1 (by rfl) ⟨3113639, by rfl⟩ : syracuseStep 4151519 = 6227279) B6227279
theorem B3499193 : Blo 726324 3499193 := bstep (se 2 (by rfl) ⟨1312197, by rfl⟩ : syracuseStep 3499193 = 2624395) B2624395
theorem B779743 : Blo 726324 779743 := bstep (se 1 (by rfl) ⟨584807, by rfl⟩ : syracuseStep 779743 = 1169615) B1169615
theorem B7891175 : Blo 726324 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B3108617 : Blo 726324 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B4157351 : Blo 726324 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B1634543 : Blo 726324 1634543 := bstep (se 1 (by rfl) ⟨1225907, by rfl⟩ : syracuseStep 1634543 = 2451815) B2451815
theorem B7008767 : Blo 726324 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B4158377 : Blo 726324 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B7009577 : Blo 726324 7009577 := bstep (se 2 (by rfl) ⟨2628591, by rfl⟩ : syracuseStep 7009577 = 5257183) B5257183
theorem B26605265 : Blo 726324 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B2620187 : Blo 726324 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B1964989 : Blo 726324 1964989 := bstep (se 3 (by rfl) ⟨368435, by rfl⟩ : syracuseStep 1964989 = 736871) B736871
theorem B10943423 : Blo 726324 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B1637567 : Blo 726324 1637567 := bstep (se 1 (by rfl) ⟨1228175, by rfl⟩ : syracuseStep 1637567 = 2456351) B2456351
theorem B3374291 : Blo 726324 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B2458619 : Blo 726324 2458619 := bstep (se 1 (by rfl) ⟨1843964, by rfl⟩ : syracuseStep 2458619 = 3687929) B3687929
theorem B2458727 : Blo 726324 2458727 := bstep (se 1 (by rfl) ⟨1844045, by rfl⟩ : syracuseStep 2458727 = 3688091) B3688091
theorem B2360935 : Blo 726324 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B1640807 : Blo 726324 1640807 := bstep (se 1 (by rfl) ⟨1230605, by rfl⟩ : syracuseStep 1640807 = 2461211) B2461211
theorem B2329145 : Blo 726324 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B5246369 : Blo 726324 5246369 := bstep (se 2 (by rfl) ⟨1967388, by rfl⟩ : syracuseStep 5246369 = 3934777) B3934777
theorem B6229669 : Blo 726324 6229669 := bstep (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) B1168063
theorem B13438723 : Blo 726324 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B70947373 : Blo 726324 70947373 := bstep (se 3 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 70947373 = 26605265) B26605265
theorem B2332795 : Blo 726324 2332795 := bstep (se 1 (by rfl) ⟨1749596, by rfl⟩ : syracuseStep 2332795 = 3499193) B3499193
theorem B727263 : Blo 726324 727263 := bstep (se 1 (by rfl) ⟨545447, by rfl⟩ : syracuseStep 727263 = 1090895) B1090895
theorem B727935 : Blo 726324 727935 := bstep (se 1 (by rfl) ⟨545951, by rfl⟩ : syracuseStep 727935 = 1091903) B1091903
theorem B728223 : Blo 726324 728223 := bstep (se 1 (by rfl) ⟨546167, by rfl⟩ : syracuseStep 728223 = 1092335) B1092335
theorem B728783 : Blo 726324 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B2072411 : Blo 726324 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B53780381 : Blo 726324 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B1089695 : Blo 726324 1089695 := bstep (se 1 (by rfl) ⟨817271, by rfl⟩ : syracuseStep 1089695 = 1634543) B1634543
theorem B729535 : Blo 726324 729535 := bstep (se 1 (by rfl) ⟨547151, by rfl⟩ : syracuseStep 729535 = 1094303) B1094303
theorem B1844167 : Blo 726324 1844167 := bstep (se 1 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 1844167 = 2766251) B2766251
theorem B1746791 : Blo 726324 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B1091711 : Blo 726324 1091711 := bstep (se 1 (by rfl) ⟨818783, by rfl⟩ : syracuseStep 1091711 = 1637567) B1637567
theorem B1092347 : Blo 726324 1092347 := bstep (se 1 (by rfl) ⟨819260, by rfl⟩ : syracuseStep 1092347 = 1638521) B1638521
theorem B1092863 : Blo 726324 1092863 := bstep (se 1 (by rfl) ⟨819647, by rfl⟩ : syracuseStep 1092863 = 1639295) B1639295
theorem B5518043 : Blo 726324 5518043 := bstep (se 1 (by rfl) ⟨4138532, by rfl⟩ : syracuseStep 5518043 = 8277065) B8277065
theorem B40907591 : Blo 726324 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B1094471 : Blo 726324 1094471 := bstep (se 1 (by rfl) ⟨820853, by rfl⟩ : syracuseStep 1094471 = 1641707) B1641707
theorem B1094891 : Blo 726324 1094891 := bstep (se 1 (by rfl) ⟨821168, by rfl⟩ : syracuseStep 1094891 = 1642337) B1642337
theorem B362985047 : Blo 726324 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1226495 : Blo 726324 1226495 := bstep (se 1 (by rfl) ⟨919871, by rfl⟩ : syracuseStep 1226495 = 1839743) B1839743
theorem B22395001 : Blo 726324 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B18659483 : Blo 726324 18659483 := bstep (se 1 (by rfl) ⟨13994612, by rfl⟩ : syracuseStep 18659483 = 27989225) B27989225
theorem B2767679 : Blo 726324 2767679 := bstep (se 1 (by rfl) ⟨2075759, by rfl⟩ : syracuseStep 2767679 = 4151519) B4151519
theorem B1164655 : Blo 726324 1164655 := bstep (se 1 (by rfl) ⟨873491, by rfl⟩ : syracuseStep 1164655 = 1746983) B1746983
theorem B5260783 : Blo 726324 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B2771567 : Blo 726324 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B26921963 : Blo 726324 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B4672511 : Blo 726324 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B2772251 : Blo 726324 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B4673051 : Blo 726324 4673051 := bstep (se 1 (by rfl) ⟨3504788, by rfl⟩ : syracuseStep 4673051 = 7009577) B7009577
theorem B1166879 : Blo 726324 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B7295615 : Blo 726324 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B2249527 : Blo 726324 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B466900375 : Blo 726324 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B1039657 : Blo 726324 1039657 := bstep (se 2 (by rfl) ⟨389871, by rfl⟩ : syracuseStep 1039657 = 779743) B779743
theorem B14966461 : Blo 726324 14966461 := bstep (se 3 (by rfl) ⟨2806211, by rfl⟩ : syracuseStep 14966461 = 5612423) B5612423
theorem B4677583 : Blo 726324 4677583 := bstep (se 1 (by rfl) ⟨3508187, by rfl⟩ : syracuseStep 4677583 = 7016375) B7016375
theorem B2452895 : Blo 726324 2452895 := bstep (se 1 (by rfl) ⟨1839671, by rfl⟩ : syracuseStep 2452895 = 3679343) B3679343
theorem B1634345 : Blo 726324 1634345 := bstep (se 2 (by rfl) ⟨612879, by rfl⟩ : syracuseStep 1634345 = 1225759) B1225759
theorem B1242793 : Blo 726324 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B1636217 : Blo 726324 1636217 := bstep (se 2 (by rfl) ⟨613581, by rfl⟩ : syracuseStep 1636217 = 1227163) B1227163
theorem B2455487 : Blo 726324 2455487 := bstep (se 1 (by rfl) ⟨1841615, by rfl⟩ : syracuseStep 2455487 = 3683231) B3683231
theorem B2619985 : Blo 726324 2619985 := bstep (se 2 (by rfl) ⟨982494, by rfl⟩ : syracuseStep 2619985 = 1964989) B1964989
theorem B1639079 : Blo 726324 1639079 := bstep (se 1 (by rfl) ⟨1229309, by rfl⟩ : syracuseStep 1639079 = 2458619) B2458619
theorem B1639151 : Blo 726324 1639151 := bstep (se 1 (by rfl) ⟨1229363, by rfl⟩ : syracuseStep 1639151 = 2458727) B2458727
theorem B2458889 : Blo 726324 2458889 := bstep (se 2 (by rfl) ⟨922083, by rfl⟩ : syracuseStep 2458889 = 1844167) B1844167
theorem B7014377 : Blo 726324 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B3115007 : Blo 726324 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B3147913 : Blo 726324 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B3115367 : Blo 726324 3115367 := bstep (se 1 (by rfl) ⟨2336525, by rfl⟩ : syracuseStep 3115367 = 4673051) B4673051
theorem B1381607 : Blo 726324 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B35853587 : Blo 726324 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B726463 : Blo 726324 726463 := bstep (se 1 (by rfl) ⟨544847, by rfl⟩ : syracuseStep 726463 = 1089695) B1089695
theorem B727807 : Blo 726324 727807 := bstep (se 1 (by rfl) ⟨545855, by rfl⟩ : syracuseStep 727807 = 1091711) B1091711
theorem B728231 : Blo 726324 728231 := bstep (se 1 (by rfl) ⟨546173, by rfl⟩ : syracuseStep 728231 = 1092347) B1092347
theorem B622533833 : Blo 726324 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B728575 : Blo 726324 728575 := bstep (se 1 (by rfl) ⟨546431, by rfl⟩ : syracuseStep 728575 = 1092863) B1092863
theorem B1089563 : Blo 726324 1089563 := bstep (se 1 (by rfl) ⟨817172, by rfl⟩ : syracuseStep 1089563 = 1634345) B1634345
theorem B29860001 : Blo 726324 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B3678695 : Blo 726324 3678695 := bstep (se 1 (by rfl) ⟨2759021, by rfl⟩ : syracuseStep 3678695 = 5518043) B5518043
theorem B27271727 : Blo 726324 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B729647 : Blo 726324 729647 := bstep (se 1 (by rfl) ⟨547235, by rfl⟩ : syracuseStep 729647 = 1094471) B1094471
theorem B729927 : Blo 726324 729927 := bstep (se 1 (by rfl) ⟨547445, by rfl⟩ : syracuseStep 729927 = 1094891) B1094891
theorem B6628229 : Blo 726324 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B1090811 : Blo 726324 1090811 := bstep (se 1 (by rfl) ⟨818108, by rfl⟩ : syracuseStep 1090811 = 1636217) B1636217
theorem B1386209 : Blo 726324 1386209 := bstep (se 2 (by rfl) ⟨519828, by rfl⟩ : syracuseStep 1386209 = 1039657) B1039657
theorem B1845119 : Blo 726324 1845119 := bstep (se 1 (by rfl) ⟨1383839, by rfl⟩ : syracuseStep 1845119 = 2767679) B2767679
theorem B6236777 : Blo 726324 6236777 := bstep (se 2 (by rfl) ⟨2338791, by rfl⟩ : syracuseStep 6236777 = 4677583) B4677583
theorem B1093871 : Blo 726324 1093871 := bstep (se 1 (by rfl) ⟨820403, by rfl⟩ : syracuseStep 1093871 = 1640807) B1640807
theorem B1552763 : Blo 726324 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B1847711 : Blo 726324 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B1552873 : Blo 726324 1552873 := bstep (se 2 (by rfl) ⟨582327, by rfl⟩ : syracuseStep 1552873 = 1164655) B1164655
theorem B1848167 : Blo 726324 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B4863743 : Blo 726324 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B8306225 : Blo 726324 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B2999369 : Blo 726324 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1164527 : Blo 726324 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B3493313 : Blo 726324 3493313 := bstep (se 2 (by rfl) ⟨1309992, by rfl⟩ : syracuseStep 3493313 = 2619985) B2619985
theorem B12439655 : Blo 726324 12439655 := bstep (se 1 (by rfl) ⟨9329741, by rfl⟩ : syracuseStep 12439655 = 18659483) B18659483
theorem B17947975 : Blo 726324 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B3497579 : Blo 726324 3497579 := bstep (se 1 (by rfl) ⟨2623184, by rfl⟩ : syracuseStep 3497579 = 5246369) B5246369
theorem B777919 : Blo 726324 777919 := bstep (se 1 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 777919 = 1166879) B1166879
theorem B17918297 : Blo 726324 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B94596497 : Blo 726324 94596497 := bstep (se 2 (by rfl) ⟨35473686, by rfl⟩ : syracuseStep 94596497 = 70947373) B70947373
theorem B1635263 : Blo 726324 1635263 := bstep (se 1 (by rfl) ⟨1226447, by rfl⟩ : syracuseStep 1635263 = 2452895) B2452895
theorem B3110393 : Blo 726324 3110393 := bstep (se 2 (by rfl) ⟨1166397, by rfl⟩ : syracuseStep 3110393 = 2332795) B2332795
theorem B241990031 : Blo 726324 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B817663 : Blo 726324 817663 := bstep (se 1 (by rfl) ⟨613247, by rfl⟩ : syracuseStep 817663 = 1226495) B1226495
theorem B1636991 : Blo 726324 1636991 := bstep (se 1 (by rfl) ⟨1227743, by rfl⟩ : syracuseStep 1636991 = 2455487) B2455487
theorem B19955281 : Blo 726324 19955281 := bstep (se 2 (by rfl) ⟨7483230, by rfl⟩ : syracuseStep 19955281 = 14966461) B14966461
theorem B1999579 : Blo 726324 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B1639259 : Blo 726324 1639259 := bstep (se 1 (by rfl) ⟨1229444, by rfl⟩ : syracuseStep 1639259 = 2458889) B2458889
theorem B2328875 : Blo 726324 2328875 := bstep (se 1 (by rfl) ⟨1746656, by rfl⟩ : syracuseStep 2328875 = 3493313) B3493313
theorem B8293103 : Blo 726324 8293103 := bstep (se 1 (by rfl) ⟨6219827, by rfl⟩ : syracuseStep 8293103 = 12439655) B12439655
theorem B4197217 : Blo 726324 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B921071 : Blo 726324 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B2331719 : Blo 726324 2331719 := bstep (se 1 (by rfl) ⟨1748789, by rfl⟩ : syracuseStep 2331719 = 3497579) B3497579
theorem B726375 : Blo 726324 726375 := bstep (se 1 (by rfl) ⟨544781, by rfl⟩ : syracuseStep 726375 = 1089563) B1089563
theorem B2070497 : Blo 726324 2070497 := bstep (se 2 (by rfl) ⟨776436, by rfl⟩ : syracuseStep 2070497 = 1552873) B1552873
theorem B727207 : Blo 726324 727207 := bstep (se 1 (by rfl) ⟨545405, by rfl⟩ : syracuseStep 727207 = 1090811) B1090811
theorem B924139 : Blo 726324 924139 := bstep (se 1 (by rfl) ⟨693104, by rfl⟩ : syracuseStep 924139 = 1386209) B1386209
theorem B729247 : Blo 726324 729247 := bstep (se 1 (by rfl) ⟨546935, by rfl⟩ : syracuseStep 729247 = 1093871) B1093871
theorem B1090175 : Blo 726324 1090175 := bstep (se 1 (by rfl) ⟨817631, by rfl⟩ : syracuseStep 1090175 = 1635263) B1635263
theorem B1090217 : Blo 726324 1090217 := bstep (se 2 (by rfl) ⟨408831, by rfl⟩ : syracuseStep 1090217 = 817663) B817663
theorem B2073595 : Blo 726324 2073595 := bstep (se 1 (by rfl) ⟨1555196, by rfl⟩ : syracuseStep 2073595 = 3110393) B3110393
theorem B161326687 : Blo 726324 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B1091327 : Blo 726324 1091327 := bstep (se 1 (by rfl) ⟨818495, by rfl⟩ : syracuseStep 1091327 = 1636991) B1636991
theorem B23930633 : Blo 726324 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B1092719 : Blo 726324 1092719 := bstep (se 1 (by rfl) ⟨819539, by rfl⟩ : syracuseStep 1092719 = 1639079) B1639079
theorem B1092767 : Blo 726324 1092767 := bstep (se 1 (by rfl) ⟨819575, by rfl⟩ : syracuseStep 1092767 = 1639151) B1639151
theorem B2076671 : Blo 726324 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B2076911 : Blo 726324 2076911 := bstep (se 1 (by rfl) ⟨1557683, by rfl⟩ : syracuseStep 2076911 = 3115367) B3115367
theorem B23902391 : Blo 726324 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B415022555 : Blo 726324 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B19906667 : Blo 726324 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B1230079 : Blo 726324 1230079 := bstep (se 1 (by rfl) ⟨922559, by rfl⟩ : syracuseStep 1230079 = 1845119) B1845119
theorem B11945531 : Blo 726324 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B63064331 : Blo 726324 63064331 := bstep (se 1 (by rfl) ⟨47298248, by rfl⟩ : syracuseStep 63064331 = 94596497) B94596497
theorem B1035175 : Blo 726324 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B1231807 : Blo 726324 1231807 := bstep (se 1 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 1231807 = 1847711) B1847711
theorem B1232111 : Blo 726324 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B1037225 : Blo 726324 1037225 := bstep (se 2 (by rfl) ⟨388959, by rfl⟩ : syracuseStep 1037225 = 777919) B777919
theorem B776351 : Blo 726324 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B4676251 : Blo 726324 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B2452463 : Blo 726324 2452463 := bstep (se 1 (by rfl) ⟨1839347, by rfl⟩ : syracuseStep 2452463 = 3678695) B3678695
theorem B18181151 : Blo 726324 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B4418819 : Blo 726324 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B4157851 : Blo 726324 4157851 := bstep (se 1 (by rfl) ⟨3118388, by rfl⟩ : syracuseStep 4157851 = 6236777) B6236777
theorem B3242495 : Blo 726324 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B26607041 : Blo 726324 26607041 := bstep (se 2 (by rfl) ⟨9977640, by rfl⟩ : syracuseStep 26607041 = 19955281) B19955281
theorem B5537483 : Blo 726324 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B13271111 : Blo 726324 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B7963687 : Blo 726324 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B42042887 : Blo 726324 42042887 := bstep (se 1 (by rfl) ⟨31532165, by rfl⟩ : syracuseStep 42042887 = 63064331) B63064331
theorem B1640105 : Blo 726324 1640105 := bstep (se 2 (by rfl) ⟨615039, by rfl⟩ : syracuseStep 1640105 = 1230079) B1230079
theorem B821407 : Blo 726324 821407 := bstep (se 1 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 821407 = 1232111) B1232111
theorem B1380233 : Blo 726324 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B1642409 : Blo 726324 1642409 := bstep (se 2 (by rfl) ⟨615903, by rfl⟩ : syracuseStep 1642409 = 1231807) B1231807
theorem B1380331 : Blo 726324 1380331 := bstep (se 1 (by rfl) ⟨1035248, by rfl⟩ : syracuseStep 1380331 = 2070497) B2070497
theorem B2070269 : Blo 726324 2070269 := bstep (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) B776351
theorem B726783 : Blo 726324 726783 := bstep (se 1 (by rfl) ⟨545087, by rfl⟩ : syracuseStep 726783 = 1090175) B1090175
theorem B726811 : Blo 726324 726811 := bstep (se 1 (by rfl) ⟨545108, by rfl⟩ : syracuseStep 726811 = 1090217) B1090217
theorem B5543801 : Blo 726324 5543801 := bstep (se 2 (by rfl) ⟨2078925, by rfl⟩ : syracuseStep 5543801 = 4157851) B4157851
theorem B727551 : Blo 726324 727551 := bstep (se 1 (by rfl) ⟨545663, by rfl⟩ : syracuseStep 727551 = 1091327) B1091327
theorem B728479 : Blo 726324 728479 := bstep (se 1 (by rfl) ⟨546359, by rfl⟩ : syracuseStep 728479 = 1092719) B1092719
theorem B728511 : Blo 726324 728511 := bstep (se 1 (by rfl) ⟨546383, by rfl⟩ : syracuseStep 728511 = 1092767) B1092767
theorem B1384447 : Blo 726324 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B1384607 : Blo 726324 1384607 := bstep (se 1 (by rfl) ⟨1038455, by rfl⟩ : syracuseStep 1384607 = 2076911) B2076911
theorem B6235001 : Blo 726324 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B15934927 : Blo 726324 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B17738027 : Blo 726324 17738027 := bstep (se 1 (by rfl) ⟨13303520, by rfl⟩ : syracuseStep 17738027 = 26607041) B26607041
theorem B1092839 : Blo 726324 1092839 := bstep (se 1 (by rfl) ⟨819629, by rfl⟩ : syracuseStep 1092839 = 1639259) B1639259
theorem B2666105 : Blo 726324 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2764793 : Blo 726324 2764793 := bstep (se 2 (by rfl) ⟨1036797, by rfl⟩ : syracuseStep 2764793 = 2073595) B2073595
theorem B1552583 : Blo 726324 1552583 := bstep (se 1 (by rfl) ⟨1164437, by rfl⟩ : syracuseStep 1552583 = 2328875) B2328875
theorem B215102249 : Blo 726324 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B2765933 : Blo 726324 2765933 := bstep (se 3 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 2765933 = 1037225) B1037225
theorem B1554479 : Blo 726324 1554479 := bstep (se 1 (by rfl) ⟨1165859, by rfl⟩ : syracuseStep 1554479 = 2331719) B2331719
theorem B1232185 : Blo 726324 1232185 := bstep (se 2 (by rfl) ⟨462069, by rfl⟩ : syracuseStep 1232185 = 924139) B924139
theorem B276681703 : Blo 726324 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B3691655 : Blo 726324 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B5528735 : Blo 726324 5528735 := bstep (se 1 (by rfl) ⟨4146551, by rfl⟩ : syracuseStep 5528735 = 8293103) B8293103
theorem B5596289 : Blo 726324 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B15953755 : Blo 726324 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B8646653 : Blo 726324 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B1634975 : Blo 726324 1634975 := bstep (se 1 (by rfl) ⟨1226231, by rfl⟩ : syracuseStep 1634975 = 2452463) B2452463
theorem B12120767 : Blo 726324 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B2945879 : Blo 726324 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B2456189 : Blo 726324 2456189 := bstep (se 3 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 2456189 = 921071) B921071
theorem B8847407 : Blo 726324 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B920155 : Blo 726324 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B2461103 : Blo 726324 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B1380179 : Blo 726324 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B1642913 : Blo 726324 1642913 := bstep (se 2 (by rfl) ⟨616092, by rfl⟩ : syracuseStep 1642913 = 1232185) B1232185
theorem B21271673 : Blo 726324 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1840441 : Blo 726324 1840441 := bstep (se 2 (by rfl) ⟨690165, by rfl⟩ : syracuseStep 1840441 = 1380331) B1380331
theorem B923071 : Blo 726324 923071 := bstep (se 1 (by rfl) ⟨692303, by rfl⟩ : syracuseStep 923071 = 1384607) B1384607
theorem B42472997 : Blo 726324 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B368908937 : Blo 726324 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B728559 : Blo 726324 728559 := bstep (se 1 (by rfl) ⟨546419, by rfl⟩ : syracuseStep 728559 = 1092839) B1092839
theorem B1777403 : Blo 726324 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B1843195 : Blo 726324 1843195 := bstep (se 1 (by rfl) ⟨1382396, by rfl⟩ : syracuseStep 1843195 = 2764793) B2764793
theorem B1089983 : Blo 726324 1089983 := bstep (se 1 (by rfl) ⟨817487, by rfl⟩ : syracuseStep 1089983 = 1634975) B1634975
theorem B143401499 : Blo 726324 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1843955 : Blo 726324 1843955 := bstep (se 1 (by rfl) ⟨1382966, by rfl⟩ : syracuseStep 1843955 = 2765933) B2765933
theorem B1845929 : Blo 726324 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B28028591 : Blo 726324 28028591 := bstep (se 1 (by rfl) ⟨21021443, by rfl⟩ : syracuseStep 28028591 = 42042887) B42042887
theorem B1093403 : Blo 726324 1093403 := bstep (se 1 (by rfl) ⟨820052, by rfl⟩ : syracuseStep 1093403 = 1640105) B1640105
theorem B21246569 : Blo 726324 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B1094939 : Blo 726324 1094939 := bstep (se 1 (by rfl) ⟨821204, by rfl⟩ : syracuseStep 1094939 = 1642409) B1642409
theorem B1095209 : Blo 726324 1095209 := bstep (se 2 (by rfl) ⟨410703, by rfl⟩ : syracuseStep 1095209 = 821407) B821407
theorem B3685823 : Blo 726324 3685823 := bstep (se 1 (by rfl) ⟨2764367, by rfl⟩ : syracuseStep 3685823 = 5528735) B5528735
theorem B1035055 : Blo 726324 1035055 := bstep (se 1 (by rfl) ⟨776291, by rfl⟩ : syracuseStep 1035055 = 1552583) B1552583
theorem B8080511 : Blo 726324 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B1036319 : Blo 726324 1036319 := bstep (se 1 (by rfl) ⟨777239, by rfl⟩ : syracuseStep 1036319 = 1554479) B1554479
theorem B23057741 : Blo 726324 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B3695867 : Blo 726324 3695867 := bstep (se 1 (by rfl) ⟨2771900, by rfl⟩ : syracuseStep 3695867 = 5543801) B5543801
theorem B4156667 : Blo 726324 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B3730859 : Blo 726324 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B11825351 : Blo 726324 11825351 := bstep (se 1 (by rfl) ⟨8869013, by rfl⟩ : syracuseStep 11825351 = 17738027) B17738027
theorem B1963919 : Blo 726324 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B1637459 : Blo 726324 1637459 := bstep (se 1 (by rfl) ⟨1228094, by rfl⟩ : syracuseStep 1637459 = 2456189) B2456189
theorem B5898271 : Blo 726324 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B1640735 : Blo 726324 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B56724461 : Blo 726324 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B28315331 : Blo 726324 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B1380073 : Blo 726324 1380073 := bstep (se 2 (by rfl) ⟨517527, by rfl⟩ : syracuseStep 1380073 = 1035055) B1035055
theorem B726655 : Blo 726324 726655 := bstep (se 1 (by rfl) ⟨544991, by rfl⟩ : syracuseStep 726655 = 1089983) B1089983
theorem B2463911 : Blo 726324 2463911 := bstep (se 1 (by rfl) ⟨1847933, by rfl⟩ : syracuseStep 2463911 = 3695867) B3695867
theorem B18685727 : Blo 726324 18685727 := bstep (se 1 (by rfl) ⟨14014295, by rfl⟩ : syracuseStep 18685727 = 28028591) B28028591
theorem B728935 : Blo 726324 728935 := bstep (se 1 (by rfl) ⟨546701, by rfl⟩ : syracuseStep 728935 = 1093403) B1093403
theorem B14164379 : Blo 726324 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B729959 : Blo 726324 729959 := bstep (se 1 (by rfl) ⟨547469, by rfl⟩ : syracuseStep 729959 = 1094939) B1094939
theorem B730139 : Blo 726324 730139 := bstep (se 1 (by rfl) ⟨547604, by rfl⟩ : syracuseStep 730139 = 1095209) B1095209
theorem B1091639 : Blo 726324 1091639 := bstep (se 1 (by rfl) ⟨818729, by rfl⟩ : syracuseStep 1091639 = 1637459) B1637459
theorem B3680477 : Blo 726324 3680477 := bstep (se 3 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 3680477 = 1380179) B1380179
theorem B2763517 : Blo 726324 2763517 := bstep (se 3 (by rfl) ⟨518159, by rfl⟩ : syracuseStep 2763517 = 1036319) B1036319
theorem B1095275 : Blo 726324 1095275 := bstep (se 1 (by rfl) ⟨821456, by rfl⟩ : syracuseStep 1095275 = 1642913) B1642913
theorem B1226873 : Blo 726324 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B61487309 : Blo 726324 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B245939291 : Blo 726324 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B95600999 : Blo 726324 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B1229303 : Blo 726324 1229303 := bstep (se 1 (by rfl) ⟨921977, by rfl⟩ : syracuseStep 1229303 = 1843955) B1843955
theorem B1230619 : Blo 726324 1230619 := bstep (se 1 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 1230619 = 1845929) B1845929
theorem B1230761 : Blo 726324 1230761 := bstep (se 2 (by rfl) ⟨461535, by rfl⟩ : syracuseStep 1230761 = 923071) B923071
theorem B2771111 : Blo 726324 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B7883567 : Blo 726324 7883567 := bstep (se 1 (by rfl) ⟨5912675, by rfl⟩ : syracuseStep 7883567 = 11825351) B11825351
theorem B21548029 : Blo 726324 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B4739741 : Blo 726324 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B2453921 : Blo 726324 2453921 := bstep (se 2 (by rfl) ⟨920220, by rfl⟩ : syracuseStep 2453921 = 1840441) B1840441
theorem B2487239 : Blo 726324 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B1309279 : Blo 726324 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B2457215 : Blo 726324 2457215 := bstep (se 1 (by rfl) ⟨1842911, by rfl⟩ : syracuseStep 2457215 = 3685823) B3685823
theorem B2457593 : Blo 726324 2457593 := bstep (se 2 (by rfl) ⟨921597, by rfl⟩ : syracuseStep 2457593 = 1843195) B1843195
theorem B7864361 : Blo 726324 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B63733999 : Blo 726324 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B819535 : Blo 726324 819535 := bstep (se 1 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 819535 = 1229303) B1229303
theorem B820507 : Blo 726324 820507 := bstep (se 1 (by rfl) ⟨615380, by rfl⟩ : syracuseStep 820507 = 1230761) B1230761
theorem B37816307 : Blo 726324 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B1640825 : Blo 726324 1640825 := bstep (se 2 (by rfl) ⟨615309, by rfl⟩ : syracuseStep 1640825 = 1230619) B1230619
theorem B18876887 : Blo 726324 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B1642607 : Blo 726324 1642607 := bstep (se 1 (by rfl) ⟨1231955, by rfl⟩ : syracuseStep 1642607 = 2463911) B2463911
theorem B1840097 : Blo 726324 1840097 := bstep (se 2 (by rfl) ⟨690036, by rfl⟩ : syracuseStep 1840097 = 1380073) B1380073
theorem B12457151 : Blo 726324 12457151 := bstep (se 1 (by rfl) ⟨9342863, by rfl⟩ : syracuseStep 12457151 = 18685727) B18685727
theorem B9442919 : Blo 726324 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B727759 : Blo 726324 727759 := bstep (se 1 (by rfl) ⟨545819, by rfl⟩ : syracuseStep 727759 = 1091639) B1091639
theorem B1745705 : Blo 726324 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B730183 : Blo 726324 730183 := bstep (se 1 (by rfl) ⟨547637, by rfl⟩ : syracuseStep 730183 = 1095275) B1095275
theorem B1847407 : Blo 726324 1847407 := bstep (se 1 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 1847407 = 2771111) B2771111
theorem B1093823 : Blo 726324 1093823 := bstep (se 1 (by rfl) ⟨820367, by rfl⟩ : syracuseStep 1093823 = 1640735) B1640735
theorem B5255711 : Blo 726324 5255711 := bstep (se 1 (by rfl) ⟨3941783, by rfl⟩ : syracuseStep 5255711 = 7883567) B7883567
theorem B3159827 : Blo 726324 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B3684689 : Blo 726324 3684689 := bstep (se 2 (by rfl) ⟨1381758, by rfl⟩ : syracuseStep 3684689 = 2763517) B2763517
theorem B1658159 : Blo 726324 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B163959527 : Blo 726324 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B28730705 : Blo 726324 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B163966157 : Blo 726324 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B2453651 : Blo 726324 2453651 := bstep (se 1 (by rfl) ⟨1840238, by rfl⟩ : syracuseStep 2453651 = 3680477) B3680477
theorem B1635947 : Blo 726324 1635947 := bstep (se 1 (by rfl) ⟨1226960, by rfl⟩ : syracuseStep 1635947 = 2453921) B2453921
theorem B817915 : Blo 726324 817915 := bstep (se 1 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 817915 = 1226873) B1226873
theorem B1638143 : Blo 726324 1638143 := bstep (se 1 (by rfl) ⟨1228607, by rfl⟩ : syracuseStep 1638143 = 2457215) B2457215
theorem B1638395 : Blo 726324 1638395 := bstep (se 1 (by rfl) ⟨1228796, by rfl⟩ : syracuseStep 1638395 = 2457593) B2457593
theorem B5242907 : Blo 726324 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B12584591 : Blo 726324 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B6295279 : Blo 726324 6295279 := bstep (se 1 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 6295279 = 9442919) B9442919
theorem B2463209 : Blo 726324 2463209 := bstep (se 2 (by rfl) ⟨923703, by rfl⟩ : syracuseStep 2463209 = 1847407) B1847407
theorem B729215 : Blo 726324 729215 := bstep (se 1 (by rfl) ⟨546911, by rfl⟩ : syracuseStep 729215 = 1093823) B1093823
theorem B1090553 : Blo 726324 1090553 := bstep (se 2 (by rfl) ⟨408957, by rfl⟩ : syracuseStep 1090553 = 817915) B817915
theorem B1090631 : Blo 726324 1090631 := bstep (se 1 (by rfl) ⟨817973, by rfl⟩ : syracuseStep 1090631 = 1635947) B1635947
theorem B2106551 : Blo 726324 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B1092095 : Blo 726324 1092095 := bstep (se 1 (by rfl) ⟨819071, by rfl⟩ : syracuseStep 1092095 = 1638143) B1638143
theorem B1092263 : Blo 726324 1092263 := bstep (se 1 (by rfl) ⟨819197, by rfl⟩ : syracuseStep 1092263 = 1638395) B1638395
theorem B84978665 : Blo 726324 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B1092713 : Blo 726324 1092713 := bstep (se 2 (by rfl) ⟨409767, by rfl⟩ : syracuseStep 1092713 = 819535) B819535
theorem B25210871 : Blo 726324 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1093883 : Blo 726324 1093883 := bstep (se 1 (by rfl) ⟨820412, by rfl⟩ : syracuseStep 1093883 = 1640825) B1640825
theorem B1094009 : Blo 726324 1094009 := bstep (se 2 (by rfl) ⟨410253, by rfl⟩ : syracuseStep 1094009 = 820507) B820507
theorem B1095071 : Blo 726324 1095071 := bstep (se 1 (by rfl) ⟨821303, by rfl⟩ : syracuseStep 1095071 = 1642607) B1642607
theorem B1226731 : Blo 726324 1226731 := bstep (se 1 (by rfl) ⟨920048, by rfl⟩ : syracuseStep 1226731 = 1840097) B1840097
theorem B8304767 : Blo 726324 8304767 := bstep (se 1 (by rfl) ⟨6228575, by rfl⟩ : syracuseStep 8304767 = 12457151) B12457151
theorem B306460853 : Blo 726324 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B1163803 : Blo 726324 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B1105439 : Blo 726324 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B109306351 : Blo 726324 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B109310771 : Blo 726324 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B1635767 : Blo 726324 1635767 := bstep (se 1 (by rfl) ⟨1226825, by rfl⟩ : syracuseStep 1635767 = 2453651) B2453651
theorem B3503807 : Blo 726324 3503807 := bstep (se 1 (by rfl) ⟨2627855, by rfl⟩ : syracuseStep 3503807 = 5255711) B5255711
theorem B2456459 : Blo 726324 2456459 := bstep (se 1 (by rfl) ⟨1842344, by rfl⟩ : syracuseStep 2456459 = 3684689) B3684689
theorem B8389727 : Blo 726324 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B1642139 : Blo 726324 1642139 := bstep (se 1 (by rfl) ⟨1231604, by rfl⟩ : syracuseStep 1642139 = 2463209) B2463209
theorem B8393705 : Blo 726324 8393705 := bstep (se 2 (by rfl) ⟨3147639, by rfl⟩ : syracuseStep 8393705 = 6295279) B6295279
theorem B727035 : Blo 726324 727035 := bstep (se 1 (by rfl) ⟨545276, by rfl⟩ : syracuseStep 727035 = 1090553) B1090553
theorem B727087 : Blo 726324 727087 := bstep (se 1 (by rfl) ⟨545315, by rfl⟩ : syracuseStep 727087 = 1090631) B1090631
theorem B728063 : Blo 726324 728063 := bstep (se 1 (by rfl) ⟨546047, by rfl⟩ : syracuseStep 728063 = 1092095) B1092095
theorem B728175 : Blo 726324 728175 := bstep (se 1 (by rfl) ⟨546131, by rfl⟩ : syracuseStep 728175 = 1092263) B1092263
theorem B728475 : Blo 726324 728475 := bstep (se 1 (by rfl) ⟨546356, by rfl⟩ : syracuseStep 728475 = 1092713) B1092713
theorem B729255 : Blo 726324 729255 := bstep (se 1 (by rfl) ⟨546941, by rfl⟩ : syracuseStep 729255 = 1093883) B1093883
theorem B729339 : Blo 726324 729339 := bstep (se 1 (by rfl) ⟨547004, by rfl⟩ : syracuseStep 729339 = 1094009) B1094009
theorem B730047 : Blo 726324 730047 := bstep (se 1 (by rfl) ⟨547535, by rfl⟩ : syracuseStep 730047 = 1095071) B1095071
theorem B1090511 : Blo 726324 1090511 := bstep (se 1 (by rfl) ⟨817883, by rfl⟩ : syracuseStep 1090511 = 1635767) B1635767
theorem B2335871 : Blo 726324 2335871 := bstep (se 1 (by rfl) ⟨1751903, by rfl⟩ : syracuseStep 2335871 = 3503807) B3503807
theorem B1551737 : Blo 726324 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B5617469 : Blo 726324 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B3495271 : Blo 726324 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B145741801 : Blo 726324 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B56652443 : Blo 726324 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B1635641 : Blo 726324 1635641 := bstep (se 2 (by rfl) ⟨613365, by rfl⟩ : syracuseStep 1635641 = 1226731) B1226731
theorem B16807247 : Blo 726324 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B72873847 : Blo 726324 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B2947837 : Blo 726324 2947837 := bstep (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) B1105439
theorem B5536511 : Blo 726324 5536511 := bstep (se 1 (by rfl) ⟨4152383, by rfl⟩ : syracuseStep 5536511 = 8304767) B8304767
theorem B204307235 : Blo 726324 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B1637639 : Blo 726324 1637639 := bstep (se 1 (by rfl) ⟨1228229, by rfl⟩ : syracuseStep 1637639 = 2456459) B2456459
theorem B14979917 : Blo 726324 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B727007 : Blo 726324 727007 := bstep (se 1 (by rfl) ⟨545255, by rfl⟩ : syracuseStep 727007 = 1090511) B1090511
theorem B4660361 : Blo 726324 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B194322401 : Blo 726324 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B1090427 : Blo 726324 1090427 := bstep (se 1 (by rfl) ⟨817820, by rfl⟩ : syracuseStep 1090427 = 1635641) B1635641
theorem B4137965 : Blo 726324 4137965 := bstep (se 3 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 4137965 = 1551737) B1551737
theorem B1091759 : Blo 726324 1091759 := bstep (se 1 (by rfl) ⟨818819, by rfl⟩ : syracuseStep 1091759 = 1637639) B1637639
theorem B1094759 : Blo 726324 1094759 := bstep (se 1 (by rfl) ⟨821069, by rfl⟩ : syracuseStep 1094759 = 1642139) B1642139
theorem B1557247 : Blo 726324 1557247 := bstep (se 1 (by rfl) ⟨1167935, by rfl⟩ : syracuseStep 1557247 = 2335871) B2335871
theorem B37768295 : Blo 726324 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B3691007 : Blo 726324 3691007 := bstep (se 1 (by rfl) ⟨2768255, by rfl⟩ : syracuseStep 3691007 = 5536511) B5536511
theorem B136204823 : Blo 726324 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B5593151 : Blo 726324 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B5595803 : Blo 726324 5595803 := bstep (se 1 (by rfl) ⟨4196852, by rfl⟩ : syracuseStep 5595803 = 8393705) B8393705
theorem B11204831 : Blo 726324 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B3930449 : Blo 726324 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B388660517 : Blo 726324 388660517 := bstep (se 4 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 388660517 = 72873847) B72873847
theorem B39946445 : Blo 726324 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B2460671 : Blo 726324 2460671 := bstep (se 1 (by rfl) ⟨1845503, by rfl⟩ : syracuseStep 2460671 = 3691007) B3691007
theorem B90803215 : Blo 726324 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B726951 : Blo 726324 726951 := bstep (se 1 (by rfl) ⟨545213, by rfl⟩ : syracuseStep 726951 = 1090427) B1090427
theorem B2758643 : Blo 726324 2758643 := bstep (se 1 (by rfl) ⟨2068982, by rfl⟩ : syracuseStep 2758643 = 4137965) B4137965
theorem B727839 : Blo 726324 727839 := bstep (se 1 (by rfl) ⟨545879, by rfl⟩ : syracuseStep 727839 = 1091759) B1091759
theorem B729839 : Blo 726324 729839 := bstep (se 1 (by rfl) ⟨547379, by rfl⟩ : syracuseStep 729839 = 1094759) B1094759
theorem B259107011 : Blo 726324 259107011 := bstep (se 1 (by rfl) ⟨194330258, by rfl⟩ : syracuseStep 259107011 = 388660517) B388660517
theorem B2076329 : Blo 726324 2076329 := bstep (se 2 (by rfl) ⟨778623, by rfl⟩ : syracuseStep 2076329 = 1557247) B1557247
theorem B25178863 : Blo 726324 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B41924789 : Blo 726324 41924789 := bstep (se 5 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 41924789 = 3930449) B3930449
theorem B129548267 : Blo 726324 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B3728767 : Blo 726324 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B3106907 : Blo 726324 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B3730535 : Blo 726324 3730535 := bstep (se 1 (by rfl) ⟨2797901, by rfl⟩ : syracuseStep 3730535 = 5595803) B5595803
theorem B7469887 : Blo 726324 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1640447 : Blo 726324 1640447 := bstep (se 1 (by rfl) ⟨1230335, by rfl⟩ : syracuseStep 1640447 = 2460671) B2460671
theorem B1839095 : Blo 726324 1839095 := bstep (se 1 (by rfl) ⟨1379321, by rfl⟩ : syracuseStep 1839095 = 2758643) B2758643
theorem B2071271 : Blo 726324 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B1384219 : Blo 726324 1384219 := bstep (se 1 (by rfl) ⟨1038164, by rfl⟩ : syracuseStep 1384219 = 2076329) B2076329
theorem B33571817 : Blo 726324 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B172738007 : Blo 726324 172738007 := bstep (se 1 (by rfl) ⟨129553505, by rfl⟩ : syracuseStep 172738007 = 259107011) B259107011
theorem B86365511 : Blo 726324 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B26630963 : Blo 726324 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B4971689 : Blo 726324 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B121070953 : Blo 726324 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B2487023 : Blo 726324 2487023 := bstep (se 1 (by rfl) ⟨1865267, by rfl⟩ : syracuseStep 2487023 = 3730535) B3730535
theorem B9959849 : Blo 726324 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B27949859 : Blo 726324 27949859 := bstep (se 1 (by rfl) ⟨20962394, by rfl⟩ : syracuseStep 27949859 = 41924789) B41924789
theorem B22381211 : Blo 726324 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B57577007 : Blo 726324 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B3314459 : Blo 726324 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B1845625 : Blo 726324 1845625 := bstep (se 2 (by rfl) ⟨692109, by rfl⟩ : syracuseStep 1845625 = 1384219) B1384219
theorem B115158671 : Blo 726324 115158671 := bstep (se 1 (by rfl) ⟨86369003, by rfl⟩ : syracuseStep 115158671 = 172738007) B172738007
theorem B1093631 : Blo 726324 1093631 := bstep (se 1 (by rfl) ⟨820223, by rfl⟩ : syracuseStep 1093631 = 1640447) B1640447
theorem B161427937 : Blo 726324 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B1226063 : Blo 726324 1226063 := bstep (se 1 (by rfl) ⟨919547, by rfl⟩ : syracuseStep 1226063 = 1839095) B1839095
theorem B5523389 : Blo 726324 5523389 := bstep (se 3 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 5523389 = 2071271) B2071271
theorem B1658015 : Blo 726324 1658015 := bstep (se 1 (by rfl) ⟨1243511, by rfl⟩ : syracuseStep 1658015 = 2487023) B2487023
theorem B6639899 : Blo 726324 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B18633239 : Blo 726324 18633239 := bstep (se 1 (by rfl) ⟨13974929, by rfl⟩ : syracuseStep 18633239 = 27949859) B27949859
theorem B17753975 : Blo 726324 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B12422159 : Blo 726324 12422159 := bstep (se 1 (by rfl) ⟨9316619, by rfl⟩ : syracuseStep 12422159 = 18633239) B18633239
theorem B2460833 : Blo 726324 2460833 := bstep (se 2 (by rfl) ⟨922812, by rfl⟩ : syracuseStep 2460833 = 1845625) B1845625
theorem B11835983 : Blo 726324 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B729087 : Blo 726324 729087 := bstep (se 1 (by rfl) ⟨546815, by rfl⟩ : syracuseStep 729087 = 1093631) B1093631
theorem B14920807 : Blo 726324 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B17706397 : Blo 726324 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B3682259 : Blo 726324 3682259 := bstep (se 1 (by rfl) ⟨2761694, by rfl⟩ : syracuseStep 3682259 = 5523389) B5523389
theorem B38384671 : Blo 726324 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B215237249 : Blo 726324 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B8838557 : Blo 726324 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B1105343 : Blo 726324 1105343 := bstep (se 1 (by rfl) ⟨829007, by rfl⟩ : syracuseStep 1105343 = 1658015) B1658015
theorem B76772447 : Blo 726324 76772447 := bstep (se 1 (by rfl) ⟨57579335, by rfl⟩ : syracuseStep 76772447 = 115158671) B115158671
theorem B817375 : Blo 726324 817375 := bstep (se 1 (by rfl) ⟨613031, by rfl⟩ : syracuseStep 817375 = 1226063) B1226063
theorem B143491499 : Blo 726324 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B1640555 : Blo 726324 1640555 := bstep (se 1 (by rfl) ⟨1230416, by rfl⟩ : syracuseStep 1640555 = 2460833) B2460833
theorem B19894409 : Blo 726324 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B1089833 : Blo 726324 1089833 := bstep (se 2 (by rfl) ⟨408687, by rfl⟩ : syracuseStep 1089833 = 817375) B817375
theorem B23608529 : Blo 726324 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B736895 : Blo 726324 736895 := bstep (se 1 (by rfl) ⟨552671, by rfl⟩ : syracuseStep 736895 = 1105343) B1105343
theorem B8281439 : Blo 726324 8281439 := bstep (se 1 (by rfl) ⟨6211079, by rfl⟩ : syracuseStep 8281439 = 12422159) B12422159
theorem B7890655 : Blo 726324 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B5892371 : Blo 726324 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B51179561 : Blo 726324 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B2454839 : Blo 726324 2454839 := bstep (se 1 (by rfl) ⟨1841129, by rfl⟩ : syracuseStep 2454839 = 3682259) B3682259
theorem B51181631 : Blo 726324 51181631 := bstep (se 1 (by rfl) ⟨38386223, by rfl⟩ : syracuseStep 51181631 = 76772447) B76772447
theorem B10520873 : Blo 726324 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B726555 : Blo 726324 726555 := bstep (se 1 (by rfl) ⟨544916, by rfl⟩ : syracuseStep 726555 = 1089833) B1089833
theorem B34119707 : Blo 726324 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B34121087 : Blo 726324 34121087 := bstep (se 1 (by rfl) ⟨25590815, by rfl⟩ : syracuseStep 34121087 = 51181631) B51181631
theorem B15739019 : Blo 726324 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B95660999 : Blo 726324 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B1093703 : Blo 726324 1093703 := bstep (se 1 (by rfl) ⟨820277, by rfl⟩ : syracuseStep 1093703 = 1640555) B1640555
theorem B5520959 : Blo 726324 5520959 := bstep (se 1 (by rfl) ⟨4140719, by rfl⟩ : syracuseStep 5520959 = 8281439) B8281439
theorem B13262939 : Blo 726324 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B3928247 : Blo 726324 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B1636559 : Blo 726324 1636559 := bstep (se 1 (by rfl) ⟨1227419, by rfl⟩ : syracuseStep 1636559 = 2454839) B2454839
theorem B1965053 : Blo 726324 1965053 := bstep (se 3 (by rfl) ⟨368447, by rfl⟩ : syracuseStep 1965053 = 736895) B736895
theorem B7013915 : Blo 726324 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B22747391 : Blo 726324 22747391 := bstep (se 1 (by rfl) ⟨17060543, by rfl⟩ : syracuseStep 22747391 = 34121087) B34121087
theorem B10492679 : Blo 726324 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B63773999 : Blo 726324 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B729135 : Blo 726324 729135 := bstep (se 1 (by rfl) ⟨546851, by rfl⟩ : syracuseStep 729135 = 1093703) B1093703
theorem B1091039 : Blo 726324 1091039 := bstep (se 1 (by rfl) ⟨818279, by rfl⟩ : syracuseStep 1091039 = 1636559) B1636559
theorem B3680639 : Blo 726324 3680639 := bstep (se 1 (by rfl) ⟨2760479, by rfl⟩ : syracuseStep 3680639 = 5520959) B5520959
theorem B90985885 : Blo 726324 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B8841959 : Blo 726324 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B2618831 : Blo 726324 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B1310035 : Blo 726324 1310035 := bstep (se 1 (by rfl) ⟨982526, by rfl⟩ : syracuseStep 1310035 = 1965053) B1965053
theorem B727359 : Blo 726324 727359 := bstep (se 1 (by rfl) ⟨545519, by rfl⟩ : syracuseStep 727359 = 1091039) B1091039
theorem B1745887 : Blo 726324 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B1746713 : Blo 726324 1746713 := bstep (se 2 (by rfl) ⟨655017, by rfl⟩ : syracuseStep 1746713 = 1310035) B1310035
theorem B6995119 : Blo 726324 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B42515999 : Blo 726324 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B4675943 : Blo 726324 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B15164927 : Blo 726324 15164927 := bstep (se 1 (by rfl) ⟨11373695, by rfl⟩ : syracuseStep 15164927 = 22747391) B22747391
theorem B2453759 : Blo 726324 2453759 := bstep (se 1 (by rfl) ⟨1840319, by rfl⟩ : syracuseStep 2453759 = 3680639) B3680639
theorem B5894639 : Blo 726324 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B485258053 : Blo 726324 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B2327849 : Blo 726324 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B3117295 : Blo 726324 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B647010737 : Blo 726324 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B10109951 : Blo 726324 10109951 := bstep (se 1 (by rfl) ⟨7582463, by rfl⟩ : syracuseStep 10109951 = 15164927) B15164927
theorem B1164475 : Blo 726324 1164475 := bstep (se 1 (by rfl) ⟨873356, by rfl⟩ : syracuseStep 1164475 = 1746713) B1746713
theorem B9326825 : Blo 726324 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B1635839 : Blo 726324 1635839 := bstep (se 1 (by rfl) ⟨1226879, by rfl⟩ : syracuseStep 1635839 = 2453759) B2453759
theorem B3929759 : Blo 726324 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B28343999 : Blo 726324 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B1090559 : Blo 726324 1090559 := bstep (se 1 (by rfl) ⟨817919, by rfl⟩ : syracuseStep 1090559 = 1635839) B1635839
theorem B1551899 : Blo 726324 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B431340491 : Blo 726324 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B6210533 : Blo 726324 6210533 := bstep (se 4 (by rfl) ⟨582237, by rfl⟩ : syracuseStep 6210533 = 1164475) B1164475
theorem B18895999 : Blo 726324 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B6739967 : Blo 726324 6739967 := bstep (se 1 (by rfl) ⟨5054975, by rfl⟩ : syracuseStep 6739967 = 10109951) B10109951
theorem B6217883 : Blo 726324 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B4156393 : Blo 726324 4156393 := bstep (se 2 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 4156393 = 3117295) B3117295
theorem B2619839 : Blo 726324 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B5541857 : Blo 726324 5541857 := bstep (se 2 (by rfl) ⟨2078196, by rfl⟩ : syracuseStep 5541857 = 4156393) B4156393
theorem B727039 : Blo 726324 727039 := bstep (se 1 (by rfl) ⟨545279, by rfl⟩ : syracuseStep 727039 = 1090559) B1090559
theorem B4138397 : Blo 726324 4138397 := bstep (se 3 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 4138397 = 1551899) B1551899
theorem B1746559 : Blo 726324 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B4140355 : Blo 726324 4140355 := bstep (se 1 (by rfl) ⟨3105266, by rfl⟩ : syracuseStep 4140355 = 6210533) B6210533
theorem B17973245 : Blo 726324 17973245 := bstep (se 3 (by rfl) ⟨3369983, by rfl⟩ : syracuseStep 17973245 = 6739967) B6739967
theorem B4145255 : Blo 726324 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B287560327 : Blo 726324 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B25194665 : Blo 726324 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B2328745 : Blo 726324 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B2758931 : Blo 726324 2758931 := bstep (se 1 (by rfl) ⟨2069198, by rfl⟩ : syracuseStep 2758931 = 4138397) B4138397
theorem B2763503 : Blo 726324 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B5520473 : Blo 726324 5520473 := bstep (se 2 (by rfl) ⟨2070177, by rfl⟩ : syracuseStep 5520473 = 4140355) B4140355
theorem B16796443 : Blo 726324 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B11982163 : Blo 726324 11982163 := bstep (se 1 (by rfl) ⟨8986622, by rfl⟩ : syracuseStep 11982163 = 17973245) B17973245
theorem B3694571 : Blo 726324 3694571 := bstep (se 1 (by rfl) ⟨2770928, by rfl⟩ : syracuseStep 3694571 = 5541857) B5541857
theorem B383413769 : Blo 726324 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B1839287 : Blo 726324 1839287 := bstep (se 1 (by rfl) ⟨1379465, by rfl⟩ : syracuseStep 1839287 = 2758931) B2758931
theorem B2463047 : Blo 726324 2463047 := bstep (se 1 (by rfl) ⟨1847285, by rfl⟩ : syracuseStep 2463047 = 3694571) B3694571
theorem B1842335 : Blo 726324 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B3680315 : Blo 726324 3680315 := bstep (se 1 (by rfl) ⟨2760236, by rfl⟩ : syracuseStep 3680315 = 5520473) B5520473
theorem B22395257 : Blo 726324 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B15976217 : Blo 726324 15976217 := bstep (se 2 (by rfl) ⟨5991081, by rfl⟩ : syracuseStep 15976217 = 11982163) B11982163
theorem B255609179 : Blo 726324 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B3104993 : Blo 726324 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B10650811 : Blo 726324 10650811 := bstep (se 1 (by rfl) ⟨7988108, by rfl⟩ : syracuseStep 10650811 = 15976217) B15976217
theorem B1642031 : Blo 726324 1642031 := bstep (se 1 (by rfl) ⟨1231523, by rfl⟩ : syracuseStep 1642031 = 2463047) B2463047
theorem B170406119 : Blo 726324 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B1226191 : Blo 726324 1226191 := bstep (se 1 (by rfl) ⟨919643, by rfl⟩ : syracuseStep 1226191 = 1839287) B1839287
theorem B1228223 : Blo 726324 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B14930171 : Blo 726324 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B8279981 : Blo 726324 8279981 := bstep (se 3 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 8279981 = 3104993) B3104993
theorem B2453543 : Blo 726324 2453543 := bstep (se 1 (by rfl) ⟨1840157, by rfl⟩ : syracuseStep 2453543 = 3680315) B3680315
theorem B14201081 : Blo 726324 14201081 := bstep (se 2 (by rfl) ⟨5325405, by rfl⟩ : syracuseStep 14201081 = 10650811) B10650811
theorem B1094687 : Blo 726324 1094687 := bstep (se 1 (by rfl) ⟨821015, by rfl⟩ : syracuseStep 1094687 = 1642031) B1642031
theorem B5519987 : Blo 726324 5519987 := bstep (se 1 (by rfl) ⟨4139990, by rfl⟩ : syracuseStep 5519987 = 8279981) B8279981
theorem B454416317 : Blo 726324 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B9953447 : Blo 726324 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B1634921 : Blo 726324 1634921 := bstep (se 2 (by rfl) ⟨613095, by rfl⟩ : syracuseStep 1634921 = 1226191) B1226191
theorem B1635695 : Blo 726324 1635695 := bstep (se 1 (by rfl) ⟨1226771, by rfl⟩ : syracuseStep 1635695 = 2453543) B2453543
theorem B818815 : Blo 726324 818815 := bstep (se 1 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 818815 = 1228223) B1228223
theorem B26542525 : Blo 726324 26542525 := bstep (se 3 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 26542525 = 9953447) B9953447
theorem B302944211 : Blo 726324 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B1089947 : Blo 726324 1089947 := bstep (se 1 (by rfl) ⟨817460, by rfl⟩ : syracuseStep 1089947 = 1634921) B1634921
theorem B729791 : Blo 726324 729791 := bstep (se 1 (by rfl) ⟨547343, by rfl⟩ : syracuseStep 729791 = 1094687) B1094687
theorem B1090463 : Blo 726324 1090463 := bstep (se 1 (by rfl) ⟨817847, by rfl⟩ : syracuseStep 1090463 = 1635695) B1635695
theorem B3679991 : Blo 726324 3679991 := bstep (se 1 (by rfl) ⟨2759993, by rfl⟩ : syracuseStep 3679991 = 5519987) B5519987
theorem B1091753 : Blo 726324 1091753 := bstep (se 2 (by rfl) ⟨409407, by rfl⟩ : syracuseStep 1091753 = 818815) B818815
theorem B9467387 : Blo 726324 9467387 := bstep (se 1 (by rfl) ⟨7100540, by rfl⟩ : syracuseStep 9467387 = 14201081) B14201081
theorem B35390033 : Blo 726324 35390033 := bstep (se 2 (by rfl) ⟨13271262, by rfl⟩ : syracuseStep 35390033 = 26542525) B26542525
theorem B726631 : Blo 726324 726631 := bstep (se 1 (by rfl) ⟨544973, by rfl⟩ : syracuseStep 726631 = 1089947) B1089947
theorem B726975 : Blo 726324 726975 := bstep (se 1 (by rfl) ⟨545231, by rfl⟩ : syracuseStep 726975 = 1090463) B1090463
theorem B727835 : Blo 726324 727835 := bstep (se 1 (by rfl) ⟨545876, by rfl⟩ : syracuseStep 727835 = 1091753) B1091753
theorem B201962807 : Blo 726324 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B6311591 : Blo 726324 6311591 := bstep (se 1 (by rfl) ⟨4733693, by rfl⟩ : syracuseStep 6311591 = 9467387) B9467387
theorem B2453327 : Blo 726324 2453327 := bstep (se 1 (by rfl) ⟨1839995, by rfl⟩ : syracuseStep 2453327 = 3679991) B3679991
theorem B23593355 : Blo 726324 23593355 := bstep (se 1 (by rfl) ⟨17695016, by rfl⟩ : syracuseStep 23593355 = 35390033) B35390033
theorem B4207727 : Blo 726324 4207727 := bstep (se 1 (by rfl) ⟨3155795, by rfl⟩ : syracuseStep 4207727 = 6311591) B6311591
theorem B1635551 : Blo 726324 1635551 := bstep (se 1 (by rfl) ⟨1226663, by rfl⟩ : syracuseStep 1635551 = 2453327) B2453327
theorem B134641871 : Blo 726324 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B15728903 : Blo 726324 15728903 := bstep (se 1 (by rfl) ⟨11796677, by rfl⟩ : syracuseStep 15728903 = 23593355) B23593355
theorem B1090367 : Blo 726324 1090367 := bstep (se 1 (by rfl) ⟨817775, by rfl⟩ : syracuseStep 1090367 = 1635551) B1635551
theorem B89761247 : Blo 726324 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B2805151 : Blo 726324 2805151 := bstep (se 1 (by rfl) ⟨2103863, by rfl⟩ : syracuseStep 2805151 = 4207727) B4207727
theorem B10485935 : Blo 726324 10485935 := bstep (se 1 (by rfl) ⟨7864451, by rfl⟩ : syracuseStep 10485935 = 15728903) B15728903
theorem B3740201 : Blo 726324 3740201 := bstep (se 2 (by rfl) ⟨1402575, by rfl⟩ : syracuseStep 3740201 = 2805151) B2805151
theorem B726911 : Blo 726324 726911 := bstep (se 1 (by rfl) ⟨545183, by rfl⟩ : syracuseStep 726911 = 1090367) B1090367
theorem B59840831 : Blo 726324 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B2493467 : Blo 726324 2493467 := bstep (se 1 (by rfl) ⟨1870100, by rfl⟩ : syracuseStep 2493467 = 3740201) B3740201
theorem B6990623 : Blo 726324 6990623 := bstep (se 1 (by rfl) ⟨5242967, by rfl⟩ : syracuseStep 6990623 = 10485935) B10485935
theorem B39893887 : Blo 726324 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B4660415 : Blo 726324 4660415 := bstep (se 1 (by rfl) ⟨3495311, by rfl⟩ : syracuseStep 4660415 = 6990623) B6990623
theorem B53191849 : Blo 726324 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B1662311 : Blo 726324 1662311 := bstep (se 1 (by rfl) ⟨1246733, by rfl⟩ : syracuseStep 1662311 = 2493467) B2493467
theorem B70922465 : Blo 726324 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B3106943 : Blo 726324 3106943 := bstep (se 1 (by rfl) ⟨2330207, by rfl⟩ : syracuseStep 3106943 = 4660415) B4660415
theorem B1108207 : Blo 726324 1108207 := bstep (se 1 (by rfl) ⟨831155, by rfl⟩ : syracuseStep 1108207 = 1662311) B1662311
theorem B1477609 : Blo 726324 1477609 := bstep (se 2 (by rfl) ⟨554103, by rfl⟩ : syracuseStep 1477609 = 1108207) B1108207
theorem B2071295 : Blo 726324 2071295 := bstep (se 1 (by rfl) ⟨1553471, by rfl⟩ : syracuseStep 2071295 = 3106943) B3106943
theorem B47281643 : Blo 726324 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B1380863 : Blo 726324 1380863 := bstep (se 1 (by rfl) ⟨1035647, by rfl⟩ : syracuseStep 1380863 = 2071295) B2071295
theorem B7880581 : Blo 726324 7880581 := bstep (se 4 (by rfl) ⟨738804, by rfl⟩ : syracuseStep 7880581 = 1477609) B1477609
theorem B31521095 : Blo 726324 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B920575 : Blo 726324 920575 := bstep (se 1 (by rfl) ⟨690431, by rfl⟩ : syracuseStep 920575 = 1380863) B1380863
theorem B21014063 : Blo 726324 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B10507441 : Blo 726324 10507441 := bstep (se 2 (by rfl) ⟨3940290, by rfl⟩ : syracuseStep 10507441 = 7880581) B7880581
theorem B1227433 : Blo 726324 1227433 := bstep (se 2 (by rfl) ⟨460287, by rfl⟩ : syracuseStep 1227433 = 920575) B920575
theorem B14009375 : Blo 726324 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B14009921 : Blo 726324 14009921 := bstep (se 2 (by rfl) ⟨5253720, by rfl⟩ : syracuseStep 14009921 = 10507441) B10507441
theorem B9339583 : Blo 726324 9339583 := bstep (se 1 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 9339583 = 14009375) B14009375
theorem B9339947 : Blo 726324 9339947 := bstep (se 1 (by rfl) ⟨7004960, by rfl⟩ : syracuseStep 9339947 = 14009921) B14009921
theorem B1636577 : Blo 726324 1636577 := bstep (se 2 (by rfl) ⟨613716, by rfl⟩ : syracuseStep 1636577 = 1227433) B1227433
theorem B6226631 : Blo 726324 6226631 := bstep (se 1 (by rfl) ⟨4669973, by rfl⟩ : syracuseStep 6226631 = 9339947) B9339947
theorem B12452777 : Blo 726324 12452777 := bstep (se 2 (by rfl) ⟨4669791, by rfl⟩ : syracuseStep 12452777 = 9339583) B9339583
theorem B1091051 : Blo 726324 1091051 := bstep (se 1 (by rfl) ⟨818288, by rfl⟩ : syracuseStep 1091051 = 1636577) B1636577
theorem B727367 : Blo 726324 727367 := bstep (se 1 (by rfl) ⟨545525, by rfl⟩ : syracuseStep 727367 = 1091051) B1091051
theorem B8301851 : Blo 726324 8301851 := bstep (se 1 (by rfl) ⟨6226388, by rfl⟩ : syracuseStep 8301851 = 12452777) B12452777
theorem B4151087 : Blo 726324 4151087 := bstep (se 1 (by rfl) ⟨3113315, by rfl⟩ : syracuseStep 4151087 = 6226631) B6226631
theorem B2767391 : Blo 726324 2767391 := bstep (se 1 (by rfl) ⟨2075543, by rfl⟩ : syracuseStep 2767391 = 4151087) B4151087
theorem B5534567 : Blo 726324 5534567 := bstep (se 1 (by rfl) ⟨4150925, by rfl⟩ : syracuseStep 5534567 = 8301851) B8301851
theorem B1844927 : Blo 726324 1844927 := bstep (se 1 (by rfl) ⟨1383695, by rfl⟩ : syracuseStep 1844927 = 2767391) B2767391
theorem B3689711 : Blo 726324 3689711 := bstep (se 1 (by rfl) ⟨2767283, by rfl⟩ : syracuseStep 3689711 = 5534567) B5534567
theorem B2459807 : Blo 726324 2459807 := bstep (se 1 (by rfl) ⟨1844855, by rfl⟩ : syracuseStep 2459807 = 3689711) B3689711
theorem B1229951 : Blo 726324 1229951 := bstep (se 1 (by rfl) ⟨922463, by rfl⟩ : syracuseStep 1229951 = 1844927) B1844927
theorem B819967 : Blo 726324 819967 := bstep (se 1 (by rfl) ⟨614975, by rfl⟩ : syracuseStep 819967 = 1229951) B1229951
theorem B1639871 : Blo 726324 1639871 := bstep (se 1 (by rfl) ⟨1229903, by rfl⟩ : syracuseStep 1639871 = 2459807) B2459807
theorem B1093247 : Blo 726324 1093247 := bstep (se 1 (by rfl) ⟨819935, by rfl⟩ : syracuseStep 1093247 = 1639871) B1639871
theorem B1093289 : Blo 726324 1093289 := bstep (se 2 (by rfl) ⟨409983, by rfl⟩ : syracuseStep 1093289 = 819967) B819967
theorem B728831 : Blo 726324 728831 := bstep (se 1 (by rfl) ⟨546623, by rfl⟩ : syracuseStep 728831 = 1093247) B1093247
theorem B728859 : Blo 726324 728859 := bstep (se 1 (by rfl) ⟨546644, by rfl⟩ : syracuseStep 728859 = 1093289) B1093289

theorem C0 (j : ℕ) (h1 : 181581 ≤ j) (h2 : j ≤ 182280) : Blo 726324 (4 * j + 3) := by
  interval_cases j
  · exact B726327
  · exact B726331
  · exact B726335
  · exact B726339
  · exact B726343
  · exact B726347
  · exact B726351
  · exact B726355
  · exact B726359
  · exact B726363
  · exact B726367
  · exact B726371
  · exact B726375
  · exact B726379
  · exact B726383
  · exact B726387
  · exact B726391
  · exact B726395
  · exact B726399
  · exact B726403
  · exact B726407
  · exact B726411
  · exact B726415
  · exact B726419
  · exact B726423
  · exact B726427
  · exact B726431
  · exact B726435
  · exact B726439
  · exact B726443
  · exact B726447
  · exact B726451
  · exact B726455
  · exact B726459
  · exact B726463
  · exact B726467
  · exact B726471
  · exact B726475
  · exact B726479
  · exact B726483
  · exact B726487
  · exact B726491
  · exact B726495
  · exact B726499
  · exact B726503
  · exact B726507
  · exact B726511
  · exact B726515
  · exact B726519
  · exact B726523
  · exact B726527
  · exact B726531
  · exact B726535
  · exact B726539
  · exact B726543
  · exact B726547
  · exact B726551
  · exact B726555
  · exact B726559
  · exact B726563
  · exact B726567
  · exact B726571
  · exact B726575
  · exact B726579
  · exact B726583
  · exact B726587
  · exact B726591
  · exact B726595
  · exact B726599
  · exact B726603
  · exact B726607
  · exact B726611
  · exact B726615
  · exact B726619
  · exact B726623
  · exact B726627
  · exact B726631
  · exact B726635
  · exact B726639
  · exact B726643
  · exact B726647
  · exact B726651
  · exact B726655
  · exact B726659
  · exact B726663
  · exact B726667
  · exact B726671
  · exact B726675
  · exact B726679
  · exact B726683
  · exact B726687
  · exact B726691
  · exact B726695
  · exact B726699
  · exact B726703
  · exact B726707
  · exact B726711
  · exact B726715
  · exact B726719
  · exact B726723
  · exact B726727
  · exact B726731
  · exact B726735
  · exact B726739
  · exact B726743
  · exact B726747
  · exact B726751
  · exact B726755
  · exact B726759
  · exact B726763
  · exact B726767
  · exact B726771
  · exact B726775
  · exact B726779
  · exact B726783
  · exact B726787
  · exact B726791
  · exact B726795
  · exact B726799
  · exact B726803
  · exact B726807
  · exact B726811
  · exact B726815
  · exact B726819
  · exact B726823
  · exact B726827
  · exact B726831
  · exact B726835
  · exact B726839
  · exact B726843
  · exact B726847
  · exact B726851
  · exact B726855
  · exact B726859
  · exact B726863
  · exact B726867
  · exact B726871
  · exact B726875
  · exact B726879
  · exact B726883
  · exact B726887
  · exact B726891
  · exact B726895
  · exact B726899
  · exact B726903
  · exact B726907
  · exact B726911
  · exact B726915
  · exact B726919
  · exact B726923
  · exact B726927
  · exact B726931
  · exact B726935
  · exact B726939
  · exact B726943
  · exact B726947
  · exact B726951
  · exact B726955
  · exact B726959
  · exact B726963
  · exact B726967
  · exact B726971
  · exact B726975
  · exact B726979
  · exact B726983
  · exact B726987
  · exact B726991
  · exact B726995
  · exact B726999
  · exact B727003
  · exact B727007
  · exact B727011
  · exact B727015
  · exact B727019
  · exact B727023
  · exact B727027
  · exact B727031
  · exact B727035
  · exact B727039
  · exact B727043
  · exact B727047
  · exact B727051
  · exact B727055
  · exact B727059
  · exact B727063
  · exact B727067
  · exact B727071
  · exact B727075
  · exact B727079
  · exact B727083
  · exact B727087
  · exact B727091
  · exact B727095
  · exact B727099
  · exact B727103
  · exact B727107
  · exact B727111
  · exact B727115
  · exact B727119
  · exact B727123
  · exact B727127
  · exact B727131
  · exact B727135
  · exact B727139
  · exact B727143
  · exact B727147
  · exact B727151
  · exact B727155
  · exact B727159
  · exact B727163
  · exact B727167
  · exact B727171
  · exact B727175
  · exact B727179
  · exact B727183
  · exact B727187
  · exact B727191
  · exact B727195
  · exact B727199
  · exact B727203
  · exact B727207
  · exact B727211
  · exact B727215
  · exact B727219
  · exact B727223
  · exact B727227
  · exact B727231
  · exact B727235
  · exact B727239
  · exact B727243
  · exact B727247
  · exact B727251
  · exact B727255
  · exact B727259
  · exact B727263
  · exact B727267
  · exact B727271
  · exact B727275
  · exact B727279
  · exact B727283
  · exact B727287
  · exact B727291
  · exact B727295
  · exact B727299
  · exact B727303
  · exact B727307
  · exact B727311
  · exact B727315
  · exact B727319
  · exact B727323
  · exact B727327
  · exact B727331
  · exact B727335
  · exact B727339
  · exact B727343
  · exact B727347
  · exact B727351
  · exact B727355
  · exact B727359
  · exact B727363
  · exact B727367
  · exact B727371
  · exact B727375
  · exact B727379
  · exact B727383
  · exact B727387
  · exact B727391
  · exact B727395
  · exact B727399
  · exact B727403
  · exact B727407
  · exact B727411
  · exact B727415
  · exact B727419
  · exact B727423
  · exact B727427
  · exact B727431
  · exact B727435
  · exact B727439
  · exact B727443
  · exact B727447
  · exact B727451
  · exact B727455
  · exact B727459
  · exact B727463
  · exact B727467
  · exact B727471
  · exact B727475
  · exact B727479
  · exact B727483
  · exact B727487
  · exact B727491
  · exact B727495
  · exact B727499
  · exact B727503
  · exact B727507
  · exact B727511
  · exact B727515
  · exact B727519
  · exact B727523
  · exact B727527
  · exact B727531
  · exact B727535
  · exact B727539
  · exact B727543
  · exact B727547
  · exact B727551
  · exact B727555
  · exact B727559
  · exact B727563
  · exact B727567
  · exact B727571
  · exact B727575
  · exact B727579
  · exact B727583
  · exact B727587
  · exact B727591
  · exact B727595
  · exact B727599
  · exact B727603
  · exact B727607
  · exact B727611
  · exact B727615
  · exact B727619
  · exact B727623
  · exact B727627
  · exact B727631
  · exact B727635
  · exact B727639
  · exact B727643
  · exact B727647
  · exact B727651
  · exact B727655
  · exact B727659
  · exact B727663
  · exact B727667
  · exact B727671
  · exact B727675
  · exact B727679
  · exact B727683
  · exact B727687
  · exact B727691
  · exact B727695
  · exact B727699
  · exact B727703
  · exact B727707
  · exact B727711
  · exact B727715
  · exact B727719
  · exact B727723
  · exact B727727
  · exact B727731
  · exact B727735
  · exact B727739
  · exact B727743
  · exact B727747
  · exact B727751
  · exact B727755
  · exact B727759
  · exact B727763
  · exact B727767
  · exact B727771
  · exact B727775
  · exact B727779
  · exact B727783
  · exact B727787
  · exact B727791
  · exact B727795
  · exact B727799
  · exact B727803
  · exact B727807
  · exact B727811
  · exact B727815
  · exact B727819
  · exact B727823
  · exact B727827
  · exact B727831
  · exact B727835
  · exact B727839
  · exact B727843
  · exact B727847
  · exact B727851
  · exact B727855
  · exact B727859
  · exact B727863
  · exact B727867
  · exact B727871
  · exact B727875
  · exact B727879
  · exact B727883
  · exact B727887
  · exact B727891
  · exact B727895
  · exact B727899
  · exact B727903
  · exact B727907
  · exact B727911
  · exact B727915
  · exact B727919
  · exact B727923
  · exact B727927
  · exact B727931
  · exact B727935
  · exact B727939
  · exact B727943
  · exact B727947
  · exact B727951
  · exact B727955
  · exact B727959
  · exact B727963
  · exact B727967
  · exact B727971
  · exact B727975
  · exact B727979
  · exact B727983
  · exact B727987
  · exact B727991
  · exact B727995
  · exact B727999
  · exact B728003
  · exact B728007
  · exact B728011
  · exact B728015
  · exact B728019
  · exact B728023
  · exact B728027
  · exact B728031
  · exact B728035
  · exact B728039
  · exact B728043
  · exact B728047
  · exact B728051
  · exact B728055
  · exact B728059
  · exact B728063
  · exact B728067
  · exact B728071
  · exact B728075
  · exact B728079
  · exact B728083
  · exact B728087
  · exact B728091
  · exact B728095
  · exact B728099
  · exact B728103
  · exact B728107
  · exact B728111
  · exact B728115
  · exact B728119
  · exact B728123
  · exact B728127
  · exact B728131
  · exact B728135
  · exact B728139
  · exact B728143
  · exact B728147
  · exact B728151
  · exact B728155
  · exact B728159
  · exact B728163
  · exact B728167
  · exact B728171
  · exact B728175
  · exact B728179
  · exact B728183
  · exact B728187
  · exact B728191
  · exact B728195
  · exact B728199
  · exact B728203
  · exact B728207
  · exact B728211
  · exact B728215
  · exact B728219
  · exact B728223
  · exact B728227
  · exact B728231
  · exact B728235
  · exact B728239
  · exact B728243
  · exact B728247
  · exact B728251
  · exact B728255
  · exact B728259
  · exact B728263
  · exact B728267
  · exact B728271
  · exact B728275
  · exact B728279
  · exact B728283
  · exact B728287
  · exact B728291
  · exact B728295
  · exact B728299
  · exact B728303
  · exact B728307
  · exact B728311
  · exact B728315
  · exact B728319
  · exact B728323
  · exact B728327
  · exact B728331
  · exact B728335
  · exact B728339
  · exact B728343
  · exact B728347
  · exact B728351
  · exact B728355
  · exact B728359
  · exact B728363
  · exact B728367
  · exact B728371
  · exact B728375
  · exact B728379
  · exact B728383
  · exact B728387
  · exact B728391
  · exact B728395
  · exact B728399
  · exact B728403
  · exact B728407
  · exact B728411
  · exact B728415
  · exact B728419
  · exact B728423
  · exact B728427
  · exact B728431
  · exact B728435
  · exact B728439
  · exact B728443
  · exact B728447
  · exact B728451
  · exact B728455
  · exact B728459
  · exact B728463
  · exact B728467
  · exact B728471
  · exact B728475
  · exact B728479
  · exact B728483
  · exact B728487
  · exact B728491
  · exact B728495
  · exact B728499
  · exact B728503
  · exact B728507
  · exact B728511
  · exact B728515
  · exact B728519
  · exact B728523
  · exact B728527
  · exact B728531
  · exact B728535
  · exact B728539
  · exact B728543
  · exact B728547
  · exact B728551
  · exact B728555
  · exact B728559
  · exact B728563
  · exact B728567
  · exact B728571
  · exact B728575
  · exact B728579
  · exact B728583
  · exact B728587
  · exact B728591
  · exact B728595
  · exact B728599
  · exact B728603
  · exact B728607
  · exact B728611
  · exact B728615
  · exact B728619
  · exact B728623
  · exact B728627
  · exact B728631
  · exact B728635
  · exact B728639
  · exact B728643
  · exact B728647
  · exact B728651
  · exact B728655
  · exact B728659
  · exact B728663
  · exact B728667
  · exact B728671
  · exact B728675
  · exact B728679
  · exact B728683
  · exact B728687
  · exact B728691
  · exact B728695
  · exact B728699
  · exact B728703
  · exact B728707
  · exact B728711
  · exact B728715
  · exact B728719
  · exact B728723
  · exact B728727
  · exact B728731
  · exact B728735
  · exact B728739
  · exact B728743
  · exact B728747
  · exact B728751
  · exact B728755
  · exact B728759
  · exact B728763
  · exact B728767
  · exact B728771
  · exact B728775
  · exact B728779
  · exact B728783
  · exact B728787
  · exact B728791
  · exact B728795
  · exact B728799
  · exact B728803
  · exact B728807
  · exact B728811
  · exact B728815
  · exact B728819
  · exact B728823
  · exact B728827
  · exact B728831
  · exact B728835
  · exact B728839
  · exact B728843
  · exact B728847
  · exact B728851
  · exact B728855
  · exact B728859
  · exact B728863
  · exact B728867
  · exact B728871
  · exact B728875
  · exact B728879
  · exact B728883
  · exact B728887
  · exact B728891
  · exact B728895
  · exact B728899
  · exact B728903
  · exact B728907
  · exact B728911
  · exact B728915
  · exact B728919
  · exact B728923
  · exact B728927
  · exact B728931
  · exact B728935
  · exact B728939
  · exact B728943
  · exact B728947
  · exact B728951
  · exact B728955
  · exact B728959
  · exact B728963
  · exact B728967
  · exact B728971
  · exact B728975
  · exact B728979
  · exact B728983
  · exact B728987
  · exact B728991
  · exact B728995
  · exact B728999
  · exact B729003
  · exact B729007
  · exact B729011
  · exact B729015
  · exact B729019
  · exact B729023
  · exact B729027
  · exact B729031
  · exact B729035
  · exact B729039
  · exact B729043
  · exact B729047
  · exact B729051
  · exact B729055
  · exact B729059
  · exact B729063
  · exact B729067
  · exact B729071
  · exact B729075
  · exact B729079
  · exact B729083
  · exact B729087
  · exact B729091
  · exact B729095
  · exact B729099
  · exact B729103
  · exact B729107
  · exact B729111
  · exact B729115
  · exact B729119
  · exact B729123

theorem C1 (j : ℕ) (h1 : 182281 ≤ j) (h2 : j ≤ 182580) : Blo 726324 (4 * j + 3) := by
  interval_cases j
  · exact B729127
  · exact B729131
  · exact B729135
  · exact B729139
  · exact B729143
  · exact B729147
  · exact B729151
  · exact B729155
  · exact B729159
  · exact B729163
  · exact B729167
  · exact B729171
  · exact B729175
  · exact B729179
  · exact B729183
  · exact B729187
  · exact B729191
  · exact B729195
  · exact B729199
  · exact B729203
  · exact B729207
  · exact B729211
  · exact B729215
  · exact B729219
  · exact B729223
  · exact B729227
  · exact B729231
  · exact B729235
  · exact B729239
  · exact B729243
  · exact B729247
  · exact B729251
  · exact B729255
  · exact B729259
  · exact B729263
  · exact B729267
  · exact B729271
  · exact B729275
  · exact B729279
  · exact B729283
  · exact B729287
  · exact B729291
  · exact B729295
  · exact B729299
  · exact B729303
  · exact B729307
  · exact B729311
  · exact B729315
  · exact B729319
  · exact B729323
  · exact B729327
  · exact B729331
  · exact B729335
  · exact B729339
  · exact B729343
  · exact B729347
  · exact B729351
  · exact B729355
  · exact B729359
  · exact B729363
  · exact B729367
  · exact B729371
  · exact B729375
  · exact B729379
  · exact B729383
  · exact B729387
  · exact B729391
  · exact B729395
  · exact B729399
  · exact B729403
  · exact B729407
  · exact B729411
  · exact B729415
  · exact B729419
  · exact B729423
  · exact B729427
  · exact B729431
  · exact B729435
  · exact B729439
  · exact B729443
  · exact B729447
  · exact B729451
  · exact B729455
  · exact B729459
  · exact B729463
  · exact B729467
  · exact B729471
  · exact B729475
  · exact B729479
  · exact B729483
  · exact B729487
  · exact B729491
  · exact B729495
  · exact B729499
  · exact B729503
  · exact B729507
  · exact B729511
  · exact B729515
  · exact B729519
  · exact B729523
  · exact B729527
  · exact B729531
  · exact B729535
  · exact B729539
  · exact B729543
  · exact B729547
  · exact B729551
  · exact B729555
  · exact B729559
  · exact B729563
  · exact B729567
  · exact B729571
  · exact B729575
  · exact B729579
  · exact B729583
  · exact B729587
  · exact B729591
  · exact B729595
  · exact B729599
  · exact B729603
  · exact B729607
  · exact B729611
  · exact B729615
  · exact B729619
  · exact B729623
  · exact B729627
  · exact B729631
  · exact B729635
  · exact B729639
  · exact B729643
  · exact B729647
  · exact B729651
  · exact B729655
  · exact B729659
  · exact B729663
  · exact B729667
  · exact B729671
  · exact B729675
  · exact B729679
  · exact B729683
  · exact B729687
  · exact B729691
  · exact B729695
  · exact B729699
  · exact B729703
  · exact B729707
  · exact B729711
  · exact B729715
  · exact B729719
  · exact B729723
  · exact B729727
  · exact B729731
  · exact B729735
  · exact B729739
  · exact B729743
  · exact B729747
  · exact B729751
  · exact B729755
  · exact B729759
  · exact B729763
  · exact B729767
  · exact B729771
  · exact B729775
  · exact B729779
  · exact B729783
  · exact B729787
  · exact B729791
  · exact B729795
  · exact B729799
  · exact B729803
  · exact B729807
  · exact B729811
  · exact B729815
  · exact B729819
  · exact B729823
  · exact B729827
  · exact B729831
  · exact B729835
  · exact B729839
  · exact B729843
  · exact B729847
  · exact B729851
  · exact B729855
  · exact B729859
  · exact B729863
  · exact B729867
  · exact B729871
  · exact B729875
  · exact B729879
  · exact B729883
  · exact B729887
  · exact B729891
  · exact B729895
  · exact B729899
  · exact B729903
  · exact B729907
  · exact B729911
  · exact B729915
  · exact B729919
  · exact B729923
  · exact B729927
  · exact B729931
  · exact B729935
  · exact B729939
  · exact B729943
  · exact B729947
  · exact B729951
  · exact B729955
  · exact B729959
  · exact B729963
  · exact B729967
  · exact B729971
  · exact B729975
  · exact B729979
  · exact B729983
  · exact B729987
  · exact B729991
  · exact B729995
  · exact B729999
  · exact B730003
  · exact B730007
  · exact B730011
  · exact B730015
  · exact B730019
  · exact B730023
  · exact B730027
  · exact B730031
  · exact B730035
  · exact B730039
  · exact B730043
  · exact B730047
  · exact B730051
  · exact B730055
  · exact B730059
  · exact B730063
  · exact B730067
  · exact B730071
  · exact B730075
  · exact B730079
  · exact B730083
  · exact B730087
  · exact B730091
  · exact B730095
  · exact B730099
  · exact B730103
  · exact B730107
  · exact B730111
  · exact B730115
  · exact B730119
  · exact B730123
  · exact B730127
  · exact B730131
  · exact B730135
  · exact B730139
  · exact B730143
  · exact B730147
  · exact B730151
  · exact B730155
  · exact B730159
  · exact B730163
  · exact B730167
  · exact B730171
  · exact B730175
  · exact B730179
  · exact B730183
  · exact B730187
  · exact B730191
  · exact B730195
  · exact B730199
  · exact B730203
  · exact B730207
  · exact B730211
  · exact B730215
  · exact B730219
  · exact B730223
  · exact B730227
  · exact B730231
  · exact B730235
  · exact B730239
  · exact B730243
  · exact B730247
  · exact B730251
  · exact B730255
  · exact B730259
  · exact B730263
  · exact B730267
  · exact B730271
  · exact B730275
  · exact B730279
  · exact B730283
  · exact B730287
  · exact B730291
  · exact B730295
  · exact B730299
  · exact B730303
  · exact B730307
  · exact B730311
  · exact B730315
  · exact B730319
  · exact B730323

theorem solution (m : ℕ) (hlo : 726324 ≤ m) (hhi : m ≤ 730324) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 181581 ≤ j := by omega
    have hj2 : j ≤ 182580 := by omega
    have hb : Blo 726324 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 182281 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
