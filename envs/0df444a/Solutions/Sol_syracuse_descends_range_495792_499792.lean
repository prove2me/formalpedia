-- Prove2me | solution 1 for syracuse_descends_range_495792_499792
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:13.39645+00:00
-- url     : https://prove2.me/submissions/1edb5502-5788-420b-944e-ee6e36b8fb16

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


theorem B2162933 : Blo 495792 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1343957 : Blo 495792 1343957 := bbase (se 7 (by rfl) ⟨15749, by rfl⟩ : syracuseStep 1343957 = 31499) (by norm_num)
theorem B2130533 : Blo 495792 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B5374613 : Blo 495792 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2523797 : Blo 495792 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B557797 : Blo 495792 557797 := bbase (se 4 (by rfl) ⟨52293, by rfl⟩ : syracuseStep 557797 = 104587) (by norm_num)
theorem B557833 : Blo 495792 557833 := bbase (se 2 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 557833 = 418375) (by norm_num)
theorem B557869 : Blo 495792 557869 := bbase (se 3 (by rfl) ⟨104600, by rfl⟩ : syracuseStep 557869 = 209201) (by norm_num)
theorem B557905 : Blo 495792 557905 := bbase (se 2 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 557905 = 418429) (by norm_num)
theorem B557941 : Blo 495792 557941 := bbase (se 5 (by rfl) ⟨26153, by rfl⟩ : syracuseStep 557941 = 52307) (by norm_num)
theorem B557977 : Blo 495792 557977 := bbase (se 2 (by rfl) ⟨209241, by rfl⟩ : syracuseStep 557977 = 418483) (by norm_num)
theorem B558013 : Blo 495792 558013 := bbase (se 3 (by rfl) ⟨104627, by rfl⟩ : syracuseStep 558013 = 209255) (by norm_num)
theorem B558049 : Blo 495792 558049 := bbase (se 2 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 558049 = 418537) (by norm_num)
theorem B558085 : Blo 495792 558085 := bbase (se 4 (by rfl) ⟨52320, by rfl⟩ : syracuseStep 558085 = 104641) (by norm_num)
theorem B558121 : Blo 495792 558121 := bbase (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) (by norm_num)
theorem B558157 : Blo 495792 558157 := bbase (se 3 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 558157 = 209309) (by norm_num)
theorem B558193 : Blo 495792 558193 := bbase (se 2 (by rfl) ⟨209322, by rfl⟩ : syracuseStep 558193 = 418645) (by norm_num)
theorem B558229 : Blo 495792 558229 := bbase (se 6 (by rfl) ⟨13083, by rfl⟩ : syracuseStep 558229 = 26167) (by norm_num)
theorem B558265 : Blo 495792 558265 := bbase (se 2 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 558265 = 418699) (by norm_num)
theorem B558301 : Blo 495792 558301 := bbase (se 3 (by rfl) ⟨104681, by rfl⟩ : syracuseStep 558301 = 209363) (by norm_num)
theorem B853237 : Blo 495792 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B558337 : Blo 495792 558337 := bbase (se 2 (by rfl) ⟨209376, by rfl⟩ : syracuseStep 558337 = 418753) (by norm_num)
theorem B558373 : Blo 495792 558373 := bbase (se 4 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 558373 = 104695) (by norm_num)
theorem B558409 : Blo 495792 558409 := bbase (se 2 (by rfl) ⟨209403, by rfl⟩ : syracuseStep 558409 = 418807) (by norm_num)
theorem B558445 : Blo 495792 558445 := bbase (se 3 (by rfl) ⟨104708, by rfl⟩ : syracuseStep 558445 = 209417) (by norm_num)
theorem B755077 : Blo 495792 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B558481 : Blo 495792 558481 := bbase (se 2 (by rfl) ⟨209430, by rfl⟩ : syracuseStep 558481 = 418861) (by norm_num)
theorem B1115549 : Blo 495792 1115549 := bbase (se 3 (by rfl) ⟨209165, by rfl⟩ : syracuseStep 1115549 = 418331) (by norm_num)
theorem B558517 : Blo 495792 558517 := bbase (se 5 (by rfl) ⟨26180, by rfl⟩ : syracuseStep 558517 = 52361) (by norm_num)
theorem B853429 : Blo 495792 853429 := bbase (se 5 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 853429 = 80009) (by norm_num)
theorem B558553 : Blo 495792 558553 := bbase (se 2 (by rfl) ⟨209457, by rfl⟩ : syracuseStep 558553 = 418915) (by norm_num)
theorem B1115621 : Blo 495792 1115621 := bbase (se 4 (by rfl) ⟨104589, by rfl⟩ : syracuseStep 1115621 = 209179) (by norm_num)
theorem B755173 : Blo 495792 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B558589 : Blo 495792 558589 := bbase (se 3 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 558589 = 209471) (by norm_num)
theorem B558625 : Blo 495792 558625 := bbase (se 2 (by rfl) ⟨209484, by rfl⟩ : syracuseStep 558625 = 418969) (by norm_num)
theorem B1115693 : Blo 495792 1115693 := bbase (se 3 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 1115693 = 418385) (by norm_num)
theorem B558661 : Blo 495792 558661 := bbase (se 4 (by rfl) ⟨52374, by rfl⟩ : syracuseStep 558661 = 104749) (by norm_num)
theorem B2131541 : Blo 495792 2131541 := bbase (se 8 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 2131541 = 24979) (by norm_num)
theorem B558697 : Blo 495792 558697 := bbase (se 2 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 558697 = 419023) (by norm_num)
theorem B1115765 : Blo 495792 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B558733 : Blo 495792 558733 := bbase (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) (by norm_num)
theorem B558769 : Blo 495792 558769 := bbase (se 2 (by rfl) ⟨209538, by rfl⟩ : syracuseStep 558769 = 419077) (by norm_num)
theorem B755381 : Blo 495792 755381 := bbase (se 5 (by rfl) ⟨35408, by rfl⟩ : syracuseStep 755381 = 70817) (by norm_num)
theorem B1115837 : Blo 495792 1115837 := bbase (se 3 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 1115837 = 418439) (by norm_num)
theorem B558805 : Blo 495792 558805 := bbase (se 7 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 558805 = 13097) (by norm_num)
theorem B558841 : Blo 495792 558841 := bbase (se 2 (by rfl) ⟨209565, by rfl⟩ : syracuseStep 558841 = 419131) (by norm_num)
theorem B1115909 : Blo 495792 1115909 := bbase (se 4 (by rfl) ⟨104616, by rfl⟩ : syracuseStep 1115909 = 209233) (by norm_num)
theorem B558877 : Blo 495792 558877 := bbase (se 3 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 558877 = 209579) (by norm_num)
theorem B558913 : Blo 495792 558913 := bbase (se 2 (by rfl) ⟨209592, by rfl⟩ : syracuseStep 558913 = 419185) (by norm_num)
theorem B1115981 : Blo 495792 1115981 := bbase (se 3 (by rfl) ⟨209246, by rfl⟩ : syracuseStep 1115981 = 418493) (by norm_num)
theorem B1509205 : Blo 495792 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B558949 : Blo 495792 558949 := bbase (se 4 (by rfl) ⟨52401, by rfl⟩ : syracuseStep 558949 = 104803) (by norm_num)
theorem B558985 : Blo 495792 558985 := bbase (se 2 (by rfl) ⟨209619, by rfl⟩ : syracuseStep 558985 = 419239) (by norm_num)
theorem B1116053 : Blo 495792 1116053 := bbase (se 6 (by rfl) ⟨26157, by rfl⟩ : syracuseStep 1116053 = 52315) (by norm_num)
theorem B2525093 : Blo 495792 2525093 := bbase (se 4 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 2525093 = 473455) (by norm_num)
theorem B559021 : Blo 495792 559021 := bbase (se 3 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 559021 = 209633) (by norm_num)
theorem B559057 : Blo 495792 559057 := bbase (se 2 (by rfl) ⟨209646, by rfl⟩ : syracuseStep 559057 = 419293) (by norm_num)
theorem B1345493 : Blo 495792 1345493 := bbase (se 7 (by rfl) ⟨15767, by rfl⟩ : syracuseStep 1345493 = 31535) (by norm_num)
theorem B1116125 : Blo 495792 1116125 := bbase (se 3 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 1116125 = 418547) (by norm_num)
theorem B559093 : Blo 495792 559093 := bbase (se 5 (by rfl) ⟨26207, by rfl⟩ : syracuseStep 559093 = 52415) (by norm_num)
theorem B1214477 : Blo 495792 1214477 := bbase (se 3 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 1214477 = 455429) (by norm_num)
theorem B559129 : Blo 495792 559129 := bbase (se 2 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 559129 = 419347) (by norm_num)
theorem B1116197 : Blo 495792 1116197 := bbase (se 4 (by rfl) ⟨104643, by rfl⟩ : syracuseStep 1116197 = 209287) (by norm_num)
theorem B559165 : Blo 495792 559165 := bbase (se 3 (by rfl) ⟨104843, by rfl⟩ : syracuseStep 559165 = 209687) (by norm_num)
theorem B559201 : Blo 495792 559201 := bbase (se 2 (by rfl) ⟨209700, by rfl⟩ : syracuseStep 559201 = 419401) (by norm_num)
theorem B1116269 : Blo 495792 1116269 := bbase (se 3 (by rfl) ⟨209300, by rfl⟩ : syracuseStep 1116269 = 418601) (by norm_num)
theorem B559237 : Blo 495792 559237 := bbase (se 4 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 559237 = 104857) (by norm_num)
theorem B559273 : Blo 495792 559273 := bbase (se 2 (by rfl) ⟨209727, by rfl⟩ : syracuseStep 559273 = 419455) (by norm_num)
theorem B1116341 : Blo 495792 1116341 := bbase (se 5 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 1116341 = 104657) (by norm_num)
theorem B559309 : Blo 495792 559309 := bbase (se 3 (by rfl) ⟨104870, by rfl⟩ : syracuseStep 559309 = 209741) (by norm_num)
theorem B821485 : Blo 495792 821485 := bbase (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) (by norm_num)
theorem B559345 : Blo 495792 559345 := bbase (se 2 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 559345 = 419509) (by norm_num)
theorem B1116413 : Blo 495792 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B559381 : Blo 495792 559381 := bbase (se 6 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 559381 = 26221) (by norm_num)
theorem B559417 : Blo 495792 559417 := bbase (se 2 (by rfl) ⟨209781, by rfl⟩ : syracuseStep 559417 = 419563) (by norm_num)
theorem B1116485 : Blo 495792 1116485 := bbase (se 4 (by rfl) ⟨104670, by rfl⟩ : syracuseStep 1116485 = 209341) (by norm_num)
theorem B559453 : Blo 495792 559453 := bbase (se 3 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 559453 = 209795) (by norm_num)
theorem B2394485 : Blo 495792 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B559489 : Blo 495792 559489 := bbase (se 2 (by rfl) ⟨209808, by rfl⟩ : syracuseStep 559489 = 419617) (by norm_num)
theorem B1116557 : Blo 495792 1116557 := bbase (se 3 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 1116557 = 418709) (by norm_num)
theorem B1673621 : Blo 495792 1673621 := bbase (se 6 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 1673621 = 78451) (by norm_num)
theorem B559525 : Blo 495792 559525 := bbase (se 4 (by rfl) ⟨52455, by rfl⟩ : syracuseStep 559525 = 104911) (by norm_num)
theorem B559561 : Blo 495792 559561 := bbase (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) (by norm_num)
theorem B1116629 : Blo 495792 1116629 := bbase (se 7 (by rfl) ⟨13085, by rfl⟩ : syracuseStep 1116629 = 26171) (by norm_num)
theorem B559597 : Blo 495792 559597 := bbase (se 3 (by rfl) ⟨104924, by rfl⟩ : syracuseStep 559597 = 209849) (by norm_num)
theorem B559633 : Blo 495792 559633 := bbase (se 2 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 559633 = 419725) (by norm_num)
theorem B1116701 : Blo 495792 1116701 := bbase (se 3 (by rfl) ⟨209381, by rfl⟩ : syracuseStep 1116701 = 418763) (by norm_num)
theorem B559669 : Blo 495792 559669 := bbase (se 5 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 559669 = 52469) (by norm_num)
theorem B2263621 : Blo 495792 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B559705 : Blo 495792 559705 := bbase (se 2 (by rfl) ⟨209889, by rfl⟩ : syracuseStep 559705 = 419779) (by norm_num)
theorem B1116773 : Blo 495792 1116773 := bbase (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) (by norm_num)
theorem B559741 : Blo 495792 559741 := bbase (se 3 (by rfl) ⟨104951, by rfl⟩ : syracuseStep 559741 = 209903) (by norm_num)
theorem B559777 : Blo 495792 559777 := bbase (se 2 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 559777 = 419833) (by norm_num)
theorem B1116845 : Blo 495792 1116845 := bbase (se 3 (by rfl) ⟨209408, by rfl⟩ : syracuseStep 1116845 = 418817) (by norm_num)
theorem B559813 : Blo 495792 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B559849 : Blo 495792 559849 := bbase (se 2 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 559849 = 419887) (by norm_num)
theorem B1116917 : Blo 495792 1116917 := bbase (se 5 (by rfl) ⟨52355, by rfl⟩ : syracuseStep 1116917 = 104711) (by norm_num)
theorem B559885 : Blo 495792 559885 := bbase (se 3 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 559885 = 209957) (by norm_num)
theorem B559921 : Blo 495792 559921 := bbase (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) (by norm_num)
theorem B1116989 : Blo 495792 1116989 := bbase (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) (by norm_num)
theorem B1674053 : Blo 495792 1674053 := bbase (se 4 (by rfl) ⟨156942, by rfl⟩ : syracuseStep 1674053 = 313885) (by norm_num)
theorem B559957 : Blo 495792 559957 := bbase (se 9 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 559957 = 3281) (by norm_num)
theorem B559993 : Blo 495792 559993 := bbase (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) (by norm_num)
theorem B1117061 : Blo 495792 1117061 := bbase (se 4 (by rfl) ⟨104724, by rfl⟩ : syracuseStep 1117061 = 209449) (by norm_num)
theorem B560029 : Blo 495792 560029 := bbase (se 3 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 560029 = 210011) (by norm_num)
theorem B1412005 : Blo 495792 1412005 := bbase (se 4 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 1412005 = 264751) (by norm_num)
theorem B560065 : Blo 495792 560065 := bbase (se 2 (by rfl) ⟨210024, by rfl⟩ : syracuseStep 560065 = 420049) (by norm_num)
theorem B756677 : Blo 495792 756677 := bbase (se 4 (by rfl) ⟨70938, by rfl⟩ : syracuseStep 756677 = 141877) (by norm_num)
theorem B1117133 : Blo 495792 1117133 := bbase (se 3 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 1117133 = 418925) (by norm_num)
theorem B560101 : Blo 495792 560101 := bbase (se 4 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 560101 = 105019) (by norm_num)
theorem B560137 : Blo 495792 560137 := bbase (se 2 (by rfl) ⟨210051, by rfl⟩ : syracuseStep 560137 = 420103) (by norm_num)
theorem B1117205 : Blo 495792 1117205 := bbase (se 6 (by rfl) ⟨26184, by rfl⟩ : syracuseStep 1117205 = 52369) (by norm_num)
theorem B560173 : Blo 495792 560173 := bbase (se 3 (by rfl) ⟨105032, by rfl⟩ : syracuseStep 560173 = 210065) (by norm_num)
theorem B560209 : Blo 495792 560209 := bbase (se 2 (by rfl) ⟨210078, by rfl⟩ : syracuseStep 560209 = 420157) (by norm_num)
theorem B1117277 : Blo 495792 1117277 := bbase (se 3 (by rfl) ⟨209489, by rfl⟩ : syracuseStep 1117277 = 418979) (by norm_num)
theorem B560245 : Blo 495792 560245 := bbase (se 5 (by rfl) ⟨26261, by rfl⟩ : syracuseStep 560245 = 52523) (by norm_num)
theorem B560281 : Blo 495792 560281 := bbase (se 2 (by rfl) ⟨210105, by rfl⟩ : syracuseStep 560281 = 420211) (by norm_num)
theorem B1117349 : Blo 495792 1117349 := bbase (se 4 (by rfl) ⟨104751, by rfl⟩ : syracuseStep 1117349 = 209503) (by norm_num)
theorem B2526389 : Blo 495792 2526389 := bbase (se 5 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 2526389 = 236849) (by norm_num)
theorem B560317 : Blo 495792 560317 := bbase (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) (by norm_num)
theorem B560353 : Blo 495792 560353 := bbase (se 2 (by rfl) ⟨210132, by rfl⟩ : syracuseStep 560353 = 420265) (by norm_num)
theorem B1117421 : Blo 495792 1117421 := bbase (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) (by norm_num)
theorem B1674485 : Blo 495792 1674485 := bbase (se 5 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 1674485 = 156983) (by norm_num)
theorem B560389 : Blo 495792 560389 := bbase (se 4 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 560389 = 105073) (by norm_num)
theorem B560425 : Blo 495792 560425 := bbase (se 2 (by rfl) ⟨210159, by rfl⟩ : syracuseStep 560425 = 420319) (by norm_num)
theorem B1117493 : Blo 495792 1117493 := bbase (se 5 (by rfl) ⟨52382, by rfl⟩ : syracuseStep 1117493 = 104765) (by norm_num)
theorem B2133317 : Blo 495792 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B560461 : Blo 495792 560461 := bbase (se 3 (by rfl) ⟨105086, by rfl⟩ : syracuseStep 560461 = 210173) (by norm_num)
theorem B560497 : Blo 495792 560497 := bbase (se 2 (by rfl) ⟨210186, by rfl⟩ : syracuseStep 560497 = 420373) (by norm_num)
theorem B1117565 : Blo 495792 1117565 := bbase (se 3 (by rfl) ⟨209543, by rfl⟩ : syracuseStep 1117565 = 419087) (by norm_num)
theorem B560533 : Blo 495792 560533 := bbase (se 6 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 560533 = 26275) (by norm_num)
theorem B560569 : Blo 495792 560569 := bbase (se 2 (by rfl) ⟨210213, by rfl⟩ : syracuseStep 560569 = 420427) (by norm_num)
theorem B1117637 : Blo 495792 1117637 := bbase (se 4 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 1117637 = 209557) (by norm_num)
theorem B560605 : Blo 495792 560605 := bbase (se 3 (by rfl) ⟨105113, by rfl⟩ : syracuseStep 560605 = 210227) (by norm_num)
theorem B560641 : Blo 495792 560641 := bbase (se 2 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 560641 = 420481) (by norm_num)
theorem B1117709 : Blo 495792 1117709 := bbase (se 3 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 1117709 = 419141) (by norm_num)
theorem B1510933 : Blo 495792 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B560677 : Blo 495792 560677 := bbase (se 4 (by rfl) ⟨52563, by rfl⟩ : syracuseStep 560677 = 105127) (by norm_num)
theorem B560713 : Blo 495792 560713 := bbase (se 2 (by rfl) ⟨210267, by rfl⟩ : syracuseStep 560713 = 420535) (by norm_num)
theorem B1117781 : Blo 495792 1117781 := bbase (se 8 (by rfl) ⟨6549, by rfl⟩ : syracuseStep 1117781 = 13099) (by norm_num)
theorem B560749 : Blo 495792 560749 := bbase (se 3 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 560749 = 210281) (by norm_num)
theorem B560785 : Blo 495792 560785 := bbase (se 2 (by rfl) ⟨210294, by rfl⟩ : syracuseStep 560785 = 420589) (by norm_num)
theorem B1117853 : Blo 495792 1117853 := bbase (se 3 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 1117853 = 419195) (by norm_num)
theorem B1674917 : Blo 495792 1674917 := bbase (se 4 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 1674917 = 314047) (by norm_num)
theorem B560821 : Blo 495792 560821 := bbase (se 5 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 560821 = 52577) (by norm_num)
theorem B560857 : Blo 495792 560857 := bbase (se 2 (by rfl) ⟨210321, by rfl⟩ : syracuseStep 560857 = 420643) (by norm_num)
theorem B1117925 : Blo 495792 1117925 := bbase (se 4 (by rfl) ⟨104805, by rfl⟩ : syracuseStep 1117925 = 209611) (by norm_num)
theorem B560893 : Blo 495792 560893 := bbase (se 3 (by rfl) ⟨105167, by rfl⟩ : syracuseStep 560893 = 210335) (by norm_num)
theorem B560929 : Blo 495792 560929 := bbase (se 2 (by rfl) ⟨210348, by rfl⟩ : syracuseStep 560929 = 420697) (by norm_num)
theorem B1117997 : Blo 495792 1117997 := bbase (se 3 (by rfl) ⟨209624, by rfl⟩ : syracuseStep 1117997 = 419249) (by norm_num)
theorem B560965 : Blo 495792 560965 := bbase (se 4 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 560965 = 105181) (by norm_num)
theorem B561001 : Blo 495792 561001 := bbase (se 2 (by rfl) ⟨210375, by rfl⟩ : syracuseStep 561001 = 420751) (by norm_num)
theorem B1118069 : Blo 495792 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B1347461 : Blo 495792 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B561037 : Blo 495792 561037 := bbase (se 3 (by rfl) ⟨105194, by rfl⟩ : syracuseStep 561037 = 210389) (by norm_num)
theorem B561073 : Blo 495792 561073 := bbase (se 2 (by rfl) ⟨210402, by rfl⟩ : syracuseStep 561073 = 420805) (by norm_num)
theorem B1118141 : Blo 495792 1118141 := bbase (se 3 (by rfl) ⟨209651, by rfl⟩ : syracuseStep 1118141 = 419303) (by norm_num)
theorem B561109 : Blo 495792 561109 := bbase (se 7 (by rfl) ⟨6575, by rfl⟩ : syracuseStep 561109 = 13151) (by norm_num)
theorem B561145 : Blo 495792 561145 := bbase (se 2 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 561145 = 420859) (by norm_num)
theorem B1118213 : Blo 495792 1118213 := bbase (se 4 (by rfl) ⟨104832, by rfl⟩ : syracuseStep 1118213 = 209665) (by norm_num)
theorem B561181 : Blo 495792 561181 := bbase (se 3 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 561181 = 210443) (by norm_num)
theorem B561217 : Blo 495792 561217 := bbase (se 2 (by rfl) ⟨210456, by rfl⟩ : syracuseStep 561217 = 420913) (by norm_num)
theorem B1118285 : Blo 495792 1118285 := bbase (se 3 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 1118285 = 419357) (by norm_num)
theorem B1675349 : Blo 495792 1675349 := bbase (se 8 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 1675349 = 19633) (by norm_num)
theorem B561253 : Blo 495792 561253 := bbase (se 4 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 561253 = 105235) (by norm_num)
theorem B561289 : Blo 495792 561289 := bbase (se 2 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 561289 = 420967) (by norm_num)
theorem B1118357 : Blo 495792 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B561325 : Blo 495792 561325 := bbase (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) (by norm_num)
theorem B561361 : Blo 495792 561361 := bbase (se 2 (by rfl) ⟨210510, by rfl⟩ : syracuseStep 561361 = 421021) (by norm_num)
theorem B1118429 : Blo 495792 1118429 := bbase (se 3 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 1118429 = 419411) (by norm_num)
theorem B561397 : Blo 495792 561397 := bbase (se 5 (by rfl) ⟨26315, by rfl⟩ : syracuseStep 561397 = 52631) (by norm_num)
theorem B561433 : Blo 495792 561433 := bbase (se 2 (by rfl) ⟨210537, by rfl⟩ : syracuseStep 561433 = 421075) (by norm_num)
theorem B1118501 : Blo 495792 1118501 := bbase (se 4 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 1118501 = 209719) (by norm_num)
theorem B561469 : Blo 495792 561469 := bbase (se 3 (by rfl) ⟨105275, by rfl⟩ : syracuseStep 561469 = 210551) (by norm_num)
theorem B561505 : Blo 495792 561505 := bbase (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) (by norm_num)
theorem B1118573 : Blo 495792 1118573 := bbase (se 3 (by rfl) ⟨209732, by rfl⟩ : syracuseStep 1118573 = 419465) (by norm_num)
theorem B561541 : Blo 495792 561541 := bbase (se 4 (by rfl) ⟨52644, by rfl⟩ : syracuseStep 561541 = 105289) (by norm_num)
theorem B561577 : Blo 495792 561577 := bbase (se 2 (by rfl) ⟨210591, by rfl⟩ : syracuseStep 561577 = 421183) (by norm_num)
theorem B1118645 : Blo 495792 1118645 := bbase (se 5 (by rfl) ⟨52436, by rfl⟩ : syracuseStep 1118645 = 104873) (by norm_num)
theorem B2527685 : Blo 495792 2527685 := bbase (se 4 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 2527685 = 473941) (by norm_num)
theorem B561613 : Blo 495792 561613 := bbase (se 3 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 561613 = 210605) (by norm_num)
theorem B561649 : Blo 495792 561649 := bbase (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) (by norm_num)
theorem B1118717 : Blo 495792 1118717 := bbase (se 3 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 1118717 = 419519) (by norm_num)
theorem B1675781 : Blo 495792 1675781 := bbase (se 4 (by rfl) ⟨157104, by rfl⟩ : syracuseStep 1675781 = 314209) (by norm_num)
theorem B561685 : Blo 495792 561685 := bbase (se 6 (by rfl) ⟨13164, by rfl⟩ : syracuseStep 561685 = 26329) (by norm_num)
theorem B1217045 : Blo 495792 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B561721 : Blo 495792 561721 := bbase (se 2 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 561721 = 421291) (by norm_num)
theorem B1118789 : Blo 495792 1118789 := bbase (se 4 (by rfl) ⟨104886, by rfl⟩ : syracuseStep 1118789 = 209773) (by norm_num)
theorem B561757 : Blo 495792 561757 := bbase (se 3 (by rfl) ⟨105329, by rfl⟩ : syracuseStep 561757 = 210659) (by norm_num)
theorem B561793 : Blo 495792 561793 := bbase (se 2 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 561793 = 421345) (by norm_num)
theorem B1118861 : Blo 495792 1118861 := bbase (se 3 (by rfl) ⟨209786, by rfl⟩ : syracuseStep 1118861 = 419573) (by norm_num)
theorem B561829 : Blo 495792 561829 := bbase (se 4 (by rfl) ⟨52671, by rfl⟩ : syracuseStep 561829 = 105343) (by norm_num)
theorem B561865 : Blo 495792 561865 := bbase (se 2 (by rfl) ⟨210699, by rfl⟩ : syracuseStep 561865 = 421399) (by norm_num)
theorem B758477 : Blo 495792 758477 := bbase (se 3 (by rfl) ⟨142214, by rfl⟩ : syracuseStep 758477 = 284429) (by norm_num)
theorem B1020629 : Blo 495792 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B1118933 : Blo 495792 1118933 := bbase (se 7 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 1118933 = 26225) (by norm_num)
theorem B561901 : Blo 495792 561901 := bbase (se 3 (by rfl) ⟨105356, by rfl⟩ : syracuseStep 561901 = 210713) (by norm_num)
theorem B561937 : Blo 495792 561937 := bbase (se 2 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 561937 = 421453) (by norm_num)
theorem B1119005 : Blo 495792 1119005 := bbase (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) (by norm_num)
theorem B561973 : Blo 495792 561973 := bbase (se 5 (by rfl) ⟨26342, by rfl⟩ : syracuseStep 561973 = 52685) (by norm_num)
theorem B627517 : Blo 495792 627517 := bbase (se 3 (by rfl) ⟨117659, by rfl⟩ : syracuseStep 627517 = 235319) (by norm_num)
theorem B562009 : Blo 495792 562009 := bbase (se 2 (by rfl) ⟨210753, by rfl⟩ : syracuseStep 562009 = 421507) (by norm_num)
theorem B1119077 : Blo 495792 1119077 := bbase (se 4 (by rfl) ⟨104913, by rfl⟩ : syracuseStep 1119077 = 209827) (by norm_num)
theorem B562045 : Blo 495792 562045 := bbase (se 3 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 562045 = 210767) (by norm_num)
theorem B562081 : Blo 495792 562081 := bbase (se 2 (by rfl) ⟨210780, by rfl⟩ : syracuseStep 562081 = 421561) (by norm_num)
theorem B1119149 : Blo 495792 1119149 := bbase (se 3 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 1119149 = 419681) (by norm_num)
theorem B1676213 : Blo 495792 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B562117 : Blo 495792 562117 := bbase (se 4 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 562117 = 105397) (by norm_num)
theorem B627689 : Blo 495792 627689 := bbase (se 2 (by rfl) ⟨235383, by rfl⟩ : syracuseStep 627689 = 470767) (by norm_num)
theorem B562153 : Blo 495792 562153 := bbase (se 2 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 562153 = 421615) (by norm_num)
theorem B1119221 : Blo 495792 1119221 := bbase (se 5 (by rfl) ⟨52463, by rfl⟩ : syracuseStep 1119221 = 104927) (by norm_num)
theorem B562189 : Blo 495792 562189 := bbase (se 3 (by rfl) ⟨105410, by rfl⟩ : syracuseStep 562189 = 210821) (by norm_num)
theorem B627745 : Blo 495792 627745 := bbase (se 2 (by rfl) ⟨235404, by rfl⟩ : syracuseStep 627745 = 470809) (by norm_num)
theorem B562225 : Blo 495792 562225 := bbase (se 2 (by rfl) ⟨210834, by rfl⟩ : syracuseStep 562225 = 421669) (by norm_num)
theorem B1119293 : Blo 495792 1119293 := bbase (se 3 (by rfl) ⟨209867, by rfl⟩ : syracuseStep 1119293 = 419735) (by norm_num)
theorem B562261 : Blo 495792 562261 := bbase (se 8 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 562261 = 6589) (by norm_num)
theorem B627841 : Blo 495792 627841 := bbase (se 2 (by rfl) ⟨235440, by rfl⟩ : syracuseStep 627841 = 470881) (by norm_num)
theorem B1119365 : Blo 495792 1119365 := bbase (se 4 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 1119365 = 209881) (by norm_num)
theorem B1119437 : Blo 495792 1119437 := bbase (se 3 (by rfl) ⟨209894, by rfl⟩ : syracuseStep 1119437 = 419789) (by norm_num)
theorem B1119509 : Blo 495792 1119509 := bbase (se 6 (by rfl) ⟨26238, by rfl⟩ : syracuseStep 1119509 = 52477) (by norm_num)
theorem B628013 : Blo 495792 628013 := bbase (se 3 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 628013 = 235505) (by norm_num)
theorem B1119581 : Blo 495792 1119581 := bbase (se 3 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 1119581 = 419843) (by norm_num)
theorem B628069 : Blo 495792 628069 := bbase (se 4 (by rfl) ⟨58881, by rfl⟩ : syracuseStep 628069 = 117763) (by norm_num)
theorem B1676645 : Blo 495792 1676645 := bbase (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) (by norm_num)
theorem B1119653 : Blo 495792 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B628165 : Blo 495792 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B1119725 : Blo 495792 1119725 := bbase (se 3 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 1119725 = 419897) (by norm_num)
theorem B1119797 : Blo 495792 1119797 := bbase (se 5 (by rfl) ⟨52490, by rfl⟩ : syracuseStep 1119797 = 104981) (by norm_num)
theorem B628337 : Blo 495792 628337 := bbase (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) (by norm_num)
theorem B1119869 : Blo 495792 1119869 := bbase (se 3 (by rfl) ⟨209975, by rfl⟩ : syracuseStep 1119869 = 419951) (by norm_num)
theorem B628393 : Blo 495792 628393 := bbase (se 2 (by rfl) ⟨235647, by rfl⟩ : syracuseStep 628393 = 471295) (by norm_num)
theorem B1414853 : Blo 495792 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B1119941 : Blo 495792 1119941 := bbase (se 4 (by rfl) ⟨104994, by rfl⟩ : syracuseStep 1119941 = 209989) (by norm_num)
theorem B2528981 : Blo 495792 2528981 := bbase (se 7 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 2528981 = 59273) (by norm_num)
theorem B530173 : Blo 495792 530173 := bbase (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) (by norm_num)
theorem B628489 : Blo 495792 628489 := bbase (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) (by norm_num)
theorem B1120013 : Blo 495792 1120013 := bbase (se 3 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 1120013 = 420005) (by norm_num)
theorem B1677077 : Blo 495792 1677077 := bbase (se 6 (by rfl) ⟨39306, by rfl⟩ : syracuseStep 1677077 = 78613) (by norm_num)
theorem B595777 : Blo 495792 595777 := bbase (se 2 (by rfl) ⟨223416, by rfl⟩ : syracuseStep 595777 = 446833) (by norm_num)
theorem B530245 : Blo 495792 530245 := bbase (se 4 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 530245 = 99421) (by norm_num)
theorem B1120085 : Blo 495792 1120085 := bbase (se 9 (by rfl) ⟨3281, by rfl⟩ : syracuseStep 1120085 = 6563) (by norm_num)
theorem B1120157 : Blo 495792 1120157 := bbase (se 3 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 1120157 = 420059) (by norm_num)
theorem B628661 : Blo 495792 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B1120229 : Blo 495792 1120229 := bbase (se 4 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 1120229 = 210043) (by norm_num)
theorem B595949 : Blo 495792 595949 := bbase (se 3 (by rfl) ⟨111740, by rfl⟩ : syracuseStep 595949 = 223481) (by norm_num)
theorem B628717 : Blo 495792 628717 := bbase (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) (by norm_num)
theorem B530425 : Blo 495792 530425 := bbase (se 2 (by rfl) ⟨198909, by rfl⟩ : syracuseStep 530425 = 397819) (by norm_num)
theorem B1120301 : Blo 495792 1120301 := bbase (se 3 (by rfl) ⟨210056, by rfl⟩ : syracuseStep 1120301 = 420113) (by norm_num)
theorem B759869 : Blo 495792 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B628813 : Blo 495792 628813 := bbase (se 3 (by rfl) ⟨117902, by rfl⟩ : syracuseStep 628813 = 235805) (by norm_num)
theorem B596065 : Blo 495792 596065 := bbase (se 2 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 596065 = 447049) (by norm_num)
theorem B1120373 : Blo 495792 1120373 := bbase (se 5 (by rfl) ⟨52517, by rfl⟩ : syracuseStep 1120373 = 105035) (by norm_num)
theorem B1120445 : Blo 495792 1120445 := bbase (se 3 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 1120445 = 420167) (by norm_num)
theorem B596161 : Blo 495792 596161 := bbase (se 2 (by rfl) ⟨223560, by rfl⟩ : syracuseStep 596161 = 447121) (by norm_num)
theorem B1677509 : Blo 495792 1677509 := bbase (se 4 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 1677509 = 314533) (by norm_num)
theorem B2398405 : Blo 495792 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B5445845 : Blo 495792 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B628985 : Blo 495792 628985 := bbase (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) (by norm_num)
theorem B1120517 : Blo 495792 1120517 := bbase (se 4 (by rfl) ⟨105048, by rfl⟩ : syracuseStep 1120517 = 210097) (by norm_num)
theorem B629041 : Blo 495792 629041 := bbase (se 2 (by rfl) ⟨235890, by rfl⟩ : syracuseStep 629041 = 471781) (by norm_num)
theorem B1120589 : Blo 495792 1120589 := bbase (se 3 (by rfl) ⟨210110, by rfl⟩ : syracuseStep 1120589 = 420221) (by norm_num)
theorem B596305 : Blo 495792 596305 := bbase (se 2 (by rfl) ⟨223614, by rfl⟩ : syracuseStep 596305 = 447229) (by norm_num)
theorem B629137 : Blo 495792 629137 := bbase (se 2 (by rfl) ⟨235926, by rfl⟩ : syracuseStep 629137 = 471853) (by norm_num)
theorem B1120661 : Blo 495792 1120661 := bbase (se 6 (by rfl) ⟨26265, by rfl⟩ : syracuseStep 1120661 = 52531) (by norm_num)
theorem B530869 : Blo 495792 530869 := bbase (se 5 (by rfl) ⟨24884, by rfl⟩ : syracuseStep 530869 = 49769) (by norm_num)
theorem B1120733 : Blo 495792 1120733 := bbase (se 3 (by rfl) ⟨210137, by rfl⟩ : syracuseStep 1120733 = 420275) (by norm_num)
theorem B1120805 : Blo 495792 1120805 := bbase (se 4 (by rfl) ⟨105075, by rfl⟩ : syracuseStep 1120805 = 210151) (by norm_num)
theorem B530993 : Blo 495792 530993 := bbase (se 2 (by rfl) ⟨199122, by rfl⟩ : syracuseStep 530993 = 398245) (by norm_num)
theorem B629309 : Blo 495792 629309 := bbase (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) (by norm_num)
theorem B1350229 : Blo 495792 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B1120877 : Blo 495792 1120877 := bbase (se 3 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 1120877 = 420329) (by norm_num)
theorem B1677941 : Blo 495792 1677941 := bbase (se 5 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 1677941 = 157307) (by norm_num)
theorem B629365 : Blo 495792 629365 := bbase (se 5 (by rfl) ⟨29501, by rfl⟩ : syracuseStep 629365 = 59003) (by norm_num)
theorem B1120949 : Blo 495792 1120949 := bbase (se 5 (by rfl) ⟨52544, by rfl⟩ : syracuseStep 1120949 = 105089) (by norm_num)
theorem B629461 : Blo 495792 629461 := bbase (se 7 (by rfl) ⟨7376, by rfl⟩ : syracuseStep 629461 = 14753) (by norm_num)
theorem B1121021 : Blo 495792 1121021 := bbase (se 3 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 1121021 = 420383) (by norm_num)
theorem B531245 : Blo 495792 531245 := bbase (se 3 (by rfl) ⟨99608, by rfl⟩ : syracuseStep 531245 = 199217) (by norm_num)
theorem B1121093 : Blo 495792 1121093 := bbase (se 4 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 1121093 = 210205) (by norm_num)
theorem B1416037 : Blo 495792 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B629633 : Blo 495792 629633 := bbase (se 2 (by rfl) ⟨236112, by rfl⟩ : syracuseStep 629633 = 472225) (by norm_num)
theorem B1121165 : Blo 495792 1121165 := bbase (se 3 (by rfl) ⟨210218, by rfl⟩ : syracuseStep 1121165 = 420437) (by norm_num)
theorem B629689 : Blo 495792 629689 := bbase (se 2 (by rfl) ⟨236133, by rfl⟩ : syracuseStep 629689 = 472267) (by norm_num)
theorem B1121237 : Blo 495792 1121237 := bbase (se 7 (by rfl) ⟨13139, by rfl⟩ : syracuseStep 1121237 = 26279) (by norm_num)
theorem B1416197 : Blo 495792 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B629785 : Blo 495792 629785 := bbase (se 2 (by rfl) ⟨236169, by rfl⟩ : syracuseStep 629785 = 472339) (by norm_num)
theorem B1121309 : Blo 495792 1121309 := bbase (se 3 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 1121309 = 420491) (by norm_num)
theorem B1678373 : Blo 495792 1678373 := bbase (se 4 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 1678373 = 314695) (by norm_num)
theorem B1121381 : Blo 495792 1121381 := bbase (se 4 (by rfl) ⟨105129, by rfl⟩ : syracuseStep 1121381 = 210259) (by norm_num)
theorem B1121453 : Blo 495792 1121453 := bbase (se 3 (by rfl) ⟨210272, by rfl⟩ : syracuseStep 1121453 = 420545) (by norm_num)
theorem B629957 : Blo 495792 629957 := bbase (se 4 (by rfl) ⟨59058, by rfl⟩ : syracuseStep 629957 = 118117) (by norm_num)
theorem B531689 : Blo 495792 531689 := bbase (se 2 (by rfl) ⟨199383, by rfl⟩ : syracuseStep 531689 = 398767) (by norm_num)
theorem B3775733 : Blo 495792 3775733 := bbase (se 5 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 3775733 = 353975) (by norm_num)
theorem B1416437 : Blo 495792 1416437 := bbase (se 5 (by rfl) ⟨66395, by rfl⟩ : syracuseStep 1416437 = 132791) (by norm_num)
theorem B1121525 : Blo 495792 1121525 := bbase (se 5 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 1121525 = 105143) (by norm_num)
theorem B630013 : Blo 495792 630013 := bbase (se 3 (by rfl) ⟨118127, by rfl⟩ : syracuseStep 630013 = 236255) (by norm_num)
theorem B1121597 : Blo 495792 1121597 := bbase (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) (by norm_num)
theorem B630109 : Blo 495792 630109 := bbase (se 3 (by rfl) ⟨118145, by rfl⟩ : syracuseStep 630109 = 236291) (by norm_num)
theorem B1121669 : Blo 495792 1121669 := bbase (se 4 (by rfl) ⟨105156, by rfl⟩ : syracuseStep 1121669 = 210313) (by norm_num)
theorem B957853 : Blo 495792 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B1416629 : Blo 495792 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B1121741 : Blo 495792 1121741 := bbase (se 3 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 1121741 = 420653) (by norm_num)
theorem B1678805 : Blo 495792 1678805 := bbase (se 7 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 1678805 = 39347) (by norm_num)
theorem B531937 : Blo 495792 531937 := bbase (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) (by norm_num)
theorem B630281 : Blo 495792 630281 := bbase (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) (by norm_num)
theorem B1121813 : Blo 495792 1121813 := bbase (se 6 (by rfl) ⟨26292, by rfl⟩ : syracuseStep 1121813 = 52585) (by norm_num)
theorem B630337 : Blo 495792 630337 := bbase (se 2 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 630337 = 472753) (by norm_num)
theorem B794189 : Blo 495792 794189 := bbase (se 3 (by rfl) ⟨148910, by rfl⟩ : syracuseStep 794189 = 297821) (by norm_num)
theorem B1121885 : Blo 495792 1121885 := bbase (se 3 (by rfl) ⟨210353, by rfl⟩ : syracuseStep 1121885 = 420707) (by norm_num)
theorem B630433 : Blo 495792 630433 := bbase (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) (by norm_num)
theorem B1121957 : Blo 495792 1121957 := bbase (se 4 (by rfl) ⟨105183, by rfl⟩ : syracuseStep 1121957 = 210367) (by norm_num)
theorem B1122029 : Blo 495792 1122029 := bbase (se 3 (by rfl) ⟨210380, by rfl⟩ : syracuseStep 1122029 = 420761) (by norm_num)
theorem B1122101 : Blo 495792 1122101 := bbase (se 5 (by rfl) ⟨52598, by rfl⟩ : syracuseStep 1122101 = 105197) (by norm_num)
theorem B630605 : Blo 495792 630605 := bbase (se 3 (by rfl) ⟨118238, by rfl⟩ : syracuseStep 630605 = 236477) (by norm_num)
theorem B1122173 : Blo 495792 1122173 := bbase (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) (by norm_num)
theorem B1679237 : Blo 495792 1679237 := bbase (se 4 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 1679237 = 314857) (by norm_num)
theorem B630661 : Blo 495792 630661 := bbase (se 4 (by rfl) ⟨59124, by rfl⟩ : syracuseStep 630661 = 118249) (by norm_num)
theorem B532381 : Blo 495792 532381 := bbase (se 3 (by rfl) ⟨99821, by rfl⟩ : syracuseStep 532381 = 199643) (by norm_num)
theorem B1122245 : Blo 495792 1122245 := bbase (se 4 (by rfl) ⟨105210, by rfl⟩ : syracuseStep 1122245 = 210421) (by norm_num)
theorem B2826197 : Blo 495792 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B532441 : Blo 495792 532441 := bbase (se 2 (by rfl) ⟨199665, by rfl⟩ : syracuseStep 532441 = 399331) (by norm_num)
theorem B630757 : Blo 495792 630757 := bbase (se 4 (by rfl) ⟨59133, by rfl⟩ : syracuseStep 630757 = 118267) (by norm_num)
theorem B598025 : Blo 495792 598025 := bbase (se 2 (by rfl) ⟨224259, by rfl⟩ : syracuseStep 598025 = 448519) (by norm_num)
theorem B1122317 : Blo 495792 1122317 := bbase (se 3 (by rfl) ⟨210434, by rfl⟩ : syracuseStep 1122317 = 420869) (by norm_num)
theorem B1122389 : Blo 495792 1122389 := bbase (se 8 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 1122389 = 13153) (by norm_num)
theorem B598141 : Blo 495792 598141 := bbase (se 3 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 598141 = 224303) (by norm_num)
theorem B630929 : Blo 495792 630929 := bbase (se 2 (by rfl) ⟨236598, by rfl⟩ : syracuseStep 630929 = 473197) (by norm_num)
theorem B1122461 : Blo 495792 1122461 := bbase (se 3 (by rfl) ⟨210461, by rfl⟩ : syracuseStep 1122461 = 420923) (by norm_num)
theorem B598213 : Blo 495792 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B630985 : Blo 495792 630985 := bbase (se 2 (by rfl) ⟨236619, by rfl⟩ : syracuseStep 630985 = 473239) (by norm_num)
theorem B1122533 : Blo 495792 1122533 := bbase (se 4 (by rfl) ⟨105237, by rfl⟩ : syracuseStep 1122533 = 210475) (by norm_num)
theorem B1515797 : Blo 495792 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B532757 : Blo 495792 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B631081 : Blo 495792 631081 := bbase (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) (by norm_num)
theorem B1122605 : Blo 495792 1122605 := bbase (se 3 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 1122605 = 420977) (by norm_num)
theorem B1679669 : Blo 495792 1679669 := bbase (se 5 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 1679669 = 157469) (by norm_num)
theorem B598333 : Blo 495792 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B1122677 : Blo 495792 1122677 := bbase (se 5 (by rfl) ⟨52625, by rfl⟩ : syracuseStep 1122677 = 105251) (by norm_num)
theorem B1417621 : Blo 495792 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B1122749 : Blo 495792 1122749 := bbase (se 3 (by rfl) ⟨210515, by rfl⟩ : syracuseStep 1122749 = 421031) (by norm_num)
theorem B631253 : Blo 495792 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B1122821 : Blo 495792 1122821 := bbase (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) (by norm_num)
theorem B631309 : Blo 495792 631309 := bbase (se 3 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 631309 = 236741) (by norm_num)
theorem B1122893 : Blo 495792 1122893 := bbase (se 3 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 1122893 = 421085) (by norm_num)
theorem B6824533 : Blo 495792 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B893549 : Blo 495792 893549 := bbase (se 3 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 893549 = 335081) (by norm_num)
theorem B631405 : Blo 495792 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B1122965 : Blo 495792 1122965 := bbase (se 6 (by rfl) ⟨26319, by rfl⟩ : syracuseStep 1122965 = 52639) (by norm_num)
theorem B893629 : Blo 495792 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B598717 : Blo 495792 598717 := bbase (se 3 (by rfl) ⟨112259, by rfl⟩ : syracuseStep 598717 = 224519) (by norm_num)
theorem B533201 : Blo 495792 533201 := bbase (se 2 (by rfl) ⟨199950, by rfl⟩ : syracuseStep 533201 = 399901) (by norm_num)
theorem B1123037 : Blo 495792 1123037 := bbase (se 3 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 1123037 = 421139) (by norm_num)
theorem B1680101 : Blo 495792 1680101 := bbase (se 4 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 1680101 = 315019) (by norm_num)
theorem B533261 : Blo 495792 533261 := bbase (se 3 (by rfl) ⟨99986, by rfl⟩ : syracuseStep 533261 = 199973) (by norm_num)
theorem B566033 : Blo 495792 566033 := bbase (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) (by norm_num)
theorem B631577 : Blo 495792 631577 := bbase (se 2 (by rfl) ⟨236841, by rfl⟩ : syracuseStep 631577 = 473683) (by norm_num)
theorem B1123109 : Blo 495792 1123109 := bbase (se 4 (by rfl) ⟨105291, by rfl⟩ : syracuseStep 1123109 = 210583) (by norm_num)
theorem B631633 : Blo 495792 631633 := bbase (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) (by norm_num)
theorem B1123181 : Blo 495792 1123181 := bbase (se 3 (by rfl) ⟨210596, by rfl⟩ : syracuseStep 1123181 = 421193) (by norm_num)
theorem B533389 : Blo 495792 533389 := bbase (se 3 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 533389 = 200021) (by norm_num)
theorem B631729 : Blo 495792 631729 := bbase (se 2 (by rfl) ⟨236898, by rfl⟩ : syracuseStep 631729 = 473797) (by norm_num)
theorem B1123253 : Blo 495792 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B1123325 : Blo 495792 1123325 := bbase (se 3 (by rfl) ⟨210623, by rfl⟩ : syracuseStep 1123325 = 421247) (by norm_num)
theorem B795701 : Blo 495792 795701 := bbase (se 5 (by rfl) ⟨37298, by rfl⟩ : syracuseStep 795701 = 74597) (by norm_num)
theorem B1123397 : Blo 495792 1123397 := bbase (se 4 (by rfl) ⟨105318, by rfl⟩ : syracuseStep 1123397 = 210637) (by norm_num)
theorem B631901 : Blo 495792 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B1123469 : Blo 495792 1123469 := bbase (se 3 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 1123469 = 421301) (by norm_num)
theorem B1680533 : Blo 495792 1680533 := bbase (se 6 (by rfl) ⟨39387, by rfl⟩ : syracuseStep 1680533 = 78775) (by norm_num)
theorem B631957 : Blo 495792 631957 := bbase (se 6 (by rfl) ⟨14811, by rfl⟩ : syracuseStep 631957 = 29623) (by norm_num)
theorem B795829 : Blo 495792 795829 := bbase (se 5 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 795829 = 74609) (by norm_num)
theorem B828613 : Blo 495792 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B9086165 : Blo 495792 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B1123541 : Blo 495792 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B632053 : Blo 495792 632053 := bbase (se 5 (by rfl) ⟨29627, by rfl⟩ : syracuseStep 632053 = 59255) (by norm_num)
theorem B1123613 : Blo 495792 1123613 := bbase (se 3 (by rfl) ⟨210677, by rfl⟩ : syracuseStep 1123613 = 421355) (by norm_num)
theorem B566617 : Blo 495792 566617 := bbase (se 2 (by rfl) ⟨212481, by rfl⟩ : syracuseStep 566617 = 424963) (by norm_num)
theorem B1123685 : Blo 495792 1123685 := bbase (se 4 (by rfl) ⟨105345, by rfl⟩ : syracuseStep 1123685 = 210691) (by norm_num)
theorem B599405 : Blo 495792 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B632225 : Blo 495792 632225 := bbase (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) (by norm_num)
theorem B1123757 : Blo 495792 1123757 := bbase (se 3 (by rfl) ⟨210704, by rfl⟩ : syracuseStep 1123757 = 421409) (by norm_num)
theorem B4793813 : Blo 495792 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B632281 : Blo 495792 632281 := bbase (se 2 (by rfl) ⟨237105, by rfl⟩ : syracuseStep 632281 = 474211) (by norm_num)
theorem B1418725 : Blo 495792 1418725 := bbase (se 4 (by rfl) ⟨133005, by rfl⟩ : syracuseStep 1418725 = 266011) (by norm_num)
theorem B1123829 : Blo 495792 1123829 := bbase (se 5 (by rfl) ⟨52679, by rfl⟩ : syracuseStep 1123829 = 105359) (by norm_num)
theorem B632377 : Blo 495792 632377 := bbase (se 2 (by rfl) ⟨237141, by rfl⟩ : syracuseStep 632377 = 474283) (by norm_num)
theorem B1123901 : Blo 495792 1123901 := bbase (se 3 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 1123901 = 421463) (by norm_num)
theorem B1680965 : Blo 495792 1680965 := bbase (se 4 (by rfl) ⟨157590, by rfl⟩ : syracuseStep 1680965 = 315181) (by norm_num)
theorem B1123973 : Blo 495792 1123973 := bbase (se 4 (by rfl) ⟨105372, by rfl⟩ : syracuseStep 1123973 = 210745) (by norm_num)
theorem B1255085 : Blo 495792 1255085 := bbase (se 3 (by rfl) ⟨235328, by rfl⟩ : syracuseStep 1255085 = 470657) (by norm_num)
theorem B1124045 : Blo 495792 1124045 := bbase (se 3 (by rfl) ⟨210758, by rfl⟩ : syracuseStep 1124045 = 421517) (by norm_num)
theorem B632549 : Blo 495792 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B1910533 : Blo 495792 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B1124117 : Blo 495792 1124117 := bbase (se 6 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 1124117 = 52693) (by norm_num)
theorem B567073 : Blo 495792 567073 := bbase (se 2 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 567073 = 425305) (by norm_num)
theorem B4237109 : Blo 495792 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B1124189 : Blo 495792 1124189 := bbase (se 3 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 1124189 = 421571) (by norm_num)
theorem B1255277 : Blo 495792 1255277 := bbase (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) (by norm_num)
theorem B1124261 : Blo 495792 1124261 := bbase (se 4 (by rfl) ⟨105399, by rfl⟩ : syracuseStep 1124261 = 210799) (by norm_num)
theorem B600005 : Blo 495792 600005 := bbase (se 4 (by rfl) ⟨56250, by rfl⟩ : syracuseStep 600005 = 112501) (by norm_num)
theorem B1124333 : Blo 495792 1124333 := bbase (se 3 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 1124333 = 421625) (by norm_num)
theorem B1681397 : Blo 495792 1681397 := bbase (se 5 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 1681397 = 157631) (by norm_num)
theorem B1124405 : Blo 495792 1124405 := bbase (se 5 (by rfl) ⟨52706, by rfl⟩ : syracuseStep 1124405 = 105413) (by norm_num)
theorem B1124477 : Blo 495792 1124477 := bbase (se 3 (by rfl) ⟨210839, by rfl⟩ : syracuseStep 1124477 = 421679) (by norm_num)
theorem B1255621 : Blo 495792 1255621 := bbase (se 4 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 1255621 = 235429) (by norm_num)
theorem B600313 : Blo 495792 600313 := bbase (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) (by norm_num)
theorem B1255733 : Blo 495792 1255733 := bbase (se 5 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 1255733 = 117725) (by norm_num)
theorem B600409 : Blo 495792 600409 := bbase (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) (by norm_num)
theorem B1681829 : Blo 495792 1681829 := bbase (se 4 (by rfl) ⟨157671, by rfl⟩ : syracuseStep 1681829 = 315343) (by norm_num)
theorem B1255925 : Blo 495792 1255925 := bbase (se 5 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 1255925 = 117743) (by norm_num)
theorem B2599445 : Blo 495792 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B797213 : Blo 495792 797213 := bbase (se 3 (by rfl) ⟨149477, by rfl⟩ : syracuseStep 797213 = 298955) (by norm_num)
theorem B1059389 : Blo 495792 1059389 := bbase (se 3 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 1059389 = 397271) (by norm_num)
theorem B3189365 : Blo 495792 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B1256269 : Blo 495792 1256269 := bbase (se 3 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 1256269 = 471101) (by norm_num)
theorem B1682261 : Blo 495792 1682261 := bbase (se 9 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 1682261 = 9857) (by norm_num)
theorem B1256381 : Blo 495792 1256381 := bbase (se 3 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 1256381 = 471143) (by norm_num)
theorem B1420229 : Blo 495792 1420229 := bbase (se 4 (by rfl) ⟨133146, by rfl⟩ : syracuseStep 1420229 = 266293) (by norm_num)
theorem B568333 : Blo 495792 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B1256573 : Blo 495792 1256573 := bbase (se 3 (by rfl) ⟨235607, by rfl⟩ : syracuseStep 1256573 = 471215) (by norm_num)
theorem B1682693 : Blo 495792 1682693 := bbase (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) (by norm_num)
theorem B1060141 : Blo 495792 1060141 := bbase (se 3 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 1060141 = 397553) (by norm_num)
theorem B1060285 : Blo 495792 1060285 := bbase (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) (by norm_num)
theorem B798149 : Blo 495792 798149 := bbase (se 4 (by rfl) ⟨74826, by rfl⟩ : syracuseStep 798149 = 149653) (by norm_num)
theorem B1256917 : Blo 495792 1256917 := bbase (se 7 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 1256917 = 29459) (by norm_num)
theorem B5385685 : Blo 495792 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B14396885 : Blo 495792 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B1191437 : Blo 495792 1191437 := bbase (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) (by norm_num)
theorem B1257029 : Blo 495792 1257029 := bbase (se 4 (by rfl) ⟨117846, by rfl⟩ : syracuseStep 1257029 = 235693) (by norm_num)
theorem B1683125 : Blo 495792 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B1257221 : Blo 495792 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B1060661 : Blo 495792 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B2273093 : Blo 495792 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B798797 : Blo 495792 798797 := bbase (se 3 (by rfl) ⟨149774, by rfl⟩ : syracuseStep 798797 = 299549) (by norm_num)
theorem B1257565 : Blo 495792 1257565 := bbase (se 3 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 1257565 = 471587) (by norm_num)
theorem B1683557 : Blo 495792 1683557 := bbase (se 4 (by rfl) ⟨157833, by rfl⟩ : syracuseStep 1683557 = 315667) (by norm_num)
theorem B2044037 : Blo 495792 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B1061029 : Blo 495792 1061029 := bbase (se 4 (by rfl) ⟨99471, by rfl⟩ : syracuseStep 1061029 = 198943) (by norm_num)
theorem B536749 : Blo 495792 536749 := bbase (se 3 (by rfl) ⟨100640, by rfl⟩ : syracuseStep 536749 = 201281) (by norm_num)
theorem B1257677 : Blo 495792 1257677 := bbase (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) (by norm_num)
theorem B504041 : Blo 495792 504041 := bbase (se 2 (by rfl) ⟨189015, by rfl⟩ : syracuseStep 504041 = 378031) (by norm_num)
theorem B2011493 : Blo 495792 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1257869 : Blo 495792 1257869 := bbase (se 3 (by rfl) ⟨235850, by rfl⟩ : syracuseStep 1257869 = 471701) (by norm_num)
theorem B1421813 : Blo 495792 1421813 := bbase (se 5 (by rfl) ⟨66647, by rfl⟩ : syracuseStep 1421813 = 133295) (by norm_num)
theorem B1683989 : Blo 495792 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B897701 : Blo 495792 897701 := bbase (se 4 (by rfl) ⟨84159, by rfl⟩ : syracuseStep 897701 = 168319) (by norm_num)
theorem B1258213 : Blo 495792 1258213 := bbase (se 4 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 1258213 = 235915) (by norm_num)
theorem B504625 : Blo 495792 504625 := bbase (se 2 (by rfl) ⟨189234, by rfl⟩ : syracuseStep 504625 = 378469) (by norm_num)
theorem B1258325 : Blo 495792 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B1684421 : Blo 495792 1684421 := bbase (se 4 (by rfl) ⟨157914, by rfl⟩ : syracuseStep 1684421 = 315829) (by norm_num)
theorem B1258517 : Blo 495792 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B799789 : Blo 495792 799789 := bbase (se 3 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 799789 = 299921) (by norm_num)
theorem B504973 : Blo 495792 504973 := bbase (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) (by norm_num)
theorem B1422485 : Blo 495792 1422485 := bbase (se 6 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 1422485 = 66679) (by norm_num)
theorem B5649749 : Blo 495792 5649749 := bbase (se 13 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 5649749 = 2069) (by norm_num)
theorem B1258861 : Blo 495792 1258861 := bbase (se 3 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 1258861 = 472073) (by norm_num)
theorem B1684853 : Blo 495792 1684853 := bbase (se 5 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 1684853 = 157955) (by norm_num)
theorem B1258973 : Blo 495792 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B800237 : Blo 495792 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B1422917 : Blo 495792 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B1062533 : Blo 495792 1062533 := bbase (se 4 (by rfl) ⟨99612, by rfl⟩ : syracuseStep 1062533 = 199225) (by norm_num)
theorem B1259165 : Blo 495792 1259165 := bbase (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) (by norm_num)
theorem B800437 : Blo 495792 800437 := bbase (se 5 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 800437 = 75041) (by norm_num)
theorem B1062677 : Blo 495792 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B1685285 : Blo 495792 1685285 := bbase (se 4 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 1685285 = 315991) (by norm_num)
theorem B505801 : Blo 495792 505801 := bbase (se 2 (by rfl) ⟨189675, by rfl⟩ : syracuseStep 505801 = 379351) (by norm_num)
theorem B1259509 : Blo 495792 1259509 := bbase (se 5 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 1259509 = 118079) (by norm_num)
theorem B3586133 : Blo 495792 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B899165 : Blo 495792 899165 := bbase (se 3 (by rfl) ⟨168593, by rfl⟩ : syracuseStep 899165 = 337187) (by norm_num)
theorem B1259621 : Blo 495792 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B2275445 : Blo 495792 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B1063037 : Blo 495792 1063037 := bbase (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) (by norm_num)
theorem B2865365 : Blo 495792 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1685717 : Blo 495792 1685717 := bbase (se 7 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 1685717 = 39509) (by norm_num)
theorem B1194205 : Blo 495792 1194205 := bbase (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) (by norm_num)
theorem B3029237 : Blo 495792 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B1259813 : Blo 495792 1259813 := bbase (se 4 (by rfl) ⟨118107, by rfl⟩ : syracuseStep 1259813 = 236215) (by norm_num)
theorem B670141 : Blo 495792 670141 := bbase (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) (by norm_num)
theorem B1194581 : Blo 495792 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B1260157 : Blo 495792 1260157 := bbase (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) (by norm_num)
theorem B1686149 : Blo 495792 1686149 := bbase (se 4 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 1686149 = 316153) (by norm_num)
theorem B1260269 : Blo 495792 1260269 := bbase (se 3 (by rfl) ⟨236300, by rfl⟩ : syracuseStep 1260269 = 472601) (by norm_num)
theorem B1882885 : Blo 495792 1882885 := bbase (se 4 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 1882885 = 353041) (by norm_num)
theorem B637733 : Blo 495792 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B3783509 : Blo 495792 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B1260461 : Blo 495792 1260461 := bbase (se 3 (by rfl) ⟨236336, by rfl⟩ : syracuseStep 1260461 = 472673) (by norm_num)
theorem B1063925 : Blo 495792 1063925 := bbase (se 5 (by rfl) ⟨49871, by rfl⟩ : syracuseStep 1063925 = 99743) (by norm_num)
theorem B1195013 : Blo 495792 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B1883189 : Blo 495792 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B1686581 : Blo 495792 1686581 := bbase (se 5 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 1686581 = 158117) (by norm_num)
theorem B670789 : Blo 495792 670789 := bbase (se 4 (by rfl) ⟨62886, by rfl⟩ : syracuseStep 670789 = 125773) (by norm_num)
theorem B900325 : Blo 495792 900325 := bbase (se 4 (by rfl) ⟨84405, by rfl⟩ : syracuseStep 900325 = 168811) (by norm_num)
theorem B1064173 : Blo 495792 1064173 := bbase (se 3 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 1064173 = 399065) (by norm_num)
theorem B1260805 : Blo 495792 1260805 := bbase (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) (by norm_num)
theorem B1260917 : Blo 495792 1260917 := bbase (se 5 (by rfl) ⟨59105, by rfl⟩ : syracuseStep 1260917 = 118211) (by norm_num)
theorem B900629 : Blo 495792 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B1261109 : Blo 495792 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B1195589 : Blo 495792 1195589 := bbase (se 4 (by rfl) ⟨112086, by rfl⟩ : syracuseStep 1195589 = 224173) (by norm_num)
theorem B638533 : Blo 495792 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B2014901 : Blo 495792 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B1064677 : Blo 495792 1064677 := bbase (se 4 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 1064677 = 199627) (by norm_num)
theorem B2834261 : Blo 495792 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B606089 : Blo 495792 606089 := bbase (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) (by norm_num)
theorem B1261453 : Blo 495792 1261453 := bbase (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) (by norm_num)
theorem B540629 : Blo 495792 540629 := bbase (se 7 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 540629 = 12671) (by norm_num)
theorem B4833269 : Blo 495792 4833269 := bbase (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) (by norm_num)
theorem B1261565 : Blo 495792 1261565 := bbase (se 3 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 1261565 = 473087) (by norm_num)
theorem B1261757 : Blo 495792 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B1589557 : Blo 495792 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1262101 : Blo 495792 1262101 := bbase (se 6 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 1262101 = 59161) (by norm_num)
theorem B3195413 : Blo 495792 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B1131101 : Blo 495792 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B1065565 : Blo 495792 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B1262213 : Blo 495792 1262213 := bbase (se 4 (by rfl) ⟨118332, by rfl⟩ : syracuseStep 1262213 = 236665) (by norm_num)
theorem B1262405 : Blo 495792 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B672605 : Blo 495792 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B2835445 : Blo 495792 2835445 := bbase (se 5 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 2835445 = 265823) (by norm_num)
theorem B967717 : Blo 495792 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B836669 : Blo 495792 836669 := bbase (se 3 (by rfl) ⟨156875, by rfl⟩ : syracuseStep 836669 = 313751) (by norm_num)
theorem B1066061 : Blo 495792 1066061 := bbase (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) (by norm_num)
theorem B1885301 : Blo 495792 1885301 := bbase (se 5 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 1885301 = 176747) (by norm_num)
theorem B2016389 : Blo 495792 2016389 := bbase (se 4 (by rfl) ⟨189036, by rfl⟩ : syracuseStep 2016389 = 378073) (by norm_num)
theorem B1262749 : Blo 495792 1262749 := bbase (se 3 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 1262749 = 473531) (by norm_num)
theorem B3884213 : Blo 495792 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B836797 : Blo 495792 836797 := bbase (se 3 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 836797 = 313799) (by norm_num)
theorem B1262861 : Blo 495792 1262861 := bbase (se 3 (by rfl) ⟨236786, by rfl⟩ : syracuseStep 1262861 = 473573) (by norm_num)
theorem B836885 : Blo 495792 836885 := bbase (se 6 (by rfl) ⟨19614, by rfl⟩ : syracuseStep 836885 = 39229) (by norm_num)
theorem B837013 : Blo 495792 837013 := bbase (se 6 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 837013 = 39235) (by norm_num)
theorem B1885589 : Blo 495792 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B1263053 : Blo 495792 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B837101 : Blo 495792 837101 := bbase (se 3 (by rfl) ⟨156956, by rfl⟩ : syracuseStep 837101 = 313913) (by norm_num)
theorem B837229 : Blo 495792 837229 := bbase (se 3 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 837229 = 313961) (by norm_num)
theorem B837317 : Blo 495792 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B673525 : Blo 495792 673525 := bbase (se 5 (by rfl) ⟨31571, by rfl⟩ : syracuseStep 673525 = 63143) (by norm_num)
theorem B706333 : Blo 495792 706333 := bbase (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) (by norm_num)
theorem B1263397 : Blo 495792 1263397 := bbase (se 4 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 1263397 = 236887) (by norm_num)
theorem B837445 : Blo 495792 837445 := bbase (se 4 (by rfl) ⟨78510, by rfl⟩ : syracuseStep 837445 = 157021) (by norm_num)
theorem B1263509 : Blo 495792 1263509 := bbase (se 6 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 1263509 = 59227) (by norm_num)
theorem B837533 : Blo 495792 837533 := bbase (se 3 (by rfl) ⟨157037, by rfl⟩ : syracuseStep 837533 = 314075) (by norm_num)
theorem B1066949 : Blo 495792 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B837661 : Blo 495792 837661 := bbase (se 3 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 837661 = 314123) (by norm_num)
theorem B1067069 : Blo 495792 1067069 := bbase (se 3 (by rfl) ⟨200075, by rfl⟩ : syracuseStep 1067069 = 400151) (by norm_num)
theorem B1198165 : Blo 495792 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B7784533 : Blo 495792 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B1263701 : Blo 495792 1263701 := bbase (se 8 (by rfl) ⟨7404, by rfl⟩ : syracuseStep 1263701 = 14809) (by norm_num)
theorem B837749 : Blo 495792 837749 := bbase (se 5 (by rfl) ⟨39269, by rfl⟩ : syracuseStep 837749 = 78539) (by norm_num)
theorem B837877 : Blo 495792 837877 := bbase (se 5 (by rfl) ⟨39275, by rfl⟩ : syracuseStep 837877 = 78551) (by norm_num)
theorem B674077 : Blo 495792 674077 := bbase (se 3 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 674077 = 252779) (by norm_num)
theorem B837965 : Blo 495792 837965 := bbase (se 3 (by rfl) ⟨157118, by rfl⟩ : syracuseStep 837965 = 314237) (by norm_num)
theorem B674141 : Blo 495792 674141 := bbase (se 3 (by rfl) ⟨126401, by rfl⟩ : syracuseStep 674141 = 252803) (by norm_num)
theorem B706925 : Blo 495792 706925 := bbase (se 3 (by rfl) ⟨132548, by rfl⟩ : syracuseStep 706925 = 265097) (by norm_num)
theorem B1264045 : Blo 495792 1264045 := bbase (se 3 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 1264045 = 474017) (by norm_num)
theorem B1296821 : Blo 495792 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B707005 : Blo 495792 707005 := bbase (se 3 (by rfl) ⟨132563, by rfl⟩ : syracuseStep 707005 = 265127) (by norm_num)
theorem B838093 : Blo 495792 838093 := bbase (se 3 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 838093 = 314285) (by norm_num)
theorem B1264157 : Blo 495792 1264157 := bbase (se 3 (by rfl) ⟨237029, by rfl⟩ : syracuseStep 1264157 = 474059) (by norm_num)
theorem B838181 : Blo 495792 838181 := bbase (se 4 (by rfl) ⟨78579, by rfl⟩ : syracuseStep 838181 = 157159) (by norm_num)
theorem B707125 : Blo 495792 707125 := bbase (se 5 (by rfl) ⟨33146, by rfl⟩ : syracuseStep 707125 = 66293) (by norm_num)
theorem B1886773 : Blo 495792 1886773 := bbase (se 5 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 1886773 = 176885) (by norm_num)
theorem B707221 : Blo 495792 707221 := bbase (se 6 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 707221 = 33151) (by norm_num)
theorem B838309 : Blo 495792 838309 := bbase (se 4 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 838309 = 157183) (by norm_num)
theorem B674509 : Blo 495792 674509 := bbase (se 3 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 674509 = 252941) (by norm_num)
theorem B1264349 : Blo 495792 1264349 := bbase (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) (by norm_num)
theorem B838397 : Blo 495792 838397 := bbase (se 3 (by rfl) ⟨157199, by rfl⟩ : syracuseStep 838397 = 314399) (by norm_num)
theorem B1887077 : Blo 495792 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B838525 : Blo 495792 838525 := bbase (se 3 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 838525 = 314447) (by norm_num)
theorem B674725 : Blo 495792 674725 := bbase (se 4 (by rfl) ⟨63255, by rfl⟩ : syracuseStep 674725 = 126511) (by norm_num)
theorem B2837429 : Blo 495792 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B576437 : Blo 495792 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B838613 : Blo 495792 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B2870261 : Blo 495792 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1264693 : Blo 495792 1264693 := bbase (se 5 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 1264693 = 118565) (by norm_num)
theorem B674893 : Blo 495792 674893 := bbase (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) (by norm_num)
theorem B838741 : Blo 495792 838741 := bbase (se 8 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 838741 = 9829) (by norm_num)
theorem B674941 : Blo 495792 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B707717 : Blo 495792 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B1264805 : Blo 495792 1264805 := bbase (se 4 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 1264805 = 237151) (by norm_num)
theorem B838829 : Blo 495792 838829 := bbase (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) (by norm_num)
theorem B1199357 : Blo 495792 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B1592581 : Blo 495792 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B838957 : Blo 495792 838957 := bbase (se 3 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 838957 = 314609) (by norm_num)
theorem B1264997 : Blo 495792 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B839045 : Blo 495792 839045 := bbase (se 4 (by rfl) ⟨78660, by rfl⟩ : syracuseStep 839045 = 157321) (by norm_num)
theorem B1199549 : Blo 495792 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B839173 : Blo 495792 839173 := bbase (se 4 (by rfl) ⟨78672, by rfl⟩ : syracuseStep 839173 = 157345) (by norm_num)
theorem B839261 : Blo 495792 839261 := bbase (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) (by norm_num)
theorem B708269 : Blo 495792 708269 := bbase (se 3 (by rfl) ⟨132800, by rfl⟩ : syracuseStep 708269 = 265601) (by norm_num)
theorem B839389 : Blo 495792 839389 := bbase (se 3 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 839389 = 314771) (by norm_num)
theorem B577325 : Blo 495792 577325 := bbase (se 3 (by rfl) ⟨108248, by rfl⟩ : syracuseStep 577325 = 216497) (by norm_num)
theorem B839477 : Blo 495792 839477 := bbase (se 5 (by rfl) ⟨39350, by rfl⟩ : syracuseStep 839477 = 78701) (by norm_num)
theorem B4771669 : Blo 495792 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B839605 : Blo 495792 839605 := bbase (se 5 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 839605 = 78713) (by norm_num)
theorem B2510837 : Blo 495792 2510837 := bbase (se 5 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 2510837 = 235391) (by norm_num)
theorem B839693 : Blo 495792 839693 := bbase (se 3 (by rfl) ⟨157442, by rfl⟩ : syracuseStep 839693 = 314885) (by norm_num)
theorem B2871413 : Blo 495792 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B839821 : Blo 495792 839821 := bbase (se 3 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 839821 = 314933) (by norm_num)
theorem B839909 : Blo 495792 839909 := bbase (se 4 (by rfl) ⟨78741, by rfl⟩ : syracuseStep 839909 = 157483) (by norm_num)
theorem B840037 : Blo 495792 840037 := bbase (se 4 (by rfl) ⟨78753, by rfl⟩ : syracuseStep 840037 = 157507) (by norm_num)
theorem B709021 : Blo 495792 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B840125 : Blo 495792 840125 := bbase (se 3 (by rfl) ⟨157523, by rfl⟩ : syracuseStep 840125 = 315047) (by norm_num)
theorem B840253 : Blo 495792 840253 := bbase (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) (by norm_num)
theorem B840341 : Blo 495792 840341 := bbase (se 6 (by rfl) ⟨19695, by rfl⟩ : syracuseStep 840341 = 39391) (by norm_num)
theorem B840469 : Blo 495792 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B1299253 : Blo 495792 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B840557 : Blo 495792 840557 := bbase (se 3 (by rfl) ⟨157604, by rfl⟩ : syracuseStep 840557 = 315209) (by norm_num)
theorem B1889189 : Blo 495792 1889189 := bbase (se 4 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 1889189 = 354223) (by norm_num)
theorem B840685 : Blo 495792 840685 := bbase (se 3 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 840685 = 315257) (by norm_num)
theorem B840773 : Blo 495792 840773 := bbase (se 4 (by rfl) ⟨78822, by rfl⟩ : syracuseStep 840773 = 157645) (by norm_num)
theorem B2839637 : Blo 495792 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B709813 : Blo 495792 709813 := bbase (se 5 (by rfl) ⟨33272, by rfl⟩ : syracuseStep 709813 = 66545) (by norm_num)
theorem B1889477 : Blo 495792 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B840901 : Blo 495792 840901 := bbase (se 4 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 840901 = 157669) (by norm_num)
theorem B2512133 : Blo 495792 2512133 := bbase (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) (by norm_num)
theorem B840989 : Blo 495792 840989 := bbase (se 3 (by rfl) ⟨157685, by rfl⟩ : syracuseStep 840989 = 315371) (by norm_num)
theorem B841117 : Blo 495792 841117 := bbase (se 3 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 841117 = 315419) (by norm_num)
theorem B1136117 : Blo 495792 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B841205 : Blo 495792 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B710149 : Blo 495792 710149 := bbase (se 4 (by rfl) ⟨66576, by rfl⟩ : syracuseStep 710149 = 133153) (by norm_num)
theorem B4052501 : Blo 495792 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B4249205 : Blo 495792 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B841333 : Blo 495792 841333 := bbase (se 5 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 841333 = 78875) (by norm_num)
theorem B841421 : Blo 495792 841421 := bbase (se 3 (by rfl) ⟨157766, by rfl⟩ : syracuseStep 841421 = 315533) (by norm_num)
theorem B710365 : Blo 495792 710365 := bbase (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) (by norm_num)
theorem B841549 : Blo 495792 841549 := bbase (se 3 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 841549 = 315581) (by norm_num)
theorem B841637 : Blo 495792 841637 := bbase (se 4 (by rfl) ⟨78903, by rfl⟩ : syracuseStep 841637 = 157807) (by norm_num)
theorem B3397621 : Blo 495792 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B1366021 : Blo 495792 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B841765 : Blo 495792 841765 := bbase (se 4 (by rfl) ⟨78915, by rfl⟩ : syracuseStep 841765 = 157831) (by norm_num)
theorem B710741 : Blo 495792 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B1595477 : Blo 495792 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B841853 : Blo 495792 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1136773 : Blo 495792 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B3037333 : Blo 495792 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B841981 : Blo 495792 841981 := bbase (se 3 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 841981 = 315743) (by norm_num)
theorem B743693 : Blo 495792 743693 := bbase (se 3 (by rfl) ⟨139442, by rfl⟩ : syracuseStep 743693 = 278885) (by norm_num)
theorem B1005853 : Blo 495792 1005853 := bbase (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) (by norm_num)
theorem B743717 : Blo 495792 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B809261 : Blo 495792 809261 := bbase (se 3 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 809261 = 303473) (by norm_num)
theorem B743741 : Blo 495792 743741 := bbase (se 3 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 743741 = 278903) (by norm_num)
theorem B743765 : Blo 495792 743765 := bbase (se 10 (by rfl) ⟨1089, by rfl⟩ : syracuseStep 743765 = 2179) (by norm_num)
theorem B842069 : Blo 495792 842069 := bbase (se 10 (by rfl) ⟨1233, by rfl⟩ : syracuseStep 842069 = 2467) (by norm_num)
theorem B1890661 : Blo 495792 1890661 := bbase (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) (by norm_num)
theorem B743789 : Blo 495792 743789 := bbase (se 3 (by rfl) ⟨139460, by rfl⟩ : syracuseStep 743789 = 278921) (by norm_num)
theorem B743813 : Blo 495792 743813 := bbase (se 4 (by rfl) ⟨69732, by rfl⟩ : syracuseStep 743813 = 139465) (by norm_num)
theorem B743837 : Blo 495792 743837 := bbase (se 3 (by rfl) ⟨139469, by rfl⟩ : syracuseStep 743837 = 278939) (by norm_num)
theorem B743861 : Blo 495792 743861 := bbase (se 5 (by rfl) ⟨34868, by rfl⟩ : syracuseStep 743861 = 69737) (by norm_num)
theorem B1431989 : Blo 495792 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B3791285 : Blo 495792 3791285 := bbase (se 5 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 3791285 = 355433) (by norm_num)
theorem B743885 : Blo 495792 743885 := bbase (se 3 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 743885 = 278957) (by norm_num)
theorem B842197 : Blo 495792 842197 := bbase (se 7 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 842197 = 19739) (by norm_num)
theorem B743909 : Blo 495792 743909 := bbase (se 4 (by rfl) ⟨69741, by rfl⟩ : syracuseStep 743909 = 139483) (by norm_num)
theorem B743933 : Blo 495792 743933 := bbase (se 3 (by rfl) ⟨139487, by rfl⟩ : syracuseStep 743933 = 278975) (by norm_num)
theorem B743957 : Blo 495792 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B2513429 : Blo 495792 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B743981 : Blo 495792 743981 := bbase (se 3 (by rfl) ⟨139496, by rfl⟩ : syracuseStep 743981 = 278993) (by norm_num)
theorem B842285 : Blo 495792 842285 := bbase (se 3 (by rfl) ⟨157928, by rfl⟩ : syracuseStep 842285 = 315857) (by norm_num)
theorem B744005 : Blo 495792 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B744029 : Blo 495792 744029 := bbase (se 3 (by rfl) ⟨139505, by rfl⟩ : syracuseStep 744029 = 279011) (by norm_num)
theorem B744053 : Blo 495792 744053 := bbase (se 5 (by rfl) ⟨34877, by rfl⟩ : syracuseStep 744053 = 69755) (by norm_num)
theorem B744077 : Blo 495792 744077 := bbase (se 3 (by rfl) ⟨139514, by rfl⟩ : syracuseStep 744077 = 279029) (by norm_num)
theorem B1890965 : Blo 495792 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B744101 : Blo 495792 744101 := bbase (se 4 (by rfl) ⟨69759, by rfl⟩ : syracuseStep 744101 = 139519) (by norm_num)
theorem B842413 : Blo 495792 842413 := bbase (se 3 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 842413 = 315905) (by norm_num)
theorem B744125 : Blo 495792 744125 := bbase (se 3 (by rfl) ⟨139523, by rfl⟩ : syracuseStep 744125 = 279047) (by norm_num)
theorem B744149 : Blo 495792 744149 := bbase (se 7 (by rfl) ⟨8720, by rfl⟩ : syracuseStep 744149 = 17441) (by norm_num)
theorem B744173 : Blo 495792 744173 := bbase (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) (by norm_num)
theorem B744197 : Blo 495792 744197 := bbase (se 4 (by rfl) ⟨69768, by rfl⟩ : syracuseStep 744197 = 139537) (by norm_num)
theorem B842501 : Blo 495792 842501 := bbase (se 4 (by rfl) ⟨78984, by rfl⟩ : syracuseStep 842501 = 157969) (by norm_num)
theorem B744221 : Blo 495792 744221 := bbase (se 3 (by rfl) ⟨139541, by rfl⟩ : syracuseStep 744221 = 279083) (by norm_num)
theorem B744245 : Blo 495792 744245 := bbase (se 5 (by rfl) ⟨34886, by rfl⟩ : syracuseStep 744245 = 69773) (by norm_num)
theorem B744269 : Blo 495792 744269 := bbase (se 3 (by rfl) ⟨139550, by rfl⟩ : syracuseStep 744269 = 279101) (by norm_num)
theorem B744293 : Blo 495792 744293 := bbase (se 4 (by rfl) ⟨69777, by rfl⟩ : syracuseStep 744293 = 139555) (by norm_num)
theorem B744317 : Blo 495792 744317 := bbase (se 3 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 744317 = 279119) (by norm_num)
theorem B842629 : Blo 495792 842629 := bbase (se 4 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 842629 = 157993) (by norm_num)
theorem B744341 : Blo 495792 744341 := bbase (se 6 (by rfl) ⟨17445, by rfl⟩ : syracuseStep 744341 = 34891) (by norm_num)
theorem B744365 : Blo 495792 744365 := bbase (se 3 (by rfl) ⟨139568, by rfl⟩ : syracuseStep 744365 = 279137) (by norm_num)
theorem B744389 : Blo 495792 744389 := bbase (se 4 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 744389 = 139573) (by norm_num)
theorem B744413 : Blo 495792 744413 := bbase (se 3 (by rfl) ⟨139577, by rfl⟩ : syracuseStep 744413 = 279155) (by norm_num)
theorem B842717 : Blo 495792 842717 := bbase (se 3 (by rfl) ⟨158009, by rfl⟩ : syracuseStep 842717 = 316019) (by norm_num)
theorem B1006573 : Blo 495792 1006573 := bbase (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) (by norm_num)
theorem B744437 : Blo 495792 744437 := bbase (se 5 (by rfl) ⟨34895, by rfl⟩ : syracuseStep 744437 = 69791) (by norm_num)
theorem B744461 : Blo 495792 744461 := bbase (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) (by norm_num)
theorem B744485 : Blo 495792 744485 := bbase (se 4 (by rfl) ⟨69795, by rfl⟩ : syracuseStep 744485 = 139591) (by norm_num)
theorem B744509 : Blo 495792 744509 := bbase (se 3 (by rfl) ⟨139595, by rfl⟩ : syracuseStep 744509 = 279191) (by norm_num)
theorem B744533 : Blo 495792 744533 := bbase (se 8 (by rfl) ⟨4362, by rfl⟩ : syracuseStep 744533 = 8725) (by norm_num)
theorem B842845 : Blo 495792 842845 := bbase (se 3 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 842845 = 316067) (by norm_num)
theorem B744557 : Blo 495792 744557 := bbase (se 3 (by rfl) ⟨139604, by rfl⟩ : syracuseStep 744557 = 279209) (by norm_num)
theorem B3398773 : Blo 495792 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B744581 : Blo 495792 744581 := bbase (se 4 (by rfl) ⟨69804, by rfl⟩ : syracuseStep 744581 = 139609) (by norm_num)
theorem B1137797 : Blo 495792 1137797 := bbase (se 4 (by rfl) ⟨106668, by rfl⟩ : syracuseStep 1137797 = 213337) (by norm_num)
theorem B744605 : Blo 495792 744605 := bbase (se 3 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 744605 = 279227) (by norm_num)
theorem B744629 : Blo 495792 744629 := bbase (se 5 (by rfl) ⟨34904, by rfl⟩ : syracuseStep 744629 = 69809) (by norm_num)
theorem B842933 : Blo 495792 842933 := bbase (se 5 (by rfl) ⟨39512, by rfl⟩ : syracuseStep 842933 = 79025) (by norm_num)
theorem B2579653 : Blo 495792 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B744653 : Blo 495792 744653 := bbase (se 3 (by rfl) ⟨139622, by rfl⟩ : syracuseStep 744653 = 279245) (by norm_num)
theorem B744677 : Blo 495792 744677 := bbase (se 4 (by rfl) ⟨69813, by rfl⟩ : syracuseStep 744677 = 139627) (by norm_num)
theorem B744701 : Blo 495792 744701 := bbase (se 3 (by rfl) ⟨139631, by rfl⟩ : syracuseStep 744701 = 279263) (by norm_num)
theorem B744725 : Blo 495792 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B1137941 : Blo 495792 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B744749 : Blo 495792 744749 := bbase (se 3 (by rfl) ⟨139640, by rfl⟩ : syracuseStep 744749 = 279281) (by norm_num)
theorem B843061 : Blo 495792 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B744773 : Blo 495792 744773 := bbase (se 4 (by rfl) ⟨69822, by rfl⟩ : syracuseStep 744773 = 139645) (by norm_num)
theorem B744797 : Blo 495792 744797 := bbase (se 3 (by rfl) ⟨139649, by rfl⟩ : syracuseStep 744797 = 279299) (by norm_num)
theorem B1596773 : Blo 495792 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B744821 : Blo 495792 744821 := bbase (se 5 (by rfl) ⟨34913, by rfl⟩ : syracuseStep 744821 = 69827) (by norm_num)
theorem B744845 : Blo 495792 744845 := bbase (se 3 (by rfl) ⟨139658, by rfl⟩ : syracuseStep 744845 = 279317) (by norm_num)
theorem B843149 : Blo 495792 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B744869 : Blo 495792 744869 := bbase (se 4 (by rfl) ⟨69831, by rfl⟩ : syracuseStep 744869 = 139663) (by norm_num)
theorem B744893 : Blo 495792 744893 := bbase (se 3 (by rfl) ⟨139667, by rfl⟩ : syracuseStep 744893 = 279335) (by norm_num)
theorem B744917 : Blo 495792 744917 := bbase (se 7 (by rfl) ⟨8729, by rfl⟩ : syracuseStep 744917 = 17459) (by norm_num)
theorem B744941 : Blo 495792 744941 := bbase (se 3 (by rfl) ⟨139676, by rfl⟩ : syracuseStep 744941 = 279353) (by norm_num)
theorem B941557 : Blo 495792 941557 := bbase (se 5 (by rfl) ⟨44135, by rfl⟩ : syracuseStep 941557 = 88271) (by norm_num)
theorem B744965 : Blo 495792 744965 := bbase (se 4 (by rfl) ⟨69840, by rfl⟩ : syracuseStep 744965 = 139681) (by norm_num)
theorem B843277 : Blo 495792 843277 := bbase (se 3 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 843277 = 316229) (by norm_num)
theorem B744989 : Blo 495792 744989 := bbase (se 3 (by rfl) ⟨139685, by rfl⟩ : syracuseStep 744989 = 279371) (by norm_num)
theorem B745013 : Blo 495792 745013 := bbase (se 5 (by rfl) ⟨34922, by rfl⟩ : syracuseStep 745013 = 69845) (by norm_num)
theorem B745037 : Blo 495792 745037 := bbase (se 3 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 745037 = 279389) (by norm_num)
theorem B908885 : Blo 495792 908885 := bbase (se 8 (by rfl) ⟨5325, by rfl⟩ : syracuseStep 908885 = 10651) (by norm_num)
theorem B745061 : Blo 495792 745061 := bbase (se 4 (by rfl) ⟨69849, by rfl⟩ : syracuseStep 745061 = 139699) (by norm_num)
theorem B843365 : Blo 495792 843365 := bbase (se 4 (by rfl) ⟨79065, by rfl⟩ : syracuseStep 843365 = 158131) (by norm_num)
theorem B745085 : Blo 495792 745085 := bbase (se 3 (by rfl) ⟨139703, by rfl⟩ : syracuseStep 745085 = 279407) (by norm_num)
theorem B941701 : Blo 495792 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B745109 : Blo 495792 745109 := bbase (se 6 (by rfl) ⟨17463, by rfl⟩ : syracuseStep 745109 = 34927) (by norm_num)
theorem B745133 : Blo 495792 745133 := bbase (se 3 (by rfl) ⟨139712, by rfl⟩ : syracuseStep 745133 = 279425) (by norm_num)
theorem B1793717 : Blo 495792 1793717 := bbase (se 5 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 1793717 = 168161) (by norm_num)
theorem B745157 : Blo 495792 745157 := bbase (se 4 (by rfl) ⟨69858, by rfl⟩ : syracuseStep 745157 = 139717) (by norm_num)
theorem B745181 : Blo 495792 745181 := bbase (se 3 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 745181 = 279443) (by norm_num)
theorem B745205 : Blo 495792 745205 := bbase (se 5 (by rfl) ⟨34931, by rfl⟩ : syracuseStep 745205 = 69863) (by norm_num)
theorem B745229 : Blo 495792 745229 := bbase (se 3 (by rfl) ⟨139730, by rfl⟩ : syracuseStep 745229 = 279461) (by norm_num)
theorem B941861 : Blo 495792 941861 := bbase (se 4 (by rfl) ⟨88299, by rfl⟩ : syracuseStep 941861 = 176599) (by norm_num)
theorem B2514725 : Blo 495792 2514725 := bbase (se 4 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 2514725 = 471511) (by norm_num)
theorem B745253 : Blo 495792 745253 := bbase (se 4 (by rfl) ⟨69867, by rfl⟩ : syracuseStep 745253 = 139735) (by norm_num)
theorem B745277 : Blo 495792 745277 := bbase (se 3 (by rfl) ⟨139739, by rfl⟩ : syracuseStep 745277 = 279479) (by norm_num)
theorem B745301 : Blo 495792 745301 := bbase (se 9 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 745301 = 4367) (by norm_num)
theorem B745325 : Blo 495792 745325 := bbase (se 3 (by rfl) ⟨139748, by rfl⟩ : syracuseStep 745325 = 279497) (by norm_num)
theorem B745349 : Blo 495792 745349 := bbase (se 4 (by rfl) ⟨69876, by rfl⟩ : syracuseStep 745349 = 139753) (by norm_num)
theorem B2547605 : Blo 495792 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B745373 : Blo 495792 745373 := bbase (se 3 (by rfl) ⟨139757, by rfl⟩ : syracuseStep 745373 = 279515) (by norm_num)
theorem B942005 : Blo 495792 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B4775861 : Blo 495792 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B745397 : Blo 495792 745397 := bbase (se 5 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 745397 = 69881) (by norm_num)
theorem B745421 : Blo 495792 745421 := bbase (se 3 (by rfl) ⟨139766, by rfl⟩ : syracuseStep 745421 = 279533) (by norm_num)
theorem B745445 : Blo 495792 745445 := bbase (se 4 (by rfl) ⟨69885, by rfl⟩ : syracuseStep 745445 = 139771) (by norm_num)
theorem B745469 : Blo 495792 745469 := bbase (se 3 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 745469 = 279551) (by norm_num)
theorem B745493 : Blo 495792 745493 := bbase (se 6 (by rfl) ⟨17472, by rfl⟩ : syracuseStep 745493 = 34945) (by norm_num)
theorem B745517 : Blo 495792 745517 := bbase (se 3 (by rfl) ⟨139784, by rfl⟩ : syracuseStep 745517 = 279569) (by norm_num)
theorem B745541 : Blo 495792 745541 := bbase (se 4 (by rfl) ⟨69894, by rfl⟩ : syracuseStep 745541 = 139789) (by norm_num)
theorem B745565 : Blo 495792 745565 := bbase (se 3 (by rfl) ⟨139793, by rfl⟩ : syracuseStep 745565 = 279587) (by norm_num)
theorem B745589 : Blo 495792 745589 := bbase (se 5 (by rfl) ⟨34949, by rfl⟩ : syracuseStep 745589 = 69899) (by norm_num)
theorem B745613 : Blo 495792 745613 := bbase (se 3 (by rfl) ⟨139802, by rfl⟩ : syracuseStep 745613 = 279605) (by norm_num)
theorem B745637 : Blo 495792 745637 := bbase (se 4 (by rfl) ⟨69903, by rfl⟩ : syracuseStep 745637 = 139807) (by norm_num)
theorem B745661 : Blo 495792 745661 := bbase (se 3 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 745661 = 279623) (by norm_num)
theorem B942293 : Blo 495792 942293 := bbase (se 7 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 942293 = 22085) (by norm_num)
theorem B745685 : Blo 495792 745685 := bbase (se 7 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 745685 = 17477) (by norm_num)
theorem B745709 : Blo 495792 745709 := bbase (se 3 (by rfl) ⟨139820, by rfl⟩ : syracuseStep 745709 = 279641) (by norm_num)
theorem B745733 : Blo 495792 745733 := bbase (se 4 (by rfl) ⟨69912, by rfl⟩ : syracuseStep 745733 = 139825) (by norm_num)
theorem B745757 : Blo 495792 745757 := bbase (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) (by norm_num)
theorem B745781 : Blo 495792 745781 := bbase (se 5 (by rfl) ⟨34958, by rfl⟩ : syracuseStep 745781 = 69917) (by norm_num)
theorem B745805 : Blo 495792 745805 := bbase (se 3 (by rfl) ⟨139838, by rfl⟩ : syracuseStep 745805 = 279677) (by norm_num)
theorem B745829 : Blo 495792 745829 := bbase (se 4 (by rfl) ⟨69921, by rfl⟩ : syracuseStep 745829 = 139843) (by norm_num)
theorem B942445 : Blo 495792 942445 := bbase (se 3 (by rfl) ⟨176708, by rfl⟩ : syracuseStep 942445 = 353417) (by norm_num)
theorem B745853 : Blo 495792 745853 := bbase (se 3 (by rfl) ⟨139847, by rfl⟩ : syracuseStep 745853 = 279695) (by norm_num)
theorem B745877 : Blo 495792 745877 := bbase (se 6 (by rfl) ⟨17481, by rfl⟩ : syracuseStep 745877 = 34963) (by norm_num)
theorem B745901 : Blo 495792 745901 := bbase (se 3 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 745901 = 279713) (by norm_num)
theorem B745925 : Blo 495792 745925 := bbase (se 4 (by rfl) ⟨69930, by rfl⟩ : syracuseStep 745925 = 139861) (by norm_num)
theorem B745949 : Blo 495792 745949 := bbase (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) (by norm_num)
theorem B1139173 : Blo 495792 1139173 := bbase (se 4 (by rfl) ⟨106797, by rfl⟩ : syracuseStep 1139173 = 213595) (by norm_num)
theorem B745973 : Blo 495792 745973 := bbase (se 5 (by rfl) ⟨34967, by rfl⟩ : syracuseStep 745973 = 69935) (by norm_num)
theorem B745997 : Blo 495792 745997 := bbase (se 3 (by rfl) ⟨139874, by rfl⟩ : syracuseStep 745997 = 279749) (by norm_num)
theorem B746021 : Blo 495792 746021 := bbase (se 4 (by rfl) ⟨69939, by rfl⟩ : syracuseStep 746021 = 139879) (by norm_num)
theorem B746045 : Blo 495792 746045 := bbase (se 3 (by rfl) ⟨139883, by rfl⟩ : syracuseStep 746045 = 279767) (by norm_num)
theorem B746069 : Blo 495792 746069 := bbase (se 8 (by rfl) ⟨4371, by rfl⟩ : syracuseStep 746069 = 8743) (by norm_num)
theorem B746093 : Blo 495792 746093 := bbase (se 3 (by rfl) ⟨139892, by rfl⟩ : syracuseStep 746093 = 279785) (by norm_num)
theorem B746117 : Blo 495792 746117 := bbase (se 4 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 746117 = 139897) (by norm_num)
theorem B942749 : Blo 495792 942749 := bbase (se 3 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 942749 = 353531) (by norm_num)
theorem B746141 : Blo 495792 746141 := bbase (se 3 (by rfl) ⟨139901, by rfl⟩ : syracuseStep 746141 = 279803) (by norm_num)
theorem B2384549 : Blo 495792 2384549 := bbase (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) (by norm_num)
theorem B746165 : Blo 495792 746165 := bbase (se 5 (by rfl) ⟨34976, by rfl⟩ : syracuseStep 746165 = 69953) (by norm_num)
theorem B746189 : Blo 495792 746189 := bbase (se 3 (by rfl) ⟨139910, by rfl⟩ : syracuseStep 746189 = 279821) (by norm_num)
theorem B1893077 : Blo 495792 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B2122469 : Blo 495792 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B746213 : Blo 495792 746213 := bbase (se 4 (by rfl) ⟨69957, by rfl⟩ : syracuseStep 746213 = 139915) (by norm_num)
theorem B746237 : Blo 495792 746237 := bbase (se 3 (by rfl) ⟨139919, by rfl⟩ : syracuseStep 746237 = 279839) (by norm_num)
theorem B2417413 : Blo 495792 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B746261 : Blo 495792 746261 := bbase (se 6 (by rfl) ⟨17490, by rfl⟩ : syracuseStep 746261 = 34981) (by norm_num)
theorem B746285 : Blo 495792 746285 := bbase (se 3 (by rfl) ⟨139928, by rfl⟩ : syracuseStep 746285 = 279857) (by norm_num)
theorem B746309 : Blo 495792 746309 := bbase (se 4 (by rfl) ⟨69966, by rfl⟩ : syracuseStep 746309 = 139933) (by norm_num)
theorem B746333 : Blo 495792 746333 := bbase (se 3 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 746333 = 279875) (by norm_num)
theorem B877405 : Blo 495792 877405 := bbase (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) (by norm_num)
theorem B615281 : Blo 495792 615281 := bbase (se 2 (by rfl) ⟨230730, by rfl⟩ : syracuseStep 615281 = 461461) (by norm_num)
theorem B746357 : Blo 495792 746357 := bbase (se 5 (by rfl) ⟨34985, by rfl⟩ : syracuseStep 746357 = 69971) (by norm_num)
theorem B746381 : Blo 495792 746381 := bbase (se 3 (by rfl) ⟨139946, by rfl⟩ : syracuseStep 746381 = 279893) (by norm_num)
theorem B3597205 : Blo 495792 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B746405 : Blo 495792 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B746429 : Blo 495792 746429 := bbase (se 3 (by rfl) ⟨139955, by rfl⟩ : syracuseStep 746429 = 279911) (by norm_num)
theorem B746453 : Blo 495792 746453 := bbase (se 7 (by rfl) ⟨8747, by rfl⟩ : syracuseStep 746453 = 17495) (by norm_num)
theorem B746477 : Blo 495792 746477 := bbase (se 3 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 746477 = 279929) (by norm_num)
theorem B1893365 : Blo 495792 1893365 := bbase (se 5 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 1893365 = 177503) (by norm_num)
theorem B2122757 : Blo 495792 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B746501 : Blo 495792 746501 := bbase (se 4 (by rfl) ⟨69984, by rfl⟩ : syracuseStep 746501 = 139969) (by norm_num)
theorem B746525 : Blo 495792 746525 := bbase (se 3 (by rfl) ⟨139973, by rfl⟩ : syracuseStep 746525 = 279947) (by norm_num)
theorem B2516021 : Blo 495792 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B746549 : Blo 495792 746549 := bbase (se 5 (by rfl) ⟨34994, by rfl⟩ : syracuseStep 746549 = 69989) (by norm_num)
theorem B746573 : Blo 495792 746573 := bbase (se 3 (by rfl) ⟨139982, by rfl⟩ : syracuseStep 746573 = 279965) (by norm_num)
theorem B746597 : Blo 495792 746597 := bbase (se 4 (by rfl) ⟨69993, by rfl⟩ : syracuseStep 746597 = 139987) (by norm_num)
theorem B746621 : Blo 495792 746621 := bbase (se 3 (by rfl) ⟨139991, by rfl⟩ : syracuseStep 746621 = 279983) (by norm_num)
theorem B1434757 : Blo 495792 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B746645 : Blo 495792 746645 := bbase (se 6 (by rfl) ⟨17499, by rfl⟩ : syracuseStep 746645 = 34999) (by norm_num)
theorem B1598629 : Blo 495792 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B746669 : Blo 495792 746669 := bbase (se 3 (by rfl) ⟨140000, by rfl⟩ : syracuseStep 746669 = 280001) (by norm_num)
theorem B746693 : Blo 495792 746693 := bbase (se 4 (by rfl) ⟨70002, by rfl⟩ : syracuseStep 746693 = 140005) (by norm_num)
theorem B1008845 : Blo 495792 1008845 := bbase (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) (by norm_num)
theorem B746717 : Blo 495792 746717 := bbase (se 3 (by rfl) ⟨140009, by rfl⟩ : syracuseStep 746717 = 280019) (by norm_num)
theorem B746741 : Blo 495792 746741 := bbase (se 5 (by rfl) ⟨35003, by rfl⟩ : syracuseStep 746741 = 70007) (by norm_num)
theorem B2024693 : Blo 495792 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B746765 : Blo 495792 746765 := bbase (se 3 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 746765 = 280037) (by norm_num)
theorem B746789 : Blo 495792 746789 := bbase (se 4 (by rfl) ⟨70011, by rfl⟩ : syracuseStep 746789 = 140023) (by norm_num)
theorem B746813 : Blo 495792 746813 := bbase (se 3 (by rfl) ⟨140027, by rfl⟩ : syracuseStep 746813 = 280055) (by norm_num)
theorem B746837 : Blo 495792 746837 := bbase (se 12 (by rfl) ⟨273, by rfl⟩ : syracuseStep 746837 = 547) (by norm_num)
theorem B746861 : Blo 495792 746861 := bbase (se 3 (by rfl) ⟨140036, by rfl⟩ : syracuseStep 746861 = 280073) (by norm_num)
theorem B746885 : Blo 495792 746885 := bbase (se 4 (by rfl) ⟨70020, by rfl⟩ : syracuseStep 746885 = 140041) (by norm_num)
theorem B943501 : Blo 495792 943501 := bbase (se 3 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 943501 = 353813) (by norm_num)
theorem B746909 : Blo 495792 746909 := bbase (se 3 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 746909 = 280091) (by norm_num)
theorem B746933 : Blo 495792 746933 := bbase (se 5 (by rfl) ⟨35012, by rfl⟩ : syracuseStep 746933 = 70025) (by norm_num)
theorem B746957 : Blo 495792 746957 := bbase (se 3 (by rfl) ⟨140054, by rfl⟩ : syracuseStep 746957 = 280109) (by norm_num)
theorem B746981 : Blo 495792 746981 := bbase (se 4 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 746981 = 140059) (by norm_num)
theorem B747005 : Blo 495792 747005 := bbase (se 3 (by rfl) ⟨140063, by rfl⟩ : syracuseStep 747005 = 280127) (by norm_num)
theorem B747029 : Blo 495792 747029 := bbase (se 6 (by rfl) ⟨17508, by rfl⟩ : syracuseStep 747029 = 35017) (by norm_num)
theorem B943645 : Blo 495792 943645 := bbase (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) (by norm_num)
theorem B747053 : Blo 495792 747053 := bbase (se 3 (by rfl) ⟨140072, by rfl⟩ : syracuseStep 747053 = 280145) (by norm_num)
theorem B747077 : Blo 495792 747077 := bbase (se 4 (by rfl) ⟨70038, by rfl⟩ : syracuseStep 747077 = 140077) (by norm_num)
theorem B747101 : Blo 495792 747101 := bbase (se 3 (by rfl) ⟨140081, by rfl⟩ : syracuseStep 747101 = 280163) (by norm_num)
theorem B747125 : Blo 495792 747125 := bbase (se 5 (by rfl) ⟨35021, by rfl⟩ : syracuseStep 747125 = 70043) (by norm_num)
theorem B747149 : Blo 495792 747149 := bbase (se 3 (by rfl) ⟨140090, by rfl⟩ : syracuseStep 747149 = 280181) (by norm_num)
theorem B747173 : Blo 495792 747173 := bbase (se 4 (by rfl) ⟨70047, by rfl⟩ : syracuseStep 747173 = 140095) (by norm_num)
theorem B943805 : Blo 495792 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B747197 : Blo 495792 747197 := bbase (se 3 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 747197 = 280199) (by norm_num)
theorem B747221 : Blo 495792 747221 := bbase (se 7 (by rfl) ⟨8756, by rfl⟩ : syracuseStep 747221 = 17513) (by norm_num)
theorem B747245 : Blo 495792 747245 := bbase (se 3 (by rfl) ⟨140108, by rfl⟩ : syracuseStep 747245 = 280217) (by norm_num)
theorem B2123509 : Blo 495792 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B747269 : Blo 495792 747269 := bbase (se 4 (by rfl) ⟨70056, by rfl⟩ : syracuseStep 747269 = 140113) (by norm_num)
theorem B747293 : Blo 495792 747293 := bbase (se 3 (by rfl) ⟨140117, by rfl⟩ : syracuseStep 747293 = 280235) (by norm_num)
theorem B747317 : Blo 495792 747317 := bbase (se 5 (by rfl) ⟨35030, by rfl⟩ : syracuseStep 747317 = 70061) (by norm_num)
theorem B943949 : Blo 495792 943949 := bbase (se 3 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 943949 = 353981) (by norm_num)
theorem B747341 : Blo 495792 747341 := bbase (se 3 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 747341 = 280253) (by norm_num)
theorem B747365 : Blo 495792 747365 := bbase (se 4 (by rfl) ⟨70065, by rfl⟩ : syracuseStep 747365 = 140131) (by norm_num)
theorem B747389 : Blo 495792 747389 := bbase (se 3 (by rfl) ⟨140135, by rfl⟩ : syracuseStep 747389 = 280271) (by norm_num)
theorem B747413 : Blo 495792 747413 := bbase (se 6 (by rfl) ⟨17517, by rfl⟩ : syracuseStep 747413 = 35035) (by norm_num)
theorem B747437 : Blo 495792 747437 := bbase (se 3 (by rfl) ⟨140144, by rfl⟩ : syracuseStep 747437 = 280289) (by norm_num)
theorem B747461 : Blo 495792 747461 := bbase (se 4 (by rfl) ⟨70074, by rfl⟩ : syracuseStep 747461 = 140149) (by norm_num)
theorem B747485 : Blo 495792 747485 := bbase (se 3 (by rfl) ⟨140153, by rfl⟩ : syracuseStep 747485 = 280307) (by norm_num)
theorem B747509 : Blo 495792 747509 := bbase (se 5 (by rfl) ⟨35039, by rfl⟩ : syracuseStep 747509 = 70079) (by norm_num)
theorem B747533 : Blo 495792 747533 := bbase (se 3 (by rfl) ⟨140162, by rfl⟩ : syracuseStep 747533 = 280325) (by norm_num)
theorem B1697813 : Blo 495792 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B747557 : Blo 495792 747557 := bbase (se 4 (by rfl) ⟨70083, by rfl⟩ : syracuseStep 747557 = 140167) (by norm_num)
theorem B747581 : Blo 495792 747581 := bbase (se 3 (by rfl) ⟨140171, by rfl⟩ : syracuseStep 747581 = 280343) (by norm_num)
theorem B682069 : Blo 495792 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B747605 : Blo 495792 747605 := bbase (se 8 (by rfl) ⟨4380, by rfl⟩ : syracuseStep 747605 = 8761) (by norm_num)
theorem B944237 : Blo 495792 944237 := bbase (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) (by norm_num)
theorem B747629 : Blo 495792 747629 := bbase (se 3 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 747629 = 280361) (by norm_num)
theorem B747653 : Blo 495792 747653 := bbase (se 4 (by rfl) ⟨70092, by rfl⟩ : syracuseStep 747653 = 140185) (by norm_num)
theorem B1894549 : Blo 495792 1894549 := bbase (se 6 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 1894549 = 88807) (by norm_num)
theorem B747677 : Blo 495792 747677 := bbase (se 3 (by rfl) ⟨140189, by rfl⟩ : syracuseStep 747677 = 280379) (by norm_num)
theorem B747701 : Blo 495792 747701 := bbase (se 5 (by rfl) ⟨35048, by rfl⟩ : syracuseStep 747701 = 70097) (by norm_num)
theorem B747725 : Blo 495792 747725 := bbase (se 3 (by rfl) ⟨140198, by rfl⟩ : syracuseStep 747725 = 280397) (by norm_num)
theorem B747749 : Blo 495792 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B1075445 : Blo 495792 1075445 := bbase (se 5 (by rfl) ⟨50411, by rfl⟩ : syracuseStep 1075445 = 100823) (by norm_num)
theorem B747773 : Blo 495792 747773 := bbase (se 3 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 747773 = 280415) (by norm_num)
theorem B944389 : Blo 495792 944389 := bbase (se 4 (by rfl) ⟨88536, by rfl⟩ : syracuseStep 944389 = 177073) (by norm_num)
theorem B747797 : Blo 495792 747797 := bbase (se 6 (by rfl) ⟨17526, by rfl⟩ : syracuseStep 747797 = 35053) (by norm_num)
theorem B747821 : Blo 495792 747821 := bbase (se 3 (by rfl) ⟨140216, by rfl⟩ : syracuseStep 747821 = 280433) (by norm_num)
theorem B2517317 : Blo 495792 2517317 := bbase (se 4 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 2517317 = 471997) (by norm_num)
theorem B747845 : Blo 495792 747845 := bbase (se 4 (by rfl) ⟨70110, by rfl⟩ : syracuseStep 747845 = 140221) (by norm_num)
theorem B747869 : Blo 495792 747869 := bbase (se 3 (by rfl) ⟨140225, by rfl⟩ : syracuseStep 747869 = 280451) (by norm_num)
theorem B1272181 : Blo 495792 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B747893 : Blo 495792 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B1010045 : Blo 495792 1010045 := bbase (se 3 (by rfl) ⟨189383, by rfl⟩ : syracuseStep 1010045 = 378767) (by norm_num)
theorem B747917 : Blo 495792 747917 := bbase (se 3 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 747917 = 280469) (by norm_num)
theorem B747941 : Blo 495792 747941 := bbase (se 4 (by rfl) ⟨70119, by rfl⟩ : syracuseStep 747941 = 140239) (by norm_num)
theorem B747965 : Blo 495792 747965 := bbase (se 3 (by rfl) ⟨140243, by rfl⟩ : syracuseStep 747965 = 280487) (by norm_num)
theorem B1894853 : Blo 495792 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B2124245 : Blo 495792 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B747989 : Blo 495792 747989 := bbase (se 7 (by rfl) ⟨8765, by rfl⟩ : syracuseStep 747989 = 17531) (by norm_num)
theorem B748013 : Blo 495792 748013 := bbase (se 3 (by rfl) ⟨140252, by rfl⟩ : syracuseStep 748013 = 280505) (by norm_num)
theorem B748037 : Blo 495792 748037 := bbase (se 4 (by rfl) ⟨70128, by rfl⟩ : syracuseStep 748037 = 140257) (by norm_num)
theorem B748061 : Blo 495792 748061 := bbase (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) (by norm_num)
theorem B944693 : Blo 495792 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B748085 : Blo 495792 748085 := bbase (se 5 (by rfl) ⟨35066, by rfl⟩ : syracuseStep 748085 = 70133) (by norm_num)
theorem B748109 : Blo 495792 748109 := bbase (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) (by norm_num)
theorem B748133 : Blo 495792 748133 := bbase (se 4 (by rfl) ⟨70137, by rfl⟩ : syracuseStep 748133 = 140275) (by norm_num)
theorem B748157 : Blo 495792 748157 := bbase (se 3 (by rfl) ⟨140279, by rfl⟩ : syracuseStep 748157 = 280559) (by norm_num)
theorem B748181 : Blo 495792 748181 := bbase (se 6 (by rfl) ⟨17535, by rfl⟩ : syracuseStep 748181 = 35071) (by norm_num)
theorem B748205 : Blo 495792 748205 := bbase (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) (by norm_num)
theorem B748229 : Blo 495792 748229 := bbase (se 4 (by rfl) ⟨70146, by rfl⟩ : syracuseStep 748229 = 140293) (by norm_num)
theorem B748253 : Blo 495792 748253 := bbase (se 3 (by rfl) ⟨140297, by rfl⟩ : syracuseStep 748253 = 280595) (by norm_num)
theorem B748277 : Blo 495792 748277 := bbase (se 5 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 748277 = 70151) (by norm_num)
theorem B748301 : Blo 495792 748301 := bbase (se 3 (by rfl) ⟨140306, by rfl⟩ : syracuseStep 748301 = 280613) (by norm_num)
theorem B748325 : Blo 495792 748325 := bbase (se 4 (by rfl) ⟨70155, by rfl⟩ : syracuseStep 748325 = 140311) (by norm_num)
theorem B748349 : Blo 495792 748349 := bbase (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) (by norm_num)
theorem B12741461 : Blo 495792 12741461 := bbase (se 9 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 12741461 = 74657) (by norm_num)
theorem B748373 : Blo 495792 748373 := bbase (se 9 (by rfl) ⟨2192, by rfl⟩ : syracuseStep 748373 = 4385) (by norm_num)
theorem B748397 : Blo 495792 748397 := bbase (se 3 (by rfl) ⟨140324, by rfl⟩ : syracuseStep 748397 = 280649) (by norm_num)
theorem B748421 : Blo 495792 748421 := bbase (se 4 (by rfl) ⟨70164, by rfl⟩ : syracuseStep 748421 = 140329) (by norm_num)
theorem B748445 : Blo 495792 748445 := bbase (se 3 (by rfl) ⟨140333, by rfl⟩ : syracuseStep 748445 = 280667) (by norm_num)
theorem B748469 : Blo 495792 748469 := bbase (se 5 (by rfl) ⟨35084, by rfl⟩ : syracuseStep 748469 = 70169) (by norm_num)
theorem B748493 : Blo 495792 748493 := bbase (se 3 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 748493 = 280685) (by norm_num)
theorem B748517 : Blo 495792 748517 := bbase (se 4 (by rfl) ⟨70173, by rfl⟩ : syracuseStep 748517 = 140347) (by norm_num)
theorem B1010677 : Blo 495792 1010677 := bbase (se 5 (by rfl) ⟨47375, by rfl⟩ : syracuseStep 1010677 = 94751) (by norm_num)
theorem B748541 : Blo 495792 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1534997 : Blo 495792 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B748565 : Blo 495792 748565 := bbase (se 6 (by rfl) ⟨17544, by rfl⟩ : syracuseStep 748565 = 35089) (by norm_num)
theorem B748589 : Blo 495792 748589 := bbase (se 3 (by rfl) ⟨140360, by rfl⟩ : syracuseStep 748589 = 280721) (by norm_num)
theorem B748613 : Blo 495792 748613 := bbase (se 4 (by rfl) ⟨70182, by rfl⟩ : syracuseStep 748613 = 140365) (by norm_num)
theorem B748637 : Blo 495792 748637 := bbase (se 3 (by rfl) ⟨140369, by rfl⟩ : syracuseStep 748637 = 280739) (by norm_num)
theorem B748661 : Blo 495792 748661 := bbase (se 5 (by rfl) ⟨35093, by rfl⟩ : syracuseStep 748661 = 70187) (by norm_num)
theorem B748685 : Blo 495792 748685 := bbase (se 3 (by rfl) ⟨140378, by rfl⟩ : syracuseStep 748685 = 280757) (by norm_num)
theorem B748709 : Blo 495792 748709 := bbase (se 4 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 748709 = 140383) (by norm_num)
theorem B1141933 : Blo 495792 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B748733 : Blo 495792 748733 := bbase (se 3 (by rfl) ⟨140387, by rfl⟩ : syracuseStep 748733 = 280775) (by norm_num)
theorem B748757 : Blo 495792 748757 := bbase (se 7 (by rfl) ⟨8774, by rfl⟩ : syracuseStep 748757 = 17549) (by norm_num)
theorem B748781 : Blo 495792 748781 := bbase (se 3 (by rfl) ⟨140396, by rfl⟩ : syracuseStep 748781 = 280793) (by norm_num)
theorem B748805 : Blo 495792 748805 := bbase (se 4 (by rfl) ⟨70200, by rfl⟩ : syracuseStep 748805 = 140401) (by norm_num)
theorem B748829 : Blo 495792 748829 := bbase (se 3 (by rfl) ⟨140405, by rfl⟩ : syracuseStep 748829 = 280811) (by norm_num)
theorem B945445 : Blo 495792 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B748853 : Blo 495792 748853 := bbase (se 5 (by rfl) ⟨35102, by rfl⟩ : syracuseStep 748853 = 70205) (by norm_num)
theorem B748877 : Blo 495792 748877 := bbase (se 3 (by rfl) ⟨140414, by rfl⟩ : syracuseStep 748877 = 280829) (by norm_num)
theorem B748901 : Blo 495792 748901 := bbase (se 4 (by rfl) ⟨70209, by rfl⟩ : syracuseStep 748901 = 140419) (by norm_num)
theorem B748925 : Blo 495792 748925 := bbase (se 3 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 748925 = 280847) (by norm_num)
theorem B2387333 : Blo 495792 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B748949 : Blo 495792 748949 := bbase (se 6 (by rfl) ⟨17553, by rfl⟩ : syracuseStep 748949 = 35107) (by norm_num)
theorem B748973 : Blo 495792 748973 := bbase (se 3 (by rfl) ⟨140432, by rfl⟩ : syracuseStep 748973 = 280865) (by norm_num)
theorem B945589 : Blo 495792 945589 := bbase (se 5 (by rfl) ⟨44324, by rfl⟩ : syracuseStep 945589 = 88649) (by norm_num)
theorem B748997 : Blo 495792 748997 := bbase (se 4 (by rfl) ⟨70218, by rfl⟩ : syracuseStep 748997 = 140437) (by norm_num)
theorem B749021 : Blo 495792 749021 := bbase (se 3 (by rfl) ⟨140441, by rfl⟩ : syracuseStep 749021 = 280883) (by norm_num)
theorem B749045 : Blo 495792 749045 := bbase (se 5 (by rfl) ⟨35111, by rfl⟩ : syracuseStep 749045 = 70223) (by norm_num)
theorem B749069 : Blo 495792 749069 := bbase (se 3 (by rfl) ⟨140450, by rfl⟩ : syracuseStep 749069 = 280901) (by norm_num)
theorem B749093 : Blo 495792 749093 := bbase (se 4 (by rfl) ⟨70227, by rfl⟩ : syracuseStep 749093 = 140455) (by norm_num)
theorem B749117 : Blo 495792 749117 := bbase (se 3 (by rfl) ⟨140459, by rfl⟩ : syracuseStep 749117 = 280919) (by norm_num)
theorem B2518613 : Blo 495792 2518613 := bbase (se 8 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 2518613 = 29515) (by norm_num)
theorem B945749 : Blo 495792 945749 := bbase (se 8 (by rfl) ⟨5541, by rfl⟩ : syracuseStep 945749 = 11083) (by norm_num)
theorem B749141 : Blo 495792 749141 := bbase (se 8 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 749141 = 8779) (by norm_num)
theorem B749165 : Blo 495792 749165 := bbase (se 3 (by rfl) ⟨140468, by rfl⟩ : syracuseStep 749165 = 280937) (by norm_num)
theorem B749189 : Blo 495792 749189 := bbase (se 4 (by rfl) ⟨70236, by rfl⟩ : syracuseStep 749189 = 140473) (by norm_num)
theorem B749213 : Blo 495792 749213 := bbase (se 3 (by rfl) ⟨140477, by rfl⟩ : syracuseStep 749213 = 280955) (by norm_num)
theorem B749237 : Blo 495792 749237 := bbase (se 5 (by rfl) ⟨35120, by rfl⟩ : syracuseStep 749237 = 70241) (by norm_num)
theorem B749261 : Blo 495792 749261 := bbase (se 3 (by rfl) ⟨140486, by rfl⟩ : syracuseStep 749261 = 280973) (by norm_num)
theorem B945893 : Blo 495792 945893 := bbase (se 4 (by rfl) ⟨88677, by rfl⟩ : syracuseStep 945893 = 177355) (by norm_num)
theorem B749285 : Blo 495792 749285 := bbase (se 4 (by rfl) ⟨70245, by rfl⟩ : syracuseStep 749285 = 140491) (by norm_num)
theorem B749309 : Blo 495792 749309 := bbase (se 3 (by rfl) ⟨140495, by rfl⟩ : syracuseStep 749309 = 280991) (by norm_num)
theorem B749333 : Blo 495792 749333 := bbase (se 6 (by rfl) ⟨17562, by rfl⟩ : syracuseStep 749333 = 35125) (by norm_num)
theorem B749357 : Blo 495792 749357 := bbase (se 3 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 749357 = 281009) (by norm_num)
theorem B749381 : Blo 495792 749381 := bbase (se 4 (by rfl) ⟨70254, by rfl⟩ : syracuseStep 749381 = 140509) (by norm_num)
theorem B6385493 : Blo 495792 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B749405 : Blo 495792 749405 := bbase (se 3 (by rfl) ⟨140513, by rfl⟩ : syracuseStep 749405 = 281027) (by norm_num)
theorem B749429 : Blo 495792 749429 := bbase (se 5 (by rfl) ⟨35129, by rfl⟩ : syracuseStep 749429 = 70259) (by norm_num)
theorem B749453 : Blo 495792 749453 := bbase (se 3 (by rfl) ⟨140522, by rfl⟩ : syracuseStep 749453 = 281045) (by norm_num)
theorem B6123413 : Blo 495792 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B749477 : Blo 495792 749477 := bbase (se 4 (by rfl) ⟨70263, by rfl⟩ : syracuseStep 749477 = 140527) (by norm_num)
theorem B749501 : Blo 495792 749501 := bbase (se 3 (by rfl) ⟨140531, by rfl⟩ : syracuseStep 749501 = 281063) (by norm_num)
theorem B749525 : Blo 495792 749525 := bbase (se 7 (by rfl) ⟨8783, by rfl⟩ : syracuseStep 749525 = 17567) (by norm_num)
theorem B749549 : Blo 495792 749549 := bbase (se 3 (by rfl) ⟨140540, by rfl⟩ : syracuseStep 749549 = 281081) (by norm_num)
theorem B946181 : Blo 495792 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B749573 : Blo 495792 749573 := bbase (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) (by norm_num)
theorem B749597 : Blo 495792 749597 := bbase (se 3 (by rfl) ⟨140549, by rfl⟩ : syracuseStep 749597 = 281099) (by norm_num)
theorem B749621 : Blo 495792 749621 := bbase (se 5 (by rfl) ⟨35138, by rfl⟩ : syracuseStep 749621 = 70277) (by norm_num)
theorem B749645 : Blo 495792 749645 := bbase (se 3 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 749645 = 281117) (by norm_num)
theorem B749669 : Blo 495792 749669 := bbase (se 4 (by rfl) ⟨70281, by rfl⟩ : syracuseStep 749669 = 140563) (by norm_num)
theorem B946333 : Blo 495792 946333 := bbase (se 3 (by rfl) ⟨177437, by rfl⟩ : syracuseStep 946333 = 354875) (by norm_num)
theorem B2585029 : Blo 495792 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B946637 : Blo 495792 946637 := bbase (se 3 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 946637 = 354989) (by norm_num)
theorem B1896965 : Blo 495792 1896965 := bbase (se 4 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 1896965 = 355681) (by norm_num)
theorem B2552485 : Blo 495792 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B1077941 : Blo 495792 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B1897253 : Blo 495792 1897253 := bbase (se 4 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 1897253 = 355735) (by norm_num)
theorem B2519909 : Blo 495792 2519909 := bbase (se 4 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 2519909 = 472483) (by norm_num)
theorem B1799093 : Blo 495792 1799093 := bbase (se 5 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 1799093 = 168665) (by norm_num)
theorem B1438661 : Blo 495792 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B1274869 : Blo 495792 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B849077 : Blo 495792 849077 := bbase (se 5 (by rfl) ⟨39800, by rfl⟩ : syracuseStep 849077 = 79601) (by norm_num)
theorem B947389 : Blo 495792 947389 := bbase (se 3 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 947389 = 355271) (by norm_num)
theorem B849133 : Blo 495792 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B4846837 : Blo 495792 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B947533 : Blo 495792 947533 := bbase (se 3 (by rfl) ⟨177662, by rfl⟩ : syracuseStep 947533 = 355325) (by norm_num)
theorem B947693 : Blo 495792 947693 := bbase (se 3 (by rfl) ⟨177692, by rfl⟩ : syracuseStep 947693 = 355385) (by norm_num)
theorem B4257269 : Blo 495792 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B947837 : Blo 495792 947837 := bbase (se 3 (by rfl) ⟨177719, by rfl⟩ : syracuseStep 947837 = 355439) (by norm_num)
theorem B2127541 : Blo 495792 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B948125 : Blo 495792 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B948277 : Blo 495792 948277 := bbase (se 5 (by rfl) ⟨44450, by rfl⟩ : syracuseStep 948277 = 88901) (by norm_num)
theorem B2521205 : Blo 495792 2521205 := bbase (se 5 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 2521205 = 236363) (by norm_num)
theorem B9664661 : Blo 495792 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B948581 : Blo 495792 948581 := bbase (se 4 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 948581 = 177859) (by norm_num)
theorem B1276573 : Blo 495792 1276573 := bbase (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) (by norm_num)
theorem B1440661 : Blo 495792 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B850877 : Blo 495792 850877 := bbase (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) (by norm_num)
theorem B1440949 : Blo 495792 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1342693 : Blo 495792 1342693 := bbase (se 4 (by rfl) ⟨125877, by rfl⟩ : syracuseStep 1342693 = 251755) (by norm_num)
theorem B2522501 : Blo 495792 2522501 := bbase (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) (by norm_num)
theorem B1277549 : Blo 495792 1277549 := bbase (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) (by norm_num)
theorem B3767957 : Blo 495792 3767957 := bbase (se 6 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 3767957 = 176623) (by norm_num)
theorem B15302357 : Blo 495792 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B851677 : Blo 495792 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B2523149 : Blo 495792 2523149 := bstep (se 3 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 2523149 = 946181) B946181
theorem B1441955 : Blo 495792 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B2130275 : Blo 495792 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B754067 : Blo 495792 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B1344109 : Blo 495792 1344109 := bstep (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) B504041
theorem B6062789 : Blo 495792 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B557779 : Blo 495792 557779 := bstep (se 1 (by rfl) ⟨418334, by rfl⟩ : syracuseStep 557779 = 836669) B836669
theorem B1344259 : Blo 495792 1344259 := bstep (se 1 (by rfl) ⟨1008194, by rfl⟩ : syracuseStep 1344259 = 2016389) B2016389
theorem B2589475 : Blo 495792 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B557923 : Blo 495792 557923 := bstep (se 1 (by rfl) ⟨418442, by rfl⟩ : syracuseStep 557923 = 836885) B836885
theorem B558067 : Blo 495792 558067 := bstep (se 1 (by rfl) ⟨418550, by rfl⟩ : syracuseStep 558067 = 837101) B837101
theorem B558211 : Blo 495792 558211 := bstep (se 1 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 558211 = 837317) B837317
theorem B558355 : Blo 495792 558355 := bstep (se 1 (by rfl) ⟨418766, by rfl⟩ : syracuseStep 558355 = 837533) B837533
theorem B558499 : Blo 495792 558499 := bstep (se 1 (by rfl) ⟨418874, by rfl⟩ : syracuseStep 558499 = 837749) B837749
theorem B2131505 : Blo 495792 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B558643 : Blo 495792 558643 := bstep (se 1 (by rfl) ⟨418982, by rfl⟩ : syracuseStep 558643 = 837965) B837965
theorem B1115729 : Blo 495792 1115729 := bstep (se 2 (by rfl) ⟨418398, by rfl⟩ : syracuseStep 1115729 = 836797) B836797
theorem B1115747 : Blo 495792 1115747 := bstep (se 1 (by rfl) ⟨836810, by rfl⟩ : syracuseStep 1115747 = 1673621) B1673621
theorem B558787 : Blo 495792 558787 := bstep (se 1 (by rfl) ⟨419090, by rfl⟩ : syracuseStep 558787 = 838181) B838181
theorem B3180293 : Blo 495792 3180293 := bstep (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) B596305
theorem B2393869 : Blo 495792 2393869 := bstep (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) B897701
theorem B755489 : Blo 495792 755489 := bstep (se 2 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 755489 = 566617) B566617
theorem B558931 : Blo 495792 558931 := bstep (se 1 (by rfl) ⟨419198, by rfl⟩ : syracuseStep 558931 = 838397) B838397
theorem B1116017 : Blo 495792 1116017 := bstep (se 2 (by rfl) ⟨418506, by rfl⟩ : syracuseStep 1116017 = 837013) B837013
theorem B1116035 : Blo 495792 1116035 := bstep (se 1 (by rfl) ⟨837026, by rfl⟩ : syracuseStep 1116035 = 1674053) B1674053
theorem B559075 : Blo 495792 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B559219 : Blo 495792 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B1116305 : Blo 495792 1116305 := bstep (se 2 (by rfl) ⟨418614, by rfl⟩ : syracuseStep 1116305 = 837229) B837229
theorem B1116323 : Blo 495792 1116323 := bstep (se 1 (by rfl) ⟨837242, by rfl⟩ : syracuseStep 1116323 = 1674485) B1674485
theorem B559363 : Blo 495792 559363 := bstep (se 1 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 559363 = 839045) B839045
theorem B1640749 : Blo 495792 1640749 := bstep (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) B615281
theorem B756097 : Blo 495792 756097 := bstep (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) B567073
theorem B559507 : Blo 495792 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B1116593 : Blo 495792 1116593 := bstep (se 2 (by rfl) ⟨418722, by rfl⟩ : syracuseStep 1116593 = 837445) B837445
theorem B1116611 : Blo 495792 1116611 := bstep (se 1 (by rfl) ⟨837458, by rfl⟩ : syracuseStep 1116611 = 1674917) B1674917
theorem B3836429 : Blo 495792 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B559651 : Blo 495792 559651 := bstep (se 1 (by rfl) ⟨419738, by rfl⟩ : syracuseStep 559651 = 839477) B839477
theorem B1673837 : Blo 495792 1673837 := bstep (se 3 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 1673837 = 627689) B627689
theorem B1673891 : Blo 495792 1673891 := bstep (se 1 (by rfl) ⟨1255418, by rfl⟩ : syracuseStep 1673891 = 2510837) B2510837
theorem B559795 : Blo 495792 559795 := bstep (se 1 (by rfl) ⟨419846, by rfl⟩ : syracuseStep 559795 = 839693) B839693
theorem B1116881 : Blo 495792 1116881 := bstep (se 2 (by rfl) ⟨418830, by rfl⟩ : syracuseStep 1116881 = 837661) B837661
theorem B1116899 : Blo 495792 1116899 := bstep (se 1 (by rfl) ⟨837674, by rfl⟩ : syracuseStep 1116899 = 1675349) B1675349
theorem B559939 : Blo 495792 559939 := bstep (se 1 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 559939 = 839909) B839909
theorem B2526065 : Blo 495792 2526065 := bstep (se 2 (by rfl) ⟨947274, by rfl⟩ : syracuseStep 2526065 = 1894549) B1894549
theorem B1674161 : Blo 495792 1674161 := bstep (se 2 (by rfl) ⟨627810, by rfl⟩ : syracuseStep 1674161 = 1255621) B1255621
theorem B560083 : Blo 495792 560083 := bstep (se 1 (by rfl) ⟨420062, by rfl⟩ : syracuseStep 560083 = 840125) B840125
theorem B1117169 : Blo 495792 1117169 := bstep (se 2 (by rfl) ⟨418938, by rfl⟩ : syracuseStep 1117169 = 837877) B837877
theorem B1117187 : Blo 495792 1117187 := bstep (se 1 (by rfl) ⟨837890, by rfl⟩ : syracuseStep 1117187 = 1675781) B1675781
theorem B560227 : Blo 495792 560227 := bstep (se 1 (by rfl) ⟨420170, by rfl⟩ : syracuseStep 560227 = 840341) B840341
theorem B560371 : Blo 495792 560371 := bstep (se 1 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 560371 = 840557) B840557
theorem B1117457 : Blo 495792 1117457 := bstep (se 2 (by rfl) ⟨419046, by rfl⟩ : syracuseStep 1117457 = 838093) B838093
theorem B1117475 : Blo 495792 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B560515 : Blo 495792 560515 := bstep (se 1 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 560515 = 840773) B840773
theorem B3018161 : Blo 495792 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B3771845 : Blo 495792 3771845 := bstep (se 4 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 3771845 = 707221) B707221
theorem B1674701 : Blo 495792 1674701 := bstep (se 3 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 1674701 = 628013) B628013
theorem B1674755 : Blo 495792 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B560659 : Blo 495792 560659 := bstep (se 1 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 560659 = 840989) B840989
theorem B1117745 : Blo 495792 1117745 := bstep (se 2 (by rfl) ⟨419154, by rfl⟩ : syracuseStep 1117745 = 838309) B838309
theorem B1117763 : Blo 495792 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B560803 : Blo 495792 560803 := bstep (se 1 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 560803 = 841205) B841205
theorem B1675025 : Blo 495792 1675025 := bstep (se 2 (by rfl) ⟨628134, by rfl⟩ : syracuseStep 1675025 = 1256269) B1256269
theorem B560947 : Blo 495792 560947 := bstep (se 1 (by rfl) ⟨420710, by rfl⟩ : syracuseStep 560947 = 841421) B841421
theorem B1118033 : Blo 495792 1118033 := bstep (se 2 (by rfl) ⟨419262, by rfl⟩ : syracuseStep 1118033 = 838525) B838525
theorem B1118051 : Blo 495792 1118051 := bstep (se 1 (by rfl) ⟨838538, by rfl⟩ : syracuseStep 1118051 = 1677077) B1677077
theorem B561091 : Blo 495792 561091 := bstep (se 1 (by rfl) ⟨420818, by rfl⟩ : syracuseStep 561091 = 841637) B841637
theorem B2133965 : Blo 495792 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B1347569 : Blo 495792 1347569 := bstep (se 2 (by rfl) ⟨505338, by rfl⟩ : syracuseStep 1347569 = 1010677) B1010677
theorem B757777 : Blo 495792 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B561235 : Blo 495792 561235 := bstep (se 1 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 561235 = 841853) B841853
theorem B1118321 : Blo 495792 1118321 := bstep (se 2 (by rfl) ⟨419370, by rfl⟩ : syracuseStep 1118321 = 838741) B838741
theorem B1118339 : Blo 495792 1118339 := bstep (se 1 (by rfl) ⟨838754, by rfl⟩ : syracuseStep 1118339 = 1677509) B1677509
theorem B495795 : Blo 495792 495795 := bstep (se 1 (by rfl) ⟨371846, by rfl⟩ : syracuseStep 495795 = 743693) B743693
theorem B495811 : Blo 495792 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B495827 : Blo 495792 495827 := bstep (se 1 (by rfl) ⟨371870, by rfl⟩ : syracuseStep 495827 = 743741) B743741
theorem B495843 : Blo 495792 495843 := bstep (se 1 (by rfl) ⟨371882, by rfl⟩ : syracuseStep 495843 = 743765) B743765
theorem B561379 : Blo 495792 561379 := bstep (se 1 (by rfl) ⟨421034, by rfl⟩ : syracuseStep 561379 = 842069) B842069
theorem B495859 : Blo 495792 495859 := bstep (se 1 (by rfl) ⟨371894, by rfl⟩ : syracuseStep 495859 = 743789) B743789
theorem B495875 : Blo 495792 495875 := bstep (se 1 (by rfl) ⟨371906, by rfl⟩ : syracuseStep 495875 = 743813) B743813
theorem B495891 : Blo 495792 495891 := bstep (se 1 (by rfl) ⟨371918, by rfl⟩ : syracuseStep 495891 = 743837) B743837
theorem B495907 : Blo 495792 495907 := bstep (se 1 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 495907 = 743861) B743861
theorem B954659 : Blo 495792 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B2527523 : Blo 495792 2527523 := bstep (se 1 (by rfl) ⟨1895642, by rfl⟩ : syracuseStep 2527523 = 3791285) B3791285
theorem B1675565 : Blo 495792 1675565 := bstep (se 3 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 1675565 = 628337) B628337
theorem B495923 : Blo 495792 495923 := bstep (se 1 (by rfl) ⟨371942, by rfl⟩ : syracuseStep 495923 = 743885) B743885
theorem B495939 : Blo 495792 495939 := bstep (se 1 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 495939 = 743909) B743909
theorem B495955 : Blo 495792 495955 := bstep (se 1 (by rfl) ⟨371966, by rfl⟩ : syracuseStep 495955 = 743933) B743933
theorem B495971 : Blo 495792 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B1675619 : Blo 495792 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B495987 : Blo 495792 495987 := bstep (se 1 (by rfl) ⟨371990, by rfl⟩ : syracuseStep 495987 = 743981) B743981
theorem B561523 : Blo 495792 561523 := bstep (se 1 (by rfl) ⟨421142, by rfl⟩ : syracuseStep 561523 = 842285) B842285
theorem B496003 : Blo 495792 496003 := bstep (se 1 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 496003 = 744005) B744005
theorem B1413521 : Blo 495792 1413521 := bstep (se 2 (by rfl) ⟨530070, by rfl⟩ : syracuseStep 1413521 = 1060141) B1060141
theorem B496019 : Blo 495792 496019 := bstep (se 1 (by rfl) ⟨372014, by rfl⟩ : syracuseStep 496019 = 744029) B744029
theorem B1118609 : Blo 495792 1118609 := bstep (se 2 (by rfl) ⟨419478, by rfl⟩ : syracuseStep 1118609 = 838957) B838957
theorem B496035 : Blo 495792 496035 := bstep (se 1 (by rfl) ⟨372026, by rfl⟩ : syracuseStep 496035 = 744053) B744053
theorem B1118627 : Blo 495792 1118627 := bstep (se 1 (by rfl) ⟨838970, by rfl⟩ : syracuseStep 1118627 = 1677941) B1677941
theorem B496051 : Blo 495792 496051 := bstep (se 1 (by rfl) ⟨372038, by rfl⟩ : syracuseStep 496051 = 744077) B744077
theorem B496067 : Blo 495792 496067 := bstep (se 1 (by rfl) ⟨372050, by rfl⟩ : syracuseStep 496067 = 744101) B744101
theorem B496083 : Blo 495792 496083 := bstep (se 1 (by rfl) ⟨372062, by rfl⟩ : syracuseStep 496083 = 744125) B744125
theorem B496099 : Blo 495792 496099 := bstep (se 1 (by rfl) ⟨372074, by rfl⟩ : syracuseStep 496099 = 744149) B744149
theorem B496115 : Blo 495792 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B496131 : Blo 495792 496131 := bstep (se 1 (by rfl) ⟨372098, by rfl⟩ : syracuseStep 496131 = 744197) B744197
theorem B561667 : Blo 495792 561667 := bstep (se 1 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 561667 = 842501) B842501
theorem B496147 : Blo 495792 496147 := bstep (se 1 (by rfl) ⟨372110, by rfl⟩ : syracuseStep 496147 = 744221) B744221
theorem B496163 : Blo 495792 496163 := bstep (se 1 (by rfl) ⟨372122, by rfl⟩ : syracuseStep 496163 = 744245) B744245
theorem B496179 : Blo 495792 496179 := bstep (se 1 (by rfl) ⟨372134, by rfl⟩ : syracuseStep 496179 = 744269) B744269
theorem B496195 : Blo 495792 496195 := bstep (se 1 (by rfl) ⟨372146, by rfl⟩ : syracuseStep 496195 = 744293) B744293
theorem B1413713 : Blo 495792 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B496211 : Blo 495792 496211 := bstep (se 1 (by rfl) ⟨372158, by rfl⟩ : syracuseStep 496211 = 744317) B744317
theorem B496227 : Blo 495792 496227 := bstep (se 1 (by rfl) ⟨372170, by rfl⟩ : syracuseStep 496227 = 744341) B744341
theorem B1675889 : Blo 495792 1675889 := bstep (se 2 (by rfl) ⟨628458, by rfl⟩ : syracuseStep 1675889 = 1256917) B1256917
theorem B7180913 : Blo 495792 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B496243 : Blo 495792 496243 := bstep (se 1 (by rfl) ⟨372182, by rfl⟩ : syracuseStep 496243 = 744365) B744365
theorem B496259 : Blo 495792 496259 := bstep (se 1 (by rfl) ⟨372194, by rfl⟩ : syracuseStep 496259 = 744389) B744389
theorem B496275 : Blo 495792 496275 := bstep (se 1 (by rfl) ⟨372206, by rfl⟩ : syracuseStep 496275 = 744413) B744413
theorem B561811 : Blo 495792 561811 := bstep (se 1 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 561811 = 842717) B842717
theorem B496291 : Blo 495792 496291 := bstep (se 1 (by rfl) ⟨372218, by rfl⟩ : syracuseStep 496291 = 744437) B744437
theorem B1118897 : Blo 495792 1118897 := bstep (se 2 (by rfl) ⟨419586, by rfl⟩ : syracuseStep 1118897 = 839173) B839173
theorem B496307 : Blo 495792 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B496323 : Blo 495792 496323 := bstep (se 1 (by rfl) ⟨372242, by rfl⟩ : syracuseStep 496323 = 744485) B744485
theorem B1118915 : Blo 495792 1118915 := bstep (se 1 (by rfl) ⟨839186, by rfl⟩ : syracuseStep 1118915 = 1678373) B1678373
theorem B496339 : Blo 495792 496339 := bstep (se 1 (by rfl) ⟨372254, by rfl⟩ : syracuseStep 496339 = 744509) B744509
theorem B496355 : Blo 495792 496355 := bstep (se 1 (by rfl) ⟨372266, by rfl⟩ : syracuseStep 496355 = 744533) B744533
theorem B496371 : Blo 495792 496371 := bstep (se 1 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 496371 = 744557) B744557
theorem B496387 : Blo 495792 496387 := bstep (se 1 (by rfl) ⟨372290, by rfl⟩ : syracuseStep 496387 = 744581) B744581
theorem B758531 : Blo 495792 758531 := bstep (se 1 (by rfl) ⟨568898, by rfl⟩ : syracuseStep 758531 = 1137797) B1137797
theorem B496403 : Blo 495792 496403 := bstep (se 1 (by rfl) ⟨372302, by rfl⟩ : syracuseStep 496403 = 744605) B744605
theorem B496419 : Blo 495792 496419 := bstep (se 1 (by rfl) ⟨372314, by rfl⟩ : syracuseStep 496419 = 744629) B744629
theorem B561955 : Blo 495792 561955 := bstep (se 1 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 561955 = 842933) B842933
theorem B496435 : Blo 495792 496435 := bstep (se 1 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 496435 = 744653) B744653
theorem B496451 : Blo 495792 496451 := bstep (se 1 (by rfl) ⟨372338, by rfl⟩ : syracuseStep 496451 = 744677) B744677
theorem B496467 : Blo 495792 496467 := bstep (se 1 (by rfl) ⟨372350, by rfl⟩ : syracuseStep 496467 = 744701) B744701
theorem B496483 : Blo 495792 496483 := bstep (se 1 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 496483 = 744725) B744725
theorem B758627 : Blo 495792 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B496499 : Blo 495792 496499 := bstep (se 1 (by rfl) ⟨372374, by rfl⟩ : syracuseStep 496499 = 744749) B744749
theorem B496515 : Blo 495792 496515 := bstep (se 1 (by rfl) ⟨372386, by rfl⟩ : syracuseStep 496515 = 744773) B744773
theorem B496531 : Blo 495792 496531 := bstep (se 1 (by rfl) ⟨372398, by rfl⟩ : syracuseStep 496531 = 744797) B744797
theorem B496547 : Blo 495792 496547 := bstep (se 1 (by rfl) ⟨372410, by rfl⟩ : syracuseStep 496547 = 744821) B744821
theorem B496563 : Blo 495792 496563 := bstep (se 1 (by rfl) ⟨372422, by rfl⟩ : syracuseStep 496563 = 744845) B744845
theorem B562099 : Blo 495792 562099 := bstep (se 1 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 562099 = 843149) B843149
theorem B496579 : Blo 495792 496579 := bstep (se 1 (by rfl) ⟨372434, by rfl⟩ : syracuseStep 496579 = 744869) B744869
theorem B1119185 : Blo 495792 1119185 := bstep (se 2 (by rfl) ⟨419694, by rfl⟩ : syracuseStep 1119185 = 839389) B839389
theorem B496595 : Blo 495792 496595 := bstep (se 1 (by rfl) ⟨372446, by rfl⟩ : syracuseStep 496595 = 744893) B744893
theorem B496611 : Blo 495792 496611 := bstep (se 1 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 496611 = 744917) B744917
theorem B1119203 : Blo 495792 1119203 := bstep (se 1 (by rfl) ⟨839402, by rfl⟩ : syracuseStep 1119203 = 1678805) B1678805
theorem B496627 : Blo 495792 496627 := bstep (se 1 (by rfl) ⟨372470, by rfl⟩ : syracuseStep 496627 = 744941) B744941
theorem B496643 : Blo 495792 496643 := bstep (se 1 (by rfl) ⟨372482, by rfl⟩ : syracuseStep 496643 = 744965) B744965
theorem B496659 : Blo 495792 496659 := bstep (se 1 (by rfl) ⟨372494, by rfl⟩ : syracuseStep 496659 = 744989) B744989
theorem B496675 : Blo 495792 496675 := bstep (se 1 (by rfl) ⟨372506, by rfl⟩ : syracuseStep 496675 = 745013) B745013
theorem B529459 : Blo 495792 529459 := bstep (se 1 (by rfl) ⟨397094, by rfl⟩ : syracuseStep 529459 = 794189) B794189
theorem B496691 : Blo 495792 496691 := bstep (se 1 (by rfl) ⟨372518, by rfl⟩ : syracuseStep 496691 = 745037) B745037
theorem B496707 : Blo 495792 496707 := bstep (se 1 (by rfl) ⟨372530, by rfl⟩ : syracuseStep 496707 = 745061) B745061
theorem B562243 : Blo 495792 562243 := bstep (se 1 (by rfl) ⟨421682, by rfl⟩ : syracuseStep 562243 = 843365) B843365
theorem B2528333 : Blo 495792 2528333 := bstep (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) B948125
theorem B496723 : Blo 495792 496723 := bstep (se 1 (by rfl) ⟨372542, by rfl⟩ : syracuseStep 496723 = 745085) B745085
theorem B496739 : Blo 495792 496739 := bstep (se 1 (by rfl) ⟨372554, by rfl⟩ : syracuseStep 496739 = 745109) B745109
theorem B6362225 : Blo 495792 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B496755 : Blo 495792 496755 := bstep (se 1 (by rfl) ⟨372566, by rfl⟩ : syracuseStep 496755 = 745133) B745133
theorem B496771 : Blo 495792 496771 := bstep (se 1 (by rfl) ⟨372578, by rfl⟩ : syracuseStep 496771 = 745157) B745157
theorem B1676429 : Blo 495792 1676429 := bstep (se 3 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 1676429 = 628661) B628661
theorem B496787 : Blo 495792 496787 := bstep (se 1 (by rfl) ⟨372590, by rfl⟩ : syracuseStep 496787 = 745181) B745181
theorem B496803 : Blo 495792 496803 := bstep (se 1 (by rfl) ⟨372602, by rfl⟩ : syracuseStep 496803 = 745205) B745205
theorem B496819 : Blo 495792 496819 := bstep (se 1 (by rfl) ⟨372614, by rfl⟩ : syracuseStep 496819 = 745229) B745229
theorem B627907 : Blo 495792 627907 := bstep (se 1 (by rfl) ⟨470930, by rfl⟩ : syracuseStep 627907 = 941861) B941861
theorem B1676483 : Blo 495792 1676483 := bstep (se 1 (by rfl) ⟨1257362, by rfl⟩ : syracuseStep 1676483 = 2514725) B2514725
theorem B496835 : Blo 495792 496835 := bstep (se 1 (by rfl) ⟨372626, by rfl⟩ : syracuseStep 496835 = 745253) B745253
theorem B496851 : Blo 495792 496851 := bstep (se 1 (by rfl) ⟨372638, by rfl⟩ : syracuseStep 496851 = 745277) B745277
theorem B496867 : Blo 495792 496867 := bstep (se 1 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 496867 = 745301) B745301
theorem B1119473 : Blo 495792 1119473 := bstep (se 2 (by rfl) ⟨419802, by rfl⟩ : syracuseStep 1119473 = 839605) B839605
theorem B496883 : Blo 495792 496883 := bstep (se 1 (by rfl) ⟨372662, by rfl⟩ : syracuseStep 496883 = 745325) B745325
theorem B496899 : Blo 495792 496899 := bstep (se 1 (by rfl) ⟨372674, by rfl⟩ : syracuseStep 496899 = 745349) B745349
theorem B1119491 : Blo 495792 1119491 := bstep (se 1 (by rfl) ⟨839618, by rfl⟩ : syracuseStep 1119491 = 1679237) B1679237
theorem B496915 : Blo 495792 496915 := bstep (se 1 (by rfl) ⟨372686, by rfl⟩ : syracuseStep 496915 = 745373) B745373
theorem B628003 : Blo 495792 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B3183907 : Blo 495792 3183907 := bstep (se 1 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 3183907 = 4775861) B4775861
theorem B496931 : Blo 495792 496931 := bstep (se 1 (by rfl) ⟨372698, by rfl⟩ : syracuseStep 496931 = 745397) B745397
theorem B496947 : Blo 495792 496947 := bstep (se 1 (by rfl) ⟨372710, by rfl⟩ : syracuseStep 496947 = 745421) B745421
theorem B496963 : Blo 495792 496963 := bstep (se 1 (by rfl) ⟨372722, by rfl⟩ : syracuseStep 496963 = 745445) B745445
theorem B496979 : Blo 495792 496979 := bstep (se 1 (by rfl) ⟨372734, by rfl⟩ : syracuseStep 496979 = 745469) B745469
theorem B496995 : Blo 495792 496995 := bstep (se 1 (by rfl) ⟨372746, by rfl⟩ : syracuseStep 496995 = 745493) B745493
theorem B497011 : Blo 495792 497011 := bstep (se 1 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 497011 = 745517) B745517
theorem B497027 : Blo 495792 497027 := bstep (se 1 (by rfl) ⟨372770, by rfl⟩ : syracuseStep 497027 = 745541) B745541
theorem B497043 : Blo 495792 497043 := bstep (se 1 (by rfl) ⟨372782, by rfl⟩ : syracuseStep 497043 = 745565) B745565
theorem B497059 : Blo 495792 497059 := bstep (se 1 (by rfl) ⟨372794, by rfl⟩ : syracuseStep 497059 = 745589) B745589
theorem B497075 : Blo 495792 497075 := bstep (se 1 (by rfl) ⟨372806, by rfl⟩ : syracuseStep 497075 = 745613) B745613
theorem B497091 : Blo 495792 497091 := bstep (se 1 (by rfl) ⟨372818, by rfl⟩ : syracuseStep 497091 = 745637) B745637
theorem B1676753 : Blo 495792 1676753 := bstep (se 2 (by rfl) ⟨628782, by rfl⟩ : syracuseStep 1676753 = 1257565) B1257565
theorem B497107 : Blo 495792 497107 := bstep (se 1 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 497107 = 745661) B745661
theorem B497123 : Blo 495792 497123 := bstep (se 1 (by rfl) ⟨372842, by rfl⟩ : syracuseStep 497123 = 745685) B745685
theorem B497139 : Blo 495792 497139 := bstep (se 1 (by rfl) ⟨372854, by rfl⟩ : syracuseStep 497139 = 745709) B745709
theorem B497155 : Blo 495792 497155 := bstep (se 1 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 497155 = 745733) B745733
theorem B1119761 : Blo 495792 1119761 := bstep (se 2 (by rfl) ⟨419910, by rfl⟩ : syracuseStep 1119761 = 839821) B839821
theorem B497171 : Blo 495792 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B497187 : Blo 495792 497187 := bstep (se 1 (by rfl) ⟨372890, by rfl⟩ : syracuseStep 497187 = 745781) B745781
theorem B1119779 : Blo 495792 1119779 := bstep (se 1 (by rfl) ⟨839834, by rfl⟩ : syracuseStep 1119779 = 1679669) B1679669
theorem B1414705 : Blo 495792 1414705 := bstep (se 2 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 1414705 = 1061029) B1061029
theorem B497203 : Blo 495792 497203 := bstep (se 1 (by rfl) ⟨372902, by rfl⟩ : syracuseStep 497203 = 745805) B745805
theorem B497219 : Blo 495792 497219 := bstep (se 1 (by rfl) ⟨372914, by rfl⟩ : syracuseStep 497219 = 745829) B745829
theorem B497235 : Blo 495792 497235 := bstep (se 1 (by rfl) ⟨372926, by rfl⟩ : syracuseStep 497235 = 745853) B745853
theorem B497251 : Blo 495792 497251 := bstep (se 1 (by rfl) ⟨372938, by rfl⟩ : syracuseStep 497251 = 745877) B745877
theorem B497267 : Blo 495792 497267 := bstep (se 1 (by rfl) ⟨372950, by rfl⟩ : syracuseStep 497267 = 745901) B745901
theorem B497283 : Blo 495792 497283 := bstep (se 1 (by rfl) ⟨372962, by rfl⟩ : syracuseStep 497283 = 745925) B745925
theorem B497299 : Blo 495792 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B497315 : Blo 495792 497315 := bstep (se 1 (by rfl) ⟨372986, by rfl⟩ : syracuseStep 497315 = 745973) B745973
theorem B497331 : Blo 495792 497331 := bstep (se 1 (by rfl) ⟨372998, by rfl⟩ : syracuseStep 497331 = 745997) B745997
theorem B497347 : Blo 495792 497347 := bstep (se 1 (by rfl) ⟨373010, by rfl⟩ : syracuseStep 497347 = 746021) B746021
theorem B497363 : Blo 495792 497363 := bstep (se 1 (by rfl) ⟨373022, by rfl⟩ : syracuseStep 497363 = 746045) B746045
theorem B497379 : Blo 495792 497379 := bstep (se 1 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 497379 = 746069) B746069
theorem B497395 : Blo 495792 497395 := bstep (se 1 (by rfl) ⟨373046, by rfl⟩ : syracuseStep 497395 = 746093) B746093
theorem B497411 : Blo 495792 497411 := bstep (se 1 (by rfl) ⟨373058, by rfl⟩ : syracuseStep 497411 = 746117) B746117
theorem B628499 : Blo 495792 628499 := bstep (se 1 (by rfl) ⟨471374, by rfl⟩ : syracuseStep 628499 = 942749) B942749
theorem B497427 : Blo 495792 497427 := bstep (se 1 (by rfl) ⟨373070, by rfl⟩ : syracuseStep 497427 = 746141) B746141
theorem B497443 : Blo 495792 497443 := bstep (se 1 (by rfl) ⟨373082, by rfl⟩ : syracuseStep 497443 = 746165) B746165
theorem B1120049 : Blo 495792 1120049 := bstep (se 2 (by rfl) ⟨420018, by rfl⟩ : syracuseStep 1120049 = 840037) B840037
theorem B497459 : Blo 495792 497459 := bstep (se 1 (by rfl) ⟨373094, by rfl⟩ : syracuseStep 497459 = 746189) B746189
theorem B1414979 : Blo 495792 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B497475 : Blo 495792 497475 := bstep (se 1 (by rfl) ⟨373106, by rfl⟩ : syracuseStep 497475 = 746213) B746213
theorem B1120067 : Blo 495792 1120067 := bstep (se 1 (by rfl) ⟨840050, by rfl⟩ : syracuseStep 1120067 = 1680101) B1680101
theorem B497491 : Blo 495792 497491 := bstep (se 1 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 497491 = 746237) B746237
theorem B497507 : Blo 495792 497507 := bstep (se 1 (by rfl) ⟨373130, by rfl⟩ : syracuseStep 497507 = 746261) B746261
theorem B497523 : Blo 495792 497523 := bstep (se 1 (by rfl) ⟨373142, by rfl⟩ : syracuseStep 497523 = 746285) B746285
theorem B497539 : Blo 495792 497539 := bstep (se 1 (by rfl) ⟨373154, by rfl⟩ : syracuseStep 497539 = 746309) B746309
theorem B497555 : Blo 495792 497555 := bstep (se 1 (by rfl) ⟨373166, by rfl⟩ : syracuseStep 497555 = 746333) B746333
theorem B497571 : Blo 495792 497571 := bstep (se 1 (by rfl) ⟨373178, by rfl⟩ : syracuseStep 497571 = 746357) B746357
theorem B3446705 : Blo 495792 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B497587 : Blo 495792 497587 := bstep (se 1 (by rfl) ⟨373190, by rfl⟩ : syracuseStep 497587 = 746381) B746381
theorem B497603 : Blo 495792 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B497619 : Blo 495792 497619 := bstep (se 1 (by rfl) ⟨373214, by rfl⟩ : syracuseStep 497619 = 746429) B746429
theorem B497635 : Blo 495792 497635 := bstep (se 1 (by rfl) ⟨373226, by rfl⟩ : syracuseStep 497635 = 746453) B746453
theorem B1677293 : Blo 495792 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B497651 : Blo 495792 497651 := bstep (se 1 (by rfl) ⟨373238, by rfl⟩ : syracuseStep 497651 = 746477) B746477
theorem B1415171 : Blo 495792 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B497667 : Blo 495792 497667 := bstep (se 1 (by rfl) ⟨373250, by rfl⟩ : syracuseStep 497667 = 746501) B746501
theorem B497683 : Blo 495792 497683 := bstep (se 1 (by rfl) ⟨373262, by rfl⟩ : syracuseStep 497683 = 746525) B746525
theorem B1677347 : Blo 495792 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B497699 : Blo 495792 497699 := bstep (se 1 (by rfl) ⟨373274, by rfl⟩ : syracuseStep 497699 = 746549) B746549
theorem B497715 : Blo 495792 497715 := bstep (se 1 (by rfl) ⟨373286, by rfl⟩ : syracuseStep 497715 = 746573) B746573
theorem B497731 : Blo 495792 497731 := bstep (se 1 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 497731 = 746597) B746597
theorem B1120337 : Blo 495792 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B497747 : Blo 495792 497747 := bstep (se 1 (by rfl) ⟨373310, by rfl⟩ : syracuseStep 497747 = 746621) B746621
theorem B497763 : Blo 495792 497763 := bstep (se 1 (by rfl) ⟨373322, by rfl⟩ : syracuseStep 497763 = 746645) B746645
theorem B1120355 : Blo 495792 1120355 := bstep (se 1 (by rfl) ⟨840266, by rfl⟩ : syracuseStep 1120355 = 1680533) B1680533
theorem B497779 : Blo 495792 497779 := bstep (se 1 (by rfl) ⟨373334, by rfl⟩ : syracuseStep 497779 = 746669) B746669
theorem B497795 : Blo 495792 497795 := bstep (se 1 (by rfl) ⟨373346, by rfl⟩ : syracuseStep 497795 = 746693) B746693
theorem B497811 : Blo 495792 497811 := bstep (se 1 (by rfl) ⟨373358, by rfl⟩ : syracuseStep 497811 = 746717) B746717
theorem B497827 : Blo 495792 497827 := bstep (se 1 (by rfl) ⟨373370, by rfl⟩ : syracuseStep 497827 = 746741) B746741
theorem B1349795 : Blo 495792 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B497843 : Blo 495792 497843 := bstep (se 1 (by rfl) ⟨373382, by rfl⟩ : syracuseStep 497843 = 746765) B746765
theorem B497859 : Blo 495792 497859 := bstep (se 1 (by rfl) ⟨373394, by rfl⟩ : syracuseStep 497859 = 746789) B746789
theorem B497875 : Blo 495792 497875 := bstep (se 1 (by rfl) ⟨373406, by rfl⟩ : syracuseStep 497875 = 746813) B746813
theorem B497891 : Blo 495792 497891 := bstep (se 1 (by rfl) ⟨373418, by rfl⟩ : syracuseStep 497891 = 746837) B746837
theorem B497907 : Blo 495792 497907 := bstep (se 1 (by rfl) ⟨373430, by rfl⟩ : syracuseStep 497907 = 746861) B746861
theorem B497923 : Blo 495792 497923 := bstep (se 1 (by rfl) ⟨373442, by rfl⟩ : syracuseStep 497923 = 746885) B746885
theorem B497939 : Blo 495792 497939 := bstep (se 1 (by rfl) ⟨373454, by rfl⟩ : syracuseStep 497939 = 746909) B746909
theorem B497955 : Blo 495792 497955 := bstep (se 1 (by rfl) ⟨373466, by rfl⟩ : syracuseStep 497955 = 746933) B746933
theorem B1677617 : Blo 495792 1677617 := bstep (se 2 (by rfl) ⟨629106, by rfl⟩ : syracuseStep 1677617 = 1258213) B1258213
theorem B497971 : Blo 495792 497971 := bstep (se 1 (by rfl) ⟨373478, by rfl⟩ : syracuseStep 497971 = 746957) B746957
theorem B497987 : Blo 495792 497987 := bstep (se 1 (by rfl) ⟨373490, by rfl⟩ : syracuseStep 497987 = 746981) B746981
theorem B498003 : Blo 495792 498003 := bstep (se 1 (by rfl) ⟨373502, by rfl⟩ : syracuseStep 498003 = 747005) B747005
theorem B498019 : Blo 495792 498019 := bstep (se 1 (by rfl) ⟨373514, by rfl⟩ : syracuseStep 498019 = 747029) B747029
theorem B1120625 : Blo 495792 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B498035 : Blo 495792 498035 := bstep (se 1 (by rfl) ⟨373526, by rfl⟩ : syracuseStep 498035 = 747053) B747053
theorem B498051 : Blo 495792 498051 := bstep (se 1 (by rfl) ⟨373538, by rfl⟩ : syracuseStep 498051 = 747077) B747077
theorem B1120643 : Blo 495792 1120643 := bstep (se 1 (by rfl) ⟨840482, by rfl⟩ : syracuseStep 1120643 = 1680965) B1680965
theorem B498067 : Blo 495792 498067 := bstep (se 1 (by rfl) ⟨373550, by rfl⟩ : syracuseStep 498067 = 747101) B747101
theorem B498083 : Blo 495792 498083 := bstep (se 1 (by rfl) ⟨373562, by rfl⟩ : syracuseStep 498083 = 747125) B747125
theorem B498099 : Blo 495792 498099 := bstep (se 1 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 498099 = 747149) B747149
theorem B498115 : Blo 495792 498115 := bstep (se 1 (by rfl) ⟨373586, by rfl⟩ : syracuseStep 498115 = 747173) B747173
theorem B629203 : Blo 495792 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B498131 : Blo 495792 498131 := bstep (se 1 (by rfl) ⟨373598, by rfl⟩ : syracuseStep 498131 = 747197) B747197
theorem B498147 : Blo 495792 498147 := bstep (se 1 (by rfl) ⟨373610, by rfl⟩ : syracuseStep 498147 = 747221) B747221
theorem B498163 : Blo 495792 498163 := bstep (se 1 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 498163 = 747245) B747245
theorem B498179 : Blo 495792 498179 := bstep (se 1 (by rfl) ⟨373634, by rfl⟩ : syracuseStep 498179 = 747269) B747269
theorem B498195 : Blo 495792 498195 := bstep (se 1 (by rfl) ⟨373646, by rfl⟩ : syracuseStep 498195 = 747293) B747293
theorem B2824739 : Blo 495792 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B498211 : Blo 495792 498211 := bstep (se 1 (by rfl) ⟨373658, by rfl⟩ : syracuseStep 498211 = 747317) B747317
theorem B629299 : Blo 495792 629299 := bstep (se 1 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 629299 = 943949) B943949
theorem B498227 : Blo 495792 498227 := bstep (se 1 (by rfl) ⟨373670, by rfl⟩ : syracuseStep 498227 = 747341) B747341
theorem B498243 : Blo 495792 498243 := bstep (se 1 (by rfl) ⟨373682, by rfl⟩ : syracuseStep 498243 = 747365) B747365
theorem B4528709 : Blo 495792 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B498259 : Blo 495792 498259 := bstep (se 1 (by rfl) ⟨373694, by rfl⟩ : syracuseStep 498259 = 747389) B747389
theorem B498275 : Blo 495792 498275 := bstep (se 1 (by rfl) ⟨373706, by rfl⟩ : syracuseStep 498275 = 747413) B747413
theorem B498291 : Blo 495792 498291 := bstep (se 1 (by rfl) ⟨373718, by rfl⟩ : syracuseStep 498291 = 747437) B747437
theorem B498307 : Blo 495792 498307 := bstep (se 1 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 498307 = 747461) B747461
theorem B1120913 : Blo 495792 1120913 := bstep (se 2 (by rfl) ⟨420342, by rfl⟩ : syracuseStep 1120913 = 840685) B840685
theorem B498323 : Blo 495792 498323 := bstep (se 1 (by rfl) ⟨373742, by rfl⟩ : syracuseStep 498323 = 747485) B747485
theorem B1120931 : Blo 495792 1120931 := bstep (se 1 (by rfl) ⟨840698, by rfl⟩ : syracuseStep 1120931 = 1681397) B1681397
theorem B498339 : Blo 495792 498339 := bstep (se 1 (by rfl) ⟨373754, by rfl⟩ : syracuseStep 498339 = 747509) B747509
theorem B498355 : Blo 495792 498355 := bstep (se 1 (by rfl) ⟨373766, by rfl⟩ : syracuseStep 498355 = 747533) B747533
theorem B498371 : Blo 495792 498371 := bstep (se 1 (by rfl) ⟨373778, by rfl⟩ : syracuseStep 498371 = 747557) B747557
theorem B498387 : Blo 495792 498387 := bstep (se 1 (by rfl) ⟨373790, by rfl⟩ : syracuseStep 498387 = 747581) B747581
theorem B498403 : Blo 495792 498403 := bstep (se 1 (by rfl) ⟨373802, by rfl⟩ : syracuseStep 498403 = 747605) B747605
theorem B498419 : Blo 495792 498419 := bstep (se 1 (by rfl) ⟨373814, by rfl⟩ : syracuseStep 498419 = 747629) B747629
theorem B498435 : Blo 495792 498435 := bstep (se 1 (by rfl) ⟨373826, by rfl⟩ : syracuseStep 498435 = 747653) B747653
theorem B498451 : Blo 495792 498451 := bstep (se 1 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 498451 = 747677) B747677
theorem B498467 : Blo 495792 498467 := bstep (se 1 (by rfl) ⟨373850, by rfl⟩ : syracuseStep 498467 = 747701) B747701
theorem B1415981 : Blo 495792 1415981 := bstep (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) B530993
theorem B498483 : Blo 495792 498483 := bstep (se 1 (by rfl) ⟨373862, by rfl⟩ : syracuseStep 498483 = 747725) B747725
theorem B498499 : Blo 495792 498499 := bstep (se 1 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 498499 = 747749) B747749
theorem B1678157 : Blo 495792 1678157 := bstep (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) B629309
theorem B498515 : Blo 495792 498515 := bstep (se 1 (by rfl) ⟨373886, by rfl⟩ : syracuseStep 498515 = 747773) B747773
theorem B498531 : Blo 495792 498531 := bstep (se 1 (by rfl) ⟨373898, by rfl⟩ : syracuseStep 498531 = 747797) B747797
theorem B498547 : Blo 495792 498547 := bstep (se 1 (by rfl) ⟨373910, by rfl⟩ : syracuseStep 498547 = 747821) B747821
theorem B1678211 : Blo 495792 1678211 := bstep (se 1 (by rfl) ⟨1258658, by rfl⟩ : syracuseStep 1678211 = 2517317) B2517317
theorem B498563 : Blo 495792 498563 := bstep (se 1 (by rfl) ⟨373922, by rfl⟩ : syracuseStep 498563 = 747845) B747845
theorem B498579 : Blo 495792 498579 := bstep (se 1 (by rfl) ⟨373934, by rfl⟩ : syracuseStep 498579 = 747869) B747869
theorem B498595 : Blo 495792 498595 := bstep (se 1 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 498595 = 747893) B747893
theorem B1121201 : Blo 495792 1121201 := bstep (se 2 (by rfl) ⟨420450, by rfl⟩ : syracuseStep 1121201 = 840901) B840901
theorem B498611 : Blo 495792 498611 := bstep (se 1 (by rfl) ⟨373958, by rfl⟩ : syracuseStep 498611 = 747917) B747917
theorem B1121219 : Blo 495792 1121219 := bstep (se 1 (by rfl) ⟨840914, by rfl⟩ : syracuseStep 1121219 = 1681829) B1681829
theorem B498627 : Blo 495792 498627 := bstep (se 1 (by rfl) ⟨373970, by rfl⟩ : syracuseStep 498627 = 747941) B747941
theorem B498643 : Blo 495792 498643 := bstep (se 1 (by rfl) ⟨373982, by rfl⟩ : syracuseStep 498643 = 747965) B747965
theorem B1416163 : Blo 495792 1416163 := bstep (se 1 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 1416163 = 2124245) B2124245
theorem B498659 : Blo 495792 498659 := bstep (se 1 (by rfl) ⟨373994, by rfl⟩ : syracuseStep 498659 = 747989) B747989
theorem B6462449 : Blo 495792 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B498675 : Blo 495792 498675 := bstep (se 1 (by rfl) ⟨374006, by rfl⟩ : syracuseStep 498675 = 748013) B748013
theorem B498691 : Blo 495792 498691 := bstep (se 1 (by rfl) ⟨374018, by rfl⟩ : syracuseStep 498691 = 748037) B748037
theorem B498707 : Blo 495792 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B629795 : Blo 495792 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B498723 : Blo 495792 498723 := bstep (se 1 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 498723 = 748085) B748085
theorem B498739 : Blo 495792 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B498755 : Blo 495792 498755 := bstep (se 1 (by rfl) ⟨374066, by rfl⟩ : syracuseStep 498755 = 748133) B748133
theorem B498771 : Blo 495792 498771 := bstep (se 1 (by rfl) ⟨374078, by rfl⟩ : syracuseStep 498771 = 748157) B748157
theorem B498787 : Blo 495792 498787 := bstep (se 1 (by rfl) ⟨374090, by rfl⟩ : syracuseStep 498787 = 748181) B748181
theorem B498803 : Blo 495792 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B498819 : Blo 495792 498819 := bstep (se 1 (by rfl) ⟨374114, by rfl⟩ : syracuseStep 498819 = 748229) B748229
theorem B1678481 : Blo 495792 1678481 := bstep (se 2 (by rfl) ⟨629430, by rfl⟩ : syracuseStep 1678481 = 1258861) B1258861
theorem B498835 : Blo 495792 498835 := bstep (se 1 (by rfl) ⟨374126, by rfl⟩ : syracuseStep 498835 = 748253) B748253
theorem B498851 : Blo 495792 498851 := bstep (se 1 (by rfl) ⟨374138, by rfl⟩ : syracuseStep 498851 = 748277) B748277
theorem B498867 : Blo 495792 498867 := bstep (se 1 (by rfl) ⟨374150, by rfl⟩ : syracuseStep 498867 = 748301) B748301
theorem B498883 : Blo 495792 498883 := bstep (se 1 (by rfl) ⟨374162, by rfl⟩ : syracuseStep 498883 = 748325) B748325
theorem B1121489 : Blo 495792 1121489 := bstep (se 2 (by rfl) ⟨420558, by rfl⟩ : syracuseStep 1121489 = 841117) B841117
theorem B498899 : Blo 495792 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B498915 : Blo 495792 498915 := bstep (se 1 (by rfl) ⟨374186, by rfl⟩ : syracuseStep 498915 = 748373) B748373
theorem B8494307 : Blo 495792 8494307 := bstep (se 1 (by rfl) ⟨6370730, by rfl⟩ : syracuseStep 8494307 = 12741461) B12741461
theorem B1121507 : Blo 495792 1121507 := bstep (se 1 (by rfl) ⟨841130, by rfl⟩ : syracuseStep 1121507 = 1682261) B1682261
theorem B498931 : Blo 495792 498931 := bstep (se 1 (by rfl) ⟨374198, by rfl⟩ : syracuseStep 498931 = 748397) B748397
theorem B498947 : Blo 495792 498947 := bstep (se 1 (by rfl) ⟨374210, by rfl⟩ : syracuseStep 498947 = 748421) B748421
theorem B498963 : Blo 495792 498963 := bstep (se 1 (by rfl) ⟨374222, by rfl⟩ : syracuseStep 498963 = 748445) B748445
theorem B498979 : Blo 495792 498979 := bstep (se 1 (by rfl) ⟨374234, by rfl⟩ : syracuseStep 498979 = 748469) B748469
theorem B498995 : Blo 495792 498995 := bstep (se 1 (by rfl) ⟨374246, by rfl⟩ : syracuseStep 498995 = 748493) B748493
theorem B499011 : Blo 495792 499011 := bstep (se 1 (by rfl) ⟨374258, by rfl⟩ : syracuseStep 499011 = 748517) B748517
theorem B499027 : Blo 495792 499027 := bstep (se 1 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 499027 = 748541) B748541
theorem B1023331 : Blo 495792 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B499043 : Blo 495792 499043 := bstep (se 1 (by rfl) ⟨374282, by rfl⟩ : syracuseStep 499043 = 748565) B748565
theorem B499059 : Blo 495792 499059 := bstep (se 1 (by rfl) ⟨374294, by rfl⟩ : syracuseStep 499059 = 748589) B748589
theorem B499075 : Blo 495792 499075 := bstep (se 1 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 499075 = 748613) B748613
theorem B499091 : Blo 495792 499091 := bstep (se 1 (by rfl) ⟨374318, by rfl⟩ : syracuseStep 499091 = 748637) B748637
theorem B499107 : Blo 495792 499107 := bstep (se 1 (by rfl) ⟨374330, by rfl⟩ : syracuseStep 499107 = 748661) B748661
theorem B499123 : Blo 495792 499123 := bstep (se 1 (by rfl) ⟨374342, by rfl⟩ : syracuseStep 499123 = 748685) B748685
theorem B499139 : Blo 495792 499139 := bstep (se 1 (by rfl) ⟨374354, by rfl⟩ : syracuseStep 499139 = 748709) B748709
theorem B1416653 : Blo 495792 1416653 := bstep (se 3 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 1416653 = 531245) B531245
theorem B499155 : Blo 495792 499155 := bstep (se 1 (by rfl) ⟨374366, by rfl⟩ : syracuseStep 499155 = 748733) B748733
theorem B499171 : Blo 495792 499171 := bstep (se 1 (by rfl) ⟨374378, by rfl⟩ : syracuseStep 499171 = 748757) B748757
theorem B1121777 : Blo 495792 1121777 := bstep (se 2 (by rfl) ⟨420666, by rfl⟩ : syracuseStep 1121777 = 841333) B841333
theorem B499187 : Blo 495792 499187 := bstep (se 1 (by rfl) ⟨374390, by rfl⟩ : syracuseStep 499187 = 748781) B748781
theorem B1121795 : Blo 495792 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B499203 : Blo 495792 499203 := bstep (se 1 (by rfl) ⟨374402, by rfl⟩ : syracuseStep 499203 = 748805) B748805
theorem B499219 : Blo 495792 499219 := bstep (se 1 (by rfl) ⟨374414, by rfl⟩ : syracuseStep 499219 = 748829) B748829
theorem B499235 : Blo 495792 499235 := bstep (se 1 (by rfl) ⟨374426, by rfl⟩ : syracuseStep 499235 = 748853) B748853
theorem B499251 : Blo 495792 499251 := bstep (se 1 (by rfl) ⟨374438, by rfl⟩ : syracuseStep 499251 = 748877) B748877
theorem B499267 : Blo 495792 499267 := bstep (se 1 (by rfl) ⟨374450, by rfl⟩ : syracuseStep 499267 = 748901) B748901
theorem B499283 : Blo 495792 499283 := bstep (se 1 (by rfl) ⟨374462, by rfl⟩ : syracuseStep 499283 = 748925) B748925
theorem B499299 : Blo 495792 499299 := bstep (se 1 (by rfl) ⟨374474, by rfl⟩ : syracuseStep 499299 = 748949) B748949
theorem B499315 : Blo 495792 499315 := bstep (se 1 (by rfl) ⟨374486, by rfl⟩ : syracuseStep 499315 = 748973) B748973
theorem B532099 : Blo 495792 532099 := bstep (se 1 (by rfl) ⟨399074, by rfl⟩ : syracuseStep 532099 = 798149) B798149
theorem B499331 : Blo 495792 499331 := bstep (se 1 (by rfl) ⟨374498, by rfl⟩ : syracuseStep 499331 = 748997) B748997
theorem B499347 : Blo 495792 499347 := bstep (se 1 (by rfl) ⟨374510, by rfl⟩ : syracuseStep 499347 = 749021) B749021
theorem B499363 : Blo 495792 499363 := bstep (se 1 (by rfl) ⟨374522, by rfl⟩ : syracuseStep 499363 = 749045) B749045
theorem B1679021 : Blo 495792 1679021 := bstep (se 3 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 1679021 = 629633) B629633
theorem B794291 : Blo 495792 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B499379 : Blo 495792 499379 := bstep (se 1 (by rfl) ⟨374534, by rfl⟩ : syracuseStep 499379 = 749069) B749069
theorem B499395 : Blo 495792 499395 := bstep (se 1 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 499395 = 749093) B749093
theorem B499411 : Blo 495792 499411 := bstep (se 1 (by rfl) ⟨374558, by rfl⟩ : syracuseStep 499411 = 749117) B749117
theorem B1679075 : Blo 495792 1679075 := bstep (se 1 (by rfl) ⟨1259306, by rfl⟩ : syracuseStep 1679075 = 2518613) B2518613
theorem B630499 : Blo 495792 630499 := bstep (se 1 (by rfl) ⟨472874, by rfl⟩ : syracuseStep 630499 = 945749) B945749
theorem B499427 : Blo 495792 499427 := bstep (se 1 (by rfl) ⟨374570, by rfl⟩ : syracuseStep 499427 = 749141) B749141
theorem B499443 : Blo 495792 499443 := bstep (se 1 (by rfl) ⟨374582, by rfl⟩ : syracuseStep 499443 = 749165) B749165
theorem B794369 : Blo 495792 794369 := bstep (se 2 (by rfl) ⟨297888, by rfl⟩ : syracuseStep 794369 = 595777) B595777
theorem B499459 : Blo 495792 499459 := bstep (se 1 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 499459 = 749189) B749189
theorem B1122065 : Blo 495792 1122065 := bstep (se 2 (by rfl) ⟨420774, by rfl⟩ : syracuseStep 1122065 = 841549) B841549
theorem B499475 : Blo 495792 499475 := bstep (se 1 (by rfl) ⟨374606, by rfl⟩ : syracuseStep 499475 = 749213) B749213
theorem B1122083 : Blo 495792 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B499491 : Blo 495792 499491 := bstep (se 1 (by rfl) ⟨374618, by rfl⟩ : syracuseStep 499491 = 749237) B749237
theorem B499507 : Blo 495792 499507 := bstep (se 1 (by rfl) ⟨374630, by rfl⟩ : syracuseStep 499507 = 749261) B749261
theorem B630595 : Blo 495792 630595 := bstep (se 1 (by rfl) ⟨472946, by rfl⟩ : syracuseStep 630595 = 945893) B945893
theorem B499523 : Blo 495792 499523 := bstep (se 1 (by rfl) ⟨374642, by rfl⟩ : syracuseStep 499523 = 749285) B749285
theorem B499539 : Blo 495792 499539 := bstep (se 1 (by rfl) ⟨374654, by rfl⟩ : syracuseStep 499539 = 749309) B749309
theorem B499555 : Blo 495792 499555 := bstep (se 1 (by rfl) ⟨374666, by rfl⟩ : syracuseStep 499555 = 749333) B749333
theorem B499571 : Blo 495792 499571 := bstep (se 1 (by rfl) ⟨374678, by rfl⟩ : syracuseStep 499571 = 749357) B749357
theorem B1515395 : Blo 495792 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B499587 : Blo 495792 499587 := bstep (se 1 (by rfl) ⟨374690, by rfl⟩ : syracuseStep 499587 = 749381) B749381
theorem B499603 : Blo 495792 499603 := bstep (se 1 (by rfl) ⟨374702, by rfl⟩ : syracuseStep 499603 = 749405) B749405
theorem B499619 : Blo 495792 499619 := bstep (se 1 (by rfl) ⟨374714, by rfl⟩ : syracuseStep 499619 = 749429) B749429
theorem B499635 : Blo 495792 499635 := bstep (se 1 (by rfl) ⟨374726, by rfl⟩ : syracuseStep 499635 = 749453) B749453
theorem B499651 : Blo 495792 499651 := bstep (se 1 (by rfl) ⟨374738, by rfl⟩ : syracuseStep 499651 = 749477) B749477
theorem B499667 : Blo 495792 499667 := bstep (se 1 (by rfl) ⟨374750, by rfl⟩ : syracuseStep 499667 = 749501) B749501
theorem B499683 : Blo 495792 499683 := bstep (se 1 (by rfl) ⟨374762, by rfl⟩ : syracuseStep 499683 = 749525) B749525
theorem B4530161 : Blo 495792 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B1679345 : Blo 495792 1679345 := bstep (se 2 (by rfl) ⟨629754, by rfl⟩ : syracuseStep 1679345 = 1259509) B1259509
theorem B499699 : Blo 495792 499699 := bstep (se 1 (by rfl) ⟨374774, by rfl⟩ : syracuseStep 499699 = 749549) B749549
theorem B499715 : Blo 495792 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B3186701 : Blo 495792 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B499731 : Blo 495792 499731 := bstep (se 1 (by rfl) ⟨374798, by rfl⟩ : syracuseStep 499731 = 749597) B749597
theorem B499747 : Blo 495792 499747 := bstep (se 1 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 499747 = 749621) B749621
theorem B1122353 : Blo 495792 1122353 := bstep (se 2 (by rfl) ⟨420882, by rfl⟩ : syracuseStep 1122353 = 841765) B841765
theorem B532531 : Blo 495792 532531 := bstep (se 1 (by rfl) ⟨399398, by rfl⟩ : syracuseStep 532531 = 798797) B798797
theorem B499763 : Blo 495792 499763 := bstep (se 1 (by rfl) ⟨374822, by rfl⟩ : syracuseStep 499763 = 749645) B749645
theorem B1122371 : Blo 495792 1122371 := bstep (se 1 (by rfl) ⟨841778, by rfl⟩ : syracuseStep 1122371 = 1683557) B1683557
theorem B499779 : Blo 495792 499779 := bstep (se 1 (by rfl) ⟨374834, by rfl⟩ : syracuseStep 499779 = 749669) B749669
theorem B794753 : Blo 495792 794753 := bstep (se 2 (by rfl) ⟨298032, by rfl⟩ : syracuseStep 794753 = 596065) B596065
theorem B6037685 : Blo 495792 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B794881 : Blo 495792 794881 := bstep (se 2 (by rfl) ⟨298080, by rfl⟩ : syracuseStep 794881 = 596161) B596161
theorem B631091 : Blo 495792 631091 := bstep (se 1 (by rfl) ⟨473318, by rfl⟩ : syracuseStep 631091 = 946637) B946637
theorem B1122641 : Blo 495792 1122641 := bstep (se 2 (by rfl) ⟨420990, by rfl⟩ : syracuseStep 1122641 = 841981) B841981
theorem B1122659 : Blo 495792 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B1679885 : Blo 495792 1679885 := bstep (se 3 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 1679885 = 629957) B629957
theorem B1679939 : Blo 495792 1679939 := bstep (se 1 (by rfl) ⟨1259954, by rfl⟩ : syracuseStep 1679939 = 2519909) B2519909
theorem B893521 : Blo 495792 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B1417837 : Blo 495792 1417837 := bstep (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) B531689
theorem B1122929 : Blo 495792 1122929 := bstep (se 2 (by rfl) ⟨421098, by rfl⟩ : syracuseStep 1122929 = 842197) B842197
theorem B1122947 : Blo 495792 1122947 := bstep (se 1 (by rfl) ⟨842210, by rfl⟩ : syracuseStep 1122947 = 1684421) B1684421
theorem B566051 : Blo 495792 566051 := bstep (se 1 (by rfl) ⟨424538, by rfl⟩ : syracuseStep 566051 = 849077) B849077
theorem B1680209 : Blo 495792 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B1123217 : Blo 495792 1123217 := bstep (se 2 (by rfl) ⟨421206, by rfl⟩ : syracuseStep 1123217 = 842413) B842413
theorem B1123235 : Blo 495792 1123235 := bstep (se 1 (by rfl) ⟨842426, by rfl⟩ : syracuseStep 1123235 = 1684853) B1684853
theorem B631795 : Blo 495792 631795 := bstep (se 1 (by rfl) ⟨473846, by rfl⟩ : syracuseStep 631795 = 947693) B947693
theorem B6366221 : Blo 495792 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B631891 : Blo 495792 631891 := bstep (se 1 (by rfl) ⟨473918, by rfl⟩ : syracuseStep 631891 = 947837) B947837
theorem B3777677 : Blo 495792 3777677 := bstep (se 3 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 3777677 = 1416629) B1416629
theorem B1123505 : Blo 495792 1123505 := bstep (se 2 (by rfl) ⟨421314, by rfl⟩ : syracuseStep 1123505 = 842629) B842629
theorem B1123523 : Blo 495792 1123523 := bstep (se 1 (by rfl) ⟨842642, by rfl⟩ : syracuseStep 1123523 = 1685285) B1685285
theorem B1680749 : Blo 495792 1680749 := bstep (se 3 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 1680749 = 630281) B630281
theorem B599443 : Blo 495792 599443 := bstep (se 1 (by rfl) ⟨449582, by rfl⟩ : syracuseStep 599443 = 899165) B899165
theorem B1680803 : Blo 495792 1680803 := bstep (se 1 (by rfl) ⟨1260602, by rfl⟩ : syracuseStep 1680803 = 2521205) B2521205
theorem B1516963 : Blo 495792 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B894385 : Blo 495792 894385 := bstep (se 2 (by rfl) ⟨335394, by rfl⟩ : syracuseStep 894385 = 670789) B670789
theorem B1123793 : Blo 495792 1123793 := bstep (se 2 (by rfl) ⟨421422, by rfl⟩ : syracuseStep 1123793 = 842845) B842845
theorem B1910243 : Blo 495792 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1123811 : Blo 495792 1123811 := bstep (se 1 (by rfl) ⟨842858, by rfl⟩ : syracuseStep 1123811 = 1685717) B1685717
theorem B4531697 : Blo 495792 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B632387 : Blo 495792 632387 := bstep (se 1 (by rfl) ⟨474290, by rfl⟩ : syracuseStep 632387 = 948581) B948581
theorem B1418897 : Blo 495792 1418897 := bstep (se 2 (by rfl) ⟨532086, by rfl⟩ : syracuseStep 1418897 = 1064173) B1064173
theorem B1681073 : Blo 495792 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B2827973 : Blo 495792 2827973 := bstep (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) B530245
theorem B796387 : Blo 495792 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B1124081 : Blo 495792 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B1124099 : Blo 495792 1124099 := bstep (se 1 (by rfl) ⟨843074, by rfl⟩ : syracuseStep 1124099 = 1686149) B1686149
theorem B567251 : Blo 495792 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B1255409 : Blo 495792 1255409 := bstep (se 2 (by rfl) ⟨470778, by rfl⟩ : syracuseStep 1255409 = 941557) B941557
theorem B1124369 : Blo 495792 1124369 := bstep (se 2 (by rfl) ⟨421638, by rfl⟩ : syracuseStep 1124369 = 843277) B843277
theorem B1255459 : Blo 495792 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1124387 : Blo 495792 1124387 := bstep (se 1 (by rfl) ⟨843290, by rfl⟩ : syracuseStep 1124387 = 1686581) B1686581
theorem B2828429 : Blo 495792 2828429 := bstep (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) B1060661
theorem B1255601 : Blo 495792 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B1681613 : Blo 495792 1681613 := bstep (se 3 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 1681613 = 630605) B630605
theorem B1681667 : Blo 495792 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1419569 : Blo 495792 1419569 := bstep (se 2 (by rfl) ⟨532338, by rfl⟩ : syracuseStep 1419569 = 1064677) B1064677
theorem B600419 : Blo 495792 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B1616237 : Blo 495792 1616237 := bstep (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) B606089
theorem B797059 : Blo 495792 797059 := bstep (se 1 (by rfl) ⟨597794, by rfl⟩ : syracuseStep 797059 = 1195589) B1195589
theorem B10201571 : Blo 495792 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B1681937 : Blo 495792 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B3222179 : Blo 495792 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B797521 : Blo 495792 797521 := bstep (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) B598141
theorem B797617 : Blo 495792 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B1682477 : Blo 495792 1682477 := bstep (se 3 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 1682477 = 630929) B630929
theorem B1420355 : Blo 495792 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B797777 : Blo 495792 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B1682531 : Blo 495792 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B1256593 : Blo 495792 1256593 := bstep (se 2 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 1256593 = 942445) B942445
theorem B1682801 : Blo 495792 1682801 := bstep (se 2 (by rfl) ⟨631050, by rfl⟩ : syracuseStep 1682801 = 1262101) B1262101
theorem B1420685 : Blo 495792 1420685 := bstep (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) B532757
theorem B1256867 : Blo 495792 1256867 := bstep (se 1 (by rfl) ⟨942650, by rfl⟩ : syracuseStep 1256867 = 1885301) B1885301
theorem B1420753 : Blo 495792 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B2862661 : Blo 495792 2862661 := bstep (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) B536749
theorem B1191505 : Blo 495792 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1257059 : Blo 495792 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B3223217 : Blo 495792 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1421027 : Blo 495792 1421027 := bstep (se 1 (by rfl) ⟨1065770, by rfl⟩ : syracuseStep 1421027 = 2131541) B2131541
theorem B503587 : Blo 495792 503587 := bstep (se 1 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 503587 = 755381) B755381
theorem B4796273 : Blo 495792 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B3583885 : Blo 495792 3583885 := bstep (se 3 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 3583885 = 1343957) B1343957
theorem B1683341 : Blo 495792 1683341 := bstep (se 3 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 1683341 = 631253) B631253
theorem B1683395 : Blo 495792 1683395 := bstep (se 1 (by rfl) ⟨1262546, by rfl⟩ : syracuseStep 1683395 = 2525093) B2525093
theorem B896995 : Blo 495792 896995 := bstep (se 1 (by rfl) ⟨672746, by rfl⟩ : syracuseStep 896995 = 1345493) B1345493
theorem B3780593 : Blo 495792 3780593 := bstep (se 2 (by rfl) ⟨1417722, by rfl⟩ : syracuseStep 3780593 = 2835445) B2835445
theorem B1290289 : Blo 495792 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B1913009 : Blo 495792 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B1683665 : Blo 495792 1683665 := bstep (se 2 (by rfl) ⟨631374, by rfl⟩ : syracuseStep 1683665 = 1262749) B1262749
theorem B1061105 : Blo 495792 1061105 := bstep (se 2 (by rfl) ⟨397914, by rfl⟩ : syracuseStep 1061105 = 795829) B795829
theorem B14332301 : Blo 495792 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1258001 : Blo 495792 1258001 := bstep (se 2 (by rfl) ⟨471750, by rfl⟩ : syracuseStep 1258001 = 943501) B943501
theorem B1421869 : Blo 495792 1421869 := bstep (se 3 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 1421869 = 533201) B533201
theorem B1258051 : Blo 495792 1258051 := bstep (se 1 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 1258051 = 1887077) B1887077
theorem B504451 : Blo 495792 504451 := bstep (se 1 (by rfl) ⟨378338, by rfl⟩ : syracuseStep 504451 = 756677) B756677
theorem B1913507 : Blo 495792 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B1422029 : Blo 495792 1422029 := bstep (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) B533261
theorem B1258193 : Blo 495792 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B1684205 : Blo 495792 1684205 := bstep (se 3 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 1684205 = 631577) B631577
theorem B1684259 : Blo 495792 1684259 := bstep (se 1 (by rfl) ⟨1263194, by rfl⟩ : syracuseStep 1684259 = 2526389) B2526389
theorem B799571 : Blo 495792 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B1422211 : Blo 495792 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B2831345 : Blo 495792 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B1684529 : Blo 495792 1684529 := bstep (se 2 (by rfl) ⟨631698, by rfl⟩ : syracuseStep 1684529 = 1263397) B1263397
theorem B2012273 : Blo 495792 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B6075589 : Blo 495792 6075589 := bstep (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) B1139173
theorem B898307 : Blo 495792 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B1914275 : Blo 495792 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B1685069 : Blo 495792 1685069 := bstep (se 3 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 1685069 = 631901) B631901
theorem B1685123 : Blo 495792 1685123 := bstep (se 1 (by rfl) ⟨1263842, by rfl⟩ : syracuseStep 1685123 = 2527685) B2527685
theorem B800417 : Blo 495792 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B1259185 : Blo 495792 1259185 := bstep (se 2 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 1259185 = 944389) B944389
theorem B898769 : Blo 495792 898769 := bstep (se 2 (by rfl) ⟨337038, by rfl⟩ : syracuseStep 898769 = 674077) B674077
theorem B800545 : Blo 495792 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B505651 : Blo 495792 505651 := bstep (se 1 (by rfl) ⟨379238, by rfl⟩ : syracuseStep 505651 = 758477) B758477
theorem B1685393 : Blo 495792 1685393 := bstep (se 2 (by rfl) ⟨632022, by rfl⟩ : syracuseStep 1685393 = 1264045) B1264045
theorem B1259459 : Blo 495792 1259459 := bstep (se 1 (by rfl) ⟨944594, by rfl⟩ : syracuseStep 1259459 = 1889189) B1889189
theorem B1259651 : Blo 495792 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B899345 : Blo 495792 899345 := bstep (se 2 (by rfl) ⟨337254, by rfl⟩ : syracuseStep 899345 = 674509) B674509
theorem B3193157 : Blo 495792 3193157 := bstep (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) B598717
theorem B2701667 : Blo 495792 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B2832803 : Blo 495792 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1685933 : Blo 495792 1685933 := bstep (se 3 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 1685933 = 632225) B632225
theorem B1685987 : Blo 495792 1685987 := bstep (se 1 (by rfl) ⟨1264490, by rfl⟩ : syracuseStep 1685987 = 2528981) B2528981
theorem B1882673 : Blo 495792 1882673 := bstep (se 2 (by rfl) ⟨706002, by rfl⟩ : syracuseStep 1882673 = 1412005) B1412005
theorem B899633 : Blo 495792 899633 := bstep (se 2 (by rfl) ⟨337362, by rfl⟩ : syracuseStep 899633 = 674725) B674725
theorem B3029645 : Blo 495792 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B506579 : Blo 495792 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B1686257 : Blo 495792 1686257 := bstep (se 2 (by rfl) ⟨632346, by rfl⟩ : syracuseStep 1686257 = 1264693) B1264693
theorem B899857 : Blo 495792 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B899921 : Blo 495792 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B539507 : Blo 495792 539507 := bstep (se 1 (by rfl) ⟨404630, by rfl⟩ : syracuseStep 539507 = 809261) B809261
theorem B1522577 : Blo 495792 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B1260593 : Blo 495792 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B1260643 : Blo 495792 1260643 := bstep (se 1 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 1260643 = 1890965) B1890965
theorem B1260785 : Blo 495792 1260785 := bstep (se 2 (by rfl) ⟨472794, by rfl⟩ : syracuseStep 1260785 = 945589) B945589
theorem B1686797 : Blo 495792 1686797 := bstep (se 3 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 1686797 = 632549) B632549
theorem B2014577 : Blo 495792 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B2833805 : Blo 495792 2833805 := bstep (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) B1062677
theorem B1064515 : Blo 495792 1064515 := bstep (se 1 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 1064515 = 1596773) B1596773
theorem B605923 : Blo 495792 605923 := bstep (se 1 (by rfl) ⟨454442, by rfl⟩ : syracuseStep 605923 = 908885) B908885
theorem B1195811 : Blo 495792 1195811 := bstep (se 1 (by rfl) ⟨896858, by rfl⟩ : syracuseStep 1195811 = 1793717) B1793717
theorem B6799301 : Blo 495792 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B1884131 : Blo 495792 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B1261777 : Blo 495792 1261777 := bstep (se 2 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 1261777 = 946333) B946333
theorem B1589699 : Blo 495792 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B1262051 : Blo 495792 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B1262243 : Blo 495792 1262243 := bstep (se 1 (by rfl) ⟨946682, by rfl⟩ : syracuseStep 1262243 = 1893365) B1893365
theorem B672563 : Blo 495792 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B1885133 : Blo 495792 1885133 := bstep (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) B706925
theorem B3195875 : Blo 495792 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B672833 : Blo 495792 672833 := bstep (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) B504625
theorem B836689 : Blo 495792 836689 := bstep (se 2 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 836689 = 627517) B627517
theorem B836723 : Blo 495792 836723 := bstep (se 1 (by rfl) ⟨627542, by rfl⟩ : syracuseStep 836723 = 1255085) B1255085
theorem B3458189 : Blo 495792 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B836851 : Blo 495792 836851 := bstep (se 1 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 836851 = 1255277) B1255277
theorem B1131875 : Blo 495792 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B836993 : Blo 495792 836993 := bstep (se 2 (by rfl) ⟨313872, by rfl⟩ : syracuseStep 836993 = 627745) B627745
theorem B1066385 : Blo 495792 1066385 := bstep (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) B799789
theorem B837121 : Blo 495792 837121 := bstep (se 2 (by rfl) ⟨313920, by rfl⟩ : syracuseStep 837121 = 627841) B627841
theorem B673297 : Blo 495792 673297 := bstep (se 2 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 673297 = 504973) B504973
theorem B837155 : Blo 495792 837155 := bstep (se 1 (by rfl) ⟨627866, by rfl⟩ : syracuseStep 837155 = 1255733) B1255733
theorem B1263185 : Blo 495792 1263185 := bstep (se 2 (by rfl) ⟨473694, by rfl⟩ : syracuseStep 1263185 = 947389) B947389
theorem B673363 : Blo 495792 673363 := bstep (se 1 (by rfl) ⟨505022, by rfl⟩ : syracuseStep 673363 = 1010045) B1010045
theorem B1263235 : Blo 495792 1263235 := bstep (se 1 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 1263235 = 1894853) B1894853
theorem B837283 : Blo 495792 837283 := bstep (se 1 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 837283 = 1255925) B1255925
theorem B706259 : Blo 495792 706259 := bstep (se 1 (by rfl) ⟨529694, by rfl⟩ : syracuseStep 706259 = 1059389) B1059389
theorem B1263377 : Blo 495792 1263377 := bstep (se 2 (by rfl) ⟨473766, by rfl⟩ : syracuseStep 1263377 = 947533) B947533
theorem B837425 : Blo 495792 837425 := bstep (se 2 (by rfl) ⟨314034, by rfl⟩ : syracuseStep 837425 = 628069) B628069
theorem B837553 : Blo 495792 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B837587 : Blo 495792 837587 := bstep (se 1 (by rfl) ⟨628190, by rfl⟩ : syracuseStep 837587 = 1256381) B1256381
theorem B837715 : Blo 495792 837715 := bstep (se 1 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 837715 = 1256573) B1256573
theorem B837857 : Blo 495792 837857 := bstep (se 2 (by rfl) ⟨314196, by rfl⟩ : syracuseStep 837857 = 628393) B628393
theorem B2836721 : Blo 495792 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B1067249 : Blo 495792 1067249 := bstep (se 2 (by rfl) ⟨400218, by rfl⟩ : syracuseStep 1067249 = 800437) B800437
theorem B706897 : Blo 495792 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B837985 : Blo 495792 837985 := bstep (se 2 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 837985 = 628489) B628489
theorem B838019 : Blo 495792 838019 := bstep (se 1 (by rfl) ⟨628514, by rfl⟩ : syracuseStep 838019 = 1257029) B1257029
theorem B838147 : Blo 495792 838147 := bstep (se 1 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 838147 = 1257221) B1257221
theorem B674401 : Blo 495792 674401 := bstep (se 2 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 674401 = 505801) B505801
theorem B4082275 : Blo 495792 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B838289 : Blo 495792 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B707233 : Blo 495792 707233 := bstep (se 2 (by rfl) ⟨265212, by rfl⟩ : syracuseStep 707233 = 530425) B530425
theorem B1821361 : Blo 495792 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1264369 : Blo 495792 1264369 := bstep (se 2 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 1264369 = 948277) B948277
theorem B1362691 : Blo 495792 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B838417 : Blo 495792 838417 := bstep (se 2 (by rfl) ⟨314406, by rfl⟩ : syracuseStep 838417 = 628813) B628813
theorem B838451 : Blo 495792 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B4049777 : Blo 495792 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B3197873 : Blo 495792 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B838579 : Blo 495792 838579 := bstep (se 1 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 838579 = 1257869) B1257869
theorem B1592273 : Blo 495792 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B1264643 : Blo 495792 1264643 := bstep (se 1 (by rfl) ⟨948482, by rfl⟩ : syracuseStep 1264643 = 1896965) B1896965
theorem B1887245 : Blo 495792 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B838721 : Blo 495792 838721 := bstep (se 2 (by rfl) ⟨314520, by rfl⟩ : syracuseStep 838721 = 629041) B629041
theorem B838849 : Blo 495792 838849 := bstep (se 2 (by rfl) ⟨314568, by rfl⟩ : syracuseStep 838849 = 629137) B629137
theorem B1264835 : Blo 495792 1264835 := bstep (se 1 (by rfl) ⟨948626, by rfl⟩ : syracuseStep 1264835 = 1897253) B1897253
theorem B838883 : Blo 495792 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B707825 : Blo 495792 707825 := bstep (se 2 (by rfl) ⟨265434, by rfl⟩ : syracuseStep 707825 = 530869) B530869
theorem B1199395 : Blo 495792 1199395 := bstep (se 1 (by rfl) ⟨899546, by rfl⟩ : syracuseStep 1199395 = 1799093) B1799093
theorem B839011 : Blo 495792 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B839153 : Blo 495792 839153 := bstep (se 2 (by rfl) ⟨314682, by rfl⟩ : syracuseStep 839153 = 629365) B629365
theorem B839281 : Blo 495792 839281 := bstep (se 2 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 839281 = 629461) B629461
theorem B839315 : Blo 495792 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B2838179 : Blo 495792 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B2510513 : Blo 495792 2510513 := bstep (se 2 (by rfl) ⟨941442, by rfl⟩ : syracuseStep 2510513 = 1882885) B1882885
theorem B708355 : Blo 495792 708355 := bstep (se 1 (by rfl) ⟨531266, by rfl⟩ : syracuseStep 708355 = 1062533) B1062533
theorem B839443 : Blo 495792 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B1888049 : Blo 495792 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B4542277 : Blo 495792 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B3198797 : Blo 495792 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B1920881 : Blo 495792 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B839585 : Blo 495792 839585 := bstep (se 2 (by rfl) ⟨314844, by rfl⟩ : syracuseStep 839585 = 629689) B629689
theorem B3592133 : Blo 495792 3592133 := bstep (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) B673525
theorem B839713 : Blo 495792 839713 := bstep (se 2 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 839713 = 629785) B629785
theorem B839747 : Blo 495792 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B708691 : Blo 495792 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B6443107 : Blo 495792 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B2019491 : Blo 495792 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B839875 : Blo 495792 839875 := bstep (se 1 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 839875 = 1259813) B1259813
theorem B1921265 : Blo 495792 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B1790257 : Blo 495792 1790257 := bstep (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) B1342693
theorem B1200433 : Blo 495792 1200433 := bstep (se 2 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 1200433 = 900325) B900325
theorem B840017 : Blo 495792 840017 := bstep (se 2 (by rfl) ⟨315006, by rfl⟩ : syracuseStep 840017 = 630013) B630013
theorem B1888717 : Blo 495792 1888717 := bstep (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) B708269
theorem B840145 : Blo 495792 840145 := bstep (se 2 (by rfl) ⟨315054, by rfl⟩ : syracuseStep 840145 = 630109) B630109
theorem B840179 : Blo 495792 840179 := bstep (se 1 (by rfl) ⟨630134, by rfl⟩ : syracuseStep 840179 = 1260269) B1260269
theorem B840307 : Blo 495792 840307 := bstep (se 1 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 840307 = 1260461) B1260461
theorem B709249 : Blo 495792 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B709283 : Blo 495792 709283 := bstep (se 1 (by rfl) ⟨531962, by rfl⟩ : syracuseStep 709283 = 1063925) B1063925
theorem B840449 : Blo 495792 840449 := bstep (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) B630337
theorem B840577 : Blo 495792 840577 := bstep (se 2 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 840577 = 630433) B630433
theorem B840611 : Blo 495792 840611 := bstep (se 1 (by rfl) ⟨630458, by rfl⟩ : syracuseStep 840611 = 1260917) B1260917
theorem B840739 : Blo 495792 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B2511971 : Blo 495792 2511971 := bstep (se 1 (by rfl) ⟨1883978, by rfl⟩ : syracuseStep 2511971 = 3767957) B3767957
theorem B840881 : Blo 495792 840881 := bstep (se 2 (by rfl) ⟨315330, by rfl⟩ : syracuseStep 840881 = 630661) B630661
theorem B709841 : Blo 495792 709841 := bstep (se 2 (by rfl) ⟨266190, by rfl⟩ : syracuseStep 709841 = 532381) B532381
theorem B1889507 : Blo 495792 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B709921 : Blo 495792 709921 := bstep (se 2 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 709921 = 532441) B532441
theorem B841009 : Blo 495792 841009 := bstep (se 2 (by rfl) ⟨315378, by rfl⟩ : syracuseStep 841009 = 630757) B630757
theorem B841043 : Blo 495792 841043 := bstep (se 1 (by rfl) ⟨630782, by rfl⟩ : syracuseStep 841043 = 1261565) B1261565
theorem B1594733 : Blo 495792 1594733 := bstep (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) B598025
theorem B841171 : Blo 495792 841171 := bstep (se 1 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 841171 = 1261757) B1261757
theorem B841313 : Blo 495792 841313 := bstep (se 2 (by rfl) ⟨315492, by rfl⟩ : syracuseStep 841313 = 630985) B630985
theorem B841441 : Blo 495792 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B2119409 : Blo 495792 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B841475 : Blo 495792 841475 := bstep (se 1 (by rfl) ⟨631106, by rfl⟩ : syracuseStep 841475 = 1262213) B1262213
theorem B1890161 : Blo 495792 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B841603 : Blo 495792 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B2512781 : Blo 495792 2512781 := bstep (se 3 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 2512781 = 942293) B942293
theorem B841745 : Blo 495792 841745 := bstep (se 2 (by rfl) ⟨315654, by rfl⟩ : syracuseStep 841745 = 631309) B631309
theorem B710707 : Blo 495792 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B9099377 : Blo 495792 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B841873 : Blo 495792 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B841907 : Blo 495792 841907 := bstep (se 1 (by rfl) ⟨631430, by rfl⟩ : syracuseStep 841907 = 1262861) B1262861
theorem B5363981 : Blo 495792 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B743699 : Blo 495792 743699 := bstep (se 1 (by rfl) ⟨557774, by rfl⟩ : syracuseStep 743699 = 1115549) B1115549
theorem B743729 : Blo 495792 743729 := bstep (se 2 (by rfl) ⟨278898, by rfl⟩ : syracuseStep 743729 = 557797) B557797
theorem B842035 : Blo 495792 842035 := bstep (se 1 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 842035 = 1263053) B1263053
theorem B743747 : Blo 495792 743747 := bstep (se 1 (by rfl) ⟨557810, by rfl⟩ : syracuseStep 743747 = 1115621) B1115621
theorem B743777 : Blo 495792 743777 := bstep (se 2 (by rfl) ⟨278916, by rfl⟩ : syracuseStep 743777 = 557833) B557833
theorem B743795 : Blo 495792 743795 := bstep (se 1 (by rfl) ⟨557846, by rfl⟩ : syracuseStep 743795 = 1115693) B1115693
theorem B743825 : Blo 495792 743825 := bstep (se 2 (by rfl) ⟨278934, by rfl⟩ : syracuseStep 743825 = 557869) B557869
theorem B743843 : Blo 495792 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B743873 : Blo 495792 743873 := bstep (se 2 (by rfl) ⟨278952, by rfl⟩ : syracuseStep 743873 = 557905) B557905
theorem B842177 : Blo 495792 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B1169873 : Blo 495792 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B743891 : Blo 495792 743891 := bstep (se 1 (by rfl) ⟨557918, by rfl⟩ : syracuseStep 743891 = 1115837) B1115837
theorem B743921 : Blo 495792 743921 := bstep (se 2 (by rfl) ⟨278970, by rfl⟩ : syracuseStep 743921 = 557941) B557941
theorem B743939 : Blo 495792 743939 := bstep (se 1 (by rfl) ⟨557954, by rfl⟩ : syracuseStep 743939 = 1115909) B1115909
theorem B711185 : Blo 495792 711185 := bstep (se 2 (by rfl) ⟨266694, by rfl⟩ : syracuseStep 711185 = 533389) B533389
theorem B743969 : Blo 495792 743969 := bstep (se 2 (by rfl) ⟨278988, by rfl⟩ : syracuseStep 743969 = 557977) B557977
theorem B743987 : Blo 495792 743987 := bstep (se 1 (by rfl) ⟨557990, by rfl⟩ : syracuseStep 743987 = 1115981) B1115981
theorem B842305 : Blo 495792 842305 := bstep (se 2 (by rfl) ⟨315864, by rfl⟩ : syracuseStep 842305 = 631729) B631729
theorem B4381253 : Blo 495792 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B744017 : Blo 495792 744017 := bstep (se 2 (by rfl) ⟨279006, by rfl⟩ : syracuseStep 744017 = 558013) B558013
theorem B744035 : Blo 495792 744035 := bstep (se 1 (by rfl) ⟨558026, by rfl⟩ : syracuseStep 744035 = 1116053) B1116053
theorem B842339 : Blo 495792 842339 := bstep (se 1 (by rfl) ⟨631754, by rfl⟩ : syracuseStep 842339 = 1263509) B1263509
theorem B744065 : Blo 495792 744065 := bstep (se 2 (by rfl) ⟨279024, by rfl⟩ : syracuseStep 744065 = 558049) B558049
theorem B711299 : Blo 495792 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B744083 : Blo 495792 744083 := bstep (se 1 (by rfl) ⟨558062, by rfl⟩ : syracuseStep 744083 = 1116125) B1116125
theorem B744113 : Blo 495792 744113 := bstep (se 2 (by rfl) ⟨279042, by rfl⟩ : syracuseStep 744113 = 558085) B558085
theorem B809651 : Blo 495792 809651 := bstep (se 1 (by rfl) ⟨607238, by rfl⟩ : syracuseStep 809651 = 1214477) B1214477
theorem B744131 : Blo 495792 744131 := bstep (se 1 (by rfl) ⟨558098, by rfl⟩ : syracuseStep 744131 = 1116197) B1116197
theorem B711379 : Blo 495792 711379 := bstep (se 1 (by rfl) ⟨533534, by rfl⟩ : syracuseStep 711379 = 1067069) B1067069
theorem B744161 : Blo 495792 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B842467 : Blo 495792 842467 := bstep (se 1 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 842467 = 1263701) B1263701
theorem B744179 : Blo 495792 744179 := bstep (se 1 (by rfl) ⟨558134, by rfl⟩ : syracuseStep 744179 = 1116269) B1116269
theorem B744209 : Blo 495792 744209 := bstep (se 2 (by rfl) ⟨279078, by rfl⟩ : syracuseStep 744209 = 558157) B558157
theorem B744227 : Blo 495792 744227 := bstep (se 1 (by rfl) ⟨558170, by rfl⟩ : syracuseStep 744227 = 1116341) B1116341
theorem B744257 : Blo 495792 744257 := bstep (se 2 (by rfl) ⟨279096, by rfl⟩ : syracuseStep 744257 = 558193) B558193
theorem B744275 : Blo 495792 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B744305 : Blo 495792 744305 := bstep (se 2 (by rfl) ⟨279114, by rfl⟩ : syracuseStep 744305 = 558229) B558229
theorem B842609 : Blo 495792 842609 := bstep (se 2 (by rfl) ⟨315978, by rfl⟩ : syracuseStep 842609 = 631957) B631957
theorem B744323 : Blo 495792 744323 := bstep (se 1 (by rfl) ⟨558242, by rfl⟩ : syracuseStep 744323 = 1116485) B1116485
theorem B744353 : Blo 495792 744353 := bstep (se 2 (by rfl) ⟨279132, by rfl⟩ : syracuseStep 744353 = 558265) B558265
theorem B1596323 : Blo 495792 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B744371 : Blo 495792 744371 := bstep (se 1 (by rfl) ⟨558278, by rfl⟩ : syracuseStep 744371 = 1116557) B1116557
theorem B2382797 : Blo 495792 2382797 := bstep (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) B893549
theorem B744401 : Blo 495792 744401 := bstep (se 2 (by rfl) ⟨279150, by rfl⟩ : syracuseStep 744401 = 558301) B558301
theorem B744419 : Blo 495792 744419 := bstep (se 1 (by rfl) ⟨558314, by rfl⟩ : syracuseStep 744419 = 1116629) B1116629
theorem B1137649 : Blo 495792 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B842737 : Blo 495792 842737 := bstep (se 2 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 842737 = 632053) B632053
theorem B744449 : Blo 495792 744449 := bstep (se 2 (by rfl) ⟨279168, by rfl⟩ : syracuseStep 744449 = 558337) B558337
theorem B744467 : Blo 495792 744467 := bstep (se 1 (by rfl) ⟨558350, by rfl⟩ : syracuseStep 744467 = 1116701) B1116701
theorem B842771 : Blo 495792 842771 := bstep (se 1 (by rfl) ⟨632078, by rfl⟩ : syracuseStep 842771 = 1264157) B1264157
theorem B744497 : Blo 495792 744497 := bstep (se 2 (by rfl) ⟨279186, by rfl⟩ : syracuseStep 744497 = 558373) B558373
theorem B744515 : Blo 495792 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B744545 : Blo 495792 744545 := bstep (se 2 (by rfl) ⟨279204, by rfl⟩ : syracuseStep 744545 = 558409) B558409
theorem B744563 : Blo 495792 744563 := bstep (se 1 (by rfl) ⟨558422, by rfl⟩ : syracuseStep 744563 = 1116845) B1116845
theorem B744593 : Blo 495792 744593 := bstep (se 2 (by rfl) ⟨279222, by rfl⟩ : syracuseStep 744593 = 558445) B558445
theorem B842899 : Blo 495792 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B744611 : Blo 495792 744611 := bstep (se 1 (by rfl) ⟨558458, by rfl⟩ : syracuseStep 744611 = 1116917) B1116917
theorem B1006769 : Blo 495792 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B744641 : Blo 495792 744641 := bstep (se 2 (by rfl) ⟨279240, by rfl⟩ : syracuseStep 744641 = 558481) B558481
theorem B744659 : Blo 495792 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B744689 : Blo 495792 744689 := bstep (se 2 (by rfl) ⟨279258, by rfl⟩ : syracuseStep 744689 = 558517) B558517
theorem B1137905 : Blo 495792 1137905 := bstep (se 2 (by rfl) ⟨426714, by rfl⟩ : syracuseStep 1137905 = 853429) B853429
theorem B744707 : Blo 495792 744707 := bstep (se 1 (by rfl) ⟨558530, by rfl⟩ : syracuseStep 744707 = 1117061) B1117061
theorem B744737 : Blo 495792 744737 := bstep (se 2 (by rfl) ⟨279276, by rfl⟩ : syracuseStep 744737 = 558553) B558553
theorem B843041 : Blo 495792 843041 := bstep (se 2 (by rfl) ⟨316140, by rfl⟩ : syracuseStep 843041 = 632281) B632281
theorem B1891619 : Blo 495792 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B1891633 : Blo 495792 1891633 := bstep (se 2 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 1891633 = 1418725) B1418725
theorem B744755 : Blo 495792 744755 := bstep (se 1 (by rfl) ⟨558566, by rfl⟩ : syracuseStep 744755 = 1117133) B1117133
theorem B744785 : Blo 495792 744785 := bstep (se 2 (by rfl) ⟨279294, by rfl⟩ : syracuseStep 744785 = 558589) B558589
theorem B744803 : Blo 495792 744803 := bstep (se 1 (by rfl) ⟨558602, by rfl⟩ : syracuseStep 744803 = 1117205) B1117205
theorem B744833 : Blo 495792 744833 := bstep (se 2 (by rfl) ⟨279312, by rfl⟩ : syracuseStep 744833 = 558625) B558625
theorem B744851 : Blo 495792 744851 := bstep (se 1 (by rfl) ⟨558638, by rfl⟩ : syracuseStep 744851 = 1117277) B1117277
theorem B843169 : Blo 495792 843169 := bstep (se 2 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 843169 = 632377) B632377
theorem B744881 : Blo 495792 744881 := bstep (se 2 (by rfl) ⟨279330, by rfl⟩ : syracuseStep 744881 = 558661) B558661
theorem B744899 : Blo 495792 744899 := bstep (se 1 (by rfl) ⟨558674, by rfl⟩ : syracuseStep 744899 = 1117349) B1117349
theorem B843203 : Blo 495792 843203 := bstep (se 1 (by rfl) ⟨632402, by rfl⟩ : syracuseStep 843203 = 1264805) B1264805
theorem B744929 : Blo 495792 744929 := bstep (se 2 (by rfl) ⟨279348, by rfl⟩ : syracuseStep 744929 = 558697) B558697
theorem B744947 : Blo 495792 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B744977 : Blo 495792 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B744995 : Blo 495792 744995 := bstep (se 1 (by rfl) ⟨558746, by rfl⟩ : syracuseStep 744995 = 1117493) B1117493
theorem B745025 : Blo 495792 745025 := bstep (se 2 (by rfl) ⟨279384, by rfl⟩ : syracuseStep 745025 = 558769) B558769
theorem B843331 : Blo 495792 843331 := bstep (se 1 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 843331 = 1264997) B1264997
theorem B745043 : Blo 495792 745043 := bstep (se 1 (by rfl) ⟨558782, by rfl⟩ : syracuseStep 745043 = 1117565) B1117565
theorem B745073 : Blo 495792 745073 := bstep (se 2 (by rfl) ⟨279402, by rfl⟩ : syracuseStep 745073 = 558805) B558805
theorem B745091 : Blo 495792 745091 := bstep (se 1 (by rfl) ⟨558818, by rfl⟩ : syracuseStep 745091 = 1117637) B1117637
theorem B745121 : Blo 495792 745121 := bstep (se 2 (by rfl) ⟨279420, by rfl⟩ : syracuseStep 745121 = 558841) B558841
theorem B2547377 : Blo 495792 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B745139 : Blo 495792 745139 := bstep (se 1 (by rfl) ⟨558854, by rfl⟩ : syracuseStep 745139 = 1117709) B1117709
theorem B941777 : Blo 495792 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B745169 : Blo 495792 745169 := bstep (se 2 (by rfl) ⟨279438, by rfl⟩ : syracuseStep 745169 = 558877) B558877
theorem B745187 : Blo 495792 745187 := bstep (se 1 (by rfl) ⟨558890, by rfl⟩ : syracuseStep 745187 = 1117781) B1117781
theorem B745217 : Blo 495792 745217 := bstep (se 2 (by rfl) ⟨279456, by rfl⟩ : syracuseStep 745217 = 558913) B558913
theorem B745235 : Blo 495792 745235 := bstep (se 1 (by rfl) ⟨558926, by rfl⟩ : syracuseStep 745235 = 1117853) B1117853
theorem B745265 : Blo 495792 745265 := bstep (se 2 (by rfl) ⟨279474, by rfl⟩ : syracuseStep 745265 = 558949) B558949
theorem B745283 : Blo 495792 745283 := bstep (se 1 (by rfl) ⟨558962, by rfl⟩ : syracuseStep 745283 = 1117925) B1117925
theorem B745313 : Blo 495792 745313 := bstep (se 2 (by rfl) ⟨279492, by rfl⟩ : syracuseStep 745313 = 558985) B558985
theorem B745331 : Blo 495792 745331 := bstep (se 1 (by rfl) ⟨558998, by rfl⟩ : syracuseStep 745331 = 1117997) B1117997
theorem B745361 : Blo 495792 745361 := bstep (se 2 (by rfl) ⟨279510, by rfl⟩ : syracuseStep 745361 = 559021) B559021
theorem B745379 : Blo 495792 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B745409 : Blo 495792 745409 := bstep (se 2 (by rfl) ⟨279528, by rfl⟩ : syracuseStep 745409 = 559057) B559057
theorem B745427 : Blo 495792 745427 := bstep (se 1 (by rfl) ⟨559070, by rfl⟩ : syracuseStep 745427 = 1118141) B1118141
theorem B745457 : Blo 495792 745457 := bstep (se 2 (by rfl) ⟨279546, by rfl⟩ : syracuseStep 745457 = 559093) B559093
theorem B745475 : Blo 495792 745475 := bstep (se 1 (by rfl) ⟨559106, by rfl⟩ : syracuseStep 745475 = 1118213) B1118213
theorem B745505 : Blo 495792 745505 := bstep (se 2 (by rfl) ⟨279564, by rfl⟩ : syracuseStep 745505 = 559129) B559129
theorem B745523 : Blo 495792 745523 := bstep (se 1 (by rfl) ⟨559142, by rfl⟩ : syracuseStep 745523 = 1118285) B1118285
theorem B745553 : Blo 495792 745553 := bstep (se 2 (by rfl) ⟨279582, by rfl⟩ : syracuseStep 745553 = 559165) B559165
theorem B745571 : Blo 495792 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B909425 : Blo 495792 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B1597553 : Blo 495792 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B10379377 : Blo 495792 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B745601 : Blo 495792 745601 := bstep (se 2 (by rfl) ⟨279600, by rfl⟩ : syracuseStep 745601 = 559201) B559201
theorem B2121869 : Blo 495792 2121869 := bstep (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) B795701
theorem B745619 : Blo 495792 745619 := bstep (se 1 (by rfl) ⟨559214, by rfl⟩ : syracuseStep 745619 = 1118429) B1118429
theorem B745649 : Blo 495792 745649 := bstep (se 2 (by rfl) ⟨279618, by rfl⟩ : syracuseStep 745649 = 559237) B559237
theorem B745667 : Blo 495792 745667 := bstep (se 1 (by rfl) ⟨559250, by rfl⟩ : syracuseStep 745667 = 1118501) B1118501
theorem B745697 : Blo 495792 745697 := bstep (se 2 (by rfl) ⟨279636, by rfl⟩ : syracuseStep 745697 = 559273) B559273
theorem B745715 : Blo 495792 745715 := bstep (se 1 (by rfl) ⟨559286, by rfl⟩ : syracuseStep 745715 = 1118573) B1118573
theorem B745745 : Blo 495792 745745 := bstep (se 2 (by rfl) ⟨279654, by rfl⟩ : syracuseStep 745745 = 559309) B559309
theorem B745763 : Blo 495792 745763 := bstep (se 1 (by rfl) ⟨559322, by rfl⟩ : syracuseStep 745763 = 1118645) B1118645
theorem B745793 : Blo 495792 745793 := bstep (se 2 (by rfl) ⟨279672, by rfl⟩ : syracuseStep 745793 = 559345) B559345
theorem B745811 : Blo 495792 745811 := bstep (se 1 (by rfl) ⟨559358, by rfl⟩ : syracuseStep 745811 = 1118717) B1118717
theorem B811363 : Blo 495792 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B745841 : Blo 495792 745841 := bstep (se 2 (by rfl) ⟨279690, by rfl⟩ : syracuseStep 745841 = 559381) B559381
theorem B745859 : Blo 495792 745859 := bstep (se 1 (by rfl) ⟨559394, by rfl⟩ : syracuseStep 745859 = 1118789) B1118789
theorem B745889 : Blo 495792 745889 := bstep (se 2 (by rfl) ⟨279708, by rfl⟩ : syracuseStep 745889 = 559417) B559417
theorem B745907 : Blo 495792 745907 := bstep (se 1 (by rfl) ⟨559430, by rfl⟩ : syracuseStep 745907 = 1118861) B1118861
theorem B745937 : Blo 495792 745937 := bstep (se 2 (by rfl) ⟨279726, by rfl⟩ : syracuseStep 745937 = 559453) B559453
theorem B680419 : Blo 495792 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B745955 : Blo 495792 745955 := bstep (se 1 (by rfl) ⟨559466, by rfl⟩ : syracuseStep 745955 = 1118933) B1118933
theorem B1696241 : Blo 495792 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B745985 : Blo 495792 745985 := bstep (se 2 (by rfl) ⟨279744, by rfl⟩ : syracuseStep 745985 = 559489) B559489
theorem B746003 : Blo 495792 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B746033 : Blo 495792 746033 := bstep (se 2 (by rfl) ⟨279762, by rfl⟩ : syracuseStep 746033 = 559525) B559525
theorem B746051 : Blo 495792 746051 := bstep (se 1 (by rfl) ⟨559538, by rfl⟩ : syracuseStep 746051 = 1119077) B1119077
theorem B942673 : Blo 495792 942673 := bstep (se 2 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 942673 = 707005) B707005
theorem B746081 : Blo 495792 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B746099 : Blo 495792 746099 := bstep (se 1 (by rfl) ⟨559574, by rfl⟩ : syracuseStep 746099 = 1119149) B1119149
theorem B746129 : Blo 495792 746129 := bstep (se 2 (by rfl) ⟨279798, by rfl⟩ : syracuseStep 746129 = 559597) B559597
theorem B746147 : Blo 495792 746147 := bstep (se 1 (by rfl) ⟨559610, by rfl⟩ : syracuseStep 746147 = 1119221) B1119221
theorem B746177 : Blo 495792 746177 := bstep (se 2 (by rfl) ⟨279816, by rfl⟩ : syracuseStep 746177 = 559633) B559633
theorem B746195 : Blo 495792 746195 := bstep (se 1 (by rfl) ⟨559646, by rfl⟩ : syracuseStep 746195 = 1119293) B1119293
theorem B1893091 : Blo 495792 1893091 := bstep (se 1 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 1893091 = 2839637) B2839637
theorem B942833 : Blo 495792 942833 := bstep (se 2 (by rfl) ⟨353562, by rfl⟩ : syracuseStep 942833 = 707125) B707125
theorem B2515697 : Blo 495792 2515697 := bstep (se 2 (by rfl) ⟨943386, by rfl⟩ : syracuseStep 2515697 = 1886773) B1886773
theorem B746225 : Blo 495792 746225 := bstep (se 2 (by rfl) ⟨279834, by rfl⟩ : syracuseStep 746225 = 559669) B559669
theorem B746243 : Blo 495792 746243 := bstep (se 1 (by rfl) ⟨559682, by rfl⟩ : syracuseStep 746243 = 1119365) B1119365
theorem B746273 : Blo 495792 746273 := bstep (se 2 (by rfl) ⟨279852, by rfl⟩ : syracuseStep 746273 = 559705) B559705
theorem B746291 : Blo 495792 746291 := bstep (se 1 (by rfl) ⟨559718, by rfl⟩ : syracuseStep 746291 = 1119437) B1119437
theorem B746321 : Blo 495792 746321 := bstep (se 2 (by rfl) ⟨279870, by rfl⟩ : syracuseStep 746321 = 559741) B559741
theorem B746339 : Blo 495792 746339 := bstep (se 1 (by rfl) ⟨559754, by rfl⟩ : syracuseStep 746339 = 1119509) B1119509
theorem B746369 : Blo 495792 746369 := bstep (se 2 (by rfl) ⟨279888, by rfl⟩ : syracuseStep 746369 = 559777) B559777
theorem B746387 : Blo 495792 746387 := bstep (se 1 (by rfl) ⟨559790, by rfl⟩ : syracuseStep 746387 = 1119581) B1119581
theorem B746417 : Blo 495792 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B746435 : Blo 495792 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B1598413 : Blo 495792 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B746465 : Blo 495792 746465 := bstep (se 2 (by rfl) ⟨279924, by rfl⟩ : syracuseStep 746465 = 559849) B559849
theorem B746483 : Blo 495792 746483 := bstep (se 1 (by rfl) ⟨559862, by rfl⟩ : syracuseStep 746483 = 1119725) B1119725
theorem B746513 : Blo 495792 746513 := bstep (se 2 (by rfl) ⟨279942, by rfl⟩ : syracuseStep 746513 = 559885) B559885
theorem B746531 : Blo 495792 746531 := bstep (se 1 (by rfl) ⟨559898, by rfl⟩ : syracuseStep 746531 = 1119797) B1119797
theorem B746561 : Blo 495792 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B746579 : Blo 495792 746579 := bstep (se 1 (by rfl) ⟨559934, by rfl⟩ : syracuseStep 746579 = 1119869) B1119869
theorem B746609 : Blo 495792 746609 := bstep (se 2 (by rfl) ⟨279978, by rfl⟩ : syracuseStep 746609 = 559957) B559957
theorem B943235 : Blo 495792 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B746627 : Blo 495792 746627 := bstep (se 1 (by rfl) ⟨559970, by rfl⟩ : syracuseStep 746627 = 1119941) B1119941
theorem B746657 : Blo 495792 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B746675 : Blo 495792 746675 := bstep (se 1 (by rfl) ⟨560006, by rfl⟩ : syracuseStep 746675 = 1120013) B1120013
theorem B746705 : Blo 495792 746705 := bstep (se 2 (by rfl) ⟨280014, by rfl⟩ : syracuseStep 746705 = 560029) B560029
theorem B28697813 : Blo 495792 28697813 := bstep (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) B672605
theorem B746723 : Blo 495792 746723 := bstep (se 1 (by rfl) ⟨560042, by rfl⟩ : syracuseStep 746723 = 1120085) B1120085
theorem B746753 : Blo 495792 746753 := bstep (se 2 (by rfl) ⟨280032, by rfl⟩ : syracuseStep 746753 = 560065) B560065
theorem B746771 : Blo 495792 746771 := bstep (se 1 (by rfl) ⟨560078, by rfl⟩ : syracuseStep 746771 = 1120157) B1120157
theorem B746801 : Blo 495792 746801 := bstep (se 2 (by rfl) ⟨280050, by rfl⟩ : syracuseStep 746801 = 560101) B560101
theorem B746819 : Blo 495792 746819 := bstep (se 1 (by rfl) ⟨560114, by rfl⟩ : syracuseStep 746819 = 1120229) B1120229
theorem B746849 : Blo 495792 746849 := bstep (se 2 (by rfl) ⟨280068, by rfl⟩ : syracuseStep 746849 = 560137) B560137
theorem B746867 : Blo 495792 746867 := bstep (se 1 (by rfl) ⟨560150, by rfl⟩ : syracuseStep 746867 = 1120301) B1120301
theorem B746897 : Blo 495792 746897 := bstep (se 2 (by rfl) ⟨280086, by rfl⟩ : syracuseStep 746897 = 560173) B560173
theorem B746915 : Blo 495792 746915 := bstep (se 1 (by rfl) ⟨560186, by rfl⟩ : syracuseStep 746915 = 1120373) B1120373
theorem B746945 : Blo 495792 746945 := bstep (se 2 (by rfl) ⟨280104, by rfl⟩ : syracuseStep 746945 = 560209) B560209
theorem B746963 : Blo 495792 746963 := bstep (se 1 (by rfl) ⟨560222, by rfl⟩ : syracuseStep 746963 = 1120445) B1120445
theorem B3630563 : Blo 495792 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B746993 : Blo 495792 746993 := bstep (se 2 (by rfl) ⟨280122, by rfl⟩ : syracuseStep 746993 = 560245) B560245
theorem B747011 : Blo 495792 747011 := bstep (se 1 (by rfl) ⟨560258, by rfl⟩ : syracuseStep 747011 = 1120517) B1120517
theorem B747041 : Blo 495792 747041 := bstep (se 2 (by rfl) ⟨280140, by rfl⟩ : syracuseStep 747041 = 560281) B560281
theorem B747059 : Blo 495792 747059 := bstep (se 1 (by rfl) ⟨560294, by rfl⟩ : syracuseStep 747059 = 1120589) B1120589
theorem B747089 : Blo 495792 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B747107 : Blo 495792 747107 := bstep (se 1 (by rfl) ⟨560330, by rfl⟩ : syracuseStep 747107 = 1120661) B1120661
theorem B747137 : Blo 495792 747137 := bstep (se 2 (by rfl) ⟨280176, by rfl⟩ : syracuseStep 747137 = 560353) B560353
theorem B747155 : Blo 495792 747155 := bstep (se 1 (by rfl) ⟨560366, by rfl⟩ : syracuseStep 747155 = 1120733) B1120733
theorem B2123441 : Blo 495792 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B747185 : Blo 495792 747185 := bstep (se 2 (by rfl) ⟨280194, by rfl⟩ : syracuseStep 747185 = 560389) B560389
theorem B747203 : Blo 495792 747203 := bstep (se 1 (by rfl) ⟨560402, by rfl⟩ : syracuseStep 747203 = 1120805) B1120805
theorem B747233 : Blo 495792 747233 := bstep (se 2 (by rfl) ⟨280212, by rfl⟩ : syracuseStep 747233 = 560425) B560425
theorem B747251 : Blo 495792 747251 := bstep (se 1 (by rfl) ⟨560438, by rfl⟩ : syracuseStep 747251 = 1120877) B1120877
theorem B747281 : Blo 495792 747281 := bstep (se 2 (by rfl) ⟨280230, by rfl⟩ : syracuseStep 747281 = 560461) B560461
theorem B747299 : Blo 495792 747299 := bstep (se 1 (by rfl) ⟨560474, by rfl⟩ : syracuseStep 747299 = 1120949) B1120949
theorem B747329 : Blo 495792 747329 := bstep (se 2 (by rfl) ⟨280248, by rfl⟩ : syracuseStep 747329 = 560497) B560497
theorem B747347 : Blo 495792 747347 := bstep (se 1 (by rfl) ⟨560510, by rfl⟩ : syracuseStep 747347 = 1121021) B1121021
theorem B747377 : Blo 495792 747377 := bstep (se 2 (by rfl) ⟨280266, by rfl⟩ : syracuseStep 747377 = 560533) B560533
theorem B747395 : Blo 495792 747395 := bstep (se 1 (by rfl) ⟨560546, by rfl⟩ : syracuseStep 747395 = 1121093) B1121093
theorem B747425 : Blo 495792 747425 := bstep (se 2 (by rfl) ⟨280284, by rfl⟩ : syracuseStep 747425 = 560569) B560569
theorem B747443 : Blo 495792 747443 := bstep (se 1 (by rfl) ⟨560582, by rfl⟩ : syracuseStep 747443 = 1121165) B1121165
theorem B747473 : Blo 495792 747473 := bstep (se 2 (by rfl) ⟨280302, by rfl⟩ : syracuseStep 747473 = 560605) B560605
theorem B747491 : Blo 495792 747491 := bstep (se 1 (by rfl) ⟨560618, by rfl⟩ : syracuseStep 747491 = 1121237) B1121237
theorem B747521 : Blo 495792 747521 := bstep (se 2 (by rfl) ⟨280320, by rfl⟩ : syracuseStep 747521 = 560641) B560641
theorem B944131 : Blo 495792 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B747539 : Blo 495792 747539 := bstep (se 1 (by rfl) ⟨560654, by rfl⟩ : syracuseStep 747539 = 1121309) B1121309
theorem B747569 : Blo 495792 747569 := bstep (se 2 (by rfl) ⟨280338, by rfl⟩ : syracuseStep 747569 = 560677) B560677
theorem B747587 : Blo 495792 747587 := bstep (se 1 (by rfl) ⟨560690, by rfl⟩ : syracuseStep 747587 = 1121381) B1121381
theorem B747617 : Blo 495792 747617 := bstep (se 2 (by rfl) ⟨280356, by rfl⟩ : syracuseStep 747617 = 560713) B560713
theorem B747635 : Blo 495792 747635 := bstep (se 1 (by rfl) ⟨560726, by rfl⟩ : syracuseStep 747635 = 1121453) B1121453
theorem B747665 : Blo 495792 747665 := bstep (se 2 (by rfl) ⟨280374, by rfl⟩ : syracuseStep 747665 = 560749) B560749
theorem B2517155 : Blo 495792 2517155 := bstep (se 1 (by rfl) ⟨1887866, by rfl⟩ : syracuseStep 2517155 = 3775733) B3775733
theorem B944291 : Blo 495792 944291 := bstep (se 1 (by rfl) ⟨708218, by rfl⟩ : syracuseStep 944291 = 1416437) B1416437
theorem B747683 : Blo 495792 747683 := bstep (se 1 (by rfl) ⟨560762, by rfl⟩ : syracuseStep 747683 = 1121525) B1121525
theorem B747713 : Blo 495792 747713 := bstep (se 2 (by rfl) ⟨280392, by rfl⟩ : syracuseStep 747713 = 560785) B560785
theorem B747731 : Blo 495792 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B747761 : Blo 495792 747761 := bstep (se 2 (by rfl) ⟨280410, by rfl⟩ : syracuseStep 747761 = 560821) B560821
theorem B747779 : Blo 495792 747779 := bstep (se 1 (by rfl) ⟨560834, by rfl⟩ : syracuseStep 747779 = 1121669) B1121669
theorem B747809 : Blo 495792 747809 := bstep (se 2 (by rfl) ⟨280428, by rfl⟩ : syracuseStep 747809 = 560857) B560857
theorem B747827 : Blo 495792 747827 := bstep (se 1 (by rfl) ⟨560870, by rfl⟩ : syracuseStep 747827 = 1121741) B1121741
theorem B747857 : Blo 495792 747857 := bstep (se 2 (by rfl) ⟨280446, by rfl⟩ : syracuseStep 747857 = 560893) B560893
theorem B747875 : Blo 495792 747875 := bstep (se 1 (by rfl) ⟨560906, by rfl⟩ : syracuseStep 747875 = 1121813) B1121813
theorem B747905 : Blo 495792 747905 := bstep (se 2 (by rfl) ⟨280464, by rfl⟩ : syracuseStep 747905 = 560929) B560929
theorem B747923 : Blo 495792 747923 := bstep (se 1 (by rfl) ⟨560942, by rfl⟩ : syracuseStep 747923 = 1121885) B1121885
theorem B747953 : Blo 495792 747953 := bstep (se 2 (by rfl) ⟨280482, by rfl⟩ : syracuseStep 747953 = 560965) B560965
theorem B747971 : Blo 495792 747971 := bstep (se 1 (by rfl) ⟨560978, by rfl⟩ : syracuseStep 747971 = 1121957) B1121957
theorem B748001 : Blo 495792 748001 := bstep (se 2 (by rfl) ⟨280500, by rfl⟩ : syracuseStep 748001 = 561001) B561001
theorem B748019 : Blo 495792 748019 := bstep (se 1 (by rfl) ⟨561014, by rfl⟩ : syracuseStep 748019 = 1122029) B1122029
theorem B1600013 : Blo 495792 1600013 := bstep (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) B600005
theorem B748049 : Blo 495792 748049 := bstep (se 2 (by rfl) ⟨280518, by rfl⟩ : syracuseStep 748049 = 561037) B561037
theorem B748067 : Blo 495792 748067 := bstep (se 1 (by rfl) ⟨561050, by rfl⟩ : syracuseStep 748067 = 1122101) B1122101
theorem B748097 : Blo 495792 748097 := bstep (se 2 (by rfl) ⟨280536, by rfl⟩ : syracuseStep 748097 = 561073) B561073
theorem B748115 : Blo 495792 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B1698403 : Blo 495792 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B748145 : Blo 495792 748145 := bstep (se 2 (by rfl) ⟨280554, by rfl⟩ : syracuseStep 748145 = 561109) B561109
theorem B748163 : Blo 495792 748163 := bstep (se 1 (by rfl) ⟨561122, by rfl⟩ : syracuseStep 748163 = 1122245) B1122245
theorem B748193 : Blo 495792 748193 := bstep (se 2 (by rfl) ⟨280572, by rfl⟩ : syracuseStep 748193 = 561145) B561145
theorem B748211 : Blo 495792 748211 := bstep (se 1 (by rfl) ⟨561158, by rfl⟩ : syracuseStep 748211 = 1122317) B1122317
theorem B748241 : Blo 495792 748241 := bstep (se 2 (by rfl) ⟨280590, by rfl⟩ : syracuseStep 748241 = 561181) B561181
theorem B748259 : Blo 495792 748259 := bstep (se 1 (by rfl) ⟨561194, by rfl⟩ : syracuseStep 748259 = 1122389) B1122389
theorem B748289 : Blo 495792 748289 := bstep (se 2 (by rfl) ⟨280608, by rfl⟩ : syracuseStep 748289 = 561217) B561217
theorem B748307 : Blo 495792 748307 := bstep (se 1 (by rfl) ⟨561230, by rfl⟩ : syracuseStep 748307 = 1122461) B1122461
theorem B748337 : Blo 495792 748337 := bstep (se 2 (by rfl) ⟨280626, by rfl⟩ : syracuseStep 748337 = 561253) B561253
theorem B748355 : Blo 495792 748355 := bstep (se 1 (by rfl) ⟨561266, by rfl⟩ : syracuseStep 748355 = 1122533) B1122533
theorem B748385 : Blo 495792 748385 := bstep (se 2 (by rfl) ⟨280644, by rfl⟩ : syracuseStep 748385 = 561289) B561289
theorem B1010531 : Blo 495792 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B748403 : Blo 495792 748403 := bstep (se 1 (by rfl) ⟨561302, by rfl⟩ : syracuseStep 748403 = 1122605) B1122605
theorem B9563021 : Blo 495792 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B4254605 : Blo 495792 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B1895309 : Blo 495792 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B748433 : Blo 495792 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B748451 : Blo 495792 748451 := bstep (se 1 (by rfl) ⟨561338, by rfl⟩ : syracuseStep 748451 = 1122677) B1122677
theorem B748481 : Blo 495792 748481 := bstep (se 2 (by rfl) ⟨280680, by rfl⟩ : syracuseStep 748481 = 561361) B561361
theorem B2517965 : Blo 495792 2517965 := bstep (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) B944237
theorem B748499 : Blo 495792 748499 := bstep (se 1 (by rfl) ⟨561374, by rfl⟩ : syracuseStep 748499 = 1122749) B1122749
theorem B748529 : Blo 495792 748529 := bstep (se 2 (by rfl) ⟨280698, by rfl⟩ : syracuseStep 748529 = 561397) B561397
theorem B748547 : Blo 495792 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B748577 : Blo 495792 748577 := bstep (se 2 (by rfl) ⟨280716, by rfl⟩ : syracuseStep 748577 = 561433) B561433
theorem B748595 : Blo 495792 748595 := bstep (se 1 (by rfl) ⟨561446, by rfl⟩ : syracuseStep 748595 = 1122893) B1122893
theorem B748625 : Blo 495792 748625 := bstep (se 2 (by rfl) ⟨280734, by rfl⟩ : syracuseStep 748625 = 561469) B561469
theorem B748643 : Blo 495792 748643 := bstep (se 1 (by rfl) ⟨561482, by rfl⟩ : syracuseStep 748643 = 1122965) B1122965
theorem B748673 : Blo 495792 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B748691 : Blo 495792 748691 := bstep (se 1 (by rfl) ⟨561518, by rfl⟩ : syracuseStep 748691 = 1123037) B1123037
theorem B748721 : Blo 495792 748721 := bstep (se 2 (by rfl) ⟨280770, by rfl⟩ : syracuseStep 748721 = 561541) B561541
theorem B748739 : Blo 495792 748739 := bstep (se 1 (by rfl) ⟨561554, by rfl⟩ : syracuseStep 748739 = 1123109) B1123109
theorem B945361 : Blo 495792 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B748769 : Blo 495792 748769 := bstep (se 2 (by rfl) ⟨280788, by rfl⟩ : syracuseStep 748769 = 561577) B561577
theorem B748787 : Blo 495792 748787 := bstep (se 1 (by rfl) ⟨561590, by rfl⟩ : syracuseStep 748787 = 1123181) B1123181
theorem B748817 : Blo 495792 748817 := bstep (se 2 (by rfl) ⟨280806, by rfl⟩ : syracuseStep 748817 = 561613) B561613
theorem B748835 : Blo 495792 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B748865 : Blo 495792 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B748883 : Blo 495792 748883 := bstep (se 1 (by rfl) ⟨561662, by rfl⟩ : syracuseStep 748883 = 1123325) B1123325
theorem B748913 : Blo 495792 748913 := bstep (se 2 (by rfl) ⟨280842, by rfl⟩ : syracuseStep 748913 = 561685) B561685
theorem B748931 : Blo 495792 748931 := bstep (se 1 (by rfl) ⟨561698, by rfl⟩ : syracuseStep 748931 = 1123397) B1123397
theorem B748961 : Blo 495792 748961 := bstep (se 2 (by rfl) ⟨280860, by rfl⟩ : syracuseStep 748961 = 561721) B561721
theorem B748979 : Blo 495792 748979 := bstep (se 1 (by rfl) ⟨561734, by rfl⟩ : syracuseStep 748979 = 1123469) B1123469
theorem B749009 : Blo 495792 749009 := bstep (se 2 (by rfl) ⟨280878, by rfl⟩ : syracuseStep 749009 = 561757) B561757
theorem B6057443 : Blo 495792 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B749027 : Blo 495792 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B749057 : Blo 495792 749057 := bstep (se 2 (by rfl) ⟨280896, by rfl⟩ : syracuseStep 749057 = 561793) B561793
theorem B749075 : Blo 495792 749075 := bstep (se 1 (by rfl) ⟨561806, by rfl⟩ : syracuseStep 749075 = 1123613) B1123613
theorem B3403313 : Blo 495792 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B749105 : Blo 495792 749105 := bstep (se 2 (by rfl) ⟨280914, by rfl⟩ : syracuseStep 749105 = 561829) B561829
theorem B749123 : Blo 495792 749123 := bstep (se 1 (by rfl) ⟨561842, by rfl⟩ : syracuseStep 749123 = 1123685) B1123685
theorem B1797709 : Blo 495792 1797709 := bstep (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) B674141
theorem B749153 : Blo 495792 749153 := bstep (se 2 (by rfl) ⟨280932, by rfl⟩ : syracuseStep 749153 = 561865) B561865
theorem B749171 : Blo 495792 749171 := bstep (se 1 (by rfl) ⟨561878, by rfl⟩ : syracuseStep 749171 = 1123757) B1123757
theorem B749201 : Blo 495792 749201 := bstep (se 2 (by rfl) ⟨280950, by rfl⟩ : syracuseStep 749201 = 561901) B561901
theorem B749219 : Blo 495792 749219 := bstep (se 1 (by rfl) ⟨561914, by rfl⟩ : syracuseStep 749219 = 1123829) B1123829
theorem B749249 : Blo 495792 749249 := bstep (se 2 (by rfl) ⟨280968, by rfl⟩ : syracuseStep 749249 = 561937) B561937
theorem B13758149 : Blo 495792 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B4419269 : Blo 495792 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B749267 : Blo 495792 749267 := bstep (se 1 (by rfl) ⟨561950, by rfl⟩ : syracuseStep 749267 = 1123901) B1123901
theorem B749297 : Blo 495792 749297 := bstep (se 2 (by rfl) ⟨280986, by rfl⟩ : syracuseStep 749297 = 561973) B561973
theorem B1732337 : Blo 495792 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B749315 : Blo 495792 749315 := bstep (se 1 (by rfl) ⟨561986, by rfl⟩ : syracuseStep 749315 = 1123973) B1123973
theorem B749345 : Blo 495792 749345 := bstep (se 2 (by rfl) ⟨281004, by rfl⟩ : syracuseStep 749345 = 562009) B562009
theorem B749363 : Blo 495792 749363 := bstep (se 1 (by rfl) ⟨562022, by rfl⟩ : syracuseStep 749363 = 1124045) B1124045
theorem B749393 : Blo 495792 749393 := bstep (se 2 (by rfl) ⟨281022, by rfl⟩ : syracuseStep 749393 = 562045) B562045
theorem B749411 : Blo 495792 749411 := bstep (se 1 (by rfl) ⟨562058, by rfl⟩ : syracuseStep 749411 = 1124117) B1124117
theorem B749441 : Blo 495792 749441 := bstep (se 2 (by rfl) ⟨281040, by rfl⟩ : syracuseStep 749441 = 562081) B562081
theorem B749459 : Blo 495792 749459 := bstep (se 1 (by rfl) ⟨562094, by rfl⟩ : syracuseStep 749459 = 1124189) B1124189
theorem B749489 : Blo 495792 749489 := bstep (se 2 (by rfl) ⟨281058, by rfl⟩ : syracuseStep 749489 = 562117) B562117
theorem B749507 : Blo 495792 749507 := bstep (se 1 (by rfl) ⟨562130, by rfl⟩ : syracuseStep 749507 = 1124261) B1124261
theorem B749537 : Blo 495792 749537 := bstep (se 2 (by rfl) ⟨281076, by rfl⟩ : syracuseStep 749537 = 562153) B562153
theorem B749555 : Blo 495792 749555 := bstep (se 1 (by rfl) ⟨562166, by rfl⟩ : syracuseStep 749555 = 1124333) B1124333
theorem B749585 : Blo 495792 749585 := bstep (se 2 (by rfl) ⟨281094, by rfl⟩ : syracuseStep 749585 = 562189) B562189
theorem B749603 : Blo 495792 749603 := bstep (se 1 (by rfl) ⟨562202, by rfl⟩ : syracuseStep 749603 = 1124405) B1124405
theorem B749633 : Blo 495792 749633 := bstep (se 2 (by rfl) ⟨281112, by rfl⟩ : syracuseStep 749633 = 562225) B562225
theorem B2125901 : Blo 495792 2125901 := bstep (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) B797213
theorem B749651 : Blo 495792 749651 := bstep (se 1 (by rfl) ⟨562238, by rfl⟩ : syracuseStep 749651 = 1124477) B1124477
theorem B749681 : Blo 495792 749681 := bstep (se 2 (by rfl) ⟨281130, by rfl⟩ : syracuseStep 749681 = 562261) B562261
theorem B716963 : Blo 495792 716963 := bstep (se 1 (by rfl) ⟨537722, by rfl⟩ : syracuseStep 716963 = 1075445) B1075445
theorem B946417 : Blo 495792 946417 := bstep (se 2 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 946417 = 709813) B709813
theorem B1732963 : Blo 495792 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B2126243 : Blo 495792 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B946819 : Blo 495792 946819 := bstep (se 1 (by rfl) ⟨710114, by rfl⟩ : syracuseStep 946819 = 1420229) B1420229
theorem B946865 : Blo 495792 946865 := bstep (se 2 (by rfl) ⟨355074, by rfl⟩ : syracuseStep 946865 = 710149) B710149
theorem B1700621 : Blo 495792 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B947153 : Blo 495792 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B9597923 : Blo 495792 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B1537165 : Blo 495792 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B4027589 : Blo 495792 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B4256995 : Blo 495792 4256995 := bstep (se 1 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 4256995 = 6385493) B6385493
theorem B947875 : Blo 495792 947875 := bstep (se 1 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 947875 = 1421813) B1421813
theorem B3405509 : Blo 495792 3405509 := bstep (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) B638533
theorem B1341137 : Blo 495792 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B718627 : Blo 495792 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B2520881 : Blo 495792 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B948323 : Blo 495792 948323 := bstep (se 1 (by rfl) ⟨711242, by rfl⟩ : syracuseStep 948323 = 1422485) B1422485
theorem B1800305 : Blo 495792 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B1702097 : Blo 495792 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B3766499 : Blo 495792 3766499 := bstep (se 1 (by rfl) ⟨2824874, by rfl⟩ : syracuseStep 3766499 = 5649749) B5649749
theorem B948611 : Blo 495792 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B1342097 : Blo 495792 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B1277137 : Blo 495792 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B2522339 : Blo 495792 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B1539533 : Blo 495792 1539533 := bstep (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) B577325
theorem B5766709 : Blo 495792 5766709 := bstep (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) B540629
theorem B851699 : Blo 495792 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B1343267 : Blo 495792 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B6356789 : Blo 495792 6356789 := bstep (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) B595949
theorem B2425133 : Blo 495792 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B1081817 : Blo 495792 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B2130583 : Blo 495792 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B557815 : Blo 495792 557815 := bstep (se 1 (by rfl) ⟨418361, by rfl⟩ : syracuseStep 557815 = 836723) B836723
theorem B557995 : Blo 495792 557995 := bstep (se 1 (by rfl) ⟨418496, by rfl⟩ : syracuseStep 557995 = 836993) B836993
theorem B2524121 : Blo 495792 2524121 := bstep (se 2 (by rfl) ⟨946545, by rfl⟩ : syracuseStep 2524121 = 1893091) B1893091
theorem B558103 : Blo 495792 558103 := bstep (se 1 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 558103 = 837155) B837155
theorem B558283 : Blo 495792 558283 := bstep (se 1 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 558283 = 837425) B837425
theorem B2131217 : Blo 495792 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B4523309 : Blo 495792 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B558391 : Blo 495792 558391 := bstep (se 1 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 558391 = 837587) B837587
theorem B1115585 : Blo 495792 1115585 := bstep (se 2 (by rfl) ⟨418344, by rfl⟩ : syracuseStep 1115585 = 836689) B836689
theorem B558571 : Blo 495792 558571 := bstep (se 1 (by rfl) ⟨418928, by rfl⟩ : syracuseStep 558571 = 837857) B837857
theorem B3769901 : Blo 495792 3769901 := bstep (se 3 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 3769901 = 1413713) B1413713
theorem B558679 : Blo 495792 558679 := bstep (se 1 (by rfl) ⟨419009, by rfl⟩ : syracuseStep 558679 = 838019) B838019
theorem B1115801 : Blo 495792 1115801 := bstep (se 2 (by rfl) ⟨418425, by rfl⟩ : syracuseStep 1115801 = 836851) B836851
theorem B2557619 : Blo 495792 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B1115891 : Blo 495792 1115891 := bstep (se 1 (by rfl) ⟨836918, by rfl⟩ : syracuseStep 1115891 = 1673837) B1673837
theorem B558859 : Blo 495792 558859 := bstep (se 1 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 558859 = 838289) B838289
theorem B1115927 : Blo 495792 1115927 := bstep (se 1 (by rfl) ⟨836945, by rfl⟩ : syracuseStep 1115927 = 1673891) B1673891
theorem B558967 : Blo 495792 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B1116107 : Blo 495792 1116107 := bstep (se 1 (by rfl) ⟨837080, by rfl⟩ : syracuseStep 1116107 = 1674161) B1674161
theorem B2131915 : Blo 495792 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B1116161 : Blo 495792 1116161 := bstep (se 2 (by rfl) ⟨418560, by rfl⟩ : syracuseStep 1116161 = 837121) B837121
theorem B4032517 : Blo 495792 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B559147 : Blo 495792 559147 := bstep (se 1 (by rfl) ⟨419360, by rfl⟩ : syracuseStep 559147 = 838721) B838721
theorem B559255 : Blo 495792 559255 := bstep (se 1 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 559255 = 838883) B838883
theorem B1116377 : Blo 495792 1116377 := bstep (se 2 (by rfl) ⟨418641, by rfl⟩ : syracuseStep 1116377 = 837283) B837283
theorem B2132189 : Blo 495792 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B1116467 : Blo 495792 1116467 := bstep (se 1 (by rfl) ⟨837350, by rfl⟩ : syracuseStep 1116467 = 1674701) B1674701
theorem B559435 : Blo 495792 559435 := bstep (se 1 (by rfl) ⟨419576, by rfl⟩ : syracuseStep 559435 = 839153) B839153
theorem B1116503 : Blo 495792 1116503 := bstep (se 1 (by rfl) ⟨837377, by rfl⟩ : syracuseStep 1116503 = 1674755) B1674755
theorem B559543 : Blo 495792 559543 := bstep (se 1 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 559543 = 839315) B839315
theorem B1673675 : Blo 495792 1673675 := bstep (se 1 (by rfl) ⟨1255256, by rfl⟩ : syracuseStep 1673675 = 2510513) B2510513
theorem B1116683 : Blo 495792 1116683 := bstep (se 1 (by rfl) ⟨837512, by rfl⟩ : syracuseStep 1116683 = 1675025) B1675025
theorem B2525741 : Blo 495792 2525741 := bstep (se 3 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 2525741 = 947153) B947153
theorem B2132531 : Blo 495792 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B1116737 : Blo 495792 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B559723 : Blo 495792 559723 := bstep (se 1 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 559723 = 839585) B839585
theorem B2394755 : Blo 495792 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B559831 : Blo 495792 559831 := bstep (se 1 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 559831 = 839747) B839747
theorem B1673945 : Blo 495792 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B1346327 : Blo 495792 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B1116953 : Blo 495792 1116953 := bstep (se 2 (by rfl) ⟨418857, by rfl⟩ : syracuseStep 1116953 = 837715) B837715
theorem B1280843 : Blo 495792 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B1117043 : Blo 495792 1117043 := bstep (se 1 (by rfl) ⟨837782, by rfl⟩ : syracuseStep 1117043 = 1675565) B1675565
theorem B560011 : Blo 495792 560011 := bstep (se 1 (by rfl) ⟨420008, by rfl⟩ : syracuseStep 560011 = 840017) B840017
theorem B1117079 : Blo 495792 1117079 := bstep (se 1 (by rfl) ⟨837809, by rfl⟩ : syracuseStep 1117079 = 1675619) B1675619
theorem B560119 : Blo 495792 560119 := bstep (se 1 (by rfl) ⟨420089, by rfl⟩ : syracuseStep 560119 = 840179) B840179
theorem B1117259 : Blo 495792 1117259 := bstep (se 1 (by rfl) ⟨837944, by rfl⟩ : syracuseStep 1117259 = 1675889) B1675889
theorem B4787275 : Blo 495792 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B1117313 : Blo 495792 1117313 := bstep (se 2 (by rfl) ⟨418992, by rfl⟩ : syracuseStep 1117313 = 837985) B837985
theorem B560299 : Blo 495792 560299 := bstep (se 1 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 560299 = 840449) B840449
theorem B560407 : Blo 495792 560407 := bstep (se 1 (by rfl) ⟨420305, by rfl⟩ : syracuseStep 560407 = 840611) B840611
theorem B1117529 : Blo 495792 1117529 := bstep (se 2 (by rfl) ⟨419073, by rfl⟩ : syracuseStep 1117529 = 838147) B838147
theorem B2690405 : Blo 495792 2690405 := bstep (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) B504451
theorem B1674647 : Blo 495792 1674647 := bstep (se 1 (by rfl) ⟨1255985, by rfl⟩ : syracuseStep 1674647 = 2511971) B2511971
theorem B1117619 : Blo 495792 1117619 := bstep (se 1 (by rfl) ⟨838214, by rfl⟩ : syracuseStep 1117619 = 1676429) B1676429
theorem B560587 : Blo 495792 560587 := bstep (se 1 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 560587 = 840881) B840881
theorem B1117655 : Blo 495792 1117655 := bstep (se 1 (by rfl) ⟨838241, by rfl⟩ : syracuseStep 1117655 = 1676483) B1676483
theorem B2264537 : Blo 495792 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B5443033 : Blo 495792 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B560695 : Blo 495792 560695 := bstep (se 1 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 560695 = 841043) B841043
theorem B2428481 : Blo 495792 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1117835 : Blo 495792 1117835 := bstep (se 1 (by rfl) ⟨838376, by rfl⟩ : syracuseStep 1117835 = 1676753) B1676753
theorem B1117889 : Blo 495792 1117889 := bstep (se 2 (by rfl) ⟨419208, by rfl⟩ : syracuseStep 1117889 = 838417) B838417
theorem B560875 : Blo 495792 560875 := bstep (se 1 (by rfl) ⟨420656, by rfl⟩ : syracuseStep 560875 = 841313) B841313
theorem B1412939 : Blo 495792 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B560983 : Blo 495792 560983 := bstep (se 1 (by rfl) ⟨420737, by rfl⟩ : syracuseStep 560983 = 841475) B841475
theorem B1118105 : Blo 495792 1118105 := bstep (se 2 (by rfl) ⟨419289, by rfl⟩ : syracuseStep 1118105 = 838579) B838579
theorem B1675187 : Blo 495792 1675187 := bstep (se 1 (by rfl) ⟨1256390, by rfl⟩ : syracuseStep 1675187 = 2512781) B2512781
theorem B2297803 : Blo 495792 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B1118195 : Blo 495792 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B561163 : Blo 495792 561163 := bstep (se 1 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 561163 = 841745) B841745
theorem B1118231 : Blo 495792 1118231 := bstep (se 1 (by rfl) ⟨838673, by rfl⟩ : syracuseStep 1118231 = 1677347) B1677347
theorem B6066251 : Blo 495792 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B561271 : Blo 495792 561271 := bstep (se 1 (by rfl) ⟨420953, by rfl⟩ : syracuseStep 561271 = 841907) B841907
theorem B3575987 : Blo 495792 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B495799 : Blo 495792 495799 := bstep (se 1 (by rfl) ⟨371849, by rfl⟩ : syracuseStep 495799 = 743699) B743699
theorem B1675457 : Blo 495792 1675457 := bstep (se 2 (by rfl) ⟨628296, by rfl⟩ : syracuseStep 1675457 = 1256593) B1256593
theorem B495819 : Blo 495792 495819 := bstep (se 1 (by rfl) ⟨371864, by rfl⟩ : syracuseStep 495819 = 743729) B743729
theorem B1118411 : Blo 495792 1118411 := bstep (se 1 (by rfl) ⟨838808, by rfl⟩ : syracuseStep 1118411 = 1677617) B1677617
theorem B495831 : Blo 495792 495831 := bstep (se 1 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 495831 = 743747) B743747
theorem B495851 : Blo 495792 495851 := bstep (se 1 (by rfl) ⟨371888, by rfl⟩ : syracuseStep 495851 = 743777) B743777
theorem B495863 : Blo 495792 495863 := bstep (se 1 (by rfl) ⟨371897, by rfl⟩ : syracuseStep 495863 = 743795) B743795
theorem B1118465 : Blo 495792 1118465 := bstep (se 2 (by rfl) ⟨419424, by rfl⟩ : syracuseStep 1118465 = 838849) B838849
theorem B495883 : Blo 495792 495883 := bstep (se 1 (by rfl) ⟨371912, by rfl⟩ : syracuseStep 495883 = 743825) B743825
theorem B495895 : Blo 495792 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B495915 : Blo 495792 495915 := bstep (se 1 (by rfl) ⟨371936, by rfl⟩ : syracuseStep 495915 = 743873) B743873
theorem B561451 : Blo 495792 561451 := bstep (se 1 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 561451 = 842177) B842177
theorem B495927 : Blo 495792 495927 := bstep (se 1 (by rfl) ⟨371945, by rfl⟩ : syracuseStep 495927 = 743891) B743891
theorem B495947 : Blo 495792 495947 := bstep (se 1 (by rfl) ⟨371960, by rfl⟩ : syracuseStep 495947 = 743921) B743921
theorem B495959 : Blo 495792 495959 := bstep (se 1 (by rfl) ⟨371969, by rfl⟩ : syracuseStep 495959 = 743939) B743939
theorem B495979 : Blo 495792 495979 := bstep (se 1 (by rfl) ⟨371984, by rfl⟩ : syracuseStep 495979 = 743969) B743969
theorem B495991 : Blo 495792 495991 := bstep (se 1 (by rfl) ⟨371993, by rfl⟩ : syracuseStep 495991 = 743987) B743987
theorem B3019139 : Blo 495792 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B2920835 : Blo 495792 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B496011 : Blo 495792 496011 := bstep (se 1 (by rfl) ⟨372008, by rfl⟩ : syracuseStep 496011 = 744017) B744017
theorem B496023 : Blo 495792 496023 := bstep (se 1 (by rfl) ⟨372017, by rfl⟩ : syracuseStep 496023 = 744035) B744035
theorem B561559 : Blo 495792 561559 := bstep (se 1 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 561559 = 842339) B842339
theorem B496043 : Blo 495792 496043 := bstep (se 1 (by rfl) ⟨372032, by rfl⟩ : syracuseStep 496043 = 744065) B744065
theorem B496055 : Blo 495792 496055 := bstep (se 1 (by rfl) ⟨372041, by rfl⟩ : syracuseStep 496055 = 744083) B744083
theorem B496075 : Blo 495792 496075 := bstep (se 1 (by rfl) ⟨372056, by rfl⟩ : syracuseStep 496075 = 744113) B744113
theorem B496087 : Blo 495792 496087 := bstep (se 1 (by rfl) ⟨372065, by rfl⟩ : syracuseStep 496087 = 744131) B744131
theorem B1118681 : Blo 495792 1118681 := bstep (se 2 (by rfl) ⟨419505, by rfl⟩ : syracuseStep 1118681 = 839011) B839011
theorem B496107 : Blo 495792 496107 := bstep (se 1 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 496107 = 744161) B744161
theorem B496119 : Blo 495792 496119 := bstep (se 1 (by rfl) ⟨372089, by rfl⟩ : syracuseStep 496119 = 744179) B744179
theorem B496139 : Blo 495792 496139 := bstep (se 1 (by rfl) ⟨372104, by rfl⟩ : syracuseStep 496139 = 744209) B744209
theorem B496151 : Blo 495792 496151 := bstep (se 1 (by rfl) ⟨372113, by rfl⟩ : syracuseStep 496151 = 744227) B744227
theorem B496171 : Blo 495792 496171 := bstep (se 1 (by rfl) ⟨372128, by rfl⟩ : syracuseStep 496171 = 744257) B744257
theorem B1118771 : Blo 495792 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B496183 : Blo 495792 496183 := bstep (se 1 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 496183 = 744275) B744275
theorem B496203 : Blo 495792 496203 := bstep (se 1 (by rfl) ⟨372152, by rfl⟩ : syracuseStep 496203 = 744305) B744305
theorem B561739 : Blo 495792 561739 := bstep (se 1 (by rfl) ⟨421304, by rfl⟩ : syracuseStep 561739 = 842609) B842609
theorem B496215 : Blo 495792 496215 := bstep (se 1 (by rfl) ⟨372161, by rfl⟩ : syracuseStep 496215 = 744323) B744323
theorem B1118807 : Blo 495792 1118807 := bstep (se 1 (by rfl) ⟨839105, by rfl⟩ : syracuseStep 1118807 = 1678211) B1678211
theorem B496235 : Blo 495792 496235 := bstep (se 1 (by rfl) ⟨372176, by rfl⟩ : syracuseStep 496235 = 744353) B744353
theorem B496247 : Blo 495792 496247 := bstep (se 1 (by rfl) ⟨372185, by rfl⟩ : syracuseStep 496247 = 744371) B744371
theorem B496267 : Blo 495792 496267 := bstep (se 1 (by rfl) ⟨372200, by rfl⟩ : syracuseStep 496267 = 744401) B744401
theorem B496279 : Blo 495792 496279 := bstep (se 1 (by rfl) ⟨372209, by rfl⟩ : syracuseStep 496279 = 744419) B744419
theorem B496299 : Blo 495792 496299 := bstep (se 1 (by rfl) ⟨372224, by rfl⟩ : syracuseStep 496299 = 744449) B744449
theorem B496311 : Blo 495792 496311 := bstep (se 1 (by rfl) ⟨372233, by rfl⟩ : syracuseStep 496311 = 744467) B744467
theorem B561847 : Blo 495792 561847 := bstep (se 1 (by rfl) ⟨421385, by rfl⟩ : syracuseStep 561847 = 842771) B842771
theorem B496331 : Blo 495792 496331 := bstep (se 1 (by rfl) ⟨372248, by rfl⟩ : syracuseStep 496331 = 744497) B744497
theorem B496343 : Blo 495792 496343 := bstep (se 1 (by rfl) ⟨372257, by rfl⟩ : syracuseStep 496343 = 744515) B744515
theorem B1675997 : Blo 495792 1675997 := bstep (se 3 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 1675997 = 628499) B628499
theorem B496363 : Blo 495792 496363 := bstep (se 1 (by rfl) ⟨372272, by rfl⟩ : syracuseStep 496363 = 744545) B744545
theorem B496375 : Blo 495792 496375 := bstep (se 1 (by rfl) ⟨372281, by rfl⟩ : syracuseStep 496375 = 744563) B744563
theorem B496395 : Blo 495792 496395 := bstep (se 1 (by rfl) ⟨372296, by rfl⟩ : syracuseStep 496395 = 744593) B744593
theorem B1118987 : Blo 495792 1118987 := bstep (se 1 (by rfl) ⟨839240, by rfl⟩ : syracuseStep 1118987 = 1678481) B1678481
theorem B2396945 : Blo 495792 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B496407 : Blo 495792 496407 := bstep (se 1 (by rfl) ⟨372305, by rfl⟩ : syracuseStep 496407 = 744611) B744611
theorem B496427 : Blo 495792 496427 := bstep (se 1 (by rfl) ⟨372320, by rfl⟩ : syracuseStep 496427 = 744641) B744641
theorem B496439 : Blo 495792 496439 := bstep (se 1 (by rfl) ⟨372329, by rfl⟩ : syracuseStep 496439 = 744659) B744659
theorem B1119041 : Blo 495792 1119041 := bstep (se 2 (by rfl) ⟨419640, by rfl⟩ : syracuseStep 1119041 = 839281) B839281
theorem B496459 : Blo 495792 496459 := bstep (se 1 (by rfl) ⟨372344, by rfl⟩ : syracuseStep 496459 = 744689) B744689
theorem B758603 : Blo 495792 758603 := bstep (se 1 (by rfl) ⟨568952, by rfl⟩ : syracuseStep 758603 = 1137905) B1137905
theorem B496471 : Blo 495792 496471 := bstep (se 1 (by rfl) ⟨372353, by rfl⟩ : syracuseStep 496471 = 744707) B744707
theorem B496491 : Blo 495792 496491 := bstep (se 1 (by rfl) ⟨372368, by rfl⟩ : syracuseStep 496491 = 744737) B744737
theorem B562027 : Blo 495792 562027 := bstep (se 1 (by rfl) ⟨421520, by rfl⟩ : syracuseStep 562027 = 843041) B843041
theorem B496503 : Blo 495792 496503 := bstep (se 1 (by rfl) ⟨372377, by rfl⟩ : syracuseStep 496503 = 744755) B744755
theorem B496523 : Blo 495792 496523 := bstep (se 1 (by rfl) ⟨372392, by rfl⟩ : syracuseStep 496523 = 744785) B744785
theorem B496535 : Blo 495792 496535 := bstep (se 1 (by rfl) ⟨372401, by rfl⟩ : syracuseStep 496535 = 744803) B744803
theorem B496555 : Blo 495792 496555 := bstep (se 1 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 496555 = 744833) B744833
theorem B496567 : Blo 495792 496567 := bstep (se 1 (by rfl) ⟨372425, by rfl⟩ : syracuseStep 496567 = 744851) B744851
theorem B496587 : Blo 495792 496587 := bstep (se 1 (by rfl) ⟨372440, by rfl⟩ : syracuseStep 496587 = 744881) B744881
theorem B496599 : Blo 495792 496599 := bstep (se 1 (by rfl) ⟨372449, by rfl⟩ : syracuseStep 496599 = 744899) B744899
theorem B562135 : Blo 495792 562135 := bstep (se 1 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 562135 = 843203) B843203
theorem B496619 : Blo 495792 496619 := bstep (se 1 (by rfl) ⟨372464, by rfl⟩ : syracuseStep 496619 = 744929) B744929
theorem B496631 : Blo 495792 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B496651 : Blo 495792 496651 := bstep (se 1 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 496651 = 744977) B744977
theorem B496663 : Blo 495792 496663 := bstep (se 1 (by rfl) ⟨372497, by rfl⟩ : syracuseStep 496663 = 744995) B744995
theorem B1119257 : Blo 495792 1119257 := bstep (se 2 (by rfl) ⟨419721, by rfl⟩ : syracuseStep 1119257 = 839443) B839443
theorem B496683 : Blo 495792 496683 := bstep (se 1 (by rfl) ⟨372512, by rfl⟩ : syracuseStep 496683 = 745025) B745025
theorem B496695 : Blo 495792 496695 := bstep (se 1 (by rfl) ⟨372521, by rfl⟩ : syracuseStep 496695 = 745043) B745043
theorem B496715 : Blo 495792 496715 := bstep (se 1 (by rfl) ⟨372536, by rfl⟩ : syracuseStep 496715 = 745073) B745073
theorem B496727 : Blo 495792 496727 := bstep (se 1 (by rfl) ⟨372545, by rfl⟩ : syracuseStep 496727 = 745091) B745091
theorem B496747 : Blo 495792 496747 := bstep (se 1 (by rfl) ⟨372560, by rfl⟩ : syracuseStep 496747 = 745121) B745121
theorem B1119347 : Blo 495792 1119347 := bstep (se 1 (by rfl) ⟨839510, by rfl⟩ : syracuseStep 1119347 = 1679021) B1679021
theorem B496759 : Blo 495792 496759 := bstep (se 1 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 496759 = 745139) B745139
theorem B627851 : Blo 495792 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B496779 : Blo 495792 496779 := bstep (se 1 (by rfl) ⟨372584, by rfl⟩ : syracuseStep 496779 = 745169) B745169
theorem B496791 : Blo 495792 496791 := bstep (se 1 (by rfl) ⟨372593, by rfl⟩ : syracuseStep 496791 = 745187) B745187
theorem B1119383 : Blo 495792 1119383 := bstep (se 1 (by rfl) ⟨839537, by rfl⟩ : syracuseStep 1119383 = 1679075) B1679075
theorem B529579 : Blo 495792 529579 := bstep (se 1 (by rfl) ⟨397184, by rfl⟩ : syracuseStep 529579 = 794369) B794369
theorem B496811 : Blo 495792 496811 := bstep (se 1 (by rfl) ⟨372608, by rfl⟩ : syracuseStep 496811 = 745217) B745217
theorem B496823 : Blo 495792 496823 := bstep (se 1 (by rfl) ⟨372617, by rfl⟩ : syracuseStep 496823 = 745235) B745235
theorem B496843 : Blo 495792 496843 := bstep (se 1 (by rfl) ⟨372632, by rfl⟩ : syracuseStep 496843 = 745265) B745265
theorem B496855 : Blo 495792 496855 := bstep (se 1 (by rfl) ⟨372641, by rfl⟩ : syracuseStep 496855 = 745283) B745283
theorem B496875 : Blo 495792 496875 := bstep (se 1 (by rfl) ⟨372656, by rfl⟩ : syracuseStep 496875 = 745313) B745313
theorem B496887 : Blo 495792 496887 := bstep (se 1 (by rfl) ⟨372665, by rfl⟩ : syracuseStep 496887 = 745331) B745331
theorem B496907 : Blo 495792 496907 := bstep (se 1 (by rfl) ⟨372680, by rfl⟩ : syracuseStep 496907 = 745361) B745361
theorem B496919 : Blo 495792 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B496939 : Blo 495792 496939 := bstep (se 1 (by rfl) ⟨372704, by rfl⟩ : syracuseStep 496939 = 745409) B745409
theorem B496951 : Blo 495792 496951 := bstep (se 1 (by rfl) ⟨372713, by rfl⟩ : syracuseStep 496951 = 745427) B745427
theorem B3020107 : Blo 495792 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B496971 : Blo 495792 496971 := bstep (se 1 (by rfl) ⟨372728, by rfl⟩ : syracuseStep 496971 = 745457) B745457
theorem B1119563 : Blo 495792 1119563 := bstep (se 1 (by rfl) ⟨839672, by rfl⟩ : syracuseStep 1119563 = 1679345) B1679345
theorem B496983 : Blo 495792 496983 := bstep (se 1 (by rfl) ⟨372737, by rfl⟩ : syracuseStep 496983 = 745475) B745475
theorem B3773789 : Blo 495792 3773789 := bstep (se 3 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 3773789 = 1415171) B1415171
theorem B497003 : Blo 495792 497003 := bstep (se 1 (by rfl) ⟨372752, by rfl⟩ : syracuseStep 497003 = 745505) B745505
theorem B497015 : Blo 495792 497015 := bstep (se 1 (by rfl) ⟨372761, by rfl⟩ : syracuseStep 497015 = 745523) B745523
theorem B1119617 : Blo 495792 1119617 := bstep (se 2 (by rfl) ⟨419856, by rfl⟩ : syracuseStep 1119617 = 839713) B839713
theorem B497035 : Blo 495792 497035 := bstep (se 1 (by rfl) ⟨372776, by rfl⟩ : syracuseStep 497035 = 745553) B745553
theorem B497047 : Blo 495792 497047 := bstep (se 1 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 497047 = 745571) B745571
theorem B529835 : Blo 495792 529835 := bstep (se 1 (by rfl) ⟨397376, by rfl⟩ : syracuseStep 529835 = 794753) B794753
theorem B497067 : Blo 495792 497067 := bstep (se 1 (by rfl) ⟨372800, by rfl⟩ : syracuseStep 497067 = 745601) B745601
theorem B1414579 : Blo 495792 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B497079 : Blo 495792 497079 := bstep (se 1 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 497079 = 745619) B745619
theorem B497099 : Blo 495792 497099 := bstep (se 1 (by rfl) ⟨372824, by rfl⟩ : syracuseStep 497099 = 745649) B745649
theorem B497111 : Blo 495792 497111 := bstep (se 1 (by rfl) ⟨372833, by rfl⟩ : syracuseStep 497111 = 745667) B745667
theorem B497131 : Blo 495792 497131 := bstep (se 1 (by rfl) ⟨372848, by rfl⟩ : syracuseStep 497131 = 745697) B745697
theorem B497143 : Blo 495792 497143 := bstep (se 1 (by rfl) ⟨372857, by rfl⟩ : syracuseStep 497143 = 745715) B745715
theorem B497163 : Blo 495792 497163 := bstep (se 1 (by rfl) ⟨372872, by rfl⟩ : syracuseStep 497163 = 745745) B745745
theorem B497175 : Blo 495792 497175 := bstep (se 1 (by rfl) ⟨372881, by rfl⟩ : syracuseStep 497175 = 745763) B745763
theorem B497195 : Blo 495792 497195 := bstep (se 1 (by rfl) ⟨372896, by rfl⟩ : syracuseStep 497195 = 745793) B745793
theorem B497207 : Blo 495792 497207 := bstep (se 1 (by rfl) ⟨372905, by rfl⟩ : syracuseStep 497207 = 745811) B745811
theorem B497227 : Blo 495792 497227 := bstep (se 1 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 497227 = 745841) B745841
theorem B497239 : Blo 495792 497239 := bstep (se 1 (by rfl) ⟨372929, by rfl⟩ : syracuseStep 497239 = 745859) B745859
theorem B1119833 : Blo 495792 1119833 := bstep (se 2 (by rfl) ⟨419937, by rfl⟩ : syracuseStep 1119833 = 839875) B839875
theorem B2823781 : Blo 495792 2823781 := bstep (se 4 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 2823781 = 529459) B529459
theorem B497259 : Blo 495792 497259 := bstep (se 1 (by rfl) ⟨372944, by rfl⟩ : syracuseStep 497259 = 745889) B745889
theorem B497271 : Blo 495792 497271 := bstep (se 1 (by rfl) ⟨372953, by rfl⟩ : syracuseStep 497271 = 745907) B745907
theorem B497291 : Blo 495792 497291 := bstep (se 1 (by rfl) ⟨372968, by rfl⟩ : syracuseStep 497291 = 745937) B745937
theorem B497303 : Blo 495792 497303 := bstep (se 1 (by rfl) ⟨372977, by rfl⟩ : syracuseStep 497303 = 745955) B745955
theorem B497323 : Blo 495792 497323 := bstep (se 1 (by rfl) ⟨372992, by rfl⟩ : syracuseStep 497323 = 745985) B745985
theorem B1119923 : Blo 495792 1119923 := bstep (se 1 (by rfl) ⟨839942, by rfl⟩ : syracuseStep 1119923 = 1679885) B1679885
theorem B497335 : Blo 495792 497335 := bstep (se 1 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 497335 = 746003) B746003
theorem B497355 : Blo 495792 497355 := bstep (se 1 (by rfl) ⟨373016, by rfl⟩ : syracuseStep 497355 = 746033) B746033
theorem B497367 : Blo 495792 497367 := bstep (se 1 (by rfl) ⟨373025, by rfl⟩ : syracuseStep 497367 = 746051) B746051
theorem B1119959 : Blo 495792 1119959 := bstep (se 1 (by rfl) ⟨839969, by rfl⟩ : syracuseStep 1119959 = 1679939) B1679939
theorem B497387 : Blo 495792 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B497399 : Blo 495792 497399 := bstep (se 1 (by rfl) ⟨373049, by rfl⟩ : syracuseStep 497399 = 746099) B746099
theorem B497419 : Blo 495792 497419 := bstep (se 1 (by rfl) ⟨373064, by rfl⟩ : syracuseStep 497419 = 746129) B746129
theorem B497431 : Blo 495792 497431 := bstep (se 1 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 497431 = 746147) B746147
theorem B497451 : Blo 495792 497451 := bstep (se 1 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 497451 = 746177) B746177
theorem B497463 : Blo 495792 497463 := bstep (se 1 (by rfl) ⟨373097, by rfl⟩ : syracuseStep 497463 = 746195) B746195
theorem B628555 : Blo 495792 628555 := bstep (se 1 (by rfl) ⟨471416, by rfl⟩ : syracuseStep 628555 = 942833) B942833
theorem B1677131 : Blo 495792 1677131 := bstep (se 1 (by rfl) ⟨1257848, by rfl⟩ : syracuseStep 1677131 = 2515697) B2515697
theorem B497483 : Blo 495792 497483 := bstep (se 1 (by rfl) ⟨373112, by rfl⟩ : syracuseStep 497483 = 746225) B746225
theorem B497495 : Blo 495792 497495 := bstep (se 1 (by rfl) ⟨373121, by rfl⟩ : syracuseStep 497495 = 746243) B746243
theorem B497515 : Blo 495792 497515 := bstep (se 1 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 497515 = 746273) B746273
theorem B497527 : Blo 495792 497527 := bstep (se 1 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 497527 = 746291) B746291
theorem B497547 : Blo 495792 497547 := bstep (se 1 (by rfl) ⟨373160, by rfl⟩ : syracuseStep 497547 = 746321) B746321
theorem B1120139 : Blo 495792 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B497559 : Blo 495792 497559 := bstep (se 1 (by rfl) ⟨373169, by rfl⟩ : syracuseStep 497559 = 746339) B746339
theorem B497579 : Blo 495792 497579 := bstep (se 1 (by rfl) ⟨373184, by rfl⟩ : syracuseStep 497579 = 746369) B746369
theorem B497591 : Blo 495792 497591 := bstep (se 1 (by rfl) ⟨373193, by rfl⟩ : syracuseStep 497591 = 746387) B746387
theorem B1120193 : Blo 495792 1120193 := bstep (se 2 (by rfl) ⟨420072, by rfl⟩ : syracuseStep 1120193 = 840145) B840145
theorem B497611 : Blo 495792 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B497623 : Blo 495792 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B497643 : Blo 495792 497643 := bstep (se 1 (by rfl) ⟨373232, by rfl⟩ : syracuseStep 497643 = 746465) B746465
theorem B497655 : Blo 495792 497655 := bstep (se 1 (by rfl) ⟨373241, by rfl⟩ : syracuseStep 497655 = 746483) B746483
theorem B497675 : Blo 495792 497675 := bstep (se 1 (by rfl) ⟨373256, by rfl⟩ : syracuseStep 497675 = 746513) B746513
theorem B497687 : Blo 495792 497687 := bstep (se 1 (by rfl) ⟨373265, by rfl⟩ : syracuseStep 497687 = 746531) B746531
theorem B497707 : Blo 495792 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B497719 : Blo 495792 497719 := bstep (se 1 (by rfl) ⟨373289, by rfl⟩ : syracuseStep 497719 = 746579) B746579
theorem B8198213 : Blo 495792 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B497739 : Blo 495792 497739 := bstep (se 1 (by rfl) ⟨373304, by rfl⟩ : syracuseStep 497739 = 746609) B746609
theorem B628823 : Blo 495792 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B1677401 : Blo 495792 1677401 := bstep (se 2 (by rfl) ⟨629025, by rfl⟩ : syracuseStep 1677401 = 1258051) B1258051
theorem B497751 : Blo 495792 497751 := bstep (se 1 (by rfl) ⟨373313, by rfl⟩ : syracuseStep 497751 = 746627) B746627
theorem B497771 : Blo 495792 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B497783 : Blo 495792 497783 := bstep (se 1 (by rfl) ⟨373337, by rfl⟩ : syracuseStep 497783 = 746675) B746675
theorem B497803 : Blo 495792 497803 := bstep (se 1 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 497803 = 746705) B746705
theorem B497815 : Blo 495792 497815 := bstep (se 1 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 497815 = 746723) B746723
theorem B1120409 : Blo 495792 1120409 := bstep (se 2 (by rfl) ⟨420153, by rfl⟩ : syracuseStep 1120409 = 840307) B840307
theorem B497835 : Blo 495792 497835 := bstep (se 1 (by rfl) ⟨373376, by rfl⟩ : syracuseStep 497835 = 746753) B746753
theorem B497847 : Blo 495792 497847 := bstep (se 1 (by rfl) ⟨373385, by rfl⟩ : syracuseStep 497847 = 746771) B746771
theorem B497867 : Blo 495792 497867 := bstep (se 1 (by rfl) ⟨373400, by rfl⟩ : syracuseStep 497867 = 746801) B746801
theorem B497879 : Blo 495792 497879 := bstep (se 1 (by rfl) ⟨373409, by rfl⟩ : syracuseStep 497879 = 746819) B746819
theorem B497899 : Blo 495792 497899 := bstep (se 1 (by rfl) ⟨373424, by rfl⟩ : syracuseStep 497899 = 746849) B746849
theorem B1120499 : Blo 495792 1120499 := bstep (se 1 (by rfl) ⟨840374, by rfl⟩ : syracuseStep 1120499 = 1680749) B1680749
theorem B497911 : Blo 495792 497911 := bstep (se 1 (by rfl) ⟨373433, by rfl⟩ : syracuseStep 497911 = 746867) B746867
theorem B497931 : Blo 495792 497931 := bstep (se 1 (by rfl) ⟨373448, by rfl⟩ : syracuseStep 497931 = 746897) B746897
theorem B497943 : Blo 495792 497943 := bstep (se 1 (by rfl) ⟨373457, by rfl⟩ : syracuseStep 497943 = 746915) B746915
theorem B1120535 : Blo 495792 1120535 := bstep (se 1 (by rfl) ⟨840401, by rfl⟩ : syracuseStep 1120535 = 1680803) B1680803
theorem B497963 : Blo 495792 497963 := bstep (se 1 (by rfl) ⟨373472, by rfl⟩ : syracuseStep 497963 = 746945) B746945
theorem B497975 : Blo 495792 497975 := bstep (se 1 (by rfl) ⟨373481, by rfl⟩ : syracuseStep 497975 = 746963) B746963
theorem B3021131 : Blo 495792 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B497995 : Blo 495792 497995 := bstep (se 1 (by rfl) ⟨373496, by rfl⟩ : syracuseStep 497995 = 746993) B746993
theorem B498007 : Blo 495792 498007 := bstep (se 1 (by rfl) ⟨373505, by rfl⟩ : syracuseStep 498007 = 747011) B747011
theorem B2529629 : Blo 495792 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B498027 : Blo 495792 498027 := bstep (se 1 (by rfl) ⟨373520, by rfl⟩ : syracuseStep 498027 = 747041) B747041
theorem B498039 : Blo 495792 498039 := bstep (se 1 (by rfl) ⟨373529, by rfl⟩ : syracuseStep 498039 = 747059) B747059
theorem B498059 : Blo 495792 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B498071 : Blo 495792 498071 := bstep (se 1 (by rfl) ⟨373553, by rfl⟩ : syracuseStep 498071 = 747107) B747107
theorem B498091 : Blo 495792 498091 := bstep (se 1 (by rfl) ⟨373568, by rfl⟩ : syracuseStep 498091 = 747137) B747137
theorem B498103 : Blo 495792 498103 := bstep (se 1 (by rfl) ⟨373577, by rfl⟩ : syracuseStep 498103 = 747155) B747155
theorem B1415627 : Blo 495792 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B1120715 : Blo 495792 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B498123 : Blo 495792 498123 := bstep (se 1 (by rfl) ⟨373592, by rfl⟩ : syracuseStep 498123 = 747185) B747185
theorem B498135 : Blo 495792 498135 := bstep (se 1 (by rfl) ⟨373601, by rfl⟩ : syracuseStep 498135 = 747203) B747203
theorem B498155 : Blo 495792 498155 := bstep (se 1 (by rfl) ⟨373616, by rfl⟩ : syracuseStep 498155 = 747233) B747233
theorem B498167 : Blo 495792 498167 := bstep (se 1 (by rfl) ⟨373625, by rfl⟩ : syracuseStep 498167 = 747251) B747251
theorem B1120769 : Blo 495792 1120769 := bstep (se 2 (by rfl) ⟨420288, by rfl⟩ : syracuseStep 1120769 = 840577) B840577
theorem B498187 : Blo 495792 498187 := bstep (se 1 (by rfl) ⟨373640, by rfl⟩ : syracuseStep 498187 = 747281) B747281
theorem B498199 : Blo 495792 498199 := bstep (se 1 (by rfl) ⟨373649, by rfl⟩ : syracuseStep 498199 = 747299) B747299
theorem B498219 : Blo 495792 498219 := bstep (se 1 (by rfl) ⟨373664, by rfl⟩ : syracuseStep 498219 = 747329) B747329
theorem B498231 : Blo 495792 498231 := bstep (se 1 (by rfl) ⟨373673, by rfl⟩ : syracuseStep 498231 = 747347) B747347
theorem B498251 : Blo 495792 498251 := bstep (se 1 (by rfl) ⟨373688, by rfl⟩ : syracuseStep 498251 = 747377) B747377
theorem B498263 : Blo 495792 498263 := bstep (se 1 (by rfl) ⟨373697, by rfl⟩ : syracuseStep 498263 = 747395) B747395
theorem B498283 : Blo 495792 498283 := bstep (se 1 (by rfl) ⟨373712, by rfl⟩ : syracuseStep 498283 = 747425) B747425
theorem B498295 : Blo 495792 498295 := bstep (se 1 (by rfl) ⟨373721, by rfl⟩ : syracuseStep 498295 = 747443) B747443
theorem B498315 : Blo 495792 498315 := bstep (se 1 (by rfl) ⟨373736, by rfl⟩ : syracuseStep 498315 = 747473) B747473
theorem B498327 : Blo 495792 498327 := bstep (se 1 (by rfl) ⟨373745, by rfl⟩ : syracuseStep 498327 = 747491) B747491
theorem B498347 : Blo 495792 498347 := bstep (se 1 (by rfl) ⟨373760, by rfl⟩ : syracuseStep 498347 = 747521) B747521
theorem B498359 : Blo 495792 498359 := bstep (se 1 (by rfl) ⟨373769, by rfl⟩ : syracuseStep 498359 = 747539) B747539
theorem B498379 : Blo 495792 498379 := bstep (se 1 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 498379 = 747569) B747569
theorem B4266701 : Blo 495792 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B498391 : Blo 495792 498391 := bstep (se 1 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 498391 = 747587) B747587
theorem B1120985 : Blo 495792 1120985 := bstep (se 2 (by rfl) ⟨420369, by rfl⟩ : syracuseStep 1120985 = 840739) B840739
theorem B498411 : Blo 495792 498411 := bstep (se 1 (by rfl) ⟨373808, by rfl⟩ : syracuseStep 498411 = 747617) B747617
theorem B498423 : Blo 495792 498423 := bstep (se 1 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 498423 = 747635) B747635
theorem B498443 : Blo 495792 498443 := bstep (se 1 (by rfl) ⟨373832, by rfl⟩ : syracuseStep 498443 = 747665) B747665
theorem B1678103 : Blo 495792 1678103 := bstep (se 1 (by rfl) ⟨1258577, by rfl⟩ : syracuseStep 1678103 = 2517155) B2517155
theorem B629527 : Blo 495792 629527 := bstep (se 1 (by rfl) ⟨472145, by rfl⟩ : syracuseStep 629527 = 944291) B944291
theorem B498455 : Blo 495792 498455 := bstep (se 1 (by rfl) ⟨373841, by rfl⟩ : syracuseStep 498455 = 747683) B747683
theorem B498475 : Blo 495792 498475 := bstep (se 1 (by rfl) ⟨373856, by rfl⟩ : syracuseStep 498475 = 747713) B747713
theorem B2399021 : Blo 495792 2399021 := bstep (se 3 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 2399021 = 899633) B899633
theorem B1121075 : Blo 495792 1121075 := bstep (se 1 (by rfl) ⟨840806, by rfl⟩ : syracuseStep 1121075 = 1681613) B1681613
theorem B498487 : Blo 495792 498487 := bstep (se 1 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 498487 = 747731) B747731
theorem B498507 : Blo 495792 498507 := bstep (se 1 (by rfl) ⟨373880, by rfl⟩ : syracuseStep 498507 = 747761) B747761
theorem B1121111 : Blo 495792 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B498519 : Blo 495792 498519 := bstep (se 1 (by rfl) ⟨373889, by rfl⟩ : syracuseStep 498519 = 747779) B747779
theorem B498539 : Blo 495792 498539 := bstep (se 1 (by rfl) ⟨373904, by rfl⟩ : syracuseStep 498539 = 747809) B747809
theorem B498551 : Blo 495792 498551 := bstep (se 1 (by rfl) ⟨373913, by rfl⟩ : syracuseStep 498551 = 747827) B747827
theorem B498571 : Blo 495792 498571 := bstep (se 1 (by rfl) ⟨373928, by rfl⟩ : syracuseStep 498571 = 747857) B747857
theorem B498583 : Blo 495792 498583 := bstep (se 1 (by rfl) ⟨373937, by rfl⟩ : syracuseStep 498583 = 747875) B747875
theorem B498603 : Blo 495792 498603 := bstep (se 1 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 498603 = 747905) B747905
theorem B8100785 : Blo 495792 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B498615 : Blo 495792 498615 := bstep (se 1 (by rfl) ⟨373961, by rfl⟩ : syracuseStep 498615 = 747923) B747923
theorem B498635 : Blo 495792 498635 := bstep (se 1 (by rfl) ⟨373976, by rfl⟩ : syracuseStep 498635 = 747953) B747953
theorem B498647 : Blo 495792 498647 := bstep (se 1 (by rfl) ⟨373985, by rfl⟩ : syracuseStep 498647 = 747971) B747971
theorem B5675993 : Blo 495792 5675993 := bstep (se 2 (by rfl) ⟨2128497, by rfl⟩ : syracuseStep 5675993 = 4256995) B4256995
theorem B498667 : Blo 495792 498667 := bstep (se 1 (by rfl) ⟨374000, by rfl⟩ : syracuseStep 498667 = 748001) B748001
theorem B498679 : Blo 495792 498679 := bstep (se 1 (by rfl) ⟨374009, by rfl⟩ : syracuseStep 498679 = 748019) B748019
theorem B1121291 : Blo 495792 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B498699 : Blo 495792 498699 := bstep (se 1 (by rfl) ⟨374024, by rfl⟩ : syracuseStep 498699 = 748049) B748049
theorem B498711 : Blo 495792 498711 := bstep (se 1 (by rfl) ⟨374033, by rfl⟩ : syracuseStep 498711 = 748067) B748067
theorem B498731 : Blo 495792 498731 := bstep (se 1 (by rfl) ⟨374048, by rfl⟩ : syracuseStep 498731 = 748097) B748097
theorem B498743 : Blo 495792 498743 := bstep (se 1 (by rfl) ⟨374057, by rfl⟩ : syracuseStep 498743 = 748115) B748115
theorem B1121345 : Blo 495792 1121345 := bstep (se 2 (by rfl) ⟨420504, by rfl⟩ : syracuseStep 1121345 = 841009) B841009
theorem B498763 : Blo 495792 498763 := bstep (se 1 (by rfl) ⟨374072, by rfl⟩ : syracuseStep 498763 = 748145) B748145
theorem B498775 : Blo 495792 498775 := bstep (se 1 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 498775 = 748163) B748163
theorem B498795 : Blo 495792 498795 := bstep (se 1 (by rfl) ⟨374096, by rfl⟩ : syracuseStep 498795 = 748193) B748193
theorem B498807 : Blo 495792 498807 := bstep (se 1 (by rfl) ⟨374105, by rfl⟩ : syracuseStep 498807 = 748211) B748211
theorem B498827 : Blo 495792 498827 := bstep (se 1 (by rfl) ⟨374120, by rfl⟩ : syracuseStep 498827 = 748241) B748241
theorem B498839 : Blo 495792 498839 := bstep (se 1 (by rfl) ⟨374129, by rfl⟩ : syracuseStep 498839 = 748259) B748259
theorem B498859 : Blo 495792 498859 := bstep (se 1 (by rfl) ⟨374144, by rfl⟩ : syracuseStep 498859 = 748289) B748289
theorem B498871 : Blo 495792 498871 := bstep (se 1 (by rfl) ⟨374153, by rfl⟩ : syracuseStep 498871 = 748307) B748307
theorem B498891 : Blo 495792 498891 := bstep (se 1 (by rfl) ⟨374168, by rfl⟩ : syracuseStep 498891 = 748337) B748337
theorem B498903 : Blo 495792 498903 := bstep (se 1 (by rfl) ⟨374177, by rfl⟩ : syracuseStep 498903 = 748355) B748355
theorem B498923 : Blo 495792 498923 := bstep (se 1 (by rfl) ⟨374192, by rfl⟩ : syracuseStep 498923 = 748385) B748385
theorem B498935 : Blo 495792 498935 := bstep (se 1 (by rfl) ⟨374201, by rfl⟩ : syracuseStep 498935 = 748403) B748403
theorem B498955 : Blo 495792 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B498967 : Blo 495792 498967 := bstep (se 1 (by rfl) ⟨374225, by rfl⟩ : syracuseStep 498967 = 748451) B748451
theorem B1121561 : Blo 495792 1121561 := bstep (se 2 (by rfl) ⟨420585, by rfl⟩ : syracuseStep 1121561 = 841171) B841171
theorem B498987 : Blo 495792 498987 := bstep (se 1 (by rfl) ⟨374240, by rfl⟩ : syracuseStep 498987 = 748481) B748481
theorem B1678643 : Blo 495792 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B498999 : Blo 495792 498999 := bstep (se 1 (by rfl) ⟨374249, by rfl⟩ : syracuseStep 498999 = 748499) B748499
theorem B499019 : Blo 495792 499019 := bstep (se 1 (by rfl) ⟨374264, by rfl⟩ : syracuseStep 499019 = 748529) B748529
theorem B499031 : Blo 495792 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B499051 : Blo 495792 499051 := bstep (se 1 (by rfl) ⟨374288, by rfl⟩ : syracuseStep 499051 = 748577) B748577
theorem B1121651 : Blo 495792 1121651 := bstep (se 1 (by rfl) ⟨841238, by rfl⟩ : syracuseStep 1121651 = 1682477) B1682477
theorem B499063 : Blo 495792 499063 := bstep (se 1 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 499063 = 748595) B748595
theorem B531851 : Blo 495792 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B499083 : Blo 495792 499083 := bstep (se 1 (by rfl) ⟨374312, by rfl⟩ : syracuseStep 499083 = 748625) B748625
theorem B1121687 : Blo 495792 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B499095 : Blo 495792 499095 := bstep (se 1 (by rfl) ⟨374321, by rfl⟩ : syracuseStep 499095 = 748643) B748643
theorem B499115 : Blo 495792 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B499127 : Blo 495792 499127 := bstep (se 1 (by rfl) ⟨374345, by rfl⟩ : syracuseStep 499127 = 748691) B748691
theorem B499147 : Blo 495792 499147 := bstep (se 1 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 499147 = 748721) B748721
theorem B499159 : Blo 495792 499159 := bstep (se 1 (by rfl) ⟨374369, by rfl⟩ : syracuseStep 499159 = 748739) B748739
theorem B499179 : Blo 495792 499179 := bstep (se 1 (by rfl) ⟨374384, by rfl⟩ : syracuseStep 499179 = 748769) B748769
theorem B499191 : Blo 495792 499191 := bstep (se 1 (by rfl) ⟨374393, by rfl⟩ : syracuseStep 499191 = 748787) B748787
theorem B499211 : Blo 495792 499211 := bstep (se 1 (by rfl) ⟨374408, by rfl⟩ : syracuseStep 499211 = 748817) B748817
theorem B499223 : Blo 495792 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B499243 : Blo 495792 499243 := bstep (se 1 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 499243 = 748865) B748865
theorem B2399789 : Blo 495792 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B499255 : Blo 495792 499255 := bstep (se 1 (by rfl) ⟨374441, by rfl⟩ : syracuseStep 499255 = 748883) B748883
theorem B1678913 : Blo 495792 1678913 := bstep (se 2 (by rfl) ⟨629592, by rfl⟩ : syracuseStep 1678913 = 1259185) B1259185
theorem B1121867 : Blo 495792 1121867 := bstep (se 1 (by rfl) ⟨841400, by rfl⟩ : syracuseStep 1121867 = 1682801) B1682801
theorem B499275 : Blo 495792 499275 := bstep (se 1 (by rfl) ⟨374456, by rfl⟩ : syracuseStep 499275 = 748913) B748913
theorem B499287 : Blo 495792 499287 := bstep (se 1 (by rfl) ⟨374465, by rfl⟩ : syracuseStep 499287 = 748931) B748931
theorem B499307 : Blo 495792 499307 := bstep (se 1 (by rfl) ⟨374480, by rfl⟩ : syracuseStep 499307 = 748961) B748961
theorem B499319 : Blo 495792 499319 := bstep (se 1 (by rfl) ⟨374489, by rfl⟩ : syracuseStep 499319 = 748979) B748979
theorem B1121921 : Blo 495792 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B499339 : Blo 495792 499339 := bstep (se 1 (by rfl) ⟨374504, by rfl⟩ : syracuseStep 499339 = 749009) B749009
theorem B499351 : Blo 495792 499351 := bstep (se 1 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 499351 = 749027) B749027
theorem B499371 : Blo 495792 499371 := bstep (se 1 (by rfl) ⟨374528, by rfl⟩ : syracuseStep 499371 = 749057) B749057
theorem B499383 : Blo 495792 499383 := bstep (se 1 (by rfl) ⟨374537, by rfl⟩ : syracuseStep 499383 = 749075) B749075
theorem B2268875 : Blo 495792 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B499403 : Blo 495792 499403 := bstep (se 1 (by rfl) ⟨374552, by rfl⟩ : syracuseStep 499403 = 749105) B749105
theorem B499415 : Blo 495792 499415 := bstep (se 1 (by rfl) ⟨374561, by rfl⟩ : syracuseStep 499415 = 749123) B749123
theorem B958169 : Blo 495792 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B499435 : Blo 495792 499435 := bstep (se 1 (by rfl) ⟨374576, by rfl⟩ : syracuseStep 499435 = 749153) B749153
theorem B499447 : Blo 495792 499447 := bstep (se 1 (by rfl) ⟨374585, by rfl⟩ : syracuseStep 499447 = 749171) B749171
theorem B499467 : Blo 495792 499467 := bstep (se 1 (by rfl) ⟨374600, by rfl⟩ : syracuseStep 499467 = 749201) B749201
theorem B499479 : Blo 495792 499479 := bstep (se 1 (by rfl) ⟨374609, by rfl⟩ : syracuseStep 499479 = 749219) B749219
theorem B499499 : Blo 495792 499499 := bstep (se 1 (by rfl) ⟨374624, by rfl⟩ : syracuseStep 499499 = 749249) B749249
theorem B499511 : Blo 495792 499511 := bstep (se 1 (by rfl) ⟨374633, by rfl⟩ : syracuseStep 499511 = 749267) B749267
theorem B499531 : Blo 495792 499531 := bstep (se 1 (by rfl) ⟨374648, by rfl⟩ : syracuseStep 499531 = 749297) B749297
theorem B1154891 : Blo 495792 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B499543 : Blo 495792 499543 := bstep (se 1 (by rfl) ⟨374657, by rfl⟩ : syracuseStep 499543 = 749315) B749315
theorem B1122137 : Blo 495792 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B499563 : Blo 495792 499563 := bstep (se 1 (by rfl) ⟨374672, by rfl⟩ : syracuseStep 499563 = 749345) B749345
theorem B499575 : Blo 495792 499575 := bstep (se 1 (by rfl) ⟨374681, by rfl⟩ : syracuseStep 499575 = 749363) B749363
theorem B499595 : Blo 495792 499595 := bstep (se 1 (by rfl) ⟨374696, by rfl⟩ : syracuseStep 499595 = 749393) B749393
theorem B499607 : Blo 495792 499607 := bstep (se 1 (by rfl) ⟨374705, by rfl⟩ : syracuseStep 499607 = 749411) B749411
theorem B499627 : Blo 495792 499627 := bstep (se 1 (by rfl) ⟨374720, by rfl⟩ : syracuseStep 499627 = 749441) B749441
theorem B1122227 : Blo 495792 1122227 := bstep (se 1 (by rfl) ⟨841670, by rfl⟩ : syracuseStep 1122227 = 1683341) B1683341
theorem B499639 : Blo 495792 499639 := bstep (se 1 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 499639 = 749459) B749459
theorem B499659 : Blo 495792 499659 := bstep (se 1 (by rfl) ⟨374744, by rfl⟩ : syracuseStep 499659 = 749489) B749489
theorem B1122263 : Blo 495792 1122263 := bstep (se 1 (by rfl) ⟨841697, by rfl⟩ : syracuseStep 1122263 = 1683395) B1683395
theorem B499671 : Blo 495792 499671 := bstep (se 1 (by rfl) ⟨374753, by rfl⟩ : syracuseStep 499671 = 749507) B749507
theorem B499691 : Blo 495792 499691 := bstep (se 1 (by rfl) ⟨374768, by rfl⟩ : syracuseStep 499691 = 749537) B749537
theorem B499703 : Blo 495792 499703 := bstep (se 1 (by rfl) ⟨374777, by rfl⟩ : syracuseStep 499703 = 749555) B749555
theorem B499723 : Blo 495792 499723 := bstep (se 1 (by rfl) ⟨374792, by rfl⟩ : syracuseStep 499723 = 749585) B749585
theorem B499735 : Blo 495792 499735 := bstep (se 1 (by rfl) ⟨374801, by rfl⟩ : syracuseStep 499735 = 749603) B749603
theorem B499755 : Blo 495792 499755 := bstep (se 1 (by rfl) ⟨374816, by rfl⟩ : syracuseStep 499755 = 749633) B749633
theorem B1417267 : Blo 495792 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B499767 : Blo 495792 499767 := bstep (se 1 (by rfl) ⟨374825, by rfl⟩ : syracuseStep 499767 = 749651) B749651
theorem B499787 : Blo 495792 499787 := bstep (se 1 (by rfl) ⟨374840, by rfl⟩ : syracuseStep 499787 = 749681) B749681
theorem B1679453 : Blo 495792 1679453 := bstep (se 3 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 1679453 = 629795) B629795
theorem B1122443 : Blo 495792 1122443 := bstep (se 1 (by rfl) ⟨841832, by rfl⟩ : syracuseStep 1122443 = 1683665) B1683665
theorem B1122497 : Blo 495792 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B1417495 : Blo 495792 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B6037877 : Blo 495792 6037877 := bstep (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) B566051
theorem B1122713 : Blo 495792 1122713 := bstep (se 2 (by rfl) ⟨421017, by rfl⟩ : syracuseStep 1122713 = 842035) B842035
theorem B631243 : Blo 495792 631243 := bstep (se 1 (by rfl) ⟨473432, by rfl⟩ : syracuseStep 631243 = 946865) B946865
theorem B1122803 : Blo 495792 1122803 := bstep (se 1 (by rfl) ⟨842102, by rfl⟩ : syracuseStep 1122803 = 1684205) B1684205
theorem B1122839 : Blo 495792 1122839 := bstep (se 1 (by rfl) ⟨842129, by rfl⟩ : syracuseStep 1122839 = 1684259) B1684259
theorem B6398615 : Blo 495792 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B1123019 : Blo 495792 1123019 := bstep (se 1 (by rfl) ⟨842264, by rfl⟩ : syracuseStep 1123019 = 1684529) B1684529
theorem B1123073 : Blo 495792 1123073 := bstep (se 2 (by rfl) ⟨421152, by rfl⟩ : syracuseStep 1123073 = 842305) B842305
theorem B598871 : Blo 495792 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B1123289 : Blo 495792 1123289 := bstep (se 2 (by rfl) ⟨421233, by rfl⟩ : syracuseStep 1123289 = 842467) B842467
theorem B1123379 : Blo 495792 1123379 := bstep (se 1 (by rfl) ⟨842534, by rfl⟩ : syracuseStep 1123379 = 1685069) B1685069
theorem B1123415 : Blo 495792 1123415 := bstep (se 1 (by rfl) ⟨842561, by rfl⟩ : syracuseStep 1123415 = 1685123) B1685123
theorem B533611 : Blo 495792 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B2270339 : Blo 495792 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B894091 : Blo 495792 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B599179 : Blo 495792 599179 := bstep (se 1 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 599179 = 898769) B898769
theorem B1680587 : Blo 495792 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B4105421 : Blo 495792 4105421 := bstep (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) B1539533
theorem B1123595 : Blo 495792 1123595 := bstep (se 1 (by rfl) ⟨842696, by rfl⟩ : syracuseStep 1123595 = 1685393) B1685393
theorem B1516865 : Blo 495792 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B1123649 : Blo 495792 1123649 := bstep (se 2 (by rfl) ⟨421368, by rfl⟩ : syracuseStep 1123649 = 842737) B842737
theorem B632215 : Blo 495792 632215 := bstep (se 1 (by rfl) ⟨474161, by rfl⟩ : syracuseStep 632215 = 948323) B948323
theorem B1680857 : Blo 495792 1680857 := bstep (se 2 (by rfl) ⟨630321, by rfl⟩ : syracuseStep 1680857 = 1260643) B1260643
theorem B599563 : Blo 495792 599563 := bstep (se 1 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 599563 = 899345) B899345
theorem B1123865 : Blo 495792 1123865 := bstep (se 2 (by rfl) ⟨421449, by rfl⟩ : syracuseStep 1123865 = 842899) B842899
theorem B1123955 : Blo 495792 1123955 := bstep (se 1 (by rfl) ⟨842966, by rfl⟩ : syracuseStep 1123955 = 1685933) B1685933
theorem B1123991 : Blo 495792 1123991 := bstep (se 1 (by rfl) ⟨842993, by rfl⟩ : syracuseStep 1123991 = 1685987) B1685987
theorem B1255115 : Blo 495792 1255115 := bstep (se 1 (by rfl) ⟨941336, by rfl⟩ : syracuseStep 1255115 = 1882673) B1882673
theorem B894731 : Blo 495792 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1124171 : Blo 495792 1124171 := bstep (se 1 (by rfl) ⟨843128, by rfl⟩ : syracuseStep 1124171 = 1686257) B1686257
theorem B1124225 : Blo 495792 1124225 := bstep (se 2 (by rfl) ⟨421584, by rfl⟩ : syracuseStep 1124225 = 843169) B843169
theorem B1419353 : Blo 495792 1419353 := bstep (se 2 (by rfl) ⟨532257, by rfl⟩ : syracuseStep 1419353 = 1064515) B1064515
theorem B1124441 : Blo 495792 1124441 := bstep (se 2 (by rfl) ⟨421665, by rfl⟩ : syracuseStep 1124441 = 843331) B843331
theorem B1681559 : Blo 495792 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B1124531 : Blo 495792 1124531 := bstep (se 1 (by rfl) ⟨843398, by rfl⟩ : syracuseStep 1124531 = 1686797) B1686797
theorem B5122349 : Blo 495792 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B4041053 : Blo 495792 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B567799 : Blo 495792 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B895511 : Blo 495792 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B797207 : Blo 495792 797207 := bstep (se 1 (by rfl) ⟨597905, by rfl⟩ : syracuseStep 797207 = 1195811) B1195811
theorem B4237859 : Blo 495792 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B4532867 : Blo 495792 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B1256087 : Blo 495792 1256087 := bstep (se 1 (by rfl) ⟨942065, by rfl⟩ : syracuseStep 1256087 = 1884131) B1884131
theorem B1682099 : Blo 495792 1682099 := bstep (se 1 (by rfl) ⟨1261574, by rfl⟩ : syracuseStep 1682099 = 2523149) B2523149
theorem B961303 : Blo 495792 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B13839169 : Blo 495792 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1420183 : Blo 495792 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1682369 : Blo 495792 1682369 := bstep (se 2 (by rfl) ⟨630888, by rfl⟩ : syracuseStep 1682369 = 1261777) B1261777
theorem B1059799 : Blo 495792 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B1059841 : Blo 495792 1059841 := bstep (se 2 (by rfl) ⟨397440, by rfl⟩ : syracuseStep 1059841 = 794881) B794881
theorem B14363669 : Blo 495792 14363669 := bstep (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) B673297
theorem B4041859 : Blo 495792 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2829613 : Blo 495792 2829613 := bstep (se 3 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 2829613 = 1061105) B1061105
theorem B1256755 : Blo 495792 1256755 := bstep (se 1 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 1256755 = 1885133) B1885133
theorem B2305459 : Blo 495792 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B1191361 : Blo 495792 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B1256897 : Blo 495792 1256897 := bstep (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) B942673
theorem B1682909 : Blo 495792 1682909 := bstep (se 3 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 1682909 = 631091) B631091
theorem B1421003 : Blo 495792 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B3452633 : Blo 495792 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2010845 : Blo 495792 2010845 := bstep (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) B754067
theorem B7647605 : Blo 495792 7647605 := bstep (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) B716963
theorem B1684043 : Blo 495792 1684043 := bstep (se 1 (by rfl) ⟨1263032, by rfl⟩ : syracuseStep 1684043 = 2526065) B2526065
theorem B1061515 : Blo 495792 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1258163 : Blo 495792 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B897817 : Blo 495792 897817 := bstep (se 2 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 897817 = 673363) B673363
theorem B1684313 : Blo 495792 1684313 := bstep (se 2 (by rfl) ⟨631617, by rfl⟩ : syracuseStep 1684313 = 1263235) B1263235
theorem B2012107 : Blo 495792 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B1061849 : Blo 495792 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B3191825 : Blo 495792 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B1258699 : Blo 495792 1258699 := bstep (se 1 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 1258699 = 1888049) B1888049
theorem B898379 : Blo 495792 898379 := bstep (se 1 (by rfl) ⟨673784, by rfl⟩ : syracuseStep 898379 = 1347569) B1347569
theorem B1258841 : Blo 495792 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B636439 : Blo 495792 636439 := bstep (se 1 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 636439 = 954659) B954659
theorem B1685015 : Blo 495792 1685015 := bstep (se 1 (by rfl) ⟨1263761, by rfl⟩ : syracuseStep 1685015 = 2527523) B2527523
theorem B505687 : Blo 495792 505687 := bstep (se 1 (by rfl) ⟨379265, by rfl⟩ : syracuseStep 505687 = 758531) B758531
theorem B1685555 : Blo 495792 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B4241483 : Blo 495792 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B899201 : Blo 495792 899201 := bstep (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) B674401
theorem B1259671 : Blo 495792 1259671 := bstep (se 1 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 1259671 = 1889507) B1889507
theorem B1685825 : Blo 495792 1685825 := bstep (se 2 (by rfl) ⟨632184, by rfl⟩ : syracuseStep 1685825 = 1264369) B1264369
theorem B1816921 : Blo 495792 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B12073333 : Blo 495792 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B1063361 : Blo 495792 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B1260107 : Blo 495792 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B1686365 : Blo 495792 1686365 := bstep (se 3 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 1686365 = 632387) B632387
theorem B1260481 : Blo 495792 1260481 := bstep (se 2 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 1260481 = 945361) B945361
theorem B1883159 : Blo 495792 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B539767 : Blo 495792 539767 := bstep (se 1 (by rfl) ⟨404825, by rfl⟩ : syracuseStep 539767 = 809651) B809651
theorem B1883357 : Blo 495792 1883357 := bstep (se 3 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 1883357 = 706259) B706259
theorem B1064215 : Blo 495792 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B4308299 : Blo 495792 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2014637 : Blo 495792 2014637 := bstep (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) B755489
theorem B3816881 : Blo 495792 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1588673 : Blo 495792 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B671179 : Blo 495792 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B1261079 : Blo 495792 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B1195993 : Blo 495792 1195993 := bstep (se 2 (by rfl) ⟨448497, by rfl⟩ : syracuseStep 1195993 = 896995) B896995
theorem B1720385 : Blo 495792 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1065035 : Blo 495792 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1261889 : Blo 495792 1261889 := bstep (se 2 (by rfl) ⟨473208, by rfl⟩ : syracuseStep 1261889 = 946417) B946417
theorem B2310617 : Blo 495792 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B4244147 : Blo 495792 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B1262425 : Blo 495792 1262425 := bstep (se 2 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 1262425 = 946819) B946819
theorem B1885315 : Blo 495792 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B836939 : Blo 495792 836939 := bstep (se 1 (by rfl) ⟨627704, by rfl⟩ : syracuseStep 836939 = 1255409) B1255409
theorem B1885619 : Blo 495792 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B837067 : Blo 495792 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B837209 : Blo 495792 837209 := bstep (se 2 (by rfl) ⟨313953, by rfl⟩ : syracuseStep 837209 = 627907) B627907
theorem B6801047 : Blo 495792 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B837337 : Blo 495792 837337 := bstep (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) B628003
theorem B4245209 : Blo 495792 4245209 := bstep (se 2 (by rfl) ⟨1591953, by rfl⟩ : syracuseStep 4245209 = 3183907) B3183907
theorem B2148119 : Blo 495792 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B8472437 : Blo 495792 8472437 := bstep (se 5 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 8472437 = 794291) B794291
theorem B673687 : Blo 495792 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B6375347 : Blo 495792 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B2836403 : Blo 495792 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1263539 : Blo 495792 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1886273 : Blo 495792 1886273 := bstep (se 2 (by rfl) ⟨707352, by rfl⟩ : syracuseStep 1886273 = 1414705) B1414705
theorem B3197029 : Blo 495792 3197029 := bstep (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) B599443
theorem B1263833 : Blo 495792 1263833 := bstep (se 2 (by rfl) ⟨473937, by rfl⟩ : syracuseStep 1263833 = 947875) B947875
theorem B4770053 : Blo 495792 4770053 := bstep (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) B894385
theorem B837911 : Blo 495792 837911 := bstep (se 1 (by rfl) ⟨628433, by rfl⟩ : syracuseStep 837911 = 1256867) B1256867
theorem B10799405 : Blo 495792 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B1067393 : Blo 495792 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B838039 : Blo 495792 838039 := bstep (se 1 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 838039 = 1257059) B1257059
theorem B674201 : Blo 495792 674201 := bstep (se 2 (by rfl) ⟨252825, by rfl⟩ : syracuseStep 674201 = 505651) B505651
theorem B2148811 : Blo 495792 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B3197515 : Blo 495792 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B9554867 : Blo 495792 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B838667 : Blo 495792 838667 := bstep (se 1 (by rfl) ⟨629000, by rfl⟩ : syracuseStep 838667 = 1258001) B1258001
theorem B838795 : Blo 495792 838795 := bstep (se 1 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 838795 = 1258193) B1258193
theorem B1133747 : Blo 495792 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B838937 : Blo 495792 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B1887533 : Blo 495792 1887533 := bstep (se 3 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 1887533 = 707825) B707825
theorem B1887563 : Blo 495792 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B2837861 : Blo 495792 2837861 := bstep (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) B532099
theorem B839065 : Blo 495792 839065 := bstep (se 2 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 839065 = 629299) B629299
theorem B24202709 : Blo 495792 24202709 := bstep (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) B567251
theorem B1199809 : Blo 495792 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B3231589 : Blo 495792 3231589 := bstep (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) B605923
theorem B839639 : Blo 495792 839639 := bstep (se 1 (by rfl) ⟨629729, by rfl⟩ : syracuseStep 839639 = 1259459) B1259459
theorem B1888217 : Blo 495792 1888217 := bstep (se 2 (by rfl) ⟨708081, by rfl⟩ : syracuseStep 1888217 = 1416163) B1416163
theorem B1200203 : Blo 495792 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B839767 : Blo 495792 839767 := bstep (se 1 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 839767 = 1259651) B1259651
theorem B1134731 : Blo 495792 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B2510999 : Blo 495792 2510999 := bstep (se 1 (by rfl) ⟨1883249, by rfl⟩ : syracuseStep 2510999 = 3766499) B3766499
theorem B1888535 : Blo 495792 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B2019763 : Blo 495792 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B1364441 : Blo 495792 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B840395 : Blo 495792 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B7688945 : Blo 495792 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B840523 : Blo 495792 840523 := bstep (se 1 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 840523 = 1260785) B1260785
theorem B1889203 : Blo 495792 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B840665 : Blo 495792 840665 := bstep (se 2 (by rfl) ⟨315249, by rfl⟩ : syracuseStep 840665 = 630499) B630499
theorem B840793 : Blo 495792 840793 := bstep (se 2 (by rfl) ⟨315297, by rfl⟩ : syracuseStep 840793 = 630595) B630595
theorem B5690573 : Blo 495792 5690573 := bstep (se 3 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 5690573 = 2133965) B2133965
theorem B710041 : Blo 495792 710041 := bstep (se 2 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 710041 = 532531) B532531
theorem B841367 : Blo 495792 841367 := bstep (se 1 (by rfl) ⟨631025, by rfl⟩ : syracuseStep 841367 = 1262051) B1262051
theorem B841495 : Blo 495792 841495 := bstep (se 1 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 841495 = 1262243) B1262243
theorem B34363237 : Blo 495792 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B1792145 : Blo 495792 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1890449 : Blo 495792 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B743705 : Blo 495792 743705 := bstep (se 2 (by rfl) ⟨278889, by rfl⟩ : syracuseStep 743705 = 557779) B557779
theorem B743819 : Blo 495792 743819 := bstep (se 1 (by rfl) ⟨557864, by rfl⟩ : syracuseStep 743819 = 1115729) B1115729
theorem B842123 : Blo 495792 842123 := bstep (se 1 (by rfl) ⟨631592, by rfl⟩ : syracuseStep 842123 = 1263185) B1263185
theorem B743831 : Blo 495792 743831 := bstep (se 1 (by rfl) ⟨557873, by rfl⟩ : syracuseStep 743831 = 1115747) B1115747
theorem B743897 : Blo 495792 743897 := bstep (se 2 (by rfl) ⟨278961, by rfl⟩ : syracuseStep 743897 = 557923) B557923
theorem B2120195 : Blo 495792 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B842251 : Blo 495792 842251 := bstep (se 1 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 842251 = 1263377) B1263377
theorem B744011 : Blo 495792 744011 := bstep (se 1 (by rfl) ⟨558008, by rfl⟩ : syracuseStep 744011 = 1116017) B1116017
theorem B744023 : Blo 495792 744023 := bstep (se 1 (by rfl) ⟨558017, by rfl⟩ : syracuseStep 744023 = 1116035) B1116035
theorem B744089 : Blo 495792 744089 := bstep (se 2 (by rfl) ⟨279033, by rfl⟩ : syracuseStep 744089 = 558067) B558067
theorem B842393 : Blo 495792 842393 := bstep (se 2 (by rfl) ⟨315897, by rfl⟩ : syracuseStep 842393 = 631795) B631795
theorem B744203 : Blo 495792 744203 := bstep (se 1 (by rfl) ⟨558152, by rfl⟩ : syracuseStep 744203 = 1116305) B1116305
theorem B744215 : Blo 495792 744215 := bstep (se 1 (by rfl) ⟨558161, by rfl⟩ : syracuseStep 744215 = 1116323) B1116323
theorem B842521 : Blo 495792 842521 := bstep (se 2 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 842521 = 631891) B631891
theorem B1891147 : Blo 495792 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B711499 : Blo 495792 711499 := bstep (se 1 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 711499 = 1067249) B1067249
theorem B744281 : Blo 495792 744281 := bstep (se 2 (by rfl) ⟨279105, by rfl⟩ : syracuseStep 744281 = 558211) B558211
theorem B744395 : Blo 495792 744395 := bstep (se 1 (by rfl) ⟨558296, by rfl⟩ : syracuseStep 744395 = 1116593) B1116593
theorem B744407 : Blo 495792 744407 := bstep (se 1 (by rfl) ⟨558305, by rfl⟩ : syracuseStep 744407 = 1116611) B1116611
theorem B744473 : Blo 495792 744473 := bstep (se 2 (by rfl) ⟨279177, by rfl⟩ : syracuseStep 744473 = 558355) B558355
theorem B1891421 : Blo 495792 1891421 := bstep (se 3 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 1891421 = 709283) B709283
theorem B744587 : Blo 495792 744587 := bstep (se 1 (by rfl) ⟨558440, by rfl⟩ : syracuseStep 744587 = 1116881) B1116881
theorem B744599 : Blo 495792 744599 := bstep (se 1 (by rfl) ⟨558449, by rfl⟩ : syracuseStep 744599 = 1116899) B1116899
theorem B20405429 : Blo 495792 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B744665 : Blo 495792 744665 := bstep (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) B558499
theorem B2022617 : Blo 495792 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B744779 : Blo 495792 744779 := bstep (se 1 (by rfl) ⟨558584, by rfl⟩ : syracuseStep 744779 = 1117169) B1117169
theorem B744791 : Blo 495792 744791 := bstep (se 1 (by rfl) ⟨558593, by rfl⟩ : syracuseStep 744791 = 1117187) B1117187
theorem B843095 : Blo 495792 843095 := bstep (se 1 (by rfl) ⟨632321, by rfl⟩ : syracuseStep 843095 = 1264643) B1264643
theorem B4250981 : Blo 495792 4250981 := bstep (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) B797059
theorem B744857 : Blo 495792 744857 := bstep (se 2 (by rfl) ⟨279321, by rfl⟩ : syracuseStep 744857 = 558643) B558643
theorem B843223 : Blo 495792 843223 := bstep (se 1 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 843223 = 1264835) B1264835
theorem B1793501 : Blo 495792 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B744971 : Blo 495792 744971 := bstep (se 1 (by rfl) ⟨558728, by rfl⟩ : syracuseStep 744971 = 1117457) B1117457
theorem B744983 : Blo 495792 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B745049 : Blo 495792 745049 := bstep (se 2 (by rfl) ⟨279393, by rfl⟩ : syracuseStep 745049 = 558787) B558787
theorem B2514563 : Blo 495792 2514563 := bstep (se 1 (by rfl) ⟨1885922, by rfl⟩ : syracuseStep 2514563 = 3771845) B3771845
theorem B745163 : Blo 495792 745163 := bstep (se 1 (by rfl) ⟨558872, by rfl⟩ : syracuseStep 745163 = 1117745) B1117745
theorem B745175 : Blo 495792 745175 := bstep (se 1 (by rfl) ⟨558881, by rfl⟩ : syracuseStep 745175 = 1117763) B1117763
theorem B1892119 : Blo 495792 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B745241 : Blo 495792 745241 := bstep (se 2 (by rfl) ⟨279465, by rfl⟩ : syracuseStep 745241 = 558931) B558931
theorem B3628901 : Blo 495792 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B745355 : Blo 495792 745355 := bstep (se 1 (by rfl) ⟨559016, by rfl⟩ : syracuseStep 745355 = 1118033) B1118033
theorem B745367 : Blo 495792 745367 := bstep (se 1 (by rfl) ⟨559025, by rfl⟩ : syracuseStep 745367 = 1118051) B1118051
theorem B745433 : Blo 495792 745433 := bstep (se 2 (by rfl) ⟨279537, by rfl⟩ : syracuseStep 745433 = 559075) B559075
theorem B745547 : Blo 495792 745547 := bstep (se 1 (by rfl) ⟨559160, by rfl⟩ : syracuseStep 745547 = 1118321) B1118321
theorem B745559 : Blo 495792 745559 := bstep (se 1 (by rfl) ⟨559169, by rfl⟩ : syracuseStep 745559 = 1118339) B1118339
theorem B745625 : Blo 495792 745625 := bstep (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) B559219
theorem B1794221 : Blo 495792 1794221 := bstep (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) B672833
theorem B942347 : Blo 495792 942347 := bstep (se 1 (by rfl) ⟨706760, by rfl⟩ : syracuseStep 942347 = 1413521) B1413521
theorem B745739 : Blo 495792 745739 := bstep (se 1 (by rfl) ⟨559304, by rfl⟩ : syracuseStep 745739 = 1118609) B1118609
theorem B745751 : Blo 495792 745751 := bstep (se 1 (by rfl) ⟨559313, by rfl⟩ : syracuseStep 745751 = 1118627) B1118627
theorem B745817 : Blo 495792 745817 := bstep (se 2 (by rfl) ⟨279681, by rfl⟩ : syracuseStep 745817 = 559363) B559363
theorem B2187665 : Blo 495792 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B942529 : Blo 495792 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B745931 : Blo 495792 745931 := bstep (se 1 (by rfl) ⟨559448, by rfl⟩ : syracuseStep 745931 = 1118897) B1118897
theorem B745943 : Blo 495792 745943 := bstep (se 1 (by rfl) ⟨559457, by rfl⟩ : syracuseStep 745943 = 1118915) B1118915
theorem B746009 : Blo 495792 746009 := bstep (se 2 (by rfl) ⟨279753, by rfl⟩ : syracuseStep 746009 = 559507) B559507
theorem B1892909 : Blo 495792 1892909 := bstep (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) B709841
theorem B746123 : Blo 495792 746123 := bstep (se 1 (by rfl) ⟨559592, by rfl⟩ : syracuseStep 746123 = 1119185) B1119185
theorem B746135 : Blo 495792 746135 := bstep (se 1 (by rfl) ⟨559601, by rfl⟩ : syracuseStep 746135 = 1119203) B1119203
theorem B746201 : Blo 495792 746201 := bstep (se 2 (by rfl) ⟨279825, by rfl⟩ : syracuseStep 746201 = 559651) B559651
theorem B746315 : Blo 495792 746315 := bstep (se 1 (by rfl) ⟨559736, by rfl⟩ : syracuseStep 746315 = 1119473) B1119473
theorem B746327 : Blo 495792 746327 := bstep (se 1 (by rfl) ⟨559745, by rfl⟩ : syracuseStep 746327 = 1119491) B1119491
theorem B942977 : Blo 495792 942977 := bstep (se 2 (by rfl) ⟨353616, by rfl⟩ : syracuseStep 942977 = 707233) B707233
theorem B746393 : Blo 495792 746393 := bstep (se 2 (by rfl) ⟨279897, by rfl⟩ : syracuseStep 746393 = 559795) B559795
theorem B4252621 : Blo 495792 4252621 := bstep (se 3 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 4252621 = 1594733) B1594733
theorem B746507 : Blo 495792 746507 := bstep (se 1 (by rfl) ⟨559880, by rfl⟩ : syracuseStep 746507 = 1119761) B1119761
theorem B746519 : Blo 495792 746519 := bstep (se 1 (by rfl) ⟨559889, by rfl⟩ : syracuseStep 746519 = 1119779) B1119779
theorem B2843693 : Blo 495792 2843693 := bstep (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) B1066385
theorem B746585 : Blo 495792 746585 := bstep (se 2 (by rfl) ⟨279969, by rfl⟩ : syracuseStep 746585 = 559939) B559939
theorem B746699 : Blo 495792 746699 := bstep (se 1 (by rfl) ⟨560024, by rfl⟩ : syracuseStep 746699 = 1120049) B1120049
theorem B943319 : Blo 495792 943319 := bstep (se 1 (by rfl) ⟨707489, by rfl⟩ : syracuseStep 943319 = 1414979) B1414979
theorem B746711 : Blo 495792 746711 := bstep (se 1 (by rfl) ⟨560033, by rfl⟩ : syracuseStep 746711 = 1120067) B1120067
theorem B746777 : Blo 495792 746777 := bstep (se 2 (by rfl) ⟨280041, by rfl⟩ : syracuseStep 746777 = 560083) B560083
theorem B7169381 : Blo 495792 7169381 := bstep (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) B1344259
theorem B746891 : Blo 495792 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B746903 : Blo 495792 746903 := bstep (se 1 (by rfl) ⟨560177, by rfl⟩ : syracuseStep 746903 = 1120355) B1120355
theorem B746969 : Blo 495792 746969 := bstep (se 2 (by rfl) ⟨280113, by rfl⟩ : syracuseStep 746969 = 560227) B560227
theorem B747083 : Blo 495792 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B747095 : Blo 495792 747095 := bstep (se 1 (by rfl) ⟨560321, by rfl⟩ : syracuseStep 747095 = 1120643) B1120643
theorem B779915 : Blo 495792 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B747161 : Blo 495792 747161 := bstep (se 2 (by rfl) ⟨280185, by rfl⟩ : syracuseStep 747161 = 560371) B560371
theorem B1599193 : Blo 495792 1599193 := bstep (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) B1199395
theorem B747275 : Blo 495792 747275 := bstep (se 1 (by rfl) ⟨560456, by rfl⟩ : syracuseStep 747275 = 1120913) B1120913
theorem B747287 : Blo 495792 747287 := bstep (se 1 (by rfl) ⟨560465, by rfl⟩ : syracuseStep 747287 = 1120931) B1120931
theorem B747353 : Blo 495792 747353 := bstep (se 2 (by rfl) ⟨280257, by rfl⟩ : syracuseStep 747353 = 560515) B560515
theorem B943987 : Blo 495792 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B1894337 : Blo 495792 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B747467 : Blo 495792 747467 := bstep (se 1 (by rfl) ⟨560600, by rfl⟩ : syracuseStep 747467 = 1121201) B1121201
theorem B747479 : Blo 495792 747479 := bstep (se 1 (by rfl) ⟨560609, by rfl⟩ : syracuseStep 747479 = 1121219) B1121219
theorem B747545 : Blo 495792 747545 := bstep (se 2 (by rfl) ⟨280329, by rfl⟩ : syracuseStep 747545 = 560659) B560659
theorem B747659 : Blo 495792 747659 := bstep (se 1 (by rfl) ⟨560744, by rfl⟩ : syracuseStep 747659 = 1121489) B1121489
theorem B5662871 : Blo 495792 5662871 := bstep (se 1 (by rfl) ⟨4247153, by rfl⟩ : syracuseStep 5662871 = 8494307) B8494307
theorem B747671 : Blo 495792 747671 := bstep (se 1 (by rfl) ⟨560753, by rfl⟩ : syracuseStep 747671 = 1121507) B1121507
theorem B747737 : Blo 495792 747737 := bstep (se 2 (by rfl) ⟨280401, by rfl⟩ : syracuseStep 747737 = 560803) B560803
theorem B4253957 : Blo 495792 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B944435 : Blo 495792 944435 := bstep (se 1 (by rfl) ⟨708326, by rfl⟩ : syracuseStep 944435 = 1416653) B1416653
theorem B747851 : Blo 495792 747851 := bstep (se 1 (by rfl) ⟨560888, by rfl⟩ : syracuseStep 747851 = 1121777) B1121777
theorem B747863 : Blo 495792 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B944473 : Blo 495792 944473 := bstep (se 2 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 944473 = 708355) B708355
theorem B747929 : Blo 495792 747929 := bstep (se 2 (by rfl) ⟨280473, by rfl⟩ : syracuseStep 747929 = 560947) B560947
theorem B6056369 : Blo 495792 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B1698251 : Blo 495792 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B748043 : Blo 495792 748043 := bstep (se 1 (by rfl) ⟨561032, by rfl⟩ : syracuseStep 748043 = 1122065) B1122065
theorem B4778513 : Blo 495792 4778513 := bstep (se 2 (by rfl) ⟨1791942, by rfl⟩ : syracuseStep 4778513 = 3583885) B3583885
theorem B748055 : Blo 495792 748055 := bstep (se 1 (by rfl) ⟨561041, by rfl⟩ : syracuseStep 748055 = 1122083) B1122083
theorem B748121 : Blo 495792 748121 := bstep (se 2 (by rfl) ⟨280545, by rfl⟩ : syracuseStep 748121 = 561091) B561091
theorem B2124467 : Blo 495792 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B1010369 : Blo 495792 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B748235 : Blo 495792 748235 := bstep (se 1 (by rfl) ⟨561176, by rfl⟩ : syracuseStep 748235 = 1122353) B1122353
theorem B748247 : Blo 495792 748247 := bstep (se 1 (by rfl) ⟨561185, by rfl⟩ : syracuseStep 748247 = 1122371) B1122371
theorem B944921 : Blo 495792 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B748313 : Blo 495792 748313 := bstep (se 2 (by rfl) ⟨280617, by rfl⟩ : syracuseStep 748313 = 561235) B561235
theorem B4025123 : Blo 495792 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B748427 : Blo 495792 748427 := bstep (se 1 (by rfl) ⟨561320, by rfl⟩ : syracuseStep 748427 = 1122641) B1122641
theorem B748439 : Blo 495792 748439 := bstep (se 1 (by rfl) ⟨561329, by rfl⟩ : syracuseStep 748439 = 1122659) B1122659
theorem B748505 : Blo 495792 748505 := bstep (se 2 (by rfl) ⟨280689, by rfl⟩ : syracuseStep 748505 = 561379) B561379
theorem B2387009 : Blo 495792 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B1600577 : Blo 495792 1600577 := bstep (se 2 (by rfl) ⟨600216, by rfl⟩ : syracuseStep 1600577 = 1200433) B1200433
theorem B748619 : Blo 495792 748619 := bstep (se 1 (by rfl) ⟨561464, by rfl⟩ : syracuseStep 748619 = 1122929) B1122929
theorem B748631 : Blo 495792 748631 := bstep (se 1 (by rfl) ⟨561473, by rfl⟩ : syracuseStep 748631 = 1122947) B1122947
theorem B3599453 : Blo 495792 3599453 := bstep (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) B1349795
theorem B748697 : Blo 495792 748697 := bstep (se 2 (by rfl) ⟨280761, by rfl⟩ : syracuseStep 748697 = 561523) B561523
theorem B748811 : Blo 495792 748811 := bstep (se 1 (by rfl) ⟨561608, by rfl⟩ : syracuseStep 748811 = 1123217) B1123217
theorem B2518289 : Blo 495792 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B748823 : Blo 495792 748823 := bstep (se 1 (by rfl) ⟨561617, by rfl⟩ : syracuseStep 748823 = 1123235) B1123235
theorem B748889 : Blo 495792 748889 := bstep (se 2 (by rfl) ⟨280833, by rfl⟩ : syracuseStep 748889 = 561667) B561667
theorem B1895825 : Blo 495792 1895825 := bstep (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) B1421869
theorem B2518451 : Blo 495792 2518451 := bstep (se 1 (by rfl) ⟨1888838, by rfl⟩ : syracuseStep 2518451 = 3777677) B3777677
theorem B749003 : Blo 495792 749003 := bstep (se 1 (by rfl) ⟨561752, by rfl⟩ : syracuseStep 749003 = 1123505) B1123505
theorem B749015 : Blo 495792 749015 := bstep (se 1 (by rfl) ⟨561761, by rfl⟩ : syracuseStep 749015 = 1123523) B1123523
theorem B19131875 : Blo 495792 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B945665 : Blo 495792 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B749081 : Blo 495792 749081 := bstep (se 2 (by rfl) ⟨280905, by rfl⟩ : syracuseStep 749081 = 561811) B561811
theorem B1601117 : Blo 495792 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B749195 : Blo 495792 749195 := bstep (se 1 (by rfl) ⟨561896, by rfl⟩ : syracuseStep 749195 = 1123793) B1123793
theorem B1273495 : Blo 495792 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2420375 : Blo 495792 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B749207 : Blo 495792 749207 := bstep (se 1 (by rfl) ⟨561905, by rfl⟩ : syracuseStep 749207 = 1123811) B1123811
theorem B749273 : Blo 495792 749273 := bstep (se 2 (by rfl) ⟨280977, by rfl⟩ : syracuseStep 749273 = 561955) B561955
theorem B6811397 : Blo 495792 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B945931 : Blo 495792 945931 := bstep (se 1 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 945931 = 1418897) B1418897
theorem B749387 : Blo 495792 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B749399 : Blo 495792 749399 := bstep (se 1 (by rfl) ⟨562049, by rfl⟩ : syracuseStep 749399 = 1124099) B1124099
theorem B1896281 : Blo 495792 1896281 := bstep (se 2 (by rfl) ⟨711105, by rfl⟩ : syracuseStep 1896281 = 1422211) B1422211
theorem B749465 : Blo 495792 749465 := bstep (se 2 (by rfl) ⟨281049, by rfl⟩ : syracuseStep 749465 = 562099) B562099
theorem B749579 : Blo 495792 749579 := bstep (se 1 (by rfl) ⟨562184, by rfl⟩ : syracuseStep 749579 = 1124369) B1124369
theorem B749591 : Blo 495792 749591 := bstep (se 1 (by rfl) ⟨562193, by rfl⟩ : syracuseStep 749591 = 1124387) B1124387
theorem B1896493 : Blo 495792 1896493 := bstep (se 3 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 1896493 = 711185) B711185
theorem B749657 : Blo 495792 749657 := bstep (se 2 (by rfl) ⟨281121, by rfl⟩ : syracuseStep 749657 = 562243) B562243
theorem B946379 : Blo 495792 946379 := bstep (se 1 (by rfl) ⟨709784, by rfl⟩ : syracuseStep 946379 = 1419569) B1419569
theorem B1077491 : Blo 495792 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B1896797 : Blo 495792 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B946561 : Blo 495792 946561 := bstep (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) B709921
theorem B946903 : Blo 495792 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B5403509 : Blo 495792 5403509 := bstep (se 5 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 5403509 = 506579) B506579
theorem B947123 : Blo 495792 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B1438685 : Blo 495792 1438685 := bstep (se 3 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 1438685 = 539507) B539507
theorem B4060205 : Blo 495792 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B9172099 : Blo 495792 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B2946179 : Blo 495792 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B947351 : Blo 495792 947351 := bstep (se 1 (by rfl) ⟨710513, by rfl⟩ : syracuseStep 947351 = 1421027) B1421027
theorem B6354125 : Blo 495792 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B2520395 : Blo 495792 2520395 := bstep (se 1 (by rfl) ⟨1890296, by rfl⟩ : syracuseStep 2520395 = 3780593) B3780593
theorem B947609 : Blo 495792 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B1275671 : Blo 495792 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B948019 : Blo 495792 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B1341515 : Blo 495792 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B2685059 : Blo 495792 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1276183 : Blo 495792 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B948505 : Blo 495792 948505 := bstep (se 2 (by rfl) ⟨355689, by rfl⟩ : syracuseStep 948505 = 711379) B711379
theorem B8092021 : Blo 495792 8092021 := bstep (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) B758627
theorem B16153181 : Blo 495792 16153181 := bstep (se 3 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 16153181 = 6057443) B6057443
theorem B2685797 : Blo 495792 2685797 := bstep (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) B503587
theorem B2128771 : Blo 495792 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B1801111 : Blo 495792 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B2522177 : Blo 495792 2522177 := bstep (se 2 (by rfl) ⟨945816, by rfl⟩ : syracuseStep 2522177 = 1891633) B1891633
theorem B1343051 : Blo 495792 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B1146923 : Blo 495792 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B3015539 : Blo 495792 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B557959 : Blo 495792 557959 := bstep (se 1 (by rfl) ⟨418469, by rfl⟩ : syracuseStep 557959 = 836939) B836939
theorem B558139 : Blo 495792 558139 := bstep (se 1 (by rfl) ⟨418604, by rfl⟩ : syracuseStep 558139 = 837209) B837209
theorem B1705079 : Blo 495792 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B6161645 : Blo 495792 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B5670161 : Blo 495792 5670161 := bstep (se 2 (by rfl) ⟨2126310, by rfl⟩ : syracuseStep 5670161 = 4252621) B4252621
theorem B3180035 : Blo 495792 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B558607 : Blo 495792 558607 := bstep (se 1 (by rfl) ⟨418955, by rfl⟩ : syracuseStep 558607 = 837911) B837911
theorem B1115783 : Blo 495792 1115783 := bstep (se 1 (by rfl) ⟨836837, by rfl⟩ : syracuseStep 1115783 = 1673675) B1673675
theorem B1115963 : Blo 495792 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B853895 : Blo 495792 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B1116089 : Blo 495792 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B559111 : Blo 495792 559111 := bstep (se 1 (by rfl) ⟨419333, by rfl⟩ : syracuseStep 559111 = 838667) B838667
theorem B755831 : Blo 495792 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B559291 : Blo 495792 559291 := bstep (se 1 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 559291 = 838937) B838937
theorem B1116431 : Blo 495792 1116431 := bstep (se 1 (by rfl) ⟨837323, by rfl⟩ : syracuseStep 1116431 = 1674647) B1674647
theorem B1116449 : Blo 495792 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B2132257 : Blo 495792 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B1509691 : Blo 495792 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B1116791 : Blo 495792 1116791 := bstep (se 1 (by rfl) ⟨837593, by rfl⟩ : syracuseStep 1116791 = 1675187) B1675187
theorem B559759 : Blo 495792 559759 := bstep (se 1 (by rfl) ⟨419819, by rfl⟩ : syracuseStep 559759 = 839639) B839639
theorem B5376689 : Blo 495792 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B756487 : Blo 495792 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B1673999 : Blo 495792 1673999 := bstep (se 1 (by rfl) ⟨1255499, by rfl⟩ : syracuseStep 1673999 = 2510999) B2510999
theorem B1116971 : Blo 495792 1116971 := bstep (se 1 (by rfl) ⟨837728, by rfl⟩ : syracuseStep 1116971 = 1675457) B1675457
theorem B4262705 : Blo 495792 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B1674269 : Blo 495792 1674269 := bstep (se 3 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 1674269 = 627851) B627851
theorem B560263 : Blo 495792 560263 := bstep (se 1 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 560263 = 840395) B840395
theorem B1117331 : Blo 495792 1117331 := bstep (se 1 (by rfl) ⟨837998, by rfl⟩ : syracuseStep 1117331 = 1675997) B1675997
theorem B1117385 : Blo 495792 1117385 := bstep (se 2 (by rfl) ⟨419019, by rfl⟩ : syracuseStep 1117385 = 838039) B838039
theorem B560443 : Blo 495792 560443 := bstep (se 1 (by rfl) ⟨420332, by rfl⟩ : syracuseStep 560443 = 840665) B840665
theorem B4263353 : Blo 495792 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B1281737 : Blo 495792 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B18452225 : Blo 495792 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B560911 : Blo 495792 560911 := bstep (se 1 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 560911 = 841367) B841367
theorem B1412893 : Blo 495792 1412893 := bstep (se 3 (by rfl) ⟨264917, by rfl⟩ : syracuseStep 1412893 = 529835) B529835
theorem B1118087 : Blo 495792 1118087 := bstep (se 1 (by rfl) ⟨838565, by rfl⟩ : syracuseStep 1118087 = 1677131) B1677131
theorem B1413065 : Blo 495792 1413065 := bstep (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) B1059799
theorem B1413121 : Blo 495792 1413121 := bstep (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) B1059841
theorem B1118267 : Blo 495792 1118267 := bstep (se 1 (by rfl) ⟨838700, by rfl⟩ : syracuseStep 1118267 = 1677401) B1677401
theorem B5673077 : Blo 495792 5673077 := bstep (se 5 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 5673077 = 531851) B531851
theorem B1118393 : Blo 495792 1118393 := bstep (se 2 (by rfl) ⟨419397, by rfl⟩ : syracuseStep 1118393 = 838795) B838795
theorem B495803 : Blo 495792 495803 := bstep (se 1 (by rfl) ⟨371852, by rfl⟩ : syracuseStep 495803 = 743705) B743705
theorem B495879 : Blo 495792 495879 := bstep (se 1 (by rfl) ⟨371909, by rfl⟩ : syracuseStep 495879 = 743819) B743819
theorem B561415 : Blo 495792 561415 := bstep (se 1 (by rfl) ⟨421061, by rfl⟩ : syracuseStep 561415 = 842123) B842123
theorem B495887 : Blo 495792 495887 := bstep (se 1 (by rfl) ⟨371915, by rfl⟩ : syracuseStep 495887 = 743831) B743831
theorem B495931 : Blo 495792 495931 := bstep (se 1 (by rfl) ⟨371948, by rfl⟩ : syracuseStep 495931 = 743897) B743897
theorem B1413463 : Blo 495792 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B496007 : Blo 495792 496007 := bstep (se 1 (by rfl) ⟨372005, by rfl⟩ : syracuseStep 496007 = 744011) B744011
theorem B496015 : Blo 495792 496015 := bstep (se 1 (by rfl) ⟨372011, by rfl⟩ : syracuseStep 496015 = 744023) B744023
theorem B3772817 : Blo 495792 3772817 := bstep (se 2 (by rfl) ⟨1414806, by rfl⟩ : syracuseStep 3772817 = 2829613) B2829613
theorem B1675673 : Blo 495792 1675673 := bstep (se 2 (by rfl) ⟨628377, by rfl⟩ : syracuseStep 1675673 = 1256755) B1256755
theorem B496059 : Blo 495792 496059 := bstep (se 1 (by rfl) ⟨372044, by rfl⟩ : syracuseStep 496059 = 744089) B744089
theorem B561595 : Blo 495792 561595 := bstep (se 1 (by rfl) ⟨421196, by rfl⟩ : syracuseStep 561595 = 842393) B842393
theorem B496135 : Blo 495792 496135 := bstep (se 1 (by rfl) ⟨372101, by rfl⟩ : syracuseStep 496135 = 744203) B744203
theorem B496143 : Blo 495792 496143 := bstep (se 1 (by rfl) ⟨372107, by rfl⟩ : syracuseStep 496143 = 744215) B744215
theorem B1118735 : Blo 495792 1118735 := bstep (se 1 (by rfl) ⟨839051, by rfl⟩ : syracuseStep 1118735 = 1678103) B1678103
theorem B1118753 : Blo 495792 1118753 := bstep (se 2 (by rfl) ⟨419532, by rfl⟩ : syracuseStep 1118753 = 839065) B839065
theorem B496187 : Blo 495792 496187 := bstep (se 1 (by rfl) ⟨372140, by rfl⟩ : syracuseStep 496187 = 744281) B744281
theorem B496263 : Blo 495792 496263 := bstep (se 1 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 496263 = 744395) B744395
theorem B496271 : Blo 495792 496271 := bstep (se 1 (by rfl) ⟨372203, by rfl⟩ : syracuseStep 496271 = 744407) B744407
theorem B496315 : Blo 495792 496315 := bstep (se 1 (by rfl) ⟨372236, by rfl⟩ : syracuseStep 496315 = 744473) B744473
theorem B496391 : Blo 495792 496391 := bstep (se 1 (by rfl) ⟨372293, by rfl⟩ : syracuseStep 496391 = 744587) B744587
theorem B496399 : Blo 495792 496399 := bstep (se 1 (by rfl) ⟨372299, by rfl⟩ : syracuseStep 496399 = 744599) B744599
theorem B13603619 : Blo 495792 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B496443 : Blo 495792 496443 := bstep (se 1 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 496443 = 744665) B744665
theorem B1348411 : Blo 495792 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B1119095 : Blo 495792 1119095 := bstep (se 1 (by rfl) ⟨839321, by rfl⟩ : syracuseStep 1119095 = 1678643) B1678643
theorem B496519 : Blo 495792 496519 := bstep (se 1 (by rfl) ⟨372389, by rfl⟩ : syracuseStep 496519 = 744779) B744779
theorem B496527 : Blo 495792 496527 := bstep (se 1 (by rfl) ⟨372395, by rfl⟩ : syracuseStep 496527 = 744791) B744791
theorem B562063 : Blo 495792 562063 := bstep (se 1 (by rfl) ⟨421547, by rfl⟩ : syracuseStep 562063 = 843095) B843095
theorem B14554037 : Blo 495792 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B11539381 : Blo 495792 11539381 := bstep (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) B1081817
theorem B496571 : Blo 495792 496571 := bstep (se 1 (by rfl) ⟨372428, by rfl⟩ : syracuseStep 496571 = 744857) B744857
theorem B496647 : Blo 495792 496647 := bstep (se 1 (by rfl) ⟨372485, by rfl⟩ : syracuseStep 496647 = 744971) B744971
theorem B496655 : Blo 495792 496655 := bstep (se 1 (by rfl) ⟨372491, by rfl⟩ : syracuseStep 496655 = 744983) B744983
theorem B1119275 : Blo 495792 1119275 := bstep (se 1 (by rfl) ⟨839456, by rfl⟩ : syracuseStep 1119275 = 1678913) B1678913
theorem B496699 : Blo 495792 496699 := bstep (se 1 (by rfl) ⟨372524, by rfl⟩ : syracuseStep 496699 = 745049) B745049
theorem B1676375 : Blo 495792 1676375 := bstep (se 1 (by rfl) ⟨1257281, by rfl⟩ : syracuseStep 1676375 = 2514563) B2514563
theorem B496775 : Blo 495792 496775 := bstep (se 1 (by rfl) ⟨372581, by rfl⟩ : syracuseStep 496775 = 745163) B745163
theorem B1512583 : Blo 495792 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B496783 : Blo 495792 496783 := bstep (se 1 (by rfl) ⟨372587, by rfl⟩ : syracuseStep 496783 = 745175) B745175
theorem B496827 : Blo 495792 496827 := bstep (se 1 (by rfl) ⟨372620, by rfl⟩ : syracuseStep 496827 = 745241) B745241
theorem B496903 : Blo 495792 496903 := bstep (se 1 (by rfl) ⟨372677, by rfl⟩ : syracuseStep 496903 = 745355) B745355
theorem B496911 : Blo 495792 496911 := bstep (se 1 (by rfl) ⟨372683, by rfl⟩ : syracuseStep 496911 = 745367) B745367
theorem B496955 : Blo 495792 496955 := bstep (se 1 (by rfl) ⟨372716, by rfl⟩ : syracuseStep 496955 = 745433) B745433
theorem B497031 : Blo 495792 497031 := bstep (se 1 (by rfl) ⟨372773, by rfl⟩ : syracuseStep 497031 = 745547) B745547
theorem B497039 : Blo 495792 497039 := bstep (se 1 (by rfl) ⟨372779, by rfl⟩ : syracuseStep 497039 = 745559) B745559
theorem B2528657 : Blo 495792 2528657 := bstep (se 2 (by rfl) ⟨948246, by rfl⟩ : syracuseStep 2528657 = 1896493) B1896493
theorem B1119635 : Blo 495792 1119635 := bstep (se 1 (by rfl) ⟨839726, by rfl⟩ : syracuseStep 1119635 = 1679453) B1679453
theorem B497083 : Blo 495792 497083 := bstep (se 1 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 497083 = 745625) B745625
theorem B1119689 : Blo 495792 1119689 := bstep (se 2 (by rfl) ⟨419883, by rfl⟩ : syracuseStep 1119689 = 839767) B839767
theorem B628231 : Blo 495792 628231 := bstep (se 1 (by rfl) ⟨471173, by rfl⟩ : syracuseStep 628231 = 942347) B942347
theorem B497159 : Blo 495792 497159 := bstep (se 1 (by rfl) ⟨372869, by rfl⟩ : syracuseStep 497159 = 745739) B745739
theorem B497167 : Blo 495792 497167 := bstep (se 1 (by rfl) ⟨372875, by rfl⟩ : syracuseStep 497167 = 745751) B745751
theorem B497211 : Blo 495792 497211 := bstep (se 1 (by rfl) ⟨372908, by rfl⟩ : syracuseStep 497211 = 745817) B745817
theorem B1676861 : Blo 495792 1676861 := bstep (se 3 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 1676861 = 628823) B628823
theorem B497287 : Blo 495792 497287 := bstep (se 1 (by rfl) ⟨372965, by rfl⟩ : syracuseStep 497287 = 745931) B745931
theorem B497295 : Blo 495792 497295 := bstep (se 1 (by rfl) ⟨372971, by rfl⟩ : syracuseStep 497295 = 745943) B745943
theorem B2397869 : Blo 495792 2397869 := bstep (se 3 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 2397869 = 899201) B899201
theorem B497339 : Blo 495792 497339 := bstep (se 1 (by rfl) ⟨373004, by rfl⟩ : syracuseStep 497339 = 746009) B746009
theorem B497415 : Blo 495792 497415 := bstep (se 1 (by rfl) ⟨373061, by rfl⟩ : syracuseStep 497415 = 746123) B746123
theorem B497423 : Blo 495792 497423 := bstep (se 1 (by rfl) ⟨373067, by rfl⟩ : syracuseStep 497423 = 746135) B746135
theorem B4265743 : Blo 495792 4265743 := bstep (se 1 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 4265743 = 6398615) B6398615
theorem B497467 : Blo 495792 497467 := bstep (se 1 (by rfl) ⟨373100, by rfl⟩ : syracuseStep 497467 = 746201) B746201
theorem B497543 : Blo 495792 497543 := bstep (se 1 (by rfl) ⟨373157, by rfl⟩ : syracuseStep 497543 = 746315) B746315
theorem B497551 : Blo 495792 497551 := bstep (se 1 (by rfl) ⟨373163, by rfl⟩ : syracuseStep 497551 = 746327) B746327
theorem B2693017 : Blo 495792 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B628651 : Blo 495792 628651 := bstep (se 1 (by rfl) ⟨471488, by rfl⟩ : syracuseStep 628651 = 942977) B942977
theorem B497595 : Blo 495792 497595 := bstep (se 1 (by rfl) ⟨373196, by rfl⟩ : syracuseStep 497595 = 746393) B746393
theorem B497671 : Blo 495792 497671 := bstep (se 1 (by rfl) ⟨373253, by rfl⟩ : syracuseStep 497671 = 746507) B746507
theorem B497679 : Blo 495792 497679 := bstep (se 1 (by rfl) ⟨373259, by rfl⟩ : syracuseStep 497679 = 746519) B746519
theorem B497723 : Blo 495792 497723 := bstep (se 1 (by rfl) ⟨373292, by rfl⟩ : syracuseStep 497723 = 746585) B746585
theorem B1513559 : Blo 495792 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B497799 : Blo 495792 497799 := bstep (se 1 (by rfl) ⟨373349, by rfl⟩ : syracuseStep 497799 = 746699) B746699
theorem B1120391 : Blo 495792 1120391 := bstep (se 1 (by rfl) ⟨840293, by rfl⟩ : syracuseStep 1120391 = 1680587) B1680587
theorem B628879 : Blo 495792 628879 := bstep (se 1 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 628879 = 943319) B943319
theorem B497807 : Blo 495792 497807 := bstep (se 1 (by rfl) ⟨373355, by rfl⟩ : syracuseStep 497807 = 746711) B746711
theorem B497851 : Blo 495792 497851 := bstep (se 1 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 497851 = 746777) B746777
theorem B497927 : Blo 495792 497927 := bstep (se 1 (by rfl) ⟨373445, by rfl⟩ : syracuseStep 497927 = 746891) B746891
theorem B497935 : Blo 495792 497935 := bstep (se 1 (by rfl) ⟨373451, by rfl⟩ : syracuseStep 497935 = 746903) B746903
theorem B497979 : Blo 495792 497979 := bstep (se 1 (by rfl) ⟨373484, by rfl⟩ : syracuseStep 497979 = 746969) B746969
theorem B1120571 : Blo 495792 1120571 := bstep (se 1 (by rfl) ⟨840428, by rfl⟩ : syracuseStep 1120571 = 1680857) B1680857
theorem B498055 : Blo 495792 498055 := bstep (se 1 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 498055 = 747083) B747083
theorem B498063 : Blo 495792 498063 := bstep (se 1 (by rfl) ⟨373547, by rfl⟩ : syracuseStep 498063 = 747095) B747095
theorem B1120697 : Blo 495792 1120697 := bstep (se 2 (by rfl) ⟨420261, by rfl⟩ : syracuseStep 1120697 = 840523) B840523
theorem B498107 : Blo 495792 498107 := bstep (se 1 (by rfl) ⟨373580, by rfl⟩ : syracuseStep 498107 = 747161) B747161
theorem B498183 : Blo 495792 498183 := bstep (se 1 (by rfl) ⟨373637, by rfl⟩ : syracuseStep 498183 = 747275) B747275
theorem B498191 : Blo 495792 498191 := bstep (se 1 (by rfl) ⟨373643, by rfl⟩ : syracuseStep 498191 = 747287) B747287
theorem B4528669 : Blo 495792 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B498235 : Blo 495792 498235 := bstep (se 1 (by rfl) ⟨373676, by rfl⟩ : syracuseStep 498235 = 747353) B747353
theorem B498311 : Blo 495792 498311 := bstep (se 1 (by rfl) ⟨373733, by rfl⟩ : syracuseStep 498311 = 747467) B747467
theorem B498319 : Blo 495792 498319 := bstep (se 1 (by rfl) ⟨373739, by rfl⟩ : syracuseStep 498319 = 747479) B747479
theorem B498363 : Blo 495792 498363 := bstep (se 1 (by rfl) ⟨373772, by rfl⟩ : syracuseStep 498363 = 747545) B747545
theorem B498439 : Blo 495792 498439 := bstep (se 1 (by rfl) ⟨373829, by rfl⟩ : syracuseStep 498439 = 747659) B747659
theorem B3775247 : Blo 495792 3775247 := bstep (se 1 (by rfl) ⟨2831435, by rfl⟩ : syracuseStep 3775247 = 5662871) B5662871
theorem B1121039 : Blo 495792 1121039 := bstep (se 1 (by rfl) ⟨840779, by rfl⟩ : syracuseStep 1121039 = 1681559) B1681559
theorem B498447 : Blo 495792 498447 := bstep (se 1 (by rfl) ⟨373835, by rfl⟩ : syracuseStep 498447 = 747671) B747671
theorem B1121057 : Blo 495792 1121057 := bstep (se 2 (by rfl) ⟨420396, by rfl⟩ : syracuseStep 1121057 = 840793) B840793
theorem B498491 : Blo 495792 498491 := bstep (se 1 (by rfl) ⟨373868, by rfl⟩ : syracuseStep 498491 = 747737) B747737
theorem B12229465 : Blo 495792 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B3414899 : Blo 495792 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B629623 : Blo 495792 629623 := bstep (se 1 (by rfl) ⟨472217, by rfl⟩ : syracuseStep 629623 = 944435) B944435
theorem B498567 : Blo 495792 498567 := bstep (se 1 (by rfl) ⟨373925, by rfl⟩ : syracuseStep 498567 = 747851) B747851
theorem B498575 : Blo 495792 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B2694035 : Blo 495792 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B1678265 : Blo 495792 1678265 := bstep (se 2 (by rfl) ⟨629349, by rfl⟩ : syracuseStep 1678265 = 1258699) B1258699
theorem B498619 : Blo 495792 498619 := bstep (se 1 (by rfl) ⟨373964, by rfl⟩ : syracuseStep 498619 = 747929) B747929
theorem B4037579 : Blo 495792 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B498695 : Blo 495792 498695 := bstep (se 1 (by rfl) ⟨374021, by rfl⟩ : syracuseStep 498695 = 748043) B748043
theorem B3185675 : Blo 495792 3185675 := bstep (se 1 (by rfl) ⟨2389256, by rfl⟩ : syracuseStep 3185675 = 4778513) B4778513
theorem B597007 : Blo 495792 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B498703 : Blo 495792 498703 := bstep (se 1 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 498703 = 748055) B748055
theorem B2825239 : Blo 495792 2825239 := bstep (se 1 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 2825239 = 4237859) B4237859
theorem B498747 : Blo 495792 498747 := bstep (se 1 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 498747 = 748121) B748121
theorem B3021911 : Blo 495792 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B1416311 : Blo 495792 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B1121399 : Blo 495792 1121399 := bstep (se 1 (by rfl) ⟨841049, by rfl⟩ : syracuseStep 1121399 = 1682099) B1682099
theorem B498823 : Blo 495792 498823 := bstep (se 1 (by rfl) ⟨374117, by rfl⟩ : syracuseStep 498823 = 748235) B748235
theorem B498831 : Blo 495792 498831 := bstep (se 1 (by rfl) ⟨374123, by rfl⟩ : syracuseStep 498831 = 748247) B748247
theorem B629947 : Blo 495792 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B498875 : Blo 495792 498875 := bstep (se 1 (by rfl) ⟨374156, by rfl⟩ : syracuseStep 498875 = 748313) B748313
theorem B498951 : Blo 495792 498951 := bstep (se 1 (by rfl) ⟨374213, by rfl⟩ : syracuseStep 498951 = 748427) B748427
theorem B498959 : Blo 495792 498959 := bstep (se 1 (by rfl) ⟨374219, by rfl⟩ : syracuseStep 498959 = 748439) B748439
theorem B1121579 : Blo 495792 1121579 := bstep (se 1 (by rfl) ⟨841184, by rfl⟩ : syracuseStep 1121579 = 1682369) B1682369
theorem B499003 : Blo 495792 499003 := bstep (se 1 (by rfl) ⟨374252, by rfl⟩ : syracuseStep 499003 = 748505) B748505
theorem B9575779 : Blo 495792 9575779 := bstep (se 1 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 9575779 = 14363669) B14363669
theorem B499079 : Blo 495792 499079 := bstep (se 1 (by rfl) ⟨374309, by rfl⟩ : syracuseStep 499079 = 748619) B748619
theorem B499087 : Blo 495792 499087 := bstep (se 1 (by rfl) ⟨374315, by rfl⟩ : syracuseStep 499087 = 748631) B748631
theorem B2399635 : Blo 495792 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B499131 : Blo 495792 499131 := bstep (se 1 (by rfl) ⟨374348, by rfl⟩ : syracuseStep 499131 = 748697) B748697
theorem B499207 : Blo 495792 499207 := bstep (se 1 (by rfl) ⟨374405, by rfl⟩ : syracuseStep 499207 = 748811) B748811
theorem B1678859 : Blo 495792 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B499215 : Blo 495792 499215 := bstep (se 1 (by rfl) ⟨374411, by rfl⟩ : syracuseStep 499215 = 748823) B748823
theorem B499259 : Blo 495792 499259 := bstep (se 1 (by rfl) ⟨374444, by rfl⟩ : syracuseStep 499259 = 748889) B748889
theorem B1678967 : Blo 495792 1678967 := bstep (se 1 (by rfl) ⟨1259225, by rfl⟩ : syracuseStep 1678967 = 2518451) B2518451
theorem B499335 : Blo 495792 499335 := bstep (se 1 (by rfl) ⟨374501, by rfl⟩ : syracuseStep 499335 = 749003) B749003
theorem B499343 : Blo 495792 499343 := bstep (se 1 (by rfl) ⟨374507, by rfl⟩ : syracuseStep 499343 = 749015) B749015
theorem B1121939 : Blo 495792 1121939 := bstep (se 1 (by rfl) ⟨841454, by rfl⟩ : syracuseStep 1121939 = 1682909) B1682909
theorem B12754583 : Blo 495792 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B630443 : Blo 495792 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B499387 : Blo 495792 499387 := bstep (se 1 (by rfl) ⟨374540, by rfl⟩ : syracuseStep 499387 = 749081) B749081
theorem B1121993 : Blo 495792 1121993 := bstep (se 2 (by rfl) ⟨420747, by rfl⟩ : syracuseStep 1121993 = 841495) B841495
theorem B499463 : Blo 495792 499463 := bstep (se 1 (by rfl) ⟨374597, by rfl⟩ : syracuseStep 499463 = 749195) B749195
theorem B499471 : Blo 495792 499471 := bstep (se 1 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 499471 = 749207) B749207
theorem B45817649 : Blo 495792 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B2301755 : Blo 495792 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B499515 : Blo 495792 499515 := bstep (se 1 (by rfl) ⟨374636, by rfl⟩ : syracuseStep 499515 = 749273) B749273
theorem B499591 : Blo 495792 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B499599 : Blo 495792 499599 := bstep (se 1 (by rfl) ⟨374699, by rfl⟩ : syracuseStep 499599 = 749399) B749399
theorem B499643 : Blo 495792 499643 := bstep (se 1 (by rfl) ⟨374732, by rfl⟩ : syracuseStep 499643 = 749465) B749465
theorem B499719 : Blo 495792 499719 := bstep (se 1 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 499719 = 749579) B749579
theorem B499727 : Blo 495792 499727 := bstep (se 1 (by rfl) ⟨374795, by rfl⟩ : syracuseStep 499727 = 749591) B749591
theorem B499771 : Blo 495792 499771 := bstep (se 1 (by rfl) ⟨374828, by rfl⟩ : syracuseStep 499771 = 749657) B749657
theorem B630919 : Blo 495792 630919 := bstep (se 1 (by rfl) ⟨473189, by rfl⟩ : syracuseStep 630919 = 946379) B946379
theorem B1679561 : Blo 495792 1679561 := bstep (se 2 (by rfl) ⟨629835, by rfl⟩ : syracuseStep 1679561 = 1259671) B1259671
theorem B1122695 : Blo 495792 1122695 := bstep (se 1 (by rfl) ⟨842021, by rfl⟩ : syracuseStep 1122695 = 1684043) B1684043
theorem B16097777 : Blo 495792 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B10789361 : Blo 495792 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B1122875 : Blo 495792 1122875 := bstep (se 1 (by rfl) ⟨842156, by rfl⟩ : syracuseStep 1122875 = 1684313) B1684313
theorem B631415 : Blo 495792 631415 := bstep (se 1 (by rfl) ⟨473561, by rfl⟩ : syracuseStep 631415 = 947123) B947123
theorem B959123 : Blo 495792 959123 := bstep (se 1 (by rfl) ⟨719342, by rfl⟩ : syracuseStep 959123 = 1438685) B1438685
theorem B1123001 : Blo 495792 1123001 := bstep (se 2 (by rfl) ⟨421125, by rfl⟩ : syracuseStep 1123001 = 842251) B842251
theorem B631567 : Blo 495792 631567 := bstep (se 1 (by rfl) ⟨473675, by rfl⟩ : syracuseStep 631567 = 947351) B947351
theorem B4236083 : Blo 495792 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B1680263 : Blo 495792 1680263 := bstep (se 1 (by rfl) ⟨1260197, by rfl⟩ : syracuseStep 1680263 = 2520395) B2520395
theorem B598919 : Blo 495792 598919 := bstep (se 1 (by rfl) ⟨449189, by rfl⟩ : syracuseStep 598919 = 898379) B898379
theorem B631739 : Blo 495792 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B1123343 : Blo 495792 1123343 := bstep (se 1 (by rfl) ⟨842507, by rfl⟩ : syracuseStep 1123343 = 1685015) B1685015
theorem B1123361 : Blo 495792 1123361 := bstep (se 2 (by rfl) ⟨421260, by rfl⟩ : syracuseStep 1123361 = 842521) B842521
theorem B4236461 : Blo 495792 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B2401481 : Blo 495792 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B1680641 : Blo 495792 1680641 := bstep (se 2 (by rfl) ⟨630240, by rfl⟩ : syracuseStep 1680641 = 1260481) B1260481
theorem B1123703 : Blo 495792 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B894343 : Blo 495792 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B2827655 : Blo 495792 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B1123883 : Blo 495792 1123883 := bstep (se 1 (by rfl) ⟨842912, by rfl⟩ : syracuseStep 1123883 = 1685825) B1685825
theorem B1418953 : Blo 495792 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B1124243 : Blo 495792 1124243 := bstep (se 1 (by rfl) ⟨843182, by rfl⟩ : syracuseStep 1124243 = 1686365) B1686365
theorem B894905 : Blo 495792 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B1124297 : Blo 495792 1124297 := bstep (se 2 (by rfl) ⟨421611, by rfl⟩ : syracuseStep 1124297 = 843223) B843223
theorem B1255439 : Blo 495792 1255439 := bstep (se 1 (by rfl) ⟨941579, by rfl⟩ : syracuseStep 1255439 = 1883159) B1883159
theorem B1681451 : Blo 495792 1681451 := bstep (se 1 (by rfl) ⟨1261088, by rfl⟩ : syracuseStep 1681451 = 2522177) B2522177
theorem B1255571 : Blo 495792 1255571 := bstep (se 1 (by rfl) ⟨941678, by rfl⟩ : syracuseStep 1255571 = 1883357) B1883357
theorem B895367 : Blo 495792 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B1616755 : Blo 495792 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B2829431 : Blo 495792 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B1256705 : Blo 495792 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B1682747 : Blo 495792 1682747 := bstep (se 1 (by rfl) ⟨1262060, by rfl⟩ : syracuseStep 1682747 = 2524121) B2524121
theorem B1420811 : Blo 495792 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B1257079 : Blo 495792 1257079 := bstep (se 1 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 1257079 = 1885619) B1885619
theorem B4534031 : Blo 495792 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B1683233 : Blo 495792 1683233 := bstep (se 2 (by rfl) ⟨631212, by rfl⟩ : syracuseStep 1683233 = 1262425) B1262425
theorem B2830139 : Blo 495792 2830139 := bstep (se 1 (by rfl) ⟨2122604, by rfl⟩ : syracuseStep 2830139 = 4245209) B4245209
theorem B5648291 : Blo 495792 5648291 := bstep (se 1 (by rfl) ⟨4236218, by rfl⟩ : syracuseStep 5648291 = 8472437) B8472437
theorem B1257515 : Blo 495792 1257515 := bstep (se 1 (by rfl) ⟨943136, by rfl⟩ : syracuseStep 1257515 = 1886273) B1886273
theorem B1421459 : Blo 495792 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1192121 : Blo 495792 1192121 := bstep (se 2 (by rfl) ⟨447045, by rfl⟩ : syracuseStep 1192121 = 894091) B894091
theorem B798905 : Blo 495792 798905 := bstep (se 2 (by rfl) ⟨299589, by rfl⟩ : syracuseStep 798905 = 599179) B599179
theorem B1683827 : Blo 495792 1683827 := bstep (se 1 (by rfl) ⟨1262870, by rfl⟩ : syracuseStep 1683827 = 2525741) B2525741
theorem B1421687 : Blo 495792 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B897551 : Blo 495792 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B6369911 : Blo 495792 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B799417 : Blo 495792 799417 := bstep (se 2 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 799417 = 599563) B599563
theorem B1258355 : Blo 495792 1258355 := bstep (se 1 (by rfl) ⟨943766, by rfl⟩ : syracuseStep 1258355 = 1887533) B1887533
theorem B1258375 : Blo 495792 1258375 := bstep (se 1 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 1258375 = 1887563) B1887563
theorem B16135139 : Blo 495792 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B1258649 : Blo 495792 1258649 := bstep (se 2 (by rfl) ⟨471993, by rfl⟩ : syracuseStep 1258649 = 943987) B943987
theorem B2831597 : Blo 495792 2831597 := bstep (se 3 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 2831597 = 1061849) B1061849
theorem B3028261 : Blo 495792 3028261 := bstep (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) B567799
theorem B1258811 : Blo 495792 1258811 := bstep (se 1 (by rfl) ⟨944108, by rfl⟩ : syracuseStep 1258811 = 1888217) B1888217
theorem B4044167 : Blo 495792 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B800135 : Blo 495792 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B1259023 : Blo 495792 1259023 := bstep (se 1 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 1259023 = 1888535) B1888535
theorem B2012759 : Blo 495792 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1947223 : Blo 495792 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B1259297 : Blo 495792 1259297 := bstep (se 2 (by rfl) ⟨472236, by rfl⟩ : syracuseStep 1259297 = 944473) B944473
theorem B5125963 : Blo 495792 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B4044973 : Blo 495792 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B1194763 : Blo 495792 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1260299 : Blo 495792 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B5389145 : Blo 495792 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B2014087 : Blo 495792 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B1686419 : Blo 495792 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B1588481 : Blo 495792 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B7257377 : Blo 495792 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B3783995 : Blo 495792 3783995 := bstep (se 1 (by rfl) ⟨2837996, by rfl⟩ : syracuseStep 3783995 = 5675993) B5675993
theorem B1260947 : Blo 495792 1260947 := bstep (se 1 (by rfl) ⟨945710, by rfl⟩ : syracuseStep 1260947 = 1891421) B1891421
theorem B2833987 : Blo 495792 2833987 := bstep (se 1 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 2833987 = 4250981) B4250981
theorem B1195667 : Blo 495792 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B1261241 : Blo 495792 1261241 := bstep (se 2 (by rfl) ⟨472965, by rfl⟩ : syracuseStep 1261241 = 945931) B945931
theorem B4308785 : Blo 495792 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B638779 : Blo 495792 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B769927 : Blo 495792 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B3063737 : Blo 495792 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1196147 : Blo 495792 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1458443 : Blo 495792 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1261939 : Blo 495792 1261939 := bstep (se 1 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 1261939 = 1892909) B1892909
theorem B1262081 : Blo 495792 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B2736947 : Blo 495792 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B1262537 : Blo 495792 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B1197089 : Blo 495792 1197089 := bstep (se 2 (by rfl) ⟨448908, by rfl⟩ : syracuseStep 1197089 = 897817) B897817
theorem B836743 : Blo 495792 836743 := bstep (se 1 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 836743 = 1255115) B1255115
theorem B1262891 : Blo 495792 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B2835971 : Blo 495792 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B706105 : Blo 495792 706105 := bstep (se 2 (by rfl) ⟨264789, by rfl⟩ : syracuseStep 706105 = 529579) B529579
theorem B837391 : Blo 495792 837391 := bstep (se 1 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 837391 = 1256087) B1256087
theorem B673579 : Blo 495792 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B1886105 : Blo 495792 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B1591339 : Blo 495792 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B1067051 : Blo 495792 1067051 := bstep (se 1 (by rfl) ⟨800288, by rfl⟩ : syracuseStep 1067051 = 1600577) B1600577
theorem B1263883 : Blo 495792 1263883 := bstep (se 1 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 1263883 = 1895825) B1895825
theorem B837931 : Blo 495792 837931 := bstep (se 1 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 837931 = 1256897) B1256897
theorem B1067411 : Blo 495792 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1264025 : Blo 495792 1264025 := bstep (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) B948019
theorem B838073 : Blo 495792 838073 := bstep (se 2 (by rfl) ⟨314277, by rfl⟩ : syracuseStep 838073 = 628555) B628555
theorem B674249 : Blo 495792 674249 := bstep (se 2 (by rfl) ⟨252843, by rfl⟩ : syracuseStep 674249 = 505687) B505687
theorem B4540931 : Blo 495792 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B1264187 : Blo 495792 1264187 := bstep (se 1 (by rfl) ⟨948140, by rfl⟩ : syracuseStep 1264187 = 1896281) B1896281
theorem B1264531 : Blo 495792 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B5098403 : Blo 495792 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B1264673 : Blo 495792 1264673 := bstep (se 2 (by rfl) ⟨474252, by rfl⟩ : syracuseStep 1264673 = 948505) B948505
theorem B838775 : Blo 495792 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B2706803 : Blo 495792 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B839227 : Blo 495792 839227 := bstep (se 1 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 839227 = 1258841) B1258841
theorem B839369 : Blo 495792 839369 := bstep (se 2 (by rfl) ⟨314763, by rfl⟩ : syracuseStep 839369 = 629527) B629527
theorem B2838361 : Blo 495792 2838361 := bstep (se 2 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 2838361 = 2128771) B2128771
theorem B1790039 : Blo 495792 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B6475949 : Blo 495792 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B708907 : Blo 495792 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B840071 : Blo 495792 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B10768787 : Blo 495792 10768787 := bstep (se 1 (by rfl) ⟨8076590, by rfl⟩ : syracuseStep 10768787 = 16153181) B16153181
theorem B3789341 : Blo 495792 3789341 := bstep (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) B1421003
theorem B1790531 : Blo 495792 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B3592997 : Blo 495792 3592997 := bstep (se 4 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 3592997 = 673687) B673687
theorem B2872199 : Blo 495792 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B2544587 : Blo 495792 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B840719 : Blo 495792 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B1594657 : Blo 495792 1594657 := bstep (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) B1195993
theorem B1889689 : Blo 495792 1889689 := bstep (se 2 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 1889689 = 1417267) B1417267
theorem B2840093 : Blo 495792 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B841259 : Blo 495792 841259 := bstep (se 1 (by rfl) ⟨630944, by rfl⟩ : syracuseStep 841259 = 1261889) B1261889
theorem B1889993 : Blo 495792 1889993 := bstep (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) B1417495
theorem B841657 : Blo 495792 841657 := bstep (se 2 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 841657 = 631243) B631243
theorem B87447605 : Blo 495792 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B2840777 : Blo 495792 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B743723 : Blo 495792 743723 := bstep (se 1 (by rfl) ⟨557792, by rfl⟩ : syracuseStep 743723 = 1115585) B1115585
theorem B743753 : Blo 495792 743753 := bstep (se 2 (by rfl) ⟨278907, by rfl⟩ : syracuseStep 743753 = 557815) B557815
theorem B2513267 : Blo 495792 2513267 := bstep (se 1 (by rfl) ⟨1884950, by rfl⟩ : syracuseStep 2513267 = 3769901) B3769901
theorem B743867 : Blo 495792 743867 := bstep (se 1 (by rfl) ⟨557900, by rfl⟩ : syracuseStep 743867 = 1115801) B1115801
theorem B743927 : Blo 495792 743927 := bstep (se 1 (by rfl) ⟨557945, by rfl⟩ : syracuseStep 743927 = 1115891) B1115891
theorem B743951 : Blo 495792 743951 := bstep (se 1 (by rfl) ⟨557963, by rfl⟩ : syracuseStep 743951 = 1115927) B1115927
theorem B1432079 : Blo 495792 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B743993 : Blo 495792 743993 := bstep (se 2 (by rfl) ⟨278997, by rfl⟩ : syracuseStep 743993 = 557995) B557995
theorem B842359 : Blo 495792 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B4250231 : Blo 495792 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B1890935 : Blo 495792 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B744071 : Blo 495792 744071 := bstep (se 1 (by rfl) ⟨558053, by rfl⟩ : syracuseStep 744071 = 1116107) B1116107
theorem B744107 : Blo 495792 744107 := bstep (se 1 (by rfl) ⟨558080, by rfl⟩ : syracuseStep 744107 = 1116161) B1116161
theorem B744137 : Blo 495792 744137 := bstep (se 2 (by rfl) ⟨279051, by rfl⟩ : syracuseStep 744137 = 558103) B558103
theorem B744251 : Blo 495792 744251 := bstep (se 1 (by rfl) ⟨558188, by rfl⟩ : syracuseStep 744251 = 1116377) B1116377
theorem B842555 : Blo 495792 842555 := bstep (se 1 (by rfl) ⟨631916, by rfl⟩ : syracuseStep 842555 = 1263833) B1263833
theorem B2513753 : Blo 495792 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B7199603 : Blo 495792 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B744311 : Blo 495792 744311 := bstep (se 1 (by rfl) ⟨558233, by rfl⟩ : syracuseStep 744311 = 1116467) B1116467
theorem B744335 : Blo 495792 744335 := bstep (se 1 (by rfl) ⟨558251, by rfl⟩ : syracuseStep 744335 = 1116503) B1116503
theorem B711595 : Blo 495792 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B744377 : Blo 495792 744377 := bstep (se 2 (by rfl) ⟨279141, by rfl⟩ : syracuseStep 744377 = 558283) B558283
theorem B744455 : Blo 495792 744455 := bstep (se 1 (by rfl) ⟨558341, by rfl⟩ : syracuseStep 744455 = 1116683) B1116683
theorem B744491 : Blo 495792 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B744521 : Blo 495792 744521 := bstep (se 2 (by rfl) ⟨279195, by rfl⟩ : syracuseStep 744521 = 558391) B558391
theorem B1596503 : Blo 495792 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B744635 : Blo 495792 744635 := bstep (se 1 (by rfl) ⟨558476, by rfl⟩ : syracuseStep 744635 = 1116953) B1116953
theorem B842953 : Blo 495792 842953 := bstep (se 2 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 842953 = 632215) B632215
theorem B744695 : Blo 495792 744695 := bstep (se 1 (by rfl) ⟨558521, by rfl⟩ : syracuseStep 744695 = 1117043) B1117043
theorem B744719 : Blo 495792 744719 := bstep (se 1 (by rfl) ⟨558539, by rfl⟩ : syracuseStep 744719 = 1117079) B1117079
theorem B744761 : Blo 495792 744761 := bstep (se 2 (by rfl) ⟨279285, by rfl⟩ : syracuseStep 744761 = 558571) B558571
theorem B744839 : Blo 495792 744839 := bstep (se 1 (by rfl) ⟨558629, by rfl⟩ : syracuseStep 744839 = 1117259) B1117259
theorem B744875 : Blo 495792 744875 := bstep (se 1 (by rfl) ⟨558656, by rfl⟩ : syracuseStep 744875 = 1117313) B1117313
theorem B744905 : Blo 495792 744905 := bstep (se 2 (by rfl) ⟨279339, by rfl⟩ : syracuseStep 744905 = 558679) B558679
theorem B2022941 : Blo 495792 2022941 := bstep (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) B758603
theorem B745019 : Blo 495792 745019 := bstep (se 1 (by rfl) ⟨558764, by rfl⟩ : syracuseStep 745019 = 1117529) B1117529
theorem B1596989 : Blo 495792 1596989 := bstep (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) B598871
theorem B1793603 : Blo 495792 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B1891907 : Blo 495792 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B745079 : Blo 495792 745079 := bstep (se 1 (by rfl) ⟨558809, by rfl⟩ : syracuseStep 745079 = 1117619) B1117619
theorem B745103 : Blo 495792 745103 := bstep (se 1 (by rfl) ⟨558827, by rfl⟩ : syracuseStep 745103 = 1117655) B1117655
theorem B745145 : Blo 495792 745145 := bstep (se 2 (by rfl) ⟨279429, by rfl⟩ : syracuseStep 745145 = 558859) B558859
theorem B11460325 : Blo 495792 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B745223 : Blo 495792 745223 := bstep (se 1 (by rfl) ⟨558917, by rfl⟩ : syracuseStep 745223 = 1117835) B1117835
theorem B745259 : Blo 495792 745259 := bstep (se 1 (by rfl) ⟨558944, by rfl⟩ : syracuseStep 745259 = 1117889) B1117889
theorem B745289 : Blo 495792 745289 := bstep (se 2 (by rfl) ⟨279483, by rfl⟩ : syracuseStep 745289 = 558967) B558967
theorem B941959 : Blo 495792 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B2842553 : Blo 495792 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B745403 : Blo 495792 745403 := bstep (se 1 (by rfl) ⟨559052, by rfl⟩ : syracuseStep 745403 = 1118105) B1118105
theorem B745463 : Blo 495792 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B745487 : Blo 495792 745487 := bstep (se 1 (by rfl) ⟨559115, by rfl⟩ : syracuseStep 745487 = 1118231) B1118231
theorem B745529 : Blo 495792 745529 := bstep (se 2 (by rfl) ⟨279573, by rfl⟩ : syracuseStep 745529 = 559147) B559147
theorem B2383991 : Blo 495792 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B745607 : Blo 495792 745607 := bstep (se 1 (by rfl) ⟨559205, by rfl⟩ : syracuseStep 745607 = 1118411) B1118411
theorem B745643 : Blo 495792 745643 := bstep (se 1 (by rfl) ⟨559232, by rfl⟩ : syracuseStep 745643 = 1118465) B1118465
theorem B745673 : Blo 495792 745673 := bstep (se 2 (by rfl) ⟨279627, by rfl⟩ : syracuseStep 745673 = 559255) B559255
theorem B745787 : Blo 495792 745787 := bstep (se 1 (by rfl) ⟨559340, by rfl⟩ : syracuseStep 745787 = 1118681) B1118681
theorem B745847 : Blo 495792 745847 := bstep (se 1 (by rfl) ⟨559385, by rfl⟩ : syracuseStep 745847 = 1118771) B1118771
theorem B745871 : Blo 495792 745871 := bstep (se 1 (by rfl) ⟨559403, by rfl⟩ : syracuseStep 745871 = 1118807) B1118807
theorem B745913 : Blo 495792 745913 := bstep (se 2 (by rfl) ⟨279717, by rfl⟩ : syracuseStep 745913 = 559435) B559435
theorem B745991 : Blo 495792 745991 := bstep (se 1 (by rfl) ⟨559493, by rfl⟩ : syracuseStep 745991 = 1118987) B1118987
theorem B1597963 : Blo 495792 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B746027 : Blo 495792 746027 := bstep (se 1 (by rfl) ⟨559520, by rfl⟩ : syracuseStep 746027 = 1119041) B1119041
theorem B746057 : Blo 495792 746057 := bstep (se 2 (by rfl) ⟨279771, by rfl⟩ : syracuseStep 746057 = 559543) B559543
theorem B746171 : Blo 495792 746171 := bstep (se 1 (by rfl) ⟨559628, by rfl⟩ : syracuseStep 746171 = 1119257) B1119257
theorem B5661413 : Blo 495792 5661413 := bstep (se 4 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 5661413 = 1061515) B1061515
theorem B746231 : Blo 495792 746231 := bstep (se 1 (by rfl) ⟨559673, by rfl⟩ : syracuseStep 746231 = 1119347) B1119347
theorem B746255 : Blo 495792 746255 := bstep (se 1 (by rfl) ⟨559691, by rfl⟩ : syracuseStep 746255 = 1119383) B1119383
theorem B3793715 : Blo 495792 3793715 := bstep (se 1 (by rfl) ⟨2845286, by rfl⟩ : syracuseStep 3793715 = 5690573) B5690573
theorem B746297 : Blo 495792 746297 := bstep (se 2 (by rfl) ⟨279861, by rfl⟩ : syracuseStep 746297 = 559723) B559723
theorem B746375 : Blo 495792 746375 := bstep (se 1 (by rfl) ⟨559781, by rfl⟩ : syracuseStep 746375 = 1119563) B1119563
theorem B2515859 : Blo 495792 2515859 := bstep (se 1 (by rfl) ⟨1886894, by rfl⟩ : syracuseStep 2515859 = 3773789) B3773789
theorem B746411 : Blo 495792 746411 := bstep (se 1 (by rfl) ⟨559808, by rfl⟩ : syracuseStep 746411 = 1119617) B1119617
theorem B746441 : Blo 495792 746441 := bstep (se 2 (by rfl) ⟨279915, by rfl⟩ : syracuseStep 746441 = 559831) B559831
theorem B746555 : Blo 495792 746555 := bstep (se 1 (by rfl) ⟨559916, by rfl⟩ : syracuseStep 746555 = 1119833) B1119833
theorem B746615 : Blo 495792 746615 := bstep (se 1 (by rfl) ⟨559961, by rfl⟩ : syracuseStep 746615 = 1119923) B1119923
theorem B746639 : Blo 495792 746639 := bstep (se 1 (by rfl) ⟨559979, by rfl⟩ : syracuseStep 746639 = 1119959) B1119959
theorem B746681 : Blo 495792 746681 := bstep (se 2 (by rfl) ⟨280005, by rfl⟩ : syracuseStep 746681 = 560011) B560011
theorem B1893577 : Blo 495792 1893577 := bstep (se 2 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 1893577 = 1420183) B1420183
theorem B746759 : Blo 495792 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B746795 : Blo 495792 746795 := bstep (se 1 (by rfl) ⟨560096, by rfl⟩ : syracuseStep 746795 = 1120193) B1120193
theorem B746825 : Blo 495792 746825 := bstep (se 2 (by rfl) ⟨280059, by rfl⟩ : syracuseStep 746825 = 560119) B560119
theorem B6383033 : Blo 495792 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B746939 : Blo 495792 746939 := bstep (se 1 (by rfl) ⟨560204, by rfl⟩ : syracuseStep 746939 = 1120409) B1120409
theorem B746999 : Blo 495792 746999 := bstep (se 1 (by rfl) ⟨560249, by rfl⟩ : syracuseStep 746999 = 1120499) B1120499
theorem B747023 : Blo 495792 747023 := bstep (se 1 (by rfl) ⟨560267, by rfl⟩ : syracuseStep 747023 = 1120535) B1120535
theorem B747065 : Blo 495792 747065 := bstep (se 2 (by rfl) ⟨280149, by rfl⟩ : syracuseStep 747065 = 560299) B560299
theorem B943751 : Blo 495792 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B747143 : Blo 495792 747143 := bstep (se 1 (by rfl) ⟨560357, by rfl⟩ : syracuseStep 747143 = 1120715) B1120715
theorem B747179 : Blo 495792 747179 := bstep (se 1 (by rfl) ⟨560384, by rfl⟩ : syracuseStep 747179 = 1120769) B1120769
theorem B747209 : Blo 495792 747209 := bstep (se 2 (by rfl) ⟨280203, by rfl⟩ : syracuseStep 747209 = 560407) B560407
theorem B2844467 : Blo 495792 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B21489461 : Blo 495792 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B747323 : Blo 495792 747323 := bstep (se 1 (by rfl) ⟨560492, by rfl⟩ : syracuseStep 747323 = 1120985) B1120985
theorem B1599347 : Blo 495792 1599347 := bstep (se 1 (by rfl) ⟨1199510, by rfl⟩ : syracuseStep 1599347 = 2399021) B2399021
theorem B747383 : Blo 495792 747383 := bstep (se 1 (by rfl) ⟨560537, by rfl⟩ : syracuseStep 747383 = 1121075) B1121075
theorem B747407 : Blo 495792 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B3073945 : Blo 495792 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B747449 : Blo 495792 747449 := bstep (se 2 (by rfl) ⟨280293, by rfl⟩ : syracuseStep 747449 = 560587) B560587
theorem B5400523 : Blo 495792 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B747527 : Blo 495792 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B2385949 : Blo 495792 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B747563 : Blo 495792 747563 := bstep (se 1 (by rfl) ⟨560672, by rfl⟩ : syracuseStep 747563 = 1121345) B1121345
theorem B747593 : Blo 495792 747593 := bstep (se 2 (by rfl) ⟨280347, by rfl⟩ : syracuseStep 747593 = 560695) B560695
theorem B747707 : Blo 495792 747707 := bstep (se 1 (by rfl) ⟨560780, by rfl⟩ : syracuseStep 747707 = 1121561) B1121561
theorem B1697993 : Blo 495792 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B747767 : Blo 495792 747767 := bstep (se 1 (by rfl) ⟨560825, by rfl⟩ : syracuseStep 747767 = 1121651) B1121651
theorem B1599745 : Blo 495792 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B747791 : Blo 495792 747791 := bstep (se 1 (by rfl) ⟨560843, by rfl⟩ : syracuseStep 747791 = 1121687) B1121687
theorem B747833 : Blo 495792 747833 := bstep (se 2 (by rfl) ⟨280437, by rfl⟩ : syracuseStep 747833 = 560875) B560875
theorem B1599859 : Blo 495792 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B747911 : Blo 495792 747911 := bstep (se 1 (by rfl) ⟨560933, by rfl⟩ : syracuseStep 747911 = 1121867) B1121867
theorem B747947 : Blo 495792 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B747977 : Blo 495792 747977 := bstep (se 2 (by rfl) ⟨280491, by rfl⟩ : syracuseStep 747977 = 560983) B560983
theorem B748091 : Blo 495792 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B2419267 : Blo 495792 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B748151 : Blo 495792 748151 := bstep (se 1 (by rfl) ⟨561113, by rfl⟩ : syracuseStep 748151 = 1122227) B1122227
theorem B748175 : Blo 495792 748175 := bstep (se 1 (by rfl) ⟨561131, by rfl⟩ : syracuseStep 748175 = 1122263) B1122263
theorem B748217 : Blo 495792 748217 := bstep (se 2 (by rfl) ⟨280581, by rfl⟩ : syracuseStep 748217 = 561163) B561163
theorem B748295 : Blo 495792 748295 := bstep (se 1 (by rfl) ⟨561221, by rfl⟩ : syracuseStep 748295 = 1122443) B1122443
theorem B748331 : Blo 495792 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B748361 : Blo 495792 748361 := bstep (se 2 (by rfl) ⟨280635, by rfl⟩ : syracuseStep 748361 = 561271) B561271
theorem B4025251 : Blo 495792 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B748475 : Blo 495792 748475 := bstep (se 1 (by rfl) ⟨561356, by rfl⟩ : syracuseStep 748475 = 1122713) B1122713
theorem B748535 : Blo 495792 748535 := bstep (se 1 (by rfl) ⟨561401, by rfl⟩ : syracuseStep 748535 = 1122803) B1122803
theorem B748559 : Blo 495792 748559 := bstep (se 1 (by rfl) ⟨561419, by rfl⟩ : syracuseStep 748559 = 1122839) B1122839
theorem B748601 : Blo 495792 748601 := bstep (se 2 (by rfl) ⟨280725, by rfl⟩ : syracuseStep 748601 = 561451) B561451
theorem B748679 : Blo 495792 748679 := bstep (se 1 (by rfl) ⟨561509, by rfl⟩ : syracuseStep 748679 = 1123019) B1123019
theorem B748715 : Blo 495792 748715 := bstep (se 1 (by rfl) ⟨561536, by rfl⟩ : syracuseStep 748715 = 1123073) B1123073
theorem B748745 : Blo 495792 748745 := bstep (se 2 (by rfl) ⟨280779, by rfl⟩ : syracuseStep 748745 = 561559) B561559
theorem B2845925 : Blo 495792 2845925 := bstep (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) B533611
theorem B748859 : Blo 495792 748859 := bstep (se 1 (by rfl) ⟨561644, by rfl⟩ : syracuseStep 748859 = 1123289) B1123289
theorem B1895795 : Blo 495792 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B748919 : Blo 495792 748919 := bstep (se 1 (by rfl) ⟨561689, by rfl⟩ : syracuseStep 748919 = 1123379) B1123379
theorem B748943 : Blo 495792 748943 := bstep (se 1 (by rfl) ⟨561707, by rfl⟩ : syracuseStep 748943 = 1123415) B1123415
theorem B748985 : Blo 495792 748985 := bstep (se 2 (by rfl) ⟨280869, by rfl⟩ : syracuseStep 748985 = 561739) B561739
theorem B749063 : Blo 495792 749063 := bstep (se 1 (by rfl) ⟨561797, by rfl⟩ : syracuseStep 749063 = 1123595) B1123595
theorem B749099 : Blo 495792 749099 := bstep (se 1 (by rfl) ⟨561824, by rfl⟩ : syracuseStep 749099 = 1123649) B1123649
theorem B4779587 : Blo 495792 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B749129 : Blo 495792 749129 := bstep (se 2 (by rfl) ⟨280923, by rfl⟩ : syracuseStep 749129 = 561847) B561847
theorem B749243 : Blo 495792 749243 := bstep (se 1 (by rfl) ⟨561932, by rfl⟩ : syracuseStep 749243 = 1123865) B1123865
theorem B1797869 : Blo 495792 1797869 := bstep (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) B674201
theorem B749303 : Blo 495792 749303 := bstep (se 1 (by rfl) ⟨561977, by rfl⟩ : syracuseStep 749303 = 1123955) B1123955
theorem B519943 : Blo 495792 519943 := bstep (se 1 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 519943 = 779915) B779915
theorem B749327 : Blo 495792 749327 := bstep (se 1 (by rfl) ⟨561995, by rfl⟩ : syracuseStep 749327 = 1123991) B1123991
theorem B749369 : Blo 495792 749369 := bstep (se 2 (by rfl) ⟨281013, by rfl⟩ : syracuseStep 749369 = 562027) B562027
theorem B749447 : Blo 495792 749447 := bstep (se 1 (by rfl) ⟨562085, by rfl⟩ : syracuseStep 749447 = 1124171) B1124171
theorem B2518937 : Blo 495792 2518937 := bstep (se 2 (by rfl) ⟨944601, by rfl⟩ : syracuseStep 2518937 = 1889203) B1889203
theorem B749483 : Blo 495792 749483 := bstep (se 1 (by rfl) ⟨562112, by rfl⟩ : syracuseStep 749483 = 1124225) B1124225
theorem B2682809 : Blo 495792 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B749513 : Blo 495792 749513 := bstep (se 2 (by rfl) ⟨281067, by rfl⟩ : syracuseStep 749513 = 562135) B562135
theorem B946235 : Blo 495792 946235 := bstep (se 1 (by rfl) ⟨709676, by rfl⟩ : syracuseStep 946235 = 1419353) B1419353
theorem B2125885 : Blo 495792 2125885 := bstep (se 3 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 2125885 = 797207) B797207
theorem B749627 : Blo 495792 749627 := bstep (se 1 (by rfl) ⟨562220, by rfl⟩ : syracuseStep 749627 = 1124441) B1124441
theorem B749687 : Blo 495792 749687 := bstep (se 1 (by rfl) ⟨562265, by rfl⟩ : syracuseStep 749687 = 1124531) B1124531
theorem B4026809 : Blo 495792 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B2683415 : Blo 495792 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B946721 : Blo 495792 946721 := bstep (se 2 (by rfl) ⟨355020, by rfl⟩ : syracuseStep 946721 = 710041) B710041
theorem B848585 : Blo 495792 848585 := bstep (se 2 (by rfl) ⟨318219, by rfl⟩ : syracuseStep 848585 = 636439) B636439
theorem B3765041 : Blo 495792 3765041 := bstep (se 2 (by rfl) ⟨1411890, by rfl⟩ : syracuseStep 3765041 = 2823781) B2823781
theorem B1340563 : Blo 495792 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B718327 : Blo 495792 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B1701577 : Blo 495792 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B2422561 : Blo 495792 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B3602339 : Blo 495792 3602339 := bstep (se 1 (by rfl) ⟨2701754, by rfl⟩ : syracuseStep 3602339 = 5403509) B5403509
theorem B2127883 : Blo 495792 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B1964119 : Blo 495792 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2521529 : Blo 495792 2521529 := bstep (se 2 (by rfl) ⟨945573, by rfl⟩ : syracuseStep 2521529 = 1891147) B1891147
theorem B948665 : Blo 495792 948665 := bstep (se 2 (by rfl) ⟨355749, by rfl⟩ : syracuseStep 948665 = 711499) B711499
theorem B850447 : Blo 495792 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B719689 : Blo 495792 719689 := bstep (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) B539767
theorem B6454333 : Blo 495792 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B2522825 : Blo 495792 2522825 := bstep (se 2 (by rfl) ⟨946059, by rfl⟩ : syracuseStep 2522825 = 1892119) B1892119
theorem B932774453 : Blo 495792 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B2130617 : Blo 495792 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B1115657 : Blo 495792 1115657 := bstep (se 2 (by rfl) ⟨418371, by rfl⟩ : syracuseStep 1115657 = 836743) B836743
theorem B2524769 : Blo 495792 2524769 := bstep (se 2 (by rfl) ⟨946788, by rfl⟩ : syracuseStep 2524769 = 1893577) B1893577
theorem B558715 : Blo 495792 558715 := bstep (se 1 (by rfl) ⟨419036, by rfl⟩ : syracuseStep 558715 = 838073) B838073
theorem B1115999 : Blo 495792 1115999 := bstep (se 1 (by rfl) ⟨836999, by rfl⟩ : syracuseStep 1115999 = 1673999) B1673999
theorem B1116179 : Blo 495792 1116179 := bstep (se 1 (by rfl) ⟨837134, by rfl⟩ : syracuseStep 1116179 = 1674269) B1674269
theorem B559183 : Blo 495792 559183 := bstep (se 1 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 559183 = 838775) B838775
theorem B1804535 : Blo 495792 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B1116521 : Blo 495792 1116521 := bstep (se 2 (by rfl) ⟨418695, by rfl⟩ : syracuseStep 1116521 = 837391) B837391
theorem B559579 : Blo 495792 559579 := bstep (se 1 (by rfl) ⟨419684, by rfl⟩ : syracuseStep 559579 = 839369) B839369
theorem B854491 : Blo 495792 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B4098593 : Blo 495792 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B3181265 : Blo 495792 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B560047 : Blo 495792 560047 := bstep (se 1 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 560047 = 840071) B840071
theorem B7179191 : Blo 495792 7179191 := bstep (se 1 (by rfl) ⟨5384393, by rfl⟩ : syracuseStep 7179191 = 10768787) B10768787
theorem B1117115 : Blo 495792 1117115 := bstep (se 1 (by rfl) ⟨837836, by rfl⟩ : syracuseStep 1117115 = 1675673) B1675673
theorem B2132993 : Blo 495792 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B2526227 : Blo 495792 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B1117241 : Blo 495792 1117241 := bstep (se 2 (by rfl) ⟨418965, by rfl⟩ : syracuseStep 1117241 = 837931) B837931
theorem B2133145 : Blo 495792 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B2395331 : Blo 495792 2395331 := bstep (se 1 (by rfl) ⟨1796498, by rfl⟩ : syracuseStep 2395331 = 3592997) B3592997
theorem B560479 : Blo 495792 560479 := bstep (se 1 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 560479 = 840719) B840719
theorem B1117583 : Blo 495792 1117583 := bstep (se 1 (by rfl) ⟨838187, by rfl⟩ : syracuseStep 1117583 = 1676375) B1676375
theorem B560839 : Blo 495792 560839 := bstep (se 1 (by rfl) ⟨420629, by rfl⟩ : syracuseStep 560839 = 841259) B841259
theorem B1117907 : Blo 495792 1117907 := bstep (se 1 (by rfl) ⟨838430, by rfl⟩ : syracuseStep 1117907 = 1676861) B1676861
theorem B495815 : Blo 495792 495815 := bstep (se 1 (by rfl) ⟨371861, by rfl⟩ : syracuseStep 495815 = 743723) B743723
theorem B495835 : Blo 495792 495835 := bstep (se 1 (by rfl) ⟨371876, by rfl⟩ : syracuseStep 495835 = 743753) B743753
theorem B1675511 : Blo 495792 1675511 := bstep (se 1 (by rfl) ⟨1256633, by rfl⟩ : syracuseStep 1675511 = 2513267) B2513267
theorem B495911 : Blo 495792 495911 := bstep (se 1 (by rfl) ⟨371933, by rfl⟩ : syracuseStep 495911 = 743867) B743867
theorem B495951 : Blo 495792 495951 := bstep (se 1 (by rfl) ⟨371963, by rfl⟩ : syracuseStep 495951 = 743927) B743927
theorem B495967 : Blo 495792 495967 := bstep (se 1 (by rfl) ⟨371975, by rfl⟩ : syracuseStep 495967 = 743951) B743951
theorem B954719 : Blo 495792 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B495995 : Blo 495792 495995 := bstep (se 1 (by rfl) ⟨371996, by rfl⟩ : syracuseStep 495995 = 743993) B743993
theorem B496047 : Blo 495792 496047 := bstep (se 1 (by rfl) ⟨372035, by rfl⟩ : syracuseStep 496047 = 744071) B744071
theorem B496071 : Blo 495792 496071 := bstep (se 1 (by rfl) ⟨372053, by rfl⟩ : syracuseStep 496071 = 744107) B744107
theorem B496091 : Blo 495792 496091 := bstep (se 1 (by rfl) ⟨372068, by rfl⟩ : syracuseStep 496091 = 744137) B744137
theorem B496167 : Blo 495792 496167 := bstep (se 1 (by rfl) ⟨372125, by rfl⟩ : syracuseStep 496167 = 744251) B744251
theorem B561703 : Blo 495792 561703 := bstep (se 1 (by rfl) ⟨421277, by rfl⟩ : syracuseStep 561703 = 842555) B842555
theorem B1675835 : Blo 495792 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B496207 : Blo 495792 496207 := bstep (se 1 (by rfl) ⟨372155, by rfl⟩ : syracuseStep 496207 = 744311) B744311
theorem B496223 : Blo 495792 496223 := bstep (se 1 (by rfl) ⟨372167, by rfl⟩ : syracuseStep 496223 = 744335) B744335
theorem B496251 : Blo 495792 496251 := bstep (se 1 (by rfl) ⟨372188, by rfl⟩ : syracuseStep 496251 = 744377) B744377
theorem B1118843 : Blo 495792 1118843 := bstep (se 1 (by rfl) ⟨839132, by rfl⟩ : syracuseStep 1118843 = 1678265) B1678265
theorem B2691719 : Blo 495792 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B496303 : Blo 495792 496303 := bstep (se 1 (by rfl) ⟨372227, by rfl⟩ : syracuseStep 496303 = 744455) B744455
theorem B496327 : Blo 495792 496327 := bstep (se 1 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 496327 = 744491) B744491
theorem B496347 : Blo 495792 496347 := bstep (se 1 (by rfl) ⟨372260, by rfl⟩ : syracuseStep 496347 = 744521) B744521
theorem B1118969 : Blo 495792 1118969 := bstep (se 2 (by rfl) ⟨419613, by rfl⟩ : syracuseStep 1118969 = 839227) B839227
theorem B496423 : Blo 495792 496423 := bstep (se 1 (by rfl) ⟨372317, by rfl⟩ : syracuseStep 496423 = 744635) B744635
theorem B1676105 : Blo 495792 1676105 := bstep (se 2 (by rfl) ⟨628539, by rfl⟩ : syracuseStep 1676105 = 1257079) B1257079
theorem B496463 : Blo 495792 496463 := bstep (se 1 (by rfl) ⟨372347, by rfl⟩ : syracuseStep 496463 = 744695) B744695
theorem B496479 : Blo 495792 496479 := bstep (se 1 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 496479 = 744719) B744719
theorem B496507 : Blo 495792 496507 := bstep (se 1 (by rfl) ⟨372380, by rfl⟩ : syracuseStep 496507 = 744761) B744761
theorem B496559 : Blo 495792 496559 := bstep (se 1 (by rfl) ⟨372419, by rfl⟩ : syracuseStep 496559 = 744839) B744839
theorem B496583 : Blo 495792 496583 := bstep (se 1 (by rfl) ⟨372437, by rfl⟩ : syracuseStep 496583 = 744875) B744875
theorem B496603 : Blo 495792 496603 := bstep (se 1 (by rfl) ⟨372452, by rfl⟩ : syracuseStep 496603 = 744905) B744905
theorem B1119239 : Blo 495792 1119239 := bstep (se 1 (by rfl) ⟨839429, by rfl⟩ : syracuseStep 1119239 = 1678859) B1678859
theorem B693257 : Blo 495792 693257 := bstep (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) B519943
theorem B496679 : Blo 495792 496679 := bstep (se 1 (by rfl) ⟨372509, by rfl⟩ : syracuseStep 496679 = 745019) B745019
theorem B496719 : Blo 495792 496719 := bstep (se 1 (by rfl) ⟨372539, by rfl⟩ : syracuseStep 496719 = 745079) B745079
theorem B1119311 : Blo 495792 1119311 := bstep (se 1 (by rfl) ⟨839483, by rfl⟩ : syracuseStep 1119311 = 1678967) B1678967
theorem B496735 : Blo 495792 496735 := bstep (se 1 (by rfl) ⟨372551, by rfl⟩ : syracuseStep 496735 = 745103) B745103
theorem B496763 : Blo 495792 496763 := bstep (se 1 (by rfl) ⟨372572, by rfl⟩ : syracuseStep 496763 = 745145) B745145
theorem B496815 : Blo 495792 496815 := bstep (se 1 (by rfl) ⟨372611, by rfl⟩ : syracuseStep 496815 = 745223) B745223
theorem B496839 : Blo 495792 496839 := bstep (se 1 (by rfl) ⟨372629, by rfl⟩ : syracuseStep 496839 = 745259) B745259
theorem B30545099 : Blo 495792 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B496859 : Blo 495792 496859 := bstep (se 1 (by rfl) ⟨372644, by rfl⟩ : syracuseStep 496859 = 745289) B745289
theorem B496935 : Blo 495792 496935 := bstep (se 1 (by rfl) ⟨372701, by rfl⟩ : syracuseStep 496935 = 745403) B745403
theorem B496975 : Blo 495792 496975 := bstep (se 1 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 496975 = 745463) B745463
theorem B496991 : Blo 495792 496991 := bstep (se 1 (by rfl) ⟨372743, by rfl⟩ : syracuseStep 496991 = 745487) B745487
theorem B497019 : Blo 495792 497019 := bstep (se 1 (by rfl) ⟨372764, by rfl⟩ : syracuseStep 497019 = 745529) B745529
theorem B497071 : Blo 495792 497071 := bstep (se 1 (by rfl) ⟨372803, by rfl⟩ : syracuseStep 497071 = 745607) B745607
theorem B497095 : Blo 495792 497095 := bstep (se 1 (by rfl) ⟨372821, by rfl⟩ : syracuseStep 497095 = 745643) B745643
theorem B497115 : Blo 495792 497115 := bstep (se 1 (by rfl) ⟨372836, by rfl⟩ : syracuseStep 497115 = 745673) B745673
theorem B1119707 : Blo 495792 1119707 := bstep (se 1 (by rfl) ⟨839780, by rfl⟩ : syracuseStep 1119707 = 1679561) B1679561
theorem B497191 : Blo 495792 497191 := bstep (se 1 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 497191 = 745787) B745787
theorem B497231 : Blo 495792 497231 := bstep (se 1 (by rfl) ⟨372923, by rfl⟩ : syracuseStep 497231 = 745847) B745847
theorem B497247 : Blo 495792 497247 := bstep (se 1 (by rfl) ⟨372935, by rfl⟩ : syracuseStep 497247 = 745871) B745871
theorem B497275 : Blo 495792 497275 := bstep (se 1 (by rfl) ⟨372956, by rfl⟩ : syracuseStep 497275 = 745913) B745913
theorem B497327 : Blo 495792 497327 := bstep (se 1 (by rfl) ⟨372995, by rfl⟩ : syracuseStep 497327 = 745991) B745991
theorem B497351 : Blo 495792 497351 := bstep (se 1 (by rfl) ⟨373013, by rfl⟩ : syracuseStep 497351 = 746027) B746027
theorem B497371 : Blo 495792 497371 := bstep (se 1 (by rfl) ⟨373028, by rfl⟩ : syracuseStep 497371 = 746057) B746057
theorem B497447 : Blo 495792 497447 := bstep (se 1 (by rfl) ⟨373085, by rfl⟩ : syracuseStep 497447 = 746171) B746171
theorem B3774275 : Blo 495792 3774275 := bstep (se 1 (by rfl) ⟨2830706, by rfl⟩ : syracuseStep 3774275 = 5661413) B5661413
theorem B497487 : Blo 495792 497487 := bstep (se 1 (by rfl) ⟨373115, by rfl⟩ : syracuseStep 497487 = 746231) B746231
theorem B497503 : Blo 495792 497503 := bstep (se 1 (by rfl) ⟨373127, by rfl⟩ : syracuseStep 497503 = 746255) B746255
theorem B2824055 : Blo 495792 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B2529143 : Blo 495792 2529143 := bstep (se 1 (by rfl) ⟨1896857, by rfl⟩ : syracuseStep 2529143 = 3793715) B3793715
theorem B497531 : Blo 495792 497531 := bstep (se 1 (by rfl) ⟨373148, by rfl⟩ : syracuseStep 497531 = 746297) B746297
theorem B497583 : Blo 495792 497583 := bstep (se 1 (by rfl) ⟨373187, by rfl⟩ : syracuseStep 497583 = 746375) B746375
theorem B1120175 : Blo 495792 1120175 := bstep (se 1 (by rfl) ⟨840131, by rfl⟩ : syracuseStep 1120175 = 1680263) B1680263
theorem B1677239 : Blo 495792 1677239 := bstep (se 1 (by rfl) ⟨1257929, by rfl⟩ : syracuseStep 1677239 = 2515859) B2515859
theorem B497607 : Blo 495792 497607 := bstep (se 1 (by rfl) ⟨373205, by rfl⟩ : syracuseStep 497607 = 746411) B746411
theorem B497627 : Blo 495792 497627 := bstep (se 1 (by rfl) ⟨373220, by rfl⟩ : syracuseStep 497627 = 746441) B746441
theorem B8067109 : Blo 495792 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B497703 : Blo 495792 497703 := bstep (se 1 (by rfl) ⟨373277, by rfl⟩ : syracuseStep 497703 = 746555) B746555
theorem B497743 : Blo 495792 497743 := bstep (se 1 (by rfl) ⟨373307, by rfl⟩ : syracuseStep 497743 = 746615) B746615
theorem B497759 : Blo 495792 497759 := bstep (se 1 (by rfl) ⟨373319, by rfl⟩ : syracuseStep 497759 = 746639) B746639
theorem B2824307 : Blo 495792 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B497787 : Blo 495792 497787 := bstep (se 1 (by rfl) ⟨373340, by rfl⟩ : syracuseStep 497787 = 746681) B746681
theorem B1120427 : Blo 495792 1120427 := bstep (se 1 (by rfl) ⟨840320, by rfl⟩ : syracuseStep 1120427 = 1680641) B1680641
theorem B497839 : Blo 495792 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B497863 : Blo 495792 497863 := bstep (se 1 (by rfl) ⟨373397, by rfl⟩ : syracuseStep 497863 = 746795) B746795
theorem B497883 : Blo 495792 497883 := bstep (se 1 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 497883 = 746825) B746825
theorem B497959 : Blo 495792 497959 := bstep (se 1 (by rfl) ⟨373469, by rfl⟩ : syracuseStep 497959 = 746939) B746939
theorem B497999 : Blo 495792 497999 := bstep (se 1 (by rfl) ⟨373499, by rfl⟩ : syracuseStep 497999 = 746999) B746999
theorem B498015 : Blo 495792 498015 := bstep (se 1 (by rfl) ⟨373511, by rfl⟩ : syracuseStep 498015 = 747023) B747023
theorem B498043 : Blo 495792 498043 := bstep (se 1 (by rfl) ⟨373532, by rfl⟩ : syracuseStep 498043 = 747065) B747065
theorem B498095 : Blo 495792 498095 := bstep (se 1 (by rfl) ⟨373571, by rfl⟩ : syracuseStep 498095 = 747143) B747143
theorem B498119 : Blo 495792 498119 := bstep (se 1 (by rfl) ⟨373589, by rfl⟩ : syracuseStep 498119 = 747179) B747179
theorem B498139 : Blo 495792 498139 := bstep (se 1 (by rfl) ⟨373604, by rfl⟩ : syracuseStep 498139 = 747209) B747209
theorem B1677833 : Blo 495792 1677833 := bstep (se 2 (by rfl) ⟨629187, by rfl⟩ : syracuseStep 1677833 = 1258375) B1258375
theorem B14326307 : Blo 495792 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B498215 : Blo 495792 498215 := bstep (se 1 (by rfl) ⟨373661, by rfl⟩ : syracuseStep 498215 = 747323) B747323
theorem B498255 : Blo 495792 498255 := bstep (se 1 (by rfl) ⟨373691, by rfl⟩ : syracuseStep 498255 = 747383) B747383
theorem B498271 : Blo 495792 498271 := bstep (se 1 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 498271 = 747407) B747407
theorem B596603 : Blo 495792 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B498299 : Blo 495792 498299 := bstep (se 1 (by rfl) ⟨373724, by rfl⟩ : syracuseStep 498299 = 747449) B747449
theorem B498351 : Blo 495792 498351 := bstep (se 1 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 498351 = 747527) B747527
theorem B1120967 : Blo 495792 1120967 := bstep (se 1 (by rfl) ⟨840725, by rfl⟩ : syracuseStep 1120967 = 1681451) B1681451
theorem B498375 : Blo 495792 498375 := bstep (se 1 (by rfl) ⟨373781, by rfl⟩ : syracuseStep 498375 = 747563) B747563
theorem B498395 : Blo 495792 498395 := bstep (se 1 (by rfl) ⟨373796, by rfl⟩ : syracuseStep 498395 = 747593) B747593
theorem B498471 : Blo 495792 498471 := bstep (se 1 (by rfl) ⟨373853, by rfl⟩ : syracuseStep 498471 = 747707) B747707
theorem B498511 : Blo 495792 498511 := bstep (se 1 (by rfl) ⟨373883, by rfl⟩ : syracuseStep 498511 = 747767) B747767
theorem B498527 : Blo 495792 498527 := bstep (se 1 (by rfl) ⟨373895, by rfl⟩ : syracuseStep 498527 = 747791) B747791
theorem B498555 : Blo 495792 498555 := bstep (se 1 (by rfl) ⟨373916, by rfl⟩ : syracuseStep 498555 = 747833) B747833
theorem B596911 : Blo 495792 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B498607 : Blo 495792 498607 := bstep (se 1 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 498607 = 747911) B747911
theorem B498631 : Blo 495792 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B498651 : Blo 495792 498651 := bstep (se 1 (by rfl) ⟨373988, by rfl⟩ : syracuseStep 498651 = 747977) B747977
theorem B498727 : Blo 495792 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B4037681 : Blo 495792 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B498767 : Blo 495792 498767 := bstep (se 1 (by rfl) ⟨374075, by rfl⟩ : syracuseStep 498767 = 748151) B748151
theorem B498783 : Blo 495792 498783 := bstep (se 1 (by rfl) ⟨374087, by rfl⟩ : syracuseStep 498783 = 748175) B748175
theorem B498811 : Blo 495792 498811 := bstep (se 1 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 498811 = 748217) B748217
theorem B498863 : Blo 495792 498863 := bstep (se 1 (by rfl) ⟨374147, by rfl⟩ : syracuseStep 498863 = 748295) B748295
theorem B498887 : Blo 495792 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B498907 : Blo 495792 498907 := bstep (se 1 (by rfl) ⟨374180, by rfl⟩ : syracuseStep 498907 = 748361) B748361
theorem B498983 : Blo 495792 498983 := bstep (se 1 (by rfl) ⟨374237, by rfl⟩ : syracuseStep 498983 = 748475) B748475
theorem B499023 : Blo 495792 499023 := bstep (se 1 (by rfl) ⟨374267, by rfl⟩ : syracuseStep 499023 = 748535) B748535
theorem B499039 : Blo 495792 499039 := bstep (se 1 (by rfl) ⟨374279, by rfl⟩ : syracuseStep 499039 = 748559) B748559
theorem B1678697 : Blo 495792 1678697 := bstep (se 2 (by rfl) ⟨629511, by rfl⟩ : syracuseStep 1678697 = 1259023) B1259023
theorem B499067 : Blo 495792 499067 := bstep (se 1 (by rfl) ⟨374300, by rfl⟩ : syracuseStep 499067 = 748601) B748601
theorem B499119 : Blo 495792 499119 := bstep (se 1 (by rfl) ⟨374339, by rfl⟩ : syracuseStep 499119 = 748679) B748679
theorem B499143 : Blo 495792 499143 := bstep (se 1 (by rfl) ⟨374357, by rfl⟩ : syracuseStep 499143 = 748715) B748715
theorem B499163 : Blo 495792 499163 := bstep (se 1 (by rfl) ⟨374372, by rfl⟩ : syracuseStep 499163 = 748745) B748745
theorem B1121831 : Blo 495792 1121831 := bstep (se 1 (by rfl) ⟨841373, by rfl⟩ : syracuseStep 1121831 = 1682747) B1682747
theorem B499239 : Blo 495792 499239 := bstep (se 1 (by rfl) ⟨374429, by rfl⟩ : syracuseStep 499239 = 748859) B748859
theorem B499279 : Blo 495792 499279 := bstep (se 1 (by rfl) ⟨374459, by rfl⟩ : syracuseStep 499279 = 748919) B748919
theorem B499295 : Blo 495792 499295 := bstep (se 1 (by rfl) ⟨374471, by rfl⟩ : syracuseStep 499295 = 748943) B748943
theorem B2268769 : Blo 495792 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B499323 : Blo 495792 499323 := bstep (se 1 (by rfl) ⟨374492, by rfl⟩ : syracuseStep 499323 = 748985) B748985
theorem B499375 : Blo 495792 499375 := bstep (se 1 (by rfl) ⟨374531, by rfl⟩ : syracuseStep 499375 = 749063) B749063
theorem B499399 : Blo 495792 499399 := bstep (se 1 (by rfl) ⟨374549, by rfl⟩ : syracuseStep 499399 = 749099) B749099
theorem B3186391 : Blo 495792 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B499419 : Blo 495792 499419 := bstep (se 1 (by rfl) ⟨374564, by rfl⟩ : syracuseStep 499419 = 749129) B749129
theorem B499495 : Blo 495792 499495 := bstep (se 1 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 499495 = 749243) B749243
theorem B499535 : Blo 495792 499535 := bstep (se 1 (by rfl) ⟨374651, by rfl⟩ : syracuseStep 499535 = 749303) B749303
theorem B3022687 : Blo 495792 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B499551 : Blo 495792 499551 := bstep (se 1 (by rfl) ⟨374663, by rfl⟩ : syracuseStep 499551 = 749327) B749327
theorem B1122155 : Blo 495792 1122155 := bstep (se 1 (by rfl) ⟨841616, by rfl⟩ : syracuseStep 1122155 = 1683233) B1683233
theorem B499579 : Blo 495792 499579 := bstep (se 1 (by rfl) ⟨374684, by rfl⟩ : syracuseStep 499579 = 749369) B749369
theorem B1122209 : Blo 495792 1122209 := bstep (se 2 (by rfl) ⟨420828, by rfl⟩ : syracuseStep 1122209 = 841657) B841657
theorem B499631 : Blo 495792 499631 := bstep (se 1 (by rfl) ⟨374723, by rfl⟩ : syracuseStep 499631 = 749447) B749447
theorem B1679291 : Blo 495792 1679291 := bstep (se 1 (by rfl) ⟨1259468, by rfl⟩ : syracuseStep 1679291 = 2518937) B2518937
theorem B499655 : Blo 495792 499655 := bstep (se 1 (by rfl) ⟨374741, by rfl⟩ : syracuseStep 499655 = 749483) B749483
theorem B499675 : Blo 495792 499675 := bstep (se 1 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 499675 = 749513) B749513
theorem B630823 : Blo 495792 630823 := bstep (se 1 (by rfl) ⟨473117, by rfl⟩ : syracuseStep 630823 = 946235) B946235
theorem B499751 : Blo 495792 499751 := bstep (se 1 (by rfl) ⟨374813, by rfl⟩ : syracuseStep 499751 = 749627) B749627
theorem B499791 : Blo 495792 499791 := bstep (se 1 (by rfl) ⟨374843, by rfl⟩ : syracuseStep 499791 = 749687) B749687
theorem B794747 : Blo 495792 794747 := bstep (se 1 (by rfl) ⟨596060, by rfl⟩ : syracuseStep 794747 = 1192121) B1192121
theorem B532603 : Blo 495792 532603 := bstep (se 1 (by rfl) ⟨399452, by rfl⟩ : syracuseStep 532603 = 798905) B798905
theorem B16425109 : Blo 495792 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B1122551 : Blo 495792 1122551 := bstep (se 1 (by rfl) ⟨841913, by rfl⟩ : syracuseStep 1122551 = 1683827) B1683827
theorem B598367 : Blo 495792 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B631147 : Blo 495792 631147 := bstep (se 1 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 631147 = 946721) B946721
theorem B565723 : Blo 495792 565723 := bstep (se 1 (by rfl) ⟨424292, by rfl⟩ : syracuseStep 565723 = 848585) B848585
theorem B10756759 : Blo 495792 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B6038225 : Blo 495792 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B1123145 : Blo 495792 1123145 := bstep (se 2 (by rfl) ⟨421179, by rfl⟩ : syracuseStep 1123145 = 842359) B842359
theorem B2696111 : Blo 495792 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B533423 : Blo 495792 533423 := bstep (se 1 (by rfl) ⟨400067, by rfl⟩ : syracuseStep 533423 = 800135) B800135
theorem B959585 : Blo 495792 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B2401559 : Blo 495792 2401559 := bstep (se 1 (by rfl) ⟨1801169, by rfl⟩ : syracuseStep 2401559 = 3602339) B3602339
theorem B796009 : Blo 495792 796009 := bstep (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) B597007
theorem B1123937 : Blo 495792 1123937 := bstep (se 2 (by rfl) ⟨421476, by rfl⟩ : syracuseStep 1123937 = 842953) B842953
theorem B1681019 : Blo 495792 1681019 := bstep (se 1 (by rfl) ⟨1260764, by rfl⟩ : syracuseStep 1681019 = 2521529) B2521529
theorem B632443 : Blo 495792 632443 := bstep (se 1 (by rfl) ⟨474332, by rfl⟩ : syracuseStep 632443 = 948665) B948665
theorem B1681181 : Blo 495792 1681181 := bstep (se 3 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 1681181 = 630443) B630443
theorem B1124279 : Blo 495792 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B3778649 : Blo 495792 3778649 := bstep (se 2 (by rfl) ⟨1416993, by rfl⟩ : syracuseStep 3778649 = 2833987) B2833987
theorem B6138013 : Blo 495792 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B1058987 : Blo 495792 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B15280433 : Blo 495792 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B797111 : Blo 495792 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B1681883 : Blo 495792 1681883 := bstep (se 1 (by rfl) ⟨1261412, by rfl⟩ : syracuseStep 1681883 = 2522825) B2522825
theorem B1255945 : Blo 495792 1255945 := bstep (se 2 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 1255945 = 941959) B941959
theorem B2042491 : Blo 495792 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B764615 : Blo 495792 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B3189725 : Blo 495792 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B1682585 : Blo 495792 1682585 := bstep (se 2 (by rfl) ⟨630969, by rfl⟩ : syracuseStep 1682585 = 1261939) B1261939
theorem B2010359 : Blo 495792 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B798059 : Blo 495792 798059 := bstep (se 1 (by rfl) ⟨598544, by rfl⟩ : syracuseStep 798059 = 1197089) B1197089
theorem B4107763 : Blo 495792 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B3780107 : Blo 495792 3780107 := bstep (se 1 (by rfl) ⟨2835080, by rfl⟩ : syracuseStep 3780107 = 5670161) B5670161
theorem B569263 : Blo 495792 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B1257403 : Blo 495792 1257403 := bstep (se 1 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 1257403 = 1886105) B1886105
theorem B7155773 : Blo 495792 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B1683773 : Blo 495792 1683773 := bstep (se 3 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 1683773 = 631415) B631415
theorem B3027287 : Blo 495792 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B3584459 : Blo 495792 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B1192457 : Blo 495792 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B38810765 : Blo 495792 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B1684637 : Blo 495792 1684637 := bstep (se 3 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 1684637 = 631739) B631739
theorem B12301483 : Blo 495792 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B3782051 : Blo 495792 3782051 := bstep (se 1 (by rfl) ⟨2836538, by rfl⟩ : syracuseStep 3782051 = 5673077) B5673077
theorem B1685177 : Blo 495792 1685177 := bstep (se 2 (by rfl) ⟨631941, by rfl⟩ : syracuseStep 1685177 = 1263883) B1263883
theorem B1193687 : Blo 495792 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B2012921 : Blo 495792 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1914799 : Blo 495792 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B3225689 : Blo 495792 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1685771 : Blo 495792 1685771 := bstep (se 1 (by rfl) ⟨1264328, by rfl⟩ : syracuseStep 1685771 = 2528657) B2528657
theorem B1259995 : Blo 495792 1259995 := bstep (se 1 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 1259995 = 1889993) B1889993
theorem B1686041 : Blo 495792 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B2833487 : Blo 495792 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B1260623 : Blo 495792 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B2276599 : Blo 495792 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B4799735 : Blo 495792 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B2014607 : Blo 495792 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B1064335 : Blo 495792 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B1883857 : Blo 495792 1883857 := bstep (se 2 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 1883857 = 1412893) B1412893
theorem B1064659 : Blo 495792 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B1195735 : Blo 495792 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1261271 : Blo 495792 1261271 := bstep (se 1 (by rfl) ⟨945953, by rfl⟩ : syracuseStep 1261271 = 1891907) B1891907
theorem B8503055 : Blo 495792 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B3784481 : Blo 495792 3784481 := bstep (se 2 (by rfl) ⟨1419180, by rfl⟩ : syracuseStep 3784481 = 2838361) B2838361
theorem B1884161 : Blo 495792 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B1589327 : Blo 495792 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B2834513 : Blo 495792 2834513 := bstep (se 2 (by rfl) ⟨1062942, by rfl⟩ : syracuseStep 2834513 = 2125885) B2125885
theorem B2015549 : Blo 495792 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B10731851 : Blo 495792 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B7192907 : Blo 495792 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B639415 : Blo 495792 639415 := bstep (se 1 (by rfl) ⟨479561, by rfl⟩ : syracuseStep 639415 = 959123) B959123
theorem B1884617 : Blo 495792 1884617 := bstep (se 2 (by rfl) ⟨706731, by rfl⟩ : syracuseStep 1884617 = 1413463) B1413463
theorem B1065889 : Blo 495792 1065889 := bstep (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) B799417
theorem B1885103 : Blo 495792 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B15385841 : Blo 495792 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B1066231 : Blo 495792 1066231 := bstep (se 1 (by rfl) ⟨799673, by rfl⟩ : syracuseStep 1066231 = 1599347) B1599347
theorem B836959 : Blo 495792 836959 := bstep (se 1 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 836959 = 1255439) B1255439
theorem B837047 : Blo 495792 837047 := bstep (se 1 (by rfl) ⟨627785, by rfl⟩ : syracuseStep 837047 = 1255571) B1255571
theorem B1131995 : Blo 495792 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1787417 : Blo 495792 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B837641 : Blo 495792 837641 := bstep (se 2 (by rfl) ⟨314115, by rfl⟩ : syracuseStep 837641 = 628231) B628231
theorem B1886287 : Blo 495792 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B837803 : Blo 495792 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B1263863 : Blo 495792 1263863 := bstep (se 1 (by rfl) ⟨947897, by rfl⟩ : syracuseStep 1263863 = 1895795) B1895795
theorem B5687657 : Blo 495792 5687657 := bstep (se 2 (by rfl) ⟨2132871, by rfl⟩ : syracuseStep 5687657 = 4265743) B4265743
theorem B3230081 : Blo 495792 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B6834617 : Blo 495792 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B1198579 : Blo 495792 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B3590689 : Blo 495792 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B1886759 : Blo 495792 1886759 := bstep (se 1 (by rfl) ⟨1415069, by rfl⟩ : syracuseStep 1886759 = 2830139) B2830139
theorem B838201 : Blo 495792 838201 := bstep (se 2 (by rfl) ⟨314325, by rfl⟩ : syracuseStep 838201 = 628651) B628651
theorem B1788539 : Blo 495792 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B2837177 : Blo 495792 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B838343 : Blo 495792 838343 := bstep (se 1 (by rfl) ⟨628757, by rfl⟩ : syracuseStep 838343 = 1257515) B1257515
theorem B838505 : Blo 495792 838505 := bstep (se 2 (by rfl) ⟨314439, by rfl⟩ : syracuseStep 838505 = 628879) B628879
theorem B5393297 : Blo 495792 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B4246607 : Blo 495792 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B2510027 : Blo 495792 2510027 := bstep (se 1 (by rfl) ⟨1882520, by rfl⟩ : syracuseStep 2510027 = 3765041) B3765041
theorem B838903 : Blo 495792 838903 := bstep (se 1 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 838903 = 1258355) B1258355
theorem B1133929 : Blo 495792 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B19353005 : Blo 495792 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B839099 : Blo 495792 839099 := bstep (se 1 (by rfl) ⟨629324, by rfl⟩ : syracuseStep 839099 = 1258649) B1258649
theorem B1887731 : Blo 495792 1887731 := bstep (se 1 (by rfl) ⟨1415798, by rfl⟩ : syracuseStep 1887731 = 2831597) B2831597
theorem B839207 : Blo 495792 839207 := bstep (se 1 (by rfl) ⟨629405, by rfl⟩ : syracuseStep 839207 = 1258811) B1258811
theorem B1593017 : Blo 495792 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B16305953 : Blo 495792 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B839497 : Blo 495792 839497 := bstep (se 2 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 839497 = 629623) B629623
theorem B839531 : Blo 495792 839531 := bstep (se 1 (by rfl) ⟨629648, by rfl⟩ : syracuseStep 839531 = 1259297) B1259297
theorem B5394509 : Blo 495792 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B8605777 : Blo 495792 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B3592421 : Blo 495792 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B839929 : Blo 495792 839929 := bstep (se 2 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 839929 = 629947) B629947
theorem B12767705 : Blo 495792 12767705 := bstep (se 2 (by rfl) ⟨4787889, by rfl⟩ : syracuseStep 12767705 = 9575779) B9575779
theorem B840199 : Blo 495792 840199 := bstep (se 1 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 840199 = 1260299) B1260299
theorem B3199513 : Blo 495792 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B3592763 : Blo 495792 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B840631 : Blo 495792 840631 := bstep (se 1 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 840631 = 1260947) B1260947
theorem B840827 : Blo 495792 840827 := bstep (se 1 (by rfl) ⟨630620, by rfl⟩ : syracuseStep 840827 = 1261241) B1261241
theorem B2872523 : Blo 495792 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B841225 : Blo 495792 841225 := bstep (se 2 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 841225 = 630919) B630919
theorem B4773437 : Blo 495792 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B841387 : Blo 495792 841387 := bstep (se 1 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 841387 = 1262081) B1262081
theorem B1824631 : Blo 495792 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B841691 : Blo 495792 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B3889181 : Blo 495792 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B1136719 : Blo 495792 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B841927 : Blo 495792 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B2120023 : Blo 495792 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B1890647 : Blo 495792 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B842089 : Blo 495792 842089 := bstep (se 2 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 842089 = 631567) B631567
theorem B743855 : Blo 495792 743855 := bstep (se 1 (by rfl) ⟨557891, by rfl⟩ : syracuseStep 743855 = 1115783) B1115783
theorem B743945 : Blo 495792 743945 := bstep (se 2 (by rfl) ⟨278979, by rfl⟩ : syracuseStep 743945 = 557959) B557959
theorem B743975 : Blo 495792 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B744059 : Blo 495792 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B744185 : Blo 495792 744185 := bstep (se 2 (by rfl) ⟨279069, by rfl⟩ : syracuseStep 744185 = 558139) B558139
theorem B744287 : Blo 495792 744287 := bstep (se 1 (by rfl) ⟨558215, by rfl⟩ : syracuseStep 744287 = 1116431) B1116431
theorem B744299 : Blo 495792 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B711607 : Blo 495792 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B842683 : Blo 495792 842683 := bstep (se 1 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 842683 = 1264025) B1264025
theorem B842791 : Blo 495792 842791 := bstep (se 1 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 842791 = 1264187) B1264187
theorem B744527 : Blo 495792 744527 := bstep (se 1 (by rfl) ⟨558395, by rfl⟩ : syracuseStep 744527 = 1116791) B1116791
theorem B744647 : Blo 495792 744647 := bstep (se 1 (by rfl) ⟨558485, by rfl⟩ : syracuseStep 744647 = 1116971) B1116971
theorem B2841803 : Blo 495792 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B3398935 : Blo 495792 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B744809 : Blo 495792 744809 := bstep (se 2 (by rfl) ⟨279303, by rfl⟩ : syracuseStep 744809 = 558607) B558607
theorem B843115 : Blo 495792 843115 := bstep (se 1 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 843115 = 1264673) B1264673
theorem B941473 : Blo 495792 941473 := bstep (se 2 (by rfl) ⟨353052, by rfl⟩ : syracuseStep 941473 = 706105) B706105
theorem B744887 : Blo 495792 744887 := bstep (se 1 (by rfl) ⟨558665, by rfl⟩ : syracuseStep 744887 = 1117331) B1117331
theorem B744923 : Blo 495792 744923 := bstep (se 1 (by rfl) ⟨558692, by rfl⟩ : syracuseStep 744923 = 1117385) B1117385
theorem B1891937 : Blo 495792 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B2842235 : Blo 495792 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B745391 : Blo 495792 745391 := bstep (se 1 (by rfl) ⟨559043, by rfl⟩ : syracuseStep 745391 = 1118087) B1118087
theorem B7200697 : Blo 495792 7200697 := bstep (se 2 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 7200697 = 5400523) B5400523
theorem B942043 : Blo 495792 942043 := bstep (se 1 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 942043 = 1413065) B1413065
theorem B745481 : Blo 495792 745481 := bstep (se 2 (by rfl) ⟨279555, by rfl⟩ : syracuseStep 745481 = 559111) B559111
theorem B745511 : Blo 495792 745511 := bstep (se 1 (by rfl) ⟨559133, by rfl⟩ : syracuseStep 745511 = 1118267) B1118267
theorem B2121785 : Blo 495792 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B4317299 : Blo 495792 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B745595 : Blo 495792 745595 := bstep (se 1 (by rfl) ⟨559196, by rfl⟩ : syracuseStep 745595 = 1118393) B1118393
theorem B745721 : Blo 495792 745721 := bstep (se 2 (by rfl) ⟨279645, by rfl⟩ : syracuseStep 745721 = 559291) B559291
theorem B2515211 : Blo 495792 2515211 := bstep (se 1 (by rfl) ⟨1886408, by rfl⟩ : syracuseStep 2515211 = 3772817) B3772817
theorem B745823 : Blo 495792 745823 := bstep (se 1 (by rfl) ⟨559367, by rfl⟩ : syracuseStep 745823 = 1118735) B1118735
theorem B745835 : Blo 495792 745835 := bstep (se 1 (by rfl) ⟨559376, by rfl⟩ : syracuseStep 745835 = 1118753) B1118753
theorem B2843009 : Blo 495792 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B9069079 : Blo 495792 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B746063 : Blo 495792 746063 := bstep (se 1 (by rfl) ⟨559547, by rfl⟩ : syracuseStep 746063 = 1119095) B1119095
theorem B1696391 : Blo 495792 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B746183 : Blo 495792 746183 := bstep (se 1 (by rfl) ⟨559637, by rfl⟩ : syracuseStep 746183 = 1119275) B1119275
theorem B746345 : Blo 495792 746345 := bstep (se 2 (by rfl) ⟨279879, by rfl⟩ : syracuseStep 746345 = 559759) B559759
theorem B746423 : Blo 495792 746423 := bstep (se 1 (by rfl) ⟨559817, by rfl⟩ : syracuseStep 746423 = 1119635) B1119635
theorem B746459 : Blo 495792 746459 := bstep (se 1 (by rfl) ⟨559844, by rfl⟩ : syracuseStep 746459 = 1119689) B1119689
theorem B1008649 : Blo 495792 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B1893395 : Blo 495792 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1598579 : Blo 495792 1598579 := bstep (se 1 (by rfl) ⟨1198934, by rfl⟩ : syracuseStep 1598579 = 2397869) B2397869
theorem B2155673 : Blo 495792 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B5367001 : Blo 495792 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B1009039 : Blo 495792 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B746927 : Blo 495792 746927 := bstep (se 1 (by rfl) ⟨560195, by rfl⟩ : syracuseStep 746927 = 1120391) B1120391
theorem B1893851 : Blo 495792 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B747017 : Blo 495792 747017 := bstep (se 2 (by rfl) ⟨280131, by rfl⟩ : syracuseStep 747017 = 560263) B560263
theorem B747047 : Blo 495792 747047 := bstep (se 1 (by rfl) ⟨560285, by rfl⟩ : syracuseStep 747047 = 1120571) B1120571
theorem B747131 : Blo 495792 747131 := bstep (se 1 (by rfl) ⟨560348, by rfl⟩ : syracuseStep 747131 = 1120697) B1120697
theorem B2516669 : Blo 495792 2516669 := bstep (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) B943751
theorem B747257 : Blo 495792 747257 := bstep (se 2 (by rfl) ⟨280221, by rfl⟩ : syracuseStep 747257 = 560443) B560443
theorem B2516831 : Blo 495792 2516831 := bstep (se 1 (by rfl) ⟨1887623, by rfl⟩ : syracuseStep 2516831 = 3775247) B3775247
theorem B747359 : Blo 495792 747359 := bstep (se 1 (by rfl) ⟨560519, by rfl⟩ : syracuseStep 747359 = 1121039) B1121039
theorem B747371 : Blo 495792 747371 := bstep (se 1 (by rfl) ⟨560528, by rfl⟩ : syracuseStep 747371 = 1121057) B1121057
theorem B1796023 : Blo 495792 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B2123783 : Blo 495792 2123783 := bstep (se 1 (by rfl) ⟨1592837, by rfl⟩ : syracuseStep 2123783 = 3185675) B3185675
theorem B944207 : Blo 495792 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B747599 : Blo 495792 747599 := bstep (se 1 (by rfl) ⟨560699, by rfl⟩ : syracuseStep 747599 = 1121399) B1121399
theorem B747719 : Blo 495792 747719 := bstep (se 1 (by rfl) ⟨560789, by rfl⟩ : syracuseStep 747719 = 1121579) B1121579
theorem B3795173 : Blo 495792 3795173 := bstep (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) B711595
theorem B747881 : Blo 495792 747881 := bstep (se 2 (by rfl) ⟨280455, by rfl⟩ : syracuseStep 747881 = 560911) B560911
theorem B747959 : Blo 495792 747959 := bstep (se 1 (by rfl) ⟨560969, by rfl⟩ : syracuseStep 747959 = 1121939) B1121939
theorem B747995 : Blo 495792 747995 := bstep (se 1 (by rfl) ⟨560996, by rfl⟩ : syracuseStep 747995 = 1121993) B1121993
theorem B1895035 : Blo 495792 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B2845469 : Blo 495792 2845469 := bstep (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) B1067051
theorem B748463 : Blo 495792 748463 := bstep (se 1 (by rfl) ⟨561347, by rfl⟩ : syracuseStep 748463 = 1122695) B1122695
theorem B748553 : Blo 495792 748553 := bstep (se 2 (by rfl) ⟨280707, by rfl⟩ : syracuseStep 748553 = 561415) B561415
theorem B748583 : Blo 495792 748583 := bstep (se 1 (by rfl) ⟨561437, by rfl⟩ : syracuseStep 748583 = 1122875) B1122875
theorem B945209 : Blo 495792 945209 := bstep (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) B708907
theorem B748667 : Blo 495792 748667 := bstep (se 1 (by rfl) ⟨561500, by rfl⟩ : syracuseStep 748667 = 1123001) B1123001
theorem B748793 : Blo 495792 748793 := bstep (se 2 (by rfl) ⟨280797, by rfl⟩ : syracuseStep 748793 = 561595) B561595
theorem B748895 : Blo 495792 748895 := bstep (se 1 (by rfl) ⟨561671, by rfl⟩ : syracuseStep 748895 = 1123343) B1123343
theorem B748907 : Blo 495792 748907 := bstep (se 1 (by rfl) ⟨561680, by rfl⟩ : syracuseStep 748907 = 1123361) B1123361
theorem B1600987 : Blo 495792 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B749135 : Blo 495792 749135 := bstep (se 1 (by rfl) ⟨561851, by rfl⟩ : syracuseStep 749135 = 1123703) B1123703
theorem B4255355 : Blo 495792 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B749255 : Blo 495792 749255 := bstep (se 1 (by rfl) ⟨561941, by rfl⟩ : syracuseStep 749255 = 1123883) B1123883
theorem B1797881 : Blo 495792 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B749417 : Blo 495792 749417 := bstep (se 2 (by rfl) ⟨281031, by rfl⟩ : syracuseStep 749417 = 562063) B562063
theorem B1797997 : Blo 495792 1797997 := bstep (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) B674249
theorem B1896311 : Blo 495792 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B749495 : Blo 495792 749495 := bstep (se 1 (by rfl) ⟨562121, by rfl⟩ : syracuseStep 749495 = 1124243) B1124243
theorem B749531 : Blo 495792 749531 := bstep (se 1 (by rfl) ⟨562148, by rfl⟩ : syracuseStep 749531 = 1124297) B1124297
theorem B2126209 : Blo 495792 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B2519585 : Blo 495792 2519585 := bstep (se 2 (by rfl) ⟨944844, by rfl⟩ : syracuseStep 2519585 = 1889689) B1889689
theorem B1897283 : Blo 495792 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B947207 : Blo 495792 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B3765527 : Blo 495792 3765527 := bstep (se 1 (by rfl) ⟨2824145, by rfl⟩ : syracuseStep 3765527 = 5648291) B5648291
theorem B3831077 : Blo 495792 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B947639 : Blo 495792 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B2618825 : Blo 495792 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B947791 : Blo 495792 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B2684539 : Blo 495792 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B10385189 : Blo 495792 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B1341839 : Blo 495792 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B2685449 : Blo 495792 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B3766985 : Blo 495792 3766985 := bstep (se 2 (by rfl) ⟨1412619, by rfl⟩ : syracuseStep 3766985 = 2825239) B2825239
theorem B6388469 : Blo 495792 6388469 := bstep (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) B598919
theorem B2522663 : Blo 495792 2522663 := bstep (se 1 (by rfl) ⟨1891997, by rfl⟩ : syracuseStep 2522663 = 3783995) B3783995
theorem B851705 : Blo 495792 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B1343699 : Blo 495792 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B6062501 : Blo 495792 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B852553 : Blo 495792 852553 := bstep (se 2 (by rfl) ⟨319707, by rfl⟩ : syracuseStep 852553 = 639415) B639415
theorem B12092105 : Blo 495792 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B10257227 : Blo 495792 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B558031 : Blo 495792 558031 := bstep (se 1 (by rfl) ⟨418523, by rfl⟩ : syracuseStep 558031 = 837047) B837047
theorem B558427 : Blo 495792 558427 := bstep (se 1 (by rfl) ⟨418820, by rfl⟩ : syracuseStep 558427 = 837641) B837641
theorem B1344865 : Blo 495792 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B558535 : Blo 495792 558535 := bstep (se 1 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 558535 = 837803) B837803
theorem B4556411 : Blo 495792 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B1115945 : Blo 495792 1115945 := bstep (se 2 (by rfl) ⟨418479, by rfl⟩ : syracuseStep 1115945 = 836959) B836959
theorem B558895 : Blo 495792 558895 := bstep (se 1 (by rfl) ⟨419171, by rfl⟩ : syracuseStep 558895 = 838343) B838343
theorem B1345385 : Blo 495792 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B559003 : Blo 495792 559003 := bstep (se 1 (by rfl) ⟨419252, by rfl⟩ : syracuseStep 559003 = 838505) B838505
theorem B4786127 : Blo 495792 4786127 := bstep (se 1 (by rfl) ⟨3589595, by rfl⟩ : syracuseStep 4786127 = 7179191) B7179191
theorem B1673351 : Blo 495792 1673351 := bstep (se 1 (by rfl) ⟨1255013, by rfl⟩ : syracuseStep 1673351 = 2510027) B2510027
theorem B559399 : Blo 495792 559399 := bstep (se 1 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 559399 = 839099) B839099
theorem B559471 : Blo 495792 559471 := bstep (se 1 (by rfl) ⟨419603, by rfl⟩ : syracuseStep 559471 = 839207) B839207
theorem B3017189 : Blo 495792 3017189 := bstep (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) B565723
theorem B559687 : Blo 495792 559687 := bstep (se 1 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 559687 = 839531) B839531
theorem B2394697 : Blo 495792 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B2394947 : Blo 495792 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B1117007 : Blo 495792 1117007 := bstep (se 1 (by rfl) ⟨837755, by rfl⟩ : syracuseStep 1117007 = 1675511) B1675511
theorem B2558893 : Blo 495792 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B1117223 : Blo 495792 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B2395175 : Blo 495792 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1117403 : Blo 495792 1117403 := bstep (se 1 (by rfl) ⟨838052, by rfl⟩ : syracuseStep 1117403 = 1676105) B1676105
theorem B1674593 : Blo 495792 1674593 := bstep (se 2 (by rfl) ⟨627972, by rfl⟩ : syracuseStep 1674593 = 1255945) B1255945
theorem B4787585 : Blo 495792 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B1117601 : Blo 495792 1117601 := bstep (se 2 (by rfl) ⟨419100, by rfl⟩ : syracuseStep 1117601 = 838201) B838201
theorem B560551 : Blo 495792 560551 := bstep (se 1 (by rfl) ⟨420413, by rfl⟩ : syracuseStep 560551 = 840827) B840827
theorem B2723321 : Blo 495792 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B2526713 : Blo 495792 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B3182291 : Blo 495792 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2527037 : Blo 495792 2527037 := bstep (se 3 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 2527037 = 947639) B947639
theorem B6983533 : Blo 495792 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B3018653 : Blo 495792 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B1118159 : Blo 495792 1118159 := bstep (se 1 (by rfl) ⟨838619, by rfl⟩ : syracuseStep 1118159 = 1677239) B1677239
theorem B561127 : Blo 495792 561127 := bstep (se 1 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 561127 = 841691) B841691
theorem B495903 : Blo 495792 495903 := bstep (se 1 (by rfl) ⟨371927, by rfl⟩ : syracuseStep 495903 = 743855) B743855
theorem B1118537 : Blo 495792 1118537 := bstep (se 2 (by rfl) ⟨419451, by rfl⟩ : syracuseStep 1118537 = 838903) B838903
theorem B495963 : Blo 495792 495963 := bstep (se 1 (by rfl) ⟨371972, by rfl⟩ : syracuseStep 495963 = 743945) B743945
theorem B1118555 : Blo 495792 1118555 := bstep (se 1 (by rfl) ⟨838916, by rfl⟩ : syracuseStep 1118555 = 1677833) B1677833
theorem B495983 : Blo 495792 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B496039 : Blo 495792 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B1511905 : Blo 495792 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B496123 : Blo 495792 496123 := bstep (se 1 (by rfl) ⟨372092, by rfl⟩ : syracuseStep 496123 = 744185) B744185
theorem B496191 : Blo 495792 496191 := bstep (se 1 (by rfl) ⟨372143, by rfl⟩ : syracuseStep 496191 = 744287) B744287
theorem B496199 : Blo 495792 496199 := bstep (se 1 (by rfl) ⟨372149, by rfl⟩ : syracuseStep 496199 = 744299) B744299
theorem B2134649 : Blo 495792 2134649 := bstep (se 2 (by rfl) ⟨800493, by rfl⟩ : syracuseStep 2134649 = 1600987) B1600987
theorem B2691787 : Blo 495792 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B496351 : Blo 495792 496351 := bstep (se 1 (by rfl) ⟨372263, by rfl⟩ : syracuseStep 496351 = 744527) B744527
theorem B496431 : Blo 495792 496431 := bstep (se 1 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 496431 = 744647) B744647
theorem B496539 : Blo 495792 496539 := bstep (se 1 (by rfl) ⟨372404, by rfl⟩ : syracuseStep 496539 = 744809) B744809
theorem B1119131 : Blo 495792 1119131 := bstep (se 1 (by rfl) ⟨839348, by rfl⟩ : syracuseStep 1119131 = 1678697) B1678697
theorem B496591 : Blo 495792 496591 := bstep (se 1 (by rfl) ⟨372443, by rfl⟩ : syracuseStep 496591 = 744887) B744887
theorem B496615 : Blo 495792 496615 := bstep (se 1 (by rfl) ⟨372461, by rfl⟩ : syracuseStep 496615 = 744923) B744923
theorem B1119329 : Blo 495792 1119329 := bstep (se 2 (by rfl) ⟨419748, by rfl⟩ : syracuseStep 1119329 = 839497) B839497
theorem B2397329 : Blo 495792 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B759017 : Blo 495792 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B1676537 : Blo 495792 1676537 := bstep (se 2 (by rfl) ⟨628701, by rfl⟩ : syracuseStep 1676537 = 1257403) B1257403
theorem B496927 : Blo 495792 496927 := bstep (se 1 (by rfl) ⟨372695, by rfl⟩ : syracuseStep 496927 = 745391) B745391
theorem B1119527 : Blo 495792 1119527 := bstep (se 1 (by rfl) ⟨839645, by rfl⟩ : syracuseStep 1119527 = 1679291) B1679291
theorem B496987 : Blo 495792 496987 := bstep (se 1 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 496987 = 745481) B745481
theorem B497007 : Blo 495792 497007 := bstep (se 1 (by rfl) ⟨372755, by rfl⟩ : syracuseStep 497007 = 745511) B745511
theorem B1414523 : Blo 495792 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B529831 : Blo 495792 529831 := bstep (se 1 (by rfl) ⟨397373, by rfl⟩ : syracuseStep 529831 = 794747) B794747
theorem B497063 : Blo 495792 497063 := bstep (se 1 (by rfl) ⟨372797, by rfl⟩ : syracuseStep 497063 = 745595) B745595
theorem B11474369 : Blo 495792 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B497147 : Blo 495792 497147 := bstep (se 1 (by rfl) ⟨372860, by rfl⟩ : syracuseStep 497147 = 745721) B745721
theorem B1676807 : Blo 495792 1676807 := bstep (se 1 (by rfl) ⟨1257605, by rfl⟩ : syracuseStep 1676807 = 2515211) B2515211
theorem B497215 : Blo 495792 497215 := bstep (se 1 (by rfl) ⟨372911, by rfl⟩ : syracuseStep 497215 = 745823) B745823
theorem B497223 : Blo 495792 497223 := bstep (se 1 (by rfl) ⟨372917, by rfl⟩ : syracuseStep 497223 = 745835) B745835
theorem B1119905 : Blo 495792 1119905 := bstep (se 2 (by rfl) ⟨419964, by rfl⟩ : syracuseStep 1119905 = 839929) B839929
theorem B497375 : Blo 495792 497375 := bstep (se 1 (by rfl) ⟨373031, by rfl⟩ : syracuseStep 497375 = 746063) B746063
theorem B497455 : Blo 495792 497455 := bstep (se 1 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 497455 = 746183) B746183
theorem B497563 : Blo 495792 497563 := bstep (se 1 (by rfl) ⟨373172, by rfl⟩ : syracuseStep 497563 = 746345) B746345
theorem B497615 : Blo 495792 497615 := bstep (se 1 (by rfl) ⟨373211, by rfl⟩ : syracuseStep 497615 = 746423) B746423
theorem B497639 : Blo 495792 497639 := bstep (se 1 (by rfl) ⟨373229, by rfl⟩ : syracuseStep 497639 = 746459) B746459
theorem B1120265 : Blo 495792 1120265 := bstep (se 2 (by rfl) ⟨420099, by rfl⟩ : syracuseStep 1120265 = 840199) B840199
theorem B4266017 : Blo 495792 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B497951 : Blo 495792 497951 := bstep (se 1 (by rfl) ⟨373463, by rfl⟩ : syracuseStep 497951 = 746927) B746927
theorem B498011 : Blo 495792 498011 := bstep (se 1 (by rfl) ⟨373508, by rfl⟩ : syracuseStep 498011 = 747017) B747017
theorem B498031 : Blo 495792 498031 := bstep (se 1 (by rfl) ⟨373523, by rfl⟩ : syracuseStep 498031 = 747047) B747047
theorem B1120679 : Blo 495792 1120679 := bstep (se 1 (by rfl) ⟨840509, by rfl⟩ : syracuseStep 1120679 = 1681019) B1681019
theorem B498087 : Blo 495792 498087 := bstep (se 1 (by rfl) ⟨373565, by rfl⟩ : syracuseStep 498087 = 747131) B747131
theorem B1677779 : Blo 495792 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B498171 : Blo 495792 498171 := bstep (se 1 (by rfl) ⟨373628, by rfl⟩ : syracuseStep 498171 = 747257) B747257
theorem B1120787 : Blo 495792 1120787 := bstep (se 1 (by rfl) ⟨840590, by rfl⟩ : syracuseStep 1120787 = 1681181) B1681181
theorem B1677887 : Blo 495792 1677887 := bstep (se 1 (by rfl) ⟨1258415, by rfl⟩ : syracuseStep 1677887 = 2516831) B2516831
theorem B498239 : Blo 495792 498239 := bstep (se 1 (by rfl) ⟨373679, by rfl⟩ : syracuseStep 498239 = 747359) B747359
theorem B498247 : Blo 495792 498247 := bstep (se 1 (by rfl) ⟨373685, by rfl⟩ : syracuseStep 498247 = 747371) B747371
theorem B1120841 : Blo 495792 1120841 := bstep (se 2 (by rfl) ⟨420315, by rfl⟩ : syracuseStep 1120841 = 840631) B840631
theorem B1415855 : Blo 495792 1415855 := bstep (se 1 (by rfl) ⟨1061891, by rfl⟩ : syracuseStep 1415855 = 2123783) B2123783
theorem B629471 : Blo 495792 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B498399 : Blo 495792 498399 := bstep (se 1 (by rfl) ⟨373799, by rfl⟩ : syracuseStep 498399 = 747599) B747599
theorem B498479 : Blo 495792 498479 := bstep (se 1 (by rfl) ⟨373859, by rfl⟩ : syracuseStep 498479 = 747719) B747719
theorem B2530115 : Blo 495792 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B498587 : Blo 495792 498587 := bstep (se 1 (by rfl) ⟨373940, by rfl⟩ : syracuseStep 498587 = 747881) B747881
theorem B531407 : Blo 495792 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B498639 : Blo 495792 498639 := bstep (se 1 (by rfl) ⟨373979, by rfl⟩ : syracuseStep 498639 = 747959) B747959
theorem B1121255 : Blo 495792 1121255 := bstep (se 1 (by rfl) ⟨840941, by rfl⟩ : syracuseStep 1121255 = 1681883) B1681883
theorem B498663 : Blo 495792 498663 := bstep (se 1 (by rfl) ⟨373997, by rfl⟩ : syracuseStep 498663 = 747995) B747995
theorem B498975 : Blo 495792 498975 := bstep (se 1 (by rfl) ⟨374231, by rfl⟩ : syracuseStep 498975 = 748463) B748463
theorem B499035 : Blo 495792 499035 := bstep (se 1 (by rfl) ⟨374276, by rfl⟩ : syracuseStep 499035 = 748553) B748553
theorem B1121633 : Blo 495792 1121633 := bstep (se 2 (by rfl) ⟨420612, by rfl⟩ : syracuseStep 1121633 = 841225) B841225
theorem B499055 : Blo 495792 499055 := bstep (se 1 (by rfl) ⟨374291, by rfl⟩ : syracuseStep 499055 = 748583) B748583
theorem B499111 : Blo 495792 499111 := bstep (se 1 (by rfl) ⟨374333, by rfl⟩ : syracuseStep 499111 = 748667) B748667
theorem B1121723 : Blo 495792 1121723 := bstep (se 1 (by rfl) ⟨841292, by rfl⟩ : syracuseStep 1121723 = 1682585) B1682585
theorem B3579385 : Blo 495792 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B499195 : Blo 495792 499195 := bstep (se 1 (by rfl) ⟨374396, by rfl⟩ : syracuseStep 499195 = 748793) B748793
theorem B1121849 : Blo 495792 1121849 := bstep (se 2 (by rfl) ⟨420693, by rfl⟩ : syracuseStep 1121849 = 841387) B841387
theorem B499263 : Blo 495792 499263 := bstep (se 1 (by rfl) ⟨374447, by rfl⟩ : syracuseStep 499263 = 748895) B748895
theorem B499271 : Blo 495792 499271 := bstep (se 1 (by rfl) ⟨374453, by rfl⟩ : syracuseStep 499271 = 748907) B748907
theorem B499423 : Blo 495792 499423 := bstep (se 1 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 499423 = 749135) B749135
theorem B499503 : Blo 495792 499503 := bstep (se 1 (by rfl) ⟨374627, by rfl⟩ : syracuseStep 499503 = 749255) B749255
theorem B499611 : Blo 495792 499611 := bstep (se 1 (by rfl) ⟨374708, by rfl⟩ : syracuseStep 499611 = 749417) B749417
theorem B499663 : Blo 495792 499663 := bstep (se 1 (by rfl) ⟨374747, by rfl⟩ : syracuseStep 499663 = 749495) B749495
theorem B499687 : Blo 495792 499687 := bstep (se 1 (by rfl) ⟨374765, by rfl⟩ : syracuseStep 499687 = 749531) B749531
theorem B10756145 : Blo 495792 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B1122515 : Blo 495792 1122515 := bstep (se 1 (by rfl) ⟨841886, by rfl⟩ : syracuseStep 1122515 = 1683773) B1683773
theorem B1122569 : Blo 495792 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B794971 : Blo 495792 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B1679723 : Blo 495792 1679723 := bstep (se 1 (by rfl) ⟨1259792, by rfl⟩ : syracuseStep 1679723 = 2519585) B2519585
theorem B2826697 : Blo 495792 2826697 := bstep (se 2 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 2826697 = 2120023) B2120023
theorem B1122785 : Blo 495792 1122785 := bstep (se 2 (by rfl) ⟨421044, by rfl⟩ : syracuseStep 1122785 = 842089) B842089
theorem B1679993 : Blo 495792 1679993 := bstep (se 2 (by rfl) ⟨629997, by rfl⟩ : syracuseStep 1679993 = 1259995) B1259995
theorem B631471 : Blo 495792 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B1123091 : Blo 495792 1123091 := bstep (se 1 (by rfl) ⟨842318, by rfl⟩ : syracuseStep 1123091 = 1684637) B1684637
theorem B1123451 : Blo 495792 1123451 := bstep (se 1 (by rfl) ⟨842588, by rfl⟩ : syracuseStep 1123451 = 1685177) B1685177
theorem B795791 : Blo 495792 795791 := bstep (se 1 (by rfl) ⟨596843, by rfl⟩ : syracuseStep 795791 = 1193687) B1193687
theorem B6923459 : Blo 495792 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B795881 : Blo 495792 795881 := bstep (se 2 (by rfl) ⟨298455, by rfl⟩ : syracuseStep 795881 = 596911) B596911
theorem B1123577 : Blo 495792 1123577 := bstep (se 2 (by rfl) ⟨421341, by rfl⟩ : syracuseStep 1123577 = 842683) B842683
theorem B1123721 : Blo 495792 1123721 := bstep (se 2 (by rfl) ⟨421395, by rfl⟩ : syracuseStep 1123721 = 842791) B842791
theorem B1123847 : Blo 495792 1123847 := bstep (se 1 (by rfl) ⟨842885, by rfl⟩ : syracuseStep 1123847 = 1685771) B1685771
theorem B894559 : Blo 495792 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B1124027 : Blo 495792 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B4531913 : Blo 495792 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B1124153 : Blo 495792 1124153 := bstep (se 2 (by rfl) ⟨421557, by rfl⟩ : syracuseStep 1124153 = 843115) B843115
theorem B1419113 : Blo 495792 1419113 := bstep (se 2 (by rfl) ⟨532167, by rfl⟩ : syracuseStep 1419113 = 1064335) B1064335
theorem B1255297 : Blo 495792 1255297 := bstep (se 2 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 1255297 = 941473) B941473
theorem B4794349 : Blo 495792 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B3025025 : Blo 495792 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B1419545 : Blo 495792 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B1681775 : Blo 495792 1681775 := bstep (se 1 (by rfl) ⟨1261331, by rfl⟩ : syracuseStep 1681775 = 2522663) B2522663
theorem B567803 : Blo 495792 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B1256057 : Blo 495792 1256057 := bstep (se 2 (by rfl) ⟨471021, by rfl⟩ : syracuseStep 1256057 = 942043) B942043
theorem B1256107 : Blo 495792 1256107 := bstep (se 1 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 1256107 = 1884161) B1884161
theorem B1059551 : Blo 495792 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B21900145 : Blo 495792 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B7154567 : Blo 495792 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B4795271 : Blo 495792 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1256411 : Blo 495792 1256411 := bstep (se 1 (by rfl) ⟨942308, by rfl⟩ : syracuseStep 1256411 = 1884617) B1884617
theorem B621849635 : Blo 495792 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1420411 : Blo 495792 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B1256735 : Blo 495792 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B1191611 : Blo 495792 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B1683179 : Blo 495792 1683179 := bstep (se 1 (by rfl) ⟨1262384, by rfl⟩ : syracuseStep 1683179 = 2524769) B2524769
theorem B7156001 : Blo 495792 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B1421641 : Blo 495792 1421641 := bstep (se 2 (by rfl) ⟨533115, by rfl⟩ : syracuseStep 1421641 = 1066231) B1066231
theorem B2732395 : Blo 495792 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B1257839 : Blo 495792 1257839 := bstep (se 1 (by rfl) ⟨943379, by rfl⟩ : syracuseStep 1257839 = 1886759) B1886759
theorem B1061345 : Blo 495792 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B1421995 : Blo 495792 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B1684151 : Blo 495792 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B2831071 : Blo 495792 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B1258487 : Blo 495792 1258487 := bstep (se 1 (by rfl) ⟨943865, by rfl⟩ : syracuseStep 1258487 = 1887731) B1887731
theorem B1062011 : Blo 495792 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B1422461 : Blo 495792 1422461 := bstep (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) B533423
theorem B1848685 : Blo 495792 1848685 := bstep (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) B693257
theorem B636479 : Blo 495792 636479 := bstep (se 1 (by rfl) ⟨477359, by rfl⟩ : syracuseStep 636479 = 954719) B954719
theorem B20363399 : Blo 495792 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B1915015 : Blo 495792 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B1882703 : Blo 495792 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B1686095 : Blo 495792 1686095 := bstep (se 1 (by rfl) ⟨1264571, by rfl⟩ : syracuseStep 1686095 = 2529143) B2529143
theorem B1882871 : Blo 495792 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B1260431 : Blo 495792 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B9550871 : Blo 495792 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B5684741 : Blo 495792 5684741 := bstep (se 4 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 5684741 = 1065889) B1065889
theorem B1261291 : Blo 495792 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B10371149 : Blo 495792 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B1130927 : Blo 495792 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B2834945 : Blo 495792 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B1262263 : Blo 495792 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B1065719 : Blo 495792 1065719 := bstep (se 1 (by rfl) ⟨799289, by rfl⟩ : syracuseStep 1065719 = 1598579) B1598579
theorem B1262567 : Blo 495792 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B705991 : Blo 495792 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B16401977 : Blo 495792 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B4769437 : Blo 495792 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B1590941 : Blo 495792 1590941 := bstep (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) B596603
theorem B509743 : Blo 495792 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B1263721 : Blo 495792 1263721 := bstep (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) B947791
theorem B2836903 : Blo 495792 2836903 := bstep (se 1 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 2836903 = 4255355) B4255355
theorem B1264207 : Blo 495792 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B21908069 : Blo 495792 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B4770515 : Blo 495792 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B2018191 : Blo 495792 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1264855 : Blo 495792 1264855 := bstep (se 1 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 1264855 = 1897283) B1897283
theorem B25873843 : Blo 495792 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B2510351 : Blo 495792 2510351 := bstep (se 1 (by rfl) ⟨1882763, by rfl⟩ : syracuseStep 2510351 = 3765527) B3765527
theorem B2150459 : Blo 495792 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B3035465 : Blo 495792 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B1790299 : Blo 495792 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B2511323 : Blo 495792 2511323 := bstep (se 1 (by rfl) ⟨1883492, by rfl⟩ : syracuseStep 2511323 = 3766985) B3766985
theorem B1888991 : Blo 495792 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B840415 : Blo 495792 840415 := bstep (se 1 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 840415 = 1260623) B1260623
theorem B3199823 : Blo 495792 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B2511809 : Blo 495792 2511809 := bstep (se 2 (by rfl) ⟨941928, by rfl⟩ : syracuseStep 2511809 = 1883857) B1883857
theorem B4248521 : Blo 495792 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B1594313 : Blo 495792 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B840847 : Blo 495792 840847 := bstep (se 1 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 840847 = 1261271) B1261271
theorem B841097 : Blo 495792 841097 := bstep (se 2 (by rfl) ⟨315411, by rfl⟩ : syracuseStep 841097 = 630823) B630823
theorem B1889675 : Blo 495792 1889675 := bstep (se 1 (by rfl) ⟨1417256, by rfl⟩ : syracuseStep 1889675 = 2834513) B2834513
theorem B710137 : Blo 495792 710137 := bstep (se 2 (by rfl) ⟨266301, by rfl⟩ : syracuseStep 710137 = 532603) B532603
theorem B841529 : Blo 495792 841529 := bstep (se 2 (by rfl) ⟨315573, by rfl⟩ : syracuseStep 841529 = 631147) B631147
theorem B14342345 : Blo 495792 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B1595645 : Blo 495792 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B743771 : Blo 495792 743771 := bstep (se 1 (by rfl) ⟨557828, by rfl⟩ : syracuseStep 743771 = 1115657) B1115657
theorem B9558557 : Blo 495792 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B743999 : Blo 495792 743999 := bstep (se 1 (by rfl) ⟨557999, by rfl⟩ : syracuseStep 743999 = 1115999) B1115999
theorem B744119 : Blo 495792 744119 := bstep (se 1 (by rfl) ⟨558089, by rfl⟩ : syracuseStep 744119 = 1116179) B1116179
theorem B842575 : Blo 495792 842575 := bstep (se 1 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 842575 = 1263863) B1263863
theorem B1203023 : Blo 495792 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B744347 : Blo 495792 744347 := bstep (se 1 (by rfl) ⟨558260, by rfl⟩ : syracuseStep 744347 = 1116521) B1116521
theorem B3791771 : Blo 495792 3791771 := bstep (se 1 (by rfl) ⟨2843828, by rfl⟩ : syracuseStep 3791771 = 5687657) B5687657
theorem B2153387 : Blo 495792 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B1891451 : Blo 495792 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B2120843 : Blo 495792 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B3595531 : Blo 495792 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B744743 : Blo 495792 744743 := bstep (se 1 (by rfl) ⟨558557, by rfl⟩ : syracuseStep 744743 = 1117115) B1117115
theorem B744827 : Blo 495792 744827 := bstep (se 1 (by rfl) ⟨558620, by rfl⟩ : syracuseStep 744827 = 1117241) B1117241
theorem B1596887 : Blo 495792 1596887 := bstep (se 1 (by rfl) ⟨1197665, by rfl⟩ : syracuseStep 1596887 = 2395331) B2395331
theorem B744953 : Blo 495792 744953 := bstep (se 2 (by rfl) ⟨279357, by rfl⟩ : syracuseStep 744953 = 558715) B558715
theorem B843257 : Blo 495792 843257 := bstep (se 2 (by rfl) ⟨316221, by rfl⟩ : syracuseStep 843257 = 632443) B632443
theorem B745055 : Blo 495792 745055 := bstep (se 1 (by rfl) ⟨558791, by rfl⟩ : syracuseStep 745055 = 1117583) B1117583
theorem B12902003 : Blo 495792 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B745271 : Blo 495792 745271 := bstep (se 1 (by rfl) ⟨558953, by rfl⟩ : syracuseStep 745271 = 1117907) B1117907
theorem B3596339 : Blo 495792 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B2515049 : Blo 495792 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B745577 : Blo 495792 745577 := bstep (se 2 (by rfl) ⟨279591, by rfl⟩ : syracuseStep 745577 = 559183) B559183
theorem B8184017 : Blo 495792 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B8511803 : Blo 495792 8511803 := bstep (se 1 (by rfl) ⟨6383852, by rfl⟩ : syracuseStep 8511803 = 12767705) B12767705
theorem B745895 : Blo 495792 745895 := bstep (se 1 (by rfl) ⟨559421, by rfl⟩ : syracuseStep 745895 = 1118843) B1118843
theorem B1794479 : Blo 495792 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B745979 : Blo 495792 745979 := bstep (se 1 (by rfl) ⟨559484, by rfl⟩ : syracuseStep 745979 = 1118969) B1118969
theorem B746105 : Blo 495792 746105 := bstep (se 2 (by rfl) ⟨279789, by rfl⟩ : syracuseStep 746105 = 559579) B559579
theorem B1139321 : Blo 495792 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1598105 : Blo 495792 1598105 := bstep (se 2 (by rfl) ⟨599289, by rfl⟩ : syracuseStep 1598105 = 1198579) B1198579
theorem B746159 : Blo 495792 746159 := bstep (se 1 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 746159 = 1119239) B1119239
theorem B746207 : Blo 495792 746207 := bstep (se 1 (by rfl) ⟨559655, by rfl⟩ : syracuseStep 746207 = 1119311) B1119311
theorem B746471 : Blo 495792 746471 := bstep (se 1 (by rfl) ⟨559853, by rfl⟩ : syracuseStep 746471 = 1119707) B1119707
theorem B2516183 : Blo 495792 2516183 := bstep (se 1 (by rfl) ⟨1887137, by rfl⟩ : syracuseStep 2516183 = 3774275) B3774275
theorem B746729 : Blo 495792 746729 := bstep (se 2 (by rfl) ⟨280023, by rfl⟩ : syracuseStep 746729 = 560047) B560047
theorem B746783 : Blo 495792 746783 := bstep (se 1 (by rfl) ⟨560087, by rfl⟩ : syracuseStep 746783 = 1120175) B1120175
theorem B746951 : Blo 495792 746951 := bstep (se 1 (by rfl) ⟨560213, by rfl⟩ : syracuseStep 746951 = 1120427) B1120427
theorem B2844193 : Blo 495792 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B747305 : Blo 495792 747305 := bstep (se 2 (by rfl) ⟨280239, by rfl⟩ : syracuseStep 747305 = 560479) B560479
theorem B747311 : Blo 495792 747311 := bstep (se 1 (by rfl) ⟨560483, by rfl⟩ : syracuseStep 747311 = 1120967) B1120967
theorem B1894535 : Blo 495792 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B747785 : Blo 495792 747785 := bstep (se 2 (by rfl) ⟨280419, by rfl⟩ : syracuseStep 747785 = 560839) B560839
theorem B747887 : Blo 495792 747887 := bstep (se 1 (by rfl) ⟨560915, by rfl⟩ : syracuseStep 747887 = 1121831) B1121831
theorem B1894823 : Blo 495792 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B748103 : Blo 495792 748103 := bstep (se 1 (by rfl) ⟨561077, by rfl⟩ : syracuseStep 748103 = 1122155) B1122155
theorem B748139 : Blo 495792 748139 := bstep (se 1 (by rfl) ⟨561104, by rfl⟩ : syracuseStep 748139 = 1122209) B1122209
theorem B2878199 : Blo 495792 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B748367 : Blo 495792 748367 := bstep (se 1 (by rfl) ⟨561275, by rfl⟩ : syracuseStep 748367 = 1122551) B1122551
theorem B1895339 : Blo 495792 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B4025483 : Blo 495792 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B748763 : Blo 495792 748763 := bstep (se 1 (by rfl) ⟨561572, by rfl⟩ : syracuseStep 748763 = 1123145) B1123145
theorem B1797407 : Blo 495792 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B748937 : Blo 495792 748937 := bstep (se 2 (by rfl) ⟨280851, by rfl⟩ : syracuseStep 748937 = 561703) B561703
theorem B1437115 : Blo 495792 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B1601039 : Blo 495792 1601039 := bstep (se 1 (by rfl) ⟨1200779, by rfl⟩ : syracuseStep 1601039 = 2401559) B2401559
theorem B749291 : Blo 495792 749291 := bstep (se 1 (by rfl) ⟨561968, by rfl⟩ : syracuseStep 749291 = 1123937) B1123937
theorem B749519 : Blo 495792 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B2519099 : Blo 495792 2519099 := bstep (se 1 (by rfl) ⟨1889324, by rfl⟩ : syracuseStep 2519099 = 3778649) B3778649
theorem B10186955 : Blo 495792 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B1896979 : Blo 495792 1896979 := bstep (se 1 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 1896979 = 2845469) B2845469
theorem B2126483 : Blo 495792 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B1340239 : Blo 495792 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B2520071 : Blo 495792 2520071 := bstep (se 1 (by rfl) ⟨1890053, by rfl⟩ : syracuseStep 2520071 = 3780107) B3780107
theorem B38925461 : Blo 495792 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B2553065 : Blo 495792 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B2520557 : Blo 495792 2520557 := bstep (se 3 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 2520557 = 945209) B945209
theorem B173930165 : Blo 495792 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B2554051 : Blo 495792 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B2521367 : Blo 495792 2521367 := bstep (se 1 (by rfl) ⟨1891025, by rfl⟩ : syracuseStep 2521367 = 3782051) B3782051
theorem B2128157 : Blo 495792 2128157 := bstep (se 3 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 2128157 = 798059) B798059
theorem B1341947 : Blo 495792 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B948809 : Blo 495792 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B4258979 : Blo 495792 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B1343071 : Blo 495792 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B4030249 : Blo 495792 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B5668703 : Blo 495792 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B2522987 : Blo 495792 2522987 := bstep (se 1 (by rfl) ⟨1892240, by rfl⟩ : syracuseStep 2522987 = 3784481) B3784481
theorem B9600929 : Blo 495792 9600929 := bstep (se 2 (by rfl) ⟨3600348, by rfl⟩ : syracuseStep 9600929 = 7200697) B7200697
theorem B6914099 : Blo 495792 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B8061403 : Blo 495792 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B3768929 : Blo 495792 3768929 := bstep (se 2 (by rfl) ⟨1413348, by rfl⟩ : syracuseStep 3768929 = 2826697) B2826697
theorem B3015805 : Blo 495792 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B4785277 : Blo 495792 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B1115567 : Blo 495792 1115567 := bstep (se 1 (by rfl) ⟨836675, by rfl⟩ : syracuseStep 1115567 = 1673351) B1673351
theorem B3180343 : Blo 495792 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B6359249 : Blo 495792 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B1116395 : Blo 495792 1116395 := bstep (se 1 (by rfl) ⟨837296, by rfl⟩ : syracuseStep 1116395 = 1674593) B1674593
theorem B1673567 : Blo 495792 1673567 := bstep (se 1 (by rfl) ⟨1255175, by rfl⟩ : syracuseStep 1673567 = 2510351) B2510351
theorem B1673729 : Blo 495792 1673729 := bstep (se 2 (by rfl) ⟨627648, by rfl⟩ : syracuseStep 1673729 = 1255297) B1255297
theorem B6392465 : Blo 495792 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B1674215 : Blo 495792 1674215 := bstep (se 1 (by rfl) ⟨1255661, by rfl⟩ : syracuseStep 1674215 = 2511323) B2511323
theorem B2133215 : Blo 495792 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B1674539 : Blo 495792 1674539 := bstep (se 1 (by rfl) ⟨1255904, by rfl⟩ : syracuseStep 1674539 = 2511809) B2511809
theorem B1117691 : Blo 495792 1117691 := bstep (se 1 (by rfl) ⟨838268, by rfl⟩ : syracuseStep 1117691 = 1676537) B1676537
theorem B1674809 : Blo 495792 1674809 := bstep (se 2 (by rfl) ⟨628053, by rfl⟩ : syracuseStep 1674809 = 1256107) B1256107
theorem B560731 : Blo 495792 560731 := bstep (se 1 (by rfl) ⟨420548, by rfl⟩ : syracuseStep 560731 = 841097) B841097
theorem B1117871 : Blo 495792 1117871 := bstep (se 1 (by rfl) ⟨838403, by rfl⟩ : syracuseStep 1117871 = 1676807) B1676807
theorem B29200193 : Blo 495792 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B2690921 : Blo 495792 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B561019 : Blo 495792 561019 := bstep (se 1 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 561019 = 841529) B841529
theorem B3411857 : Blo 495792 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B495847 : Blo 495792 495847 := bstep (se 1 (by rfl) ⟨371885, by rfl⟩ : syracuseStep 495847 = 743771) B743771
theorem B1118519 : Blo 495792 1118519 := bstep (se 1 (by rfl) ⟨838889, by rfl⟩ : syracuseStep 1118519 = 1677779) B1677779
theorem B495999 : Blo 495792 495999 := bstep (se 1 (by rfl) ⟨371999, by rfl⟩ : syracuseStep 495999 = 743999) B743999
theorem B1118591 : Blo 495792 1118591 := bstep (se 1 (by rfl) ⟨838943, by rfl⟩ : syracuseStep 1118591 = 1677887) B1677887
theorem B496079 : Blo 495792 496079 := bstep (se 1 (by rfl) ⟨372059, by rfl⟩ : syracuseStep 496079 = 744119) B744119
theorem B496231 : Blo 495792 496231 := bstep (se 1 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 496231 = 744347) B744347
theorem B2527847 : Blo 495792 2527847 := bstep (se 1 (by rfl) ⟨1895885, by rfl⟩ : syracuseStep 2527847 = 3791771) B3791771
theorem B496495 : Blo 495792 496495 := bstep (se 1 (by rfl) ⟨372371, by rfl⟩ : syracuseStep 496495 = 744743) B744743
theorem B496551 : Blo 495792 496551 := bstep (se 1 (by rfl) ⟨372413, by rfl⟩ : syracuseStep 496551 = 744827) B744827
theorem B496635 : Blo 495792 496635 := bstep (se 1 (by rfl) ⟨372476, by rfl⟩ : syracuseStep 496635 = 744953) B744953
theorem B562171 : Blo 495792 562171 := bstep (se 1 (by rfl) ⟨421628, by rfl⟩ : syracuseStep 562171 = 843257) B843257
theorem B496703 : Blo 495792 496703 := bstep (se 1 (by rfl) ⟨372527, by rfl⟩ : syracuseStep 496703 = 745055) B745055
theorem B9311377 : Blo 495792 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B496847 : Blo 495792 496847 := bstep (se 1 (by rfl) ⟨372635, by rfl⟩ : syracuseStep 496847 = 745271) B745271
theorem B1676699 : Blo 495792 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B497051 : Blo 495792 497051 := bstep (se 1 (by rfl) ⟨372788, by rfl⟩ : syracuseStep 497051 = 745577) B745577
theorem B5674535 : Blo 495792 5674535 := bstep (se 1 (by rfl) ⟨4255901, by rfl⟩ : syracuseStep 5674535 = 8511803) B8511803
theorem B1119815 : Blo 495792 1119815 := bstep (se 1 (by rfl) ⟨839861, by rfl⟩ : syracuseStep 1119815 = 1679723) B1679723
theorem B497263 : Blo 495792 497263 := bstep (se 1 (by rfl) ⟨372947, by rfl⟩ : syracuseStep 497263 = 745895) B745895
theorem B497319 : Blo 495792 497319 := bstep (se 1 (by rfl) ⟨372989, by rfl⟩ : syracuseStep 497319 = 745979) B745979
theorem B497403 : Blo 495792 497403 := bstep (se 1 (by rfl) ⟨373052, by rfl⟩ : syracuseStep 497403 = 746105) B746105
theorem B1119995 : Blo 495792 1119995 := bstep (se 1 (by rfl) ⟨839996, by rfl⟩ : syracuseStep 1119995 = 1679993) B1679993
theorem B759547 : Blo 495792 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B497439 : Blo 495792 497439 := bstep (se 1 (by rfl) ⟨373079, by rfl⟩ : syracuseStep 497439 = 746159) B746159
theorem B3643193 : Blo 495792 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B497471 : Blo 495792 497471 := bstep (se 1 (by rfl) ⟨373103, by rfl⟩ : syracuseStep 497471 = 746207) B746207
theorem B497647 : Blo 495792 497647 := bstep (se 1 (by rfl) ⟨373235, by rfl⟩ : syracuseStep 497647 = 746471) B746471
theorem B6789109 : Blo 495792 6789109 := bstep (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) B636479
theorem B2529305 : Blo 495792 2529305 := bstep (se 2 (by rfl) ⟨948489, by rfl⟩ : syracuseStep 2529305 = 1896979) B1896979
theorem B1677455 : Blo 495792 1677455 := bstep (se 1 (by rfl) ⟨1258091, by rfl⟩ : syracuseStep 1677455 = 2516183) B2516183
theorem B530587 : Blo 495792 530587 := bstep (se 1 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 530587 = 795881) B795881
theorem B497819 : Blo 495792 497819 := bstep (se 1 (by rfl) ⟨373364, by rfl⟩ : syracuseStep 497819 = 746729) B746729
theorem B497855 : Blo 495792 497855 := bstep (se 1 (by rfl) ⟨373391, by rfl⟩ : syracuseStep 497855 = 746783) B746783
theorem B3774761 : Blo 495792 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1120553 : Blo 495792 1120553 := bstep (se 2 (by rfl) ⟨420207, by rfl⟩ : syracuseStep 1120553 = 840415) B840415
theorem B497967 : Blo 495792 497967 := bstep (se 1 (by rfl) ⟨373475, by rfl⟩ : syracuseStep 497967 = 746951) B746951
theorem B3021275 : Blo 495792 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B498203 : Blo 495792 498203 := bstep (se 1 (by rfl) ⟨373652, by rfl⟩ : syracuseStep 498203 = 747305) B747305
theorem B498207 : Blo 495792 498207 := bstep (se 1 (by rfl) ⟨373655, by rfl⟩ : syracuseStep 498207 = 747311) B747311
theorem B3578525 : Blo 495792 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B1514141 : Blo 495792 1514141 := bstep (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) B567803
theorem B498523 : Blo 495792 498523 := bstep (se 1 (by rfl) ⟨373892, by rfl⟩ : syracuseStep 498523 = 747785) B747785
theorem B1121129 : Blo 495792 1121129 := bstep (se 2 (by rfl) ⟨420423, by rfl⟩ : syracuseStep 1121129 = 840847) B840847
theorem B1121183 : Blo 495792 1121183 := bstep (se 1 (by rfl) ⟨840887, by rfl⟩ : syracuseStep 1121183 = 1681775) B1681775
theorem B498591 : Blo 495792 498591 := bstep (se 1 (by rfl) ⟨373943, by rfl⟩ : syracuseStep 498591 = 747887) B747887
theorem B498735 : Blo 495792 498735 := bstep (se 1 (by rfl) ⟨374051, by rfl⟩ : syracuseStep 498735 = 748103) B748103
theorem B498759 : Blo 495792 498759 := bstep (se 1 (by rfl) ⟨374069, by rfl⟩ : syracuseStep 498759 = 748139) B748139
theorem B2464913 : Blo 495792 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B498911 : Blo 495792 498911 := bstep (se 1 (by rfl) ⟨374183, by rfl⟩ : syracuseStep 498911 = 748367) B748367
theorem B1678589 : Blo 495792 1678589 := bstep (se 3 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 1678589 = 629471) B629471
theorem B499175 : Blo 495792 499175 := bstep (se 1 (by rfl) ⟨374381, by rfl⟩ : syracuseStep 499175 = 748763) B748763
theorem B2825765 : Blo 495792 2825765 := bstep (se 4 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 2825765 = 529831) B529831
theorem B499291 : Blo 495792 499291 := bstep (se 1 (by rfl) ⟨374468, by rfl⟩ : syracuseStep 499291 = 748937) B748937
theorem B1122119 : Blo 495792 1122119 := bstep (se 1 (by rfl) ⟨841589, by rfl⟩ : syracuseStep 1122119 = 1683179) B1683179
theorem B499527 : Blo 495792 499527 := bstep (se 1 (by rfl) ⟨374645, by rfl⟩ : syracuseStep 499527 = 749291) B749291
theorem B1417085 : Blo 495792 1417085 := bstep (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) B531407
theorem B499679 : Blo 495792 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B1679399 : Blo 495792 1679399 := bstep (se 1 (by rfl) ⟨1259549, by rfl⟩ : syracuseStep 1679399 = 2519099) B2519099
theorem B6791303 : Blo 495792 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B1417655 : Blo 495792 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B1122767 : Blo 495792 1122767 := bstep (se 1 (by rfl) ⟨842075, by rfl⟩ : syracuseStep 1122767 = 1684151) B1684151
theorem B1680047 : Blo 495792 1680047 := bstep (se 1 (by rfl) ⟨1260035, by rfl⟩ : syracuseStep 1680047 = 2520071) B2520071
theorem B1680371 : Blo 495792 1680371 := bstep (se 1 (by rfl) ⟨1260278, by rfl⟩ : syracuseStep 1680371 = 2520557) B2520557
theorem B1123433 : Blo 495792 1123433 := bstep (se 2 (by rfl) ⟨421287, by rfl⟩ : syracuseStep 1123433 = 842575) B842575
theorem B13575599 : Blo 495792 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B1680911 : Blo 495792 1680911 := bstep (se 1 (by rfl) ⟨1260683, by rfl⟩ : syracuseStep 1680911 = 2521367) B2521367
theorem B1418771 : Blo 495792 1418771 := bstep (se 1 (by rfl) ⟨1064078, by rfl⟩ : syracuseStep 1418771 = 2128157) B2128157
theorem B4794041 : Blo 495792 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B632539 : Blo 495792 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B1255135 : Blo 495792 1255135 := bstep (se 1 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 1255135 = 1882703) B1882703
theorem B1124063 : Blo 495792 1124063 := bstep (se 1 (by rfl) ⟨843047, by rfl⟩ : syracuseStep 1124063 = 1686095) B1686095
theorem B1255247 : Blo 495792 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B6367247 : Blo 495792 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B1681721 : Blo 495792 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B3779135 : Blo 495792 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B1681991 : Blo 495792 1681991 := bstep (se 1 (by rfl) ⟨1261493, by rfl⟩ : syracuseStep 1681991 = 2522987) B2522987
theorem B6400619 : Blo 495792 6400619 := bstep (se 1 (by rfl) ⟨4800464, by rfl⟩ : syracuseStep 6400619 = 9600929) B9600929
theorem B895799 : Blo 495792 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B4041667 : Blo 495792 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B1059961 : Blo 495792 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B1683017 : Blo 495792 1683017 := bstep (se 2 (by rfl) ⟨631131, by rfl⟩ : syracuseStep 1683017 = 1262263) B1262263
theorem B1060627 : Blo 495792 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B896923 : Blo 495792 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B3190751 : Blo 495792 3190751 := bstep (se 1 (by rfl) ⟨2393063, by rfl⟩ : syracuseStep 3190751 = 4786127) B4786127
theorem B1192745 : Blo 495792 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B3191723 : Blo 495792 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1815547 : Blo 495792 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B1684475 : Blo 495792 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B1684691 : Blo 495792 1684691 := bstep (se 1 (by rfl) ⟨1263518, by rfl⟩ : syracuseStep 1684691 = 2527037) B2527037
theorem B2012435 : Blo 495792 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B1684961 : Blo 495792 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B2832029 : Blo 495792 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B1423099 : Blo 495792 1423099 := bstep (se 1 (by rfl) ⟨1067324, by rfl⟩ : syracuseStep 1423099 = 2134649) B2134649
theorem B1259327 : Blo 495792 1259327 := bstep (se 1 (by rfl) ⟨944495, by rfl⟩ : syracuseStep 1259327 = 1888991) B1888991
theorem B3782537 : Blo 495792 3782537 := bstep (se 2 (by rfl) ⟨1418451, by rfl⟩ : syracuseStep 3782537 = 2836903) B2836903
theorem B2832347 : Blo 495792 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B1062875 : Blo 495792 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B3192929 : Blo 495792 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B1685609 : Blo 495792 1685609 := bstep (se 2 (by rfl) ⟨632103, by rfl⟩ : syracuseStep 1685609 = 1264207) B1264207
theorem B506011 : Blo 495792 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B1259783 : Blo 495792 1259783 := bstep (se 1 (by rfl) ⟨944837, by rfl⟩ : syracuseStep 1259783 = 1889675) B1889675
theorem B7649579 : Blo 495792 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1063763 : Blo 495792 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1686473 : Blo 495792 1686473 := bstep (se 2 (by rfl) ⟨632427, by rfl⟩ : syracuseStep 1686473 = 1264855) B1264855
theorem B6372371 : Blo 495792 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B1686743 : Blo 495792 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B1916153 : Blo 495792 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B1260967 : Blo 495792 1260967 := bstep (se 1 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 1260967 = 1891451) B1891451
theorem B1064591 : Blo 495792 1064591 := bstep (se 1 (by rfl) ⟨798443, by rfl⟩ : syracuseStep 1064591 = 1596887) B1596887
theorem B8601335 : Blo 495792 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B5456011 : Blo 495792 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B1065403 : Blo 495792 1065403 := bstep (se 1 (by rfl) ⟨799052, by rfl⟩ : syracuseStep 1065403 = 1598105) B1598105
theorem B2015873 : Blo 495792 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B3785453 : Blo 495792 3785453 := bstep (se 3 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 3785453 = 1419545) B1419545
theorem B3589049 : Blo 495792 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1786985 : Blo 495792 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B8045837 : Blo 495792 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B2016683 : Blo 495792 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B1263023 : Blo 495792 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B1263215 : Blo 495792 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B837371 : Blo 495792 837371 := bstep (se 1 (by rfl) ⟨628028, by rfl⟩ : syracuseStep 837371 = 1256057) B1256057
theorem B706367 : Blo 495792 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B1918799 : Blo 495792 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B4769711 : Blo 495792 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B3196847 : Blo 495792 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B1263559 : Blo 495792 1263559 := bstep (se 1 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 1263559 = 1895339) B1895339
theorem B837607 : Blo 495792 837607 := bstep (se 1 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 837607 = 1256411) B1256411
theorem B414566423 : Blo 495792 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B837823 : Blo 495792 837823 := bstep (se 1 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 837823 = 1256735) B1256735
theorem B1198271 : Blo 495792 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B1067359 : Blo 495792 1067359 := bstep (se 1 (by rfl) ⟨800519, by rfl⟩ : syracuseStep 1067359 = 1601039) B1601039
theorem B3787397 : Blo 495792 3787397 := bstep (se 4 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 3787397 = 710137) B710137
theorem B4770667 : Blo 495792 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B838559 : Blo 495792 838559 := bstep (se 1 (by rfl) ⟨628919, by rfl⟩ : syracuseStep 838559 = 1257839) B1257839
theorem B707563 : Blo 495792 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B5655581 : Blo 495792 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B838991 : Blo 495792 838991 := bstep (se 1 (by rfl) ⟨629243, by rfl⟩ : syracuseStep 838991 = 1258487) B1258487
theorem B115953443 : Blo 495792 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B840287 : Blo 495792 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B4772513 : Blo 495792 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B2839319 : Blo 495792 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B1790761 : Blo 495792 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B3789827 : Blo 495792 3789827 := bstep (se 1 (by rfl) ⟨2842370, by rfl⟩ : syracuseStep 3789827 = 5684741) B5684741
theorem B9590237 : Blo 495792 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B1889963 : Blo 495792 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B710479 : Blo 495792 710479 := bstep (se 1 (by rfl) ⟨532859, by rfl⟩ : syracuseStep 710479 = 1065719) B1065719
theorem B6838151 : Blo 495792 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B841711 : Blo 495792 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B1136737 : Blo 495792 1136737 := bstep (se 2 (by rfl) ⟨426276, by rfl⟩ : syracuseStep 1136737 = 852553) B852553
theorem B841961 : Blo 495792 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B10934651 : Blo 495792 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B3037607 : Blo 495792 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B743963 : Blo 495792 743963 := bstep (se 1 (by rfl) ⟨557972, by rfl⟩ : syracuseStep 743963 = 1115945) B1115945
theorem B744041 : Blo 495792 744041 := bstep (se 2 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 744041 = 558031) B558031
theorem B14605379 : Blo 495792 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B744569 : Blo 495792 744569 := bstep (se 2 (by rfl) ⟨279213, by rfl⟩ : syracuseStep 744569 = 558427) B558427
theorem B1793153 : Blo 495792 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1596631 : Blo 495792 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B744671 : Blo 495792 744671 := bstep (se 1 (by rfl) ⟨558503, by rfl⟩ : syracuseStep 744671 = 1117007) B1117007
theorem B941321 : Blo 495792 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B744713 : Blo 495792 744713 := bstep (se 2 (by rfl) ⟨279267, by rfl⟩ : syracuseStep 744713 = 558535) B558535
theorem B744815 : Blo 495792 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B3792257 : Blo 495792 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B744935 : Blo 495792 744935 := bstep (se 1 (by rfl) ⟨558701, by rfl⟩ : syracuseStep 744935 = 1117403) B1117403
theorem B745067 : Blo 495792 745067 := bstep (se 1 (by rfl) ⟨558800, by rfl⟩ : syracuseStep 745067 = 1117601) B1117601
theorem B679657 : Blo 495792 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B745193 : Blo 495792 745193 := bstep (se 2 (by rfl) ⟨279447, by rfl⟩ : syracuseStep 745193 = 558895) B558895
theorem B2121527 : Blo 495792 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B745337 : Blo 495792 745337 := bstep (se 2 (by rfl) ⟨279501, by rfl⟩ : syracuseStep 745337 = 559003) B559003
theorem B745439 : Blo 495792 745439 := bstep (se 1 (by rfl) ⟨559079, by rfl⟩ : syracuseStep 745439 = 1118159) B1118159
theorem B1433639 : Blo 495792 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B745691 : Blo 495792 745691 := bstep (se 1 (by rfl) ⟨559268, by rfl⟩ : syracuseStep 745691 = 1118537) B1118537
theorem B2023643 : Blo 495792 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B745703 : Blo 495792 745703 := bstep (se 1 (by rfl) ⟨559277, by rfl⟩ : syracuseStep 745703 = 1118555) B1118555
theorem B3793229 : Blo 495792 3793229 := bstep (se 3 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 3793229 = 1422461) B1422461
theorem B2122109 : Blo 495792 2122109 := bstep (se 3 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 2122109 = 795791) B795791
theorem B745865 : Blo 495792 745865 := bstep (se 2 (by rfl) ⟨279699, by rfl⟩ : syracuseStep 745865 = 559399) B559399
theorem B745961 : Blo 495792 745961 := bstep (se 2 (by rfl) ⟨279735, by rfl⟩ : syracuseStep 745961 = 559471) B559471
theorem B746087 : Blo 495792 746087 := bstep (se 1 (by rfl) ⟨559565, by rfl⟩ : syracuseStep 746087 = 1119131) B1119131
theorem B746219 : Blo 495792 746219 := bstep (se 1 (by rfl) ⟨559664, by rfl⟩ : syracuseStep 746219 = 1119329) B1119329
theorem B746249 : Blo 495792 746249 := bstep (se 2 (by rfl) ⟨279843, by rfl⟩ : syracuseStep 746249 = 559687) B559687
theorem B1598219 : Blo 495792 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B746351 : Blo 495792 746351 := bstep (se 1 (by rfl) ⟨559763, by rfl⟩ : syracuseStep 746351 = 1119527) B1119527
theorem B943015 : Blo 495792 943015 := bstep (se 1 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 943015 = 1414523) B1414523
theorem B746603 : Blo 495792 746603 := bstep (se 1 (by rfl) ⟨559952, by rfl⟩ : syracuseStep 746603 = 1119905) B1119905
theorem B746843 : Blo 495792 746843 := bstep (se 1 (by rfl) ⟨560132, by rfl⟩ : syracuseStep 746843 = 1120265) B1120265
theorem B2844011 : Blo 495792 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B9561563 : Blo 495792 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B1893881 : Blo 495792 1893881 := bstep (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) B1420411
theorem B747119 : Blo 495792 747119 := bstep (se 1 (by rfl) ⟨560339, by rfl⟩ : syracuseStep 747119 = 1120679) B1120679
theorem B747191 : Blo 495792 747191 := bstep (se 1 (by rfl) ⟨560393, by rfl⟩ : syracuseStep 747191 = 1120787) B1120787
theorem B747227 : Blo 495792 747227 := bstep (se 1 (by rfl) ⟨560420, by rfl⟩ : syracuseStep 747227 = 1120841) B1120841
theorem B943903 : Blo 495792 943903 := bstep (se 1 (by rfl) ⟨707927, by rfl⟩ : syracuseStep 943903 = 1415855) B1415855
theorem B747401 : Blo 495792 747401 := bstep (se 2 (by rfl) ⟨280275, by rfl⟩ : syracuseStep 747401 = 560551) B560551
theorem B34498457 : Blo 495792 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B1435591 : Blo 495792 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B747503 : Blo 495792 747503 := bstep (se 1 (by rfl) ⟨560627, by rfl⟩ : syracuseStep 747503 = 1121255) B1121255
theorem B747755 : Blo 495792 747755 := bstep (se 1 (by rfl) ⟨560816, by rfl⟩ : syracuseStep 747755 = 1121633) B1121633
theorem B747815 : Blo 495792 747815 := bstep (se 1 (by rfl) ⟨560861, by rfl⟩ : syracuseStep 747815 = 1121723) B1121723
theorem B747899 : Blo 495792 747899 := bstep (se 1 (by rfl) ⟨560924, by rfl⟩ : syracuseStep 747899 = 1121849) B1121849
theorem B748169 : Blo 495792 748169 := bstep (se 2 (by rfl) ⟨280563, by rfl⟩ : syracuseStep 748169 = 561127) B561127
theorem B7170763 : Blo 495792 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B748343 : Blo 495792 748343 := bstep (se 1 (by rfl) ⟨561257, by rfl⟩ : syracuseStep 748343 = 1122515) B1122515
theorem B748379 : Blo 495792 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B748523 : Blo 495792 748523 := bstep (se 1 (by rfl) ⟨561392, by rfl⟩ : syracuseStep 748523 = 1122785) B1122785
theorem B1895521 : Blo 495792 1895521 := bstep (se 2 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 1895521 = 1421641) B1421641
theorem B2387065 : Blo 495792 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B748727 : Blo 495792 748727 := bstep (se 1 (by rfl) ⟨561545, by rfl⟩ : syracuseStep 748727 = 1123091) B1123091
theorem B748967 : Blo 495792 748967 := bstep (se 1 (by rfl) ⟨561725, by rfl⟩ : syracuseStep 748967 = 1123451) B1123451
theorem B4615639 : Blo 495792 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B749051 : Blo 495792 749051 := bstep (se 1 (by rfl) ⟨561788, by rfl⟩ : syracuseStep 749051 = 1123577) B1123577
theorem B1895993 : Blo 495792 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B749147 : Blo 495792 749147 := bstep (se 1 (by rfl) ⟨561860, by rfl⟩ : syracuseStep 749147 = 1123721) B1123721
theorem B749231 : Blo 495792 749231 := bstep (se 1 (by rfl) ⟨561923, by rfl⟩ : syracuseStep 749231 = 1123847) B1123847
theorem B749351 : Blo 495792 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B749435 : Blo 495792 749435 := bstep (se 1 (by rfl) ⟨562076, by rfl⟩ : syracuseStep 749435 = 1124153) B1124153
theorem B946075 : Blo 495792 946075 := bstep (se 1 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 946075 = 1419113) B1419113
theorem B2683655 : Blo 495792 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B3208061 : Blo 495792 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B6387133 : Blo 495792 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B2553353 : Blo 495792 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B3405401 : Blo 495792 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B25950307 : Blo 495792 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B1702043 : Blo 495792 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B3177629 : Blo 495792 3177629 := bstep (se 3 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 3177629 = 1191611) B1191611
theorem B5373665 : Blo 495792 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B7274681 : Blo 495792 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B1343915 : Blo 495792 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B2523635 : Blo 495792 2523635 := bstep (se 1 (by rfl) ⟨1892726, by rfl⟩ : syracuseStep 2523635 = 3785453) B3785453
theorem B6062597 : Blo 495792 6062597 := bstep (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) B1136737
theorem B10748537 : Blo 495792 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B2392699 : Blo 495792 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B1344455 : Blo 495792 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B558247 : Blo 495792 558247 := bstep (se 1 (by rfl) ⟨418685, by rfl⟩ : syracuseStep 558247 = 837371) B837371
theorem B1279199 : Blo 495792 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B3179807 : Blo 495792 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B1115711 : Blo 495792 1115711 := bstep (se 1 (by rfl) ⟨836783, by rfl⟩ : syracuseStep 1115711 = 1673567) B1673567
theorem B1115819 : Blo 495792 1115819 := bstep (se 1 (by rfl) ⟨836864, by rfl⟩ : syracuseStep 1115819 = 1673729) B1673729
theorem B2524931 : Blo 495792 2524931 := bstep (se 1 (by rfl) ⟨1893698, by rfl⟩ : syracuseStep 2524931 = 3787397) B3787397
theorem B4261643 : Blo 495792 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B559039 : Blo 495792 559039 := bstep (se 1 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 559039 = 838559) B838559
theorem B1116143 : Blo 495792 1116143 := bstep (se 1 (by rfl) ⟨837107, by rfl⟩ : syracuseStep 1116143 = 1674215) B1674215
theorem B3770387 : Blo 495792 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B1116359 : Blo 495792 1116359 := bstep (se 1 (by rfl) ⟨837269, by rfl⟩ : syracuseStep 1116359 = 1674539) B1674539
theorem B559327 : Blo 495792 559327 := bstep (se 1 (by rfl) ⟨419495, by rfl⟩ : syracuseStep 559327 = 838991) B838991
theorem B1673513 : Blo 495792 1673513 := bstep (se 2 (by rfl) ⟨627567, by rfl⟩ : syracuseStep 1673513 = 1255135) B1255135
theorem B1116539 : Blo 495792 1116539 := bstep (se 1 (by rfl) ⟨837404, by rfl⟩ : syracuseStep 1116539 = 1674809) B1674809
theorem B77302295 : Blo 495792 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B19466795 : Blo 495792 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B1116809 : Blo 495792 1116809 := bstep (se 2 (by rfl) ⟨418803, by rfl⟩ : syracuseStep 1116809 = 837607) B837607
theorem B1117097 : Blo 495792 1117097 := bstep (se 2 (by rfl) ⟨418911, by rfl⟩ : syracuseStep 1117097 = 837823) B837823
theorem B560191 : Blo 495792 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B3181675 : Blo 495792 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B2526551 : Blo 495792 2526551 := bstep (se 1 (by rfl) ⟨1894913, by rfl⟩ : syracuseStep 2526551 = 3789827) B3789827
theorem B1117799 : Blo 495792 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B6393491 : Blo 495792 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B6360889 : Blo 495792 6360889 := bstep (se 2 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 6360889 = 4770667) B4770667
theorem B2428795 : Blo 495792 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B1118303 : Blo 495792 1118303 := bstep (se 1 (by rfl) ⟨838727, by rfl⟩ : syracuseStep 1118303 = 1677455) B1677455
theorem B2527361 : Blo 495792 2527361 := bstep (se 2 (by rfl) ⟨947760, by rfl⟩ : syracuseStep 2527361 = 1895521) B1895521
theorem B561307 : Blo 495792 561307 := bstep (se 1 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 561307 = 841961) B841961
theorem B1413281 : Blo 495792 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B3182753 : Blo 495792 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B495975 : Blo 495792 495975 := bstep (se 1 (by rfl) ⟨371981, by rfl⟩ : syracuseStep 495975 = 743963) B743963
theorem B496027 : Blo 495792 496027 := bstep (se 1 (by rfl) ⟨372020, by rfl⟩ : syracuseStep 496027 = 744041) B744041
theorem B9736919 : Blo 495792 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B496379 : Blo 495792 496379 := bstep (se 1 (by rfl) ⟨372284, by rfl⟩ : syracuseStep 496379 = 744569) B744569
theorem B1643275 : Blo 495792 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B496447 : Blo 495792 496447 := bstep (se 1 (by rfl) ⟨372335, by rfl⟩ : syracuseStep 496447 = 744671) B744671
theorem B1119059 : Blo 495792 1119059 := bstep (se 1 (by rfl) ⟨839294, by rfl⟩ : syracuseStep 1119059 = 1678589) B1678589
theorem B496475 : Blo 495792 496475 := bstep (se 1 (by rfl) ⟨372356, by rfl⟩ : syracuseStep 496475 = 744713) B744713
theorem B496543 : Blo 495792 496543 := bstep (se 1 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 496543 = 744815) B744815
theorem B2528171 : Blo 495792 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B496623 : Blo 495792 496623 := bstep (se 1 (by rfl) ⟨372467, by rfl⟩ : syracuseStep 496623 = 744935) B744935
theorem B1414169 : Blo 495792 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B496711 : Blo 495792 496711 := bstep (se 1 (by rfl) ⟨372533, by rfl⟩ : syracuseStep 496711 = 745067) B745067
theorem B8524925 : Blo 495792 8524925 := bstep (se 3 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 8524925 = 3196847) B3196847
theorem B496795 : Blo 495792 496795 := bstep (se 1 (by rfl) ⟨372596, by rfl⟩ : syracuseStep 496795 = 745193) B745193
theorem B1414351 : Blo 495792 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B496891 : Blo 495792 496891 := bstep (se 1 (by rfl) ⟨372668, by rfl⟩ : syracuseStep 496891 = 745337) B745337
theorem B496959 : Blo 495792 496959 := bstep (se 1 (by rfl) ⟨372719, by rfl⟩ : syracuseStep 496959 = 745439) B745439
theorem B1119599 : Blo 495792 1119599 := bstep (se 1 (by rfl) ⟨839699, by rfl⟩ : syracuseStep 1119599 = 1679399) B1679399
theorem B4527535 : Blo 495792 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B497127 : Blo 495792 497127 := bstep (se 1 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 497127 = 745691) B745691
theorem B1349095 : Blo 495792 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B497135 : Blo 495792 497135 := bstep (se 1 (by rfl) ⟨372851, by rfl⟩ : syracuseStep 497135 = 745703) B745703
theorem B2528819 : Blo 495792 2528819 := bstep (se 1 (by rfl) ⟨1896614, by rfl⟩ : syracuseStep 2528819 = 3793229) B3793229
theorem B1414739 : Blo 495792 1414739 := bstep (se 1 (by rfl) ⟨1061054, by rfl⟩ : syracuseStep 1414739 = 2122109) B2122109
theorem B497243 : Blo 495792 497243 := bstep (se 1 (by rfl) ⟨372932, by rfl⟩ : syracuseStep 497243 = 745865) B745865
theorem B497307 : Blo 495792 497307 := bstep (se 1 (by rfl) ⟨372980, by rfl⟩ : syracuseStep 497307 = 745961) B745961
theorem B497391 : Blo 495792 497391 := bstep (se 1 (by rfl) ⟨373043, by rfl⟩ : syracuseStep 497391 = 746087) B746087
theorem B1120031 : Blo 495792 1120031 := bstep (se 1 (by rfl) ⟨840023, by rfl⟩ : syracuseStep 1120031 = 1680047) B1680047
theorem B497479 : Blo 495792 497479 := bstep (se 1 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 497479 = 746219) B746219
theorem B497499 : Blo 495792 497499 := bstep (se 1 (by rfl) ⟨373124, by rfl⟩ : syracuseStep 497499 = 746249) B746249
theorem B497567 : Blo 495792 497567 := bstep (se 1 (by rfl) ⟨373175, by rfl⟩ : syracuseStep 497567 = 746351) B746351
theorem B1120247 : Blo 495792 1120247 := bstep (se 1 (by rfl) ⟨840185, by rfl⟩ : syracuseStep 1120247 = 1680371) B1680371
theorem B497735 : Blo 495792 497735 := bstep (se 1 (by rfl) ⟨373301, by rfl⟩ : syracuseStep 497735 = 746603) B746603
theorem B497895 : Blo 495792 497895 := bstep (se 1 (by rfl) ⟨373421, by rfl⟩ : syracuseStep 497895 = 746843) B746843
theorem B9050399 : Blo 495792 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B1120607 : Blo 495792 1120607 := bstep (se 1 (by rfl) ⟨840455, by rfl⟩ : syracuseStep 1120607 = 1680911) B1680911
theorem B498079 : Blo 495792 498079 := bstep (se 1 (by rfl) ⟨373559, by rfl⟩ : syracuseStep 498079 = 747119) B747119
theorem B498127 : Blo 495792 498127 := bstep (se 1 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 498127 = 747191) B747191
theorem B498151 : Blo 495792 498151 := bstep (se 1 (by rfl) ⟨373613, by rfl⟩ : syracuseStep 498151 = 747227) B747227
theorem B498267 : Blo 495792 498267 := bstep (se 1 (by rfl) ⟨373700, by rfl⟩ : syracuseStep 498267 = 747401) B747401
theorem B498335 : Blo 495792 498335 := bstep (se 1 (by rfl) ⟨373751, by rfl⟩ : syracuseStep 498335 = 747503) B747503
theorem B498503 : Blo 495792 498503 := bstep (se 1 (by rfl) ⟨373877, by rfl⟩ : syracuseStep 498503 = 747755) B747755
theorem B498543 : Blo 495792 498543 := bstep (se 1 (by rfl) ⟨373907, by rfl⟩ : syracuseStep 498543 = 747815) B747815
theorem B1121147 : Blo 495792 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B498599 : Blo 495792 498599 := bstep (se 1 (by rfl) ⟨373949, by rfl⟩ : syracuseStep 498599 = 747899) B747899
theorem B1121327 : Blo 495792 1121327 := bstep (se 1 (by rfl) ⟨840995, by rfl⟩ : syracuseStep 1121327 = 1681991) B1681991
theorem B4267079 : Blo 495792 4267079 := bstep (se 1 (by rfl) ⟨3200309, by rfl⟩ : syracuseStep 4267079 = 6400619) B6400619
theorem B498779 : Blo 495792 498779 := bstep (se 1 (by rfl) ⟨374084, by rfl⟩ : syracuseStep 498779 = 748169) B748169
theorem B498895 : Blo 495792 498895 := bstep (se 1 (by rfl) ⟨374171, by rfl⟩ : syracuseStep 498895 = 748343) B748343
theorem B498919 : Blo 495792 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B499015 : Blo 495792 499015 := bstep (se 1 (by rfl) ⟨374261, by rfl⟩ : syracuseStep 499015 = 748523) B748523
theorem B499151 : Blo 495792 499151 := bstep (se 1 (by rfl) ⟨374363, by rfl⟩ : syracuseStep 499151 = 748727) B748727
theorem B499311 : Blo 495792 499311 := bstep (se 1 (by rfl) ⟨374483, by rfl⟩ : syracuseStep 499311 = 748967) B748967
theorem B499367 : Blo 495792 499367 := bstep (se 1 (by rfl) ⟨374525, by rfl⟩ : syracuseStep 499367 = 749051) B749051
theorem B1122011 : Blo 495792 1122011 := bstep (se 1 (by rfl) ⟨841508, by rfl⟩ : syracuseStep 1122011 = 1683017) B1683017
theorem B499431 : Blo 495792 499431 := bstep (se 1 (by rfl) ⟨374573, by rfl⟩ : syracuseStep 499431 = 749147) B749147
theorem B499487 : Blo 495792 499487 := bstep (se 1 (by rfl) ⟨374615, by rfl⟩ : syracuseStep 499487 = 749231) B749231
theorem B499567 : Blo 495792 499567 := bstep (se 1 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 499567 = 749351) B749351
theorem B499623 : Blo 495792 499623 := bstep (se 1 (by rfl) ⟨374717, by rfl⟩ : syracuseStep 499623 = 749435) B749435
theorem B1122281 : Blo 495792 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B9052145 : Blo 495792 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B795163 : Blo 495792 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B2138707 : Blo 495792 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1122983 : Blo 495792 1122983 := bstep (se 1 (by rfl) ⟨842237, by rfl⟩ : syracuseStep 1122983 = 1684475) B1684475
theorem B1123127 : Blo 495792 1123127 := bstep (se 1 (by rfl) ⟨842345, by rfl⟩ : syracuseStep 1123127 = 1684691) B1684691
theorem B1123307 : Blo 495792 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B2270267 : Blo 495792 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B1123739 : Blo 495792 1123739 := bstep (se 1 (by rfl) ⟨842804, by rfl⟩ : syracuseStep 1123739 = 1685609) B1685609
theorem B1681289 : Blo 495792 1681289 := bstep (se 2 (by rfl) ⟨630483, by rfl⟩ : syracuseStep 1681289 = 1260967) B1260967
theorem B1124315 : Blo 495792 1124315 := bstep (se 1 (by rfl) ⟨843236, by rfl⟩ : syracuseStep 1124315 = 1686473) B1686473
theorem B1124495 : Blo 495792 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B3582443 : Blo 495792 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B1420537 : Blo 495792 1420537 := bstep (se 2 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 1420537 = 1065403) B1065403
theorem B1191323 : Blo 495792 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B1257353 : Blo 495792 1257353 := bstep (se 2 (by rfl) ⟨471507, by rfl⟩ : syracuseStep 1257353 = 943015) B943015
theorem B276377615 : Blo 495792 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B4239499 : Blo 495792 4239499 := bstep (se 1 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 4239499 = 6359249) B6359249
theorem B1422143 : Blo 495792 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B1258537 : Blo 495792 1258537 := bstep (se 2 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 1258537 = 943903) B943903
theorem B4240457 : Blo 495792 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B1914121 : Blo 495792 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B1684745 : Blo 495792 1684745 := bstep (se 2 (by rfl) ⟨631779, by rfl⟩ : syracuseStep 1684745 = 1263559) B1263559
theorem B2274571 : Blo 495792 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B1685231 : Blo 495792 1685231 := bstep (se 1 (by rfl) ⟨1263923, by rfl⟩ : syracuseStep 1685231 = 2527847) B2527847
theorem B1423145 : Blo 495792 1423145 := bstep (se 2 (by rfl) ⟨533679, by rfl⟩ : syracuseStep 1423145 = 1067359) B1067359
theorem B3783023 : Blo 495792 3783023 := bstep (se 1 (by rfl) ⟨2837267, by rfl⟩ : syracuseStep 3783023 = 5674535) B5674535
theorem B1259975 : Blo 495792 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B5388889 : Blo 495792 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B1686203 : Blo 495792 1686203 := bstep (se 1 (by rfl) ⟨1264652, by rfl⟩ : syracuseStep 1686203 = 2529305) B2529305
theorem B7289767 : Blo 495792 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B2014183 : Blo 495792 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B1195435 : Blo 495792 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B1883645 : Blo 495792 1883645 := bstep (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) B706367
theorem B1883843 : Blo 495792 1883843 := bstep (se 1 (by rfl) ⟨1412882, by rfl⟩ : syracuseStep 1883843 = 2825765) B2825765
theorem B1195897 : Blo 495792 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B1261433 : Blo 495792 1261433 := bstep (se 2 (by rfl) ⟨473037, by rfl⟩ : syracuseStep 1261433 = 946075) B946075
theorem B3195389 : Blo 495792 3195389 := bstep (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) B1198271
theorem B1065479 : Blo 495792 1065479 := bstep (se 1 (by rfl) ⟨799109, by rfl⟩ : syracuseStep 1065479 = 1598219) B1598219
theorem B6374375 : Blo 495792 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B1262587 : Blo 495792 1262587 := bstep (se 1 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 1262587 = 1893881) B1893881
theorem B3196027 : Blo 495792 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B836831 : Blo 495792 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B4244831 : Blo 495792 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B1263995 : Blo 495792 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B707449 : Blo 495792 707449 := bstep (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) B530587
theorem B674681 : Blo 495792 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B1789103 : Blo 495792 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B2510189 : Blo 495792 2510189 := bstep (se 3 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 2510189 = 941321) B941321
theorem B1888019 : Blo 495792 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B839551 : Blo 495792 839551 := bstep (se 1 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 839551 = 1259327) B1259327
theorem B4050917 : Blo 495792 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1888231 : Blo 495792 1888231 := bstep (se 1 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 1888231 = 2832347) B2832347
theorem B708583 : Blo 495792 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B1134695 : Blo 495792 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B839855 : Blo 495792 839855 := bstep (se 1 (by rfl) ⟨629891, by rfl⟩ : syracuseStep 839855 = 1259783) B1259783
theorem B5099719 : Blo 495792 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B709175 : Blo 495792 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B4248247 : Blo 495792 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B2118419 : Blo 495792 2118419 := bstep (se 1 (by rfl) ⟨1588814, by rfl⟩ : syracuseStep 2118419 = 3177629) B3177629
theorem B906209 : Blo 495792 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B709727 : Blo 495792 709727 := bstep (se 1 (by rfl) ⟨532295, by rfl⟩ : syracuseStep 709727 = 1064591) B1064591
theorem B4609399 : Blo 495792 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B3823037 : Blo 495792 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B2512619 : Blo 495792 2512619 := bstep (se 1 (by rfl) ⟨1884464, by rfl⟩ : syracuseStep 2512619 = 3768929) B3768929
theorem B5363891 : Blo 495792 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B743711 : Blo 495792 743711 := bstep (se 1 (by rfl) ⟨557783, by rfl⟩ : syracuseStep 743711 = 1115567) B1115567
theorem B842015 : Blo 495792 842015 := bstep (se 1 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 842015 = 1263023) B1263023
theorem B842143 : Blo 495792 842143 := bstep (se 1 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 842143 = 1263215) B1263215
theorem B744263 : Blo 495792 744263 := bstep (se 1 (by rfl) ⟨558197, by rfl⟩ : syracuseStep 744263 = 1116395) B1116395
theorem B4021073 : Blo 495792 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B6380369 : Blo 495792 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B843385 : Blo 495792 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B745127 : Blo 495792 745127 := bstep (se 1 (by rfl) ⟨558845, by rfl⟩ : syracuseStep 745127 = 1117691) B1117691
theorem B745247 : Blo 495792 745247 := bstep (se 1 (by rfl) ⟨558935, by rfl⟩ : syracuseStep 745247 = 1117871) B1117871
theorem B745679 : Blo 495792 745679 := bstep (se 1 (by rfl) ⟨559259, by rfl⟩ : syracuseStep 745679 = 1118519) B1118519
theorem B745727 : Blo 495792 745727 := bstep (se 1 (by rfl) ⟨559295, by rfl⟩ : syracuseStep 745727 = 1118591) B1118591
theorem B1892879 : Blo 495792 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B9561017 : Blo 495792 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B746543 : Blo 495792 746543 := bstep (se 1 (by rfl) ⟨559907, by rfl⟩ : syracuseStep 746543 = 1119815) B1119815
theorem B746663 : Blo 495792 746663 := bstep (se 1 (by rfl) ⟨559997, by rfl⟩ : syracuseStep 746663 = 1119995) B1119995
theorem B943417 : Blo 495792 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B2516507 : Blo 495792 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B747035 : Blo 495792 747035 := bstep (se 1 (by rfl) ⟨560276, by rfl⟩ : syracuseStep 747035 = 1120553) B1120553
theorem B2025071 : Blo 495792 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B2385683 : Blo 495792 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B1009427 : Blo 495792 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B747419 : Blo 495792 747419 := bstep (se 1 (by rfl) ⟨560564, by rfl⟩ : syracuseStep 747419 = 1121129) B1121129
theorem B747455 : Blo 495792 747455 := bstep (se 1 (by rfl) ⟨560591, by rfl⟩ : syracuseStep 747455 = 1121183) B1121183
theorem B747641 : Blo 495792 747641 := bstep (se 2 (by rfl) ⟨280365, by rfl⟩ : syracuseStep 747641 = 560731) B560731
theorem B748025 : Blo 495792 748025 := bstep (se 2 (by rfl) ⟨280509, by rfl⟩ : syracuseStep 748025 = 561019) B561019
theorem B748079 : Blo 495792 748079 := bstep (se 1 (by rfl) ⟨561059, by rfl⟩ : syracuseStep 748079 = 1122119) B1122119
theorem B944723 : Blo 495792 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B945103 : Blo 495792 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B748511 : Blo 495792 748511 := bstep (se 1 (by rfl) ⟨561383, by rfl⟩ : syracuseStep 748511 = 1122767) B1122767
theorem B748955 : Blo 495792 748955 := bstep (se 1 (by rfl) ⟨561716, by rfl⟩ : syracuseStep 748955 = 1123433) B1123433
theorem B1896007 : Blo 495792 1896007 := bstep (se 1 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 1896007 = 2844011) B2844011
theorem B945847 : Blo 495792 945847 := bstep (se 1 (by rfl) ⟨709385, by rfl⟩ : syracuseStep 945847 = 1418771) B1418771
theorem B2387681 : Blo 495792 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B749375 : Blo 495792 749375 := bstep (se 1 (by rfl) ⟨562031, by rfl⟩ : syracuseStep 749375 = 1124063) B1124063
theorem B22998971 : Blo 495792 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B2420729 : Blo 495792 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B749561 : Blo 495792 749561 := bstep (se 2 (by rfl) ⟨281085, by rfl⟩ : syracuseStep 749561 = 562171) B562171
theorem B12415169 : Blo 495792 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B2519423 : Blo 495792 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B8516177 : Blo 495792 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B2388797 : Blo 495792 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B1897465 : Blo 495792 1897465 := bstep (se 2 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 1897465 = 1423099) B1423099
theorem B947305 : Blo 495792 947305 := bstep (se 2 (by rfl) ⟨355239, by rfl⟩ : syracuseStep 947305 = 710479) B710479
theorem B2127167 : Blo 495792 2127167 := bstep (se 1 (by rfl) ⟨1595375, by rfl⟩ : syracuseStep 2127167 = 3190751) B3190751
theorem B34600409 : Blo 495792 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B2127815 : Blo 495792 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B1341623 : Blo 495792 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B1702235 : Blo 495792 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B2521691 : Blo 495792 2521691 := bstep (se 1 (by rfl) ⟨1891268, by rfl⟩ : syracuseStep 2521691 = 3782537) B3782537
theorem B2128619 : Blo 495792 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B72940277 : Blo 495792 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B2128841 : Blo 495792 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B98466965 : Blo 495792 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B1277435 : Blo 495792 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B7175789 : Blo 495792 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B5734223 : Blo 495792 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B4849787 : Blo 495792 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B2130259 : Blo 495792 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B2851609 : Blo 495792 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B557887 : Blo 495792 557887 := bstep (se 1 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 557887 = 836831) B836831
theorem B4261369 : Blo 495792 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1115675 : Blo 495792 1115675 := bstep (se 1 (by rfl) ⟨836756, by rfl⟩ : syracuseStep 1115675 = 1673513) B1673513
theorem B12977863 : Blo 495792 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B1673459 : Blo 495792 1673459 := bstep (se 1 (by rfl) ⟨1255094, by rfl⟩ : syracuseStep 1673459 = 2510189) B2510189
theorem B4262327 : Blo 495792 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B756463 : Blo 495792 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B559903 : Blo 495792 559903 := bstep (se 1 (by rfl) ⟨419927, by rfl⟩ : syracuseStep 559903 = 839855) B839855
theorem B6491279 : Blo 495792 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B1412279 : Blo 495792 1412279 := bstep (se 1 (by rfl) ⟨1059209, by rfl⟩ : syracuseStep 1412279 = 2118419) B2118419
theorem B3411197 : Blo 495792 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B1675079 : Blo 495792 1675079 := bstep (se 1 (by rfl) ⟨1256309, by rfl⟩ : syracuseStep 1675079 = 2512619) B2512619
theorem B3575927 : Blo 495792 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B495807 : Blo 495792 495807 := bstep (se 1 (by rfl) ⟨371855, by rfl⟩ : syracuseStep 495807 = 743711) B743711
theorem B6033599 : Blo 495792 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B561343 : Blo 495792 561343 := bstep (se 1 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 561343 = 842015) B842015
theorem B496175 : Blo 495792 496175 := bstep (se 1 (by rfl) ⟨372131, by rfl⟩ : syracuseStep 496175 = 744263) B744263
theorem B2691805 : Blo 495792 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B2528009 : Blo 495792 2528009 := bstep (se 2 (by rfl) ⟨948003, by rfl⟩ : syracuseStep 2528009 = 1896007) B1896007
theorem B496751 : Blo 495792 496751 := bstep (se 1 (by rfl) ⟨372563, by rfl⟩ : syracuseStep 496751 = 745127) B745127
theorem B1119401 : Blo 495792 1119401 := bstep (se 2 (by rfl) ⟨419775, by rfl⟩ : syracuseStep 1119401 = 839551) B839551
theorem B496831 : Blo 495792 496831 := bstep (se 1 (by rfl) ⟨372623, by rfl⟩ : syracuseStep 496831 = 745247) B745247
theorem B6034763 : Blo 495792 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B497119 : Blo 495792 497119 := bstep (se 1 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 497119 = 745679) B745679
theorem B497151 : Blo 495792 497151 := bstep (se 1 (by rfl) ⟨372863, by rfl⟩ : syracuseStep 497151 = 745727) B745727
theorem B497695 : Blo 495792 497695 := bstep (se 1 (by rfl) ⟨373271, by rfl⟩ : syracuseStep 497695 = 746543) B746543
theorem B1513511 : Blo 495792 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B497775 : Blo 495792 497775 := bstep (se 1 (by rfl) ⟨373331, by rfl⟩ : syracuseStep 497775 = 746663) B746663
theorem B1677671 : Blo 495792 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B498023 : Blo 495792 498023 := bstep (se 1 (by rfl) ⟨373517, by rfl⟩ : syracuseStep 498023 = 747035) B747035
theorem B1350047 : Blo 495792 1350047 := bstep (se 1 (by rfl) ⟨1012535, by rfl⟩ : syracuseStep 1350047 = 2025071) B2025071
theorem B1120859 : Blo 495792 1120859 := bstep (se 1 (by rfl) ⟨840644, by rfl⟩ : syracuseStep 1120859 = 1681289) B1681289
theorem B498279 : Blo 495792 498279 := bstep (se 1 (by rfl) ⟨373709, by rfl⟩ : syracuseStep 498279 = 747419) B747419
theorem B498303 : Blo 495792 498303 := bstep (se 1 (by rfl) ⟨373727, by rfl⟩ : syracuseStep 498303 = 747455) B747455
theorem B2529953 : Blo 495792 2529953 := bstep (se 2 (by rfl) ⟨948732, by rfl⟩ : syracuseStep 2529953 = 1897465) B1897465
theorem B1678049 : Blo 495792 1678049 := bstep (se 2 (by rfl) ⟨629268, by rfl⟩ : syracuseStep 1678049 = 1258537) B1258537
theorem B498427 : Blo 495792 498427 := bstep (se 1 (by rfl) ⟨373820, by rfl⟩ : syracuseStep 498427 = 747641) B747641
theorem B498683 : Blo 495792 498683 := bstep (se 1 (by rfl) ⟨374012, by rfl⟩ : syracuseStep 498683 = 748025) B748025
theorem B498719 : Blo 495792 498719 := bstep (se 1 (by rfl) ⟨374039, by rfl⟩ : syracuseStep 498719 = 748079) B748079
theorem B6036713 : Blo 495792 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B499007 : Blo 495792 499007 := bstep (se 1 (by rfl) ⟨374255, by rfl⟩ : syracuseStep 499007 = 748511) B748511
theorem B794215 : Blo 495792 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B499303 : Blo 495792 499303 := bstep (se 1 (by rfl) ⟨374477, by rfl⟩ : syracuseStep 499303 = 748955) B748955
theorem B499583 : Blo 495792 499583 := bstep (se 1 (by rfl) ⟨374687, by rfl⟩ : syracuseStep 499583 = 749375) B749375
theorem B1613819 : Blo 495792 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B499707 : Blo 495792 499707 := bstep (se 1 (by rfl) ⟨374780, by rfl⟩ : syracuseStep 499707 = 749561) B749561
theorem B1679615 : Blo 495792 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B5677451 : Blo 495792 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B1122857 : Blo 495792 1122857 := bstep (se 2 (by rfl) ⟨421071, by rfl⟩ : syracuseStep 1122857 = 842143) B842143
theorem B2826971 : Blo 495792 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B7185185 : Blo 495792 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B1123163 : Blo 495792 1123163 := bstep (se 1 (by rfl) ⟨842372, by rfl⟩ : syracuseStep 1123163 = 1684745) B1684745
theorem B1418111 : Blo 495792 1418111 := bstep (se 1 (by rfl) ⟨1063583, by rfl⟩ : syracuseStep 1418111 = 2127167) B2127167
theorem B1123487 : Blo 495792 1123487 := bstep (se 1 (by rfl) ⟨842615, by rfl⟩ : syracuseStep 1123487 = 1685231) B1685231
theorem B1418543 : Blo 495792 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B894415 : Blo 495792 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B1681127 : Blo 495792 1681127 := bstep (se 1 (by rfl) ⟨1260845, by rfl⟩ : syracuseStep 1681127 = 2521691) B2521691
theorem B1124135 : Blo 495792 1124135 := bstep (se 1 (by rfl) ⟨843101, by rfl⟩ : syracuseStep 1124135 = 1686203) B1686203
theorem B1419079 : Blo 495792 1419079 := bstep (se 1 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 1419079 = 2128619) B2128619
theorem B1419227 : Blo 495792 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B65644643 : Blo 495792 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B1124513 : Blo 495792 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B1255763 : Blo 495792 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1255895 : Blo 495792 1255895 := bstep (se 1 (by rfl) ⟨941921, by rfl⟩ : syracuseStep 1255895 = 1883843) B1883843
theorem B895943 : Blo 495792 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B1682423 : Blo 495792 1682423 := bstep (se 1 (by rfl) ⟨1261817, by rfl⟩ : syracuseStep 1682423 = 2523635) B2523635
theorem B4041731 : Blo 495792 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B896303 : Blo 495792 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B1060217 : Blo 495792 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B3190265 : Blo 495792 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B2829887 : Blo 495792 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B1683287 : Blo 495792 1683287 := bstep (se 1 (by rfl) ⟨1262465, by rfl⟩ : syracuseStep 1683287 = 2524931) B2524931
theorem B1683449 : Blo 495792 1683449 := bstep (se 2 (by rfl) ⟨631293, by rfl⟩ : syracuseStep 1683449 = 1262587) B1262587
theorem B1257889 : Blo 495792 1257889 := bstep (se 2 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 1257889 = 943417) B943417
theorem B1192735 : Blo 495792 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B1684367 : Blo 495792 1684367 := bstep (se 1 (by rfl) ⟨1263275, by rfl⟩ : syracuseStep 1684367 = 2526551) B2526551
theorem B1258679 : Blo 495792 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B2700611 : Blo 495792 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1684907 : Blo 495792 1684907 := bstep (se 1 (by rfl) ⟨1263680, by rfl⟩ : syracuseStep 1684907 = 2527361) B2527361
theorem B1685447 : Blo 495792 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B604139 : Blo 495792 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B5683283 : Blo 495792 5683283 := bstep (se 1 (by rfl) ⟨4262462, by rfl⟩ : syracuseStep 5683283 = 8524925) B8524925
theorem B1685879 : Blo 495792 1685879 := bstep (se 1 (by rfl) ⟨1264409, by rfl⟩ : syracuseStep 1685879 = 2528819) B2528819
theorem B1260137 : Blo 495792 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B4242233 : Blo 495792 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B1261129 : Blo 495792 1261129 := bstep (se 2 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 1261129 = 945847) B945847
theorem B5652665 : Blo 495792 5652665 := bstep (se 2 (by rfl) ⟨2119749, by rfl⟩ : syracuseStep 5652665 = 4239499) B4239499
theorem B6799625 : Blo 495792 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B1261919 : Blo 495792 1261919 := bstep (se 1 (by rfl) ⟨946439, by rfl⟩ : syracuseStep 1261919 = 1892879) B1892879
theorem B6374011 : Blo 495792 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B1590455 : Blo 495792 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B1263073 : Blo 495792 1263073 := bstep (se 2 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 1263073 = 947305) B947305
theorem B1885801 : Blo 495792 1885801 := bstep (se 2 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 1885801 = 1414351) B1414351
theorem B3032761 : Blo 495792 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B6145865 : Blo 495792 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B1591787 : Blo 495792 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B838235 : Blo 495792 838235 := bstep (se 1 (by rfl) ⟨628676, by rfl⟩ : syracuseStep 838235 = 1257353) B1257353
theorem B8276779 : Blo 495792 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1592531 : Blo 495792 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B9719689 : Blo 495792 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B7196597 : Blo 495792 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B1134823 : Blo 495792 1134823 := bstep (se 1 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 1134823 = 1702235) B1702235
theorem B839983 : Blo 495792 839983 := bstep (se 1 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 839983 = 1259975) B1259975
theorem B1593913 : Blo 495792 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B1594529 : Blo 495792 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B3822815 : Blo 495792 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B840955 : Blo 495792 840955 := bstep (se 1 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 840955 = 1261433) B1261433
theorem B7165691 : Blo 495792 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B4249583 : Blo 495792 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B2119871 : Blo 495792 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B743807 : Blo 495792 743807 := bstep (se 1 (by rfl) ⟨557855, by rfl⟩ : syracuseStep 743807 = 1115711) B1115711
theorem B743879 : Blo 495792 743879 := bstep (se 1 (by rfl) ⟨557909, by rfl⟩ : syracuseStep 743879 = 1115819) B1115819
theorem B2841095 : Blo 495792 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B744095 : Blo 495792 744095 := bstep (se 1 (by rfl) ⟨558071, by rfl⟩ : syracuseStep 744095 = 1116143) B1116143
theorem B2513591 : Blo 495792 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B2841277 : Blo 495792 2841277 := bstep (se 3 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 2841277 = 1065479) B1065479
theorem B744239 : Blo 495792 744239 := bstep (se 1 (by rfl) ⟨558179, by rfl⟩ : syracuseStep 744239 = 1116359) B1116359
theorem B1891133 : Blo 495792 1891133 := bstep (se 3 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 1891133 = 709175) B709175
theorem B744329 : Blo 495792 744329 := bstep (se 2 (by rfl) ⟨279123, by rfl⟩ : syracuseStep 744329 = 558247) B558247
theorem B744359 : Blo 495792 744359 := bstep (se 1 (by rfl) ⟨558269, by rfl⟩ : syracuseStep 744359 = 1116539) B1116539
theorem B842663 : Blo 495792 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B51534863 : Blo 495792 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B744539 : Blo 495792 744539 := bstep (se 1 (by rfl) ⟨558404, by rfl⟩ : syracuseStep 744539 = 1116809) B1116809
theorem B744731 : Blo 495792 744731 := bstep (se 1 (by rfl) ⟨558548, by rfl⟩ : syracuseStep 744731 = 1117097) B1117097
theorem B745199 : Blo 495792 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B745385 : Blo 495792 745385 := bstep (se 2 (by rfl) ⟨279519, by rfl⟩ : syracuseStep 745385 = 559039) B559039
theorem B745535 : Blo 495792 745535 := bstep (se 1 (by rfl) ⟨559151, by rfl⟩ : syracuseStep 745535 = 1118303) B1118303
theorem B942187 : Blo 495792 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B2121835 : Blo 495792 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B1892605 : Blo 495792 1892605 := bstep (se 3 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 1892605 = 709727) B709727
theorem B745769 : Blo 495792 745769 := bstep (se 2 (by rfl) ⟨279663, by rfl⟩ : syracuseStep 745769 = 559327) B559327
theorem B746039 : Blo 495792 746039 := bstep (se 1 (by rfl) ⟨559529, by rfl⟩ : syracuseStep 746039 = 1119059) B1119059
theorem B942779 : Blo 495792 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B746399 : Blo 495792 746399 := bstep (se 1 (by rfl) ⟨559799, by rfl⟩ : syracuseStep 746399 = 1119599) B1119599
theorem B2548691 : Blo 495792 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B943159 : Blo 495792 943159 := bstep (se 1 (by rfl) ⟨707369, by rfl⟩ : syracuseStep 943159 = 1414739) B1414739
theorem B943265 : Blo 495792 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B746687 : Blo 495792 746687 := bstep (se 1 (by rfl) ⟨560015, by rfl⟩ : syracuseStep 746687 = 1120031) B1120031
theorem B746831 : Blo 495792 746831 := bstep (se 1 (by rfl) ⟨560123, by rfl⟩ : syracuseStep 746831 = 1120247) B1120247
theorem B746921 : Blo 495792 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B747071 : Blo 495792 747071 := bstep (se 1 (by rfl) ⟨560303, by rfl⟩ : syracuseStep 747071 = 1120607) B1120607
theorem B1894049 : Blo 495792 1894049 := bstep (se 2 (by rfl) ⟨710268, by rfl⟩ : syracuseStep 1894049 = 1420537) B1420537
theorem B2680715 : Blo 495792 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B4253579 : Blo 495792 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B747431 : Blo 495792 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B747551 : Blo 495792 747551 := bstep (se 1 (by rfl) ⟨560663, by rfl⟩ : syracuseStep 747551 = 1121327) B1121327
theorem B2844719 : Blo 495792 2844719 := bstep (se 1 (by rfl) ⟨2133539, by rfl⟩ : syracuseStep 2844719 = 4267079) B4267079
theorem B8481185 : Blo 495792 8481185 := bstep (se 2 (by rfl) ⟨3180444, by rfl⟩ : syracuseStep 8481185 = 6360889) B6360889
theorem B748007 : Blo 495792 748007 := bstep (se 1 (by rfl) ⟨561005, by rfl⟩ : syracuseStep 748007 = 1122011) B1122011
theorem B3238393 : Blo 495792 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B2517641 : Blo 495792 2517641 := bstep (se 2 (by rfl) ⟨944115, by rfl⟩ : syracuseStep 2517641 = 1888231) B1888231
theorem B944777 : Blo 495792 944777 := bstep (se 2 (by rfl) ⟨354291, by rfl⟩ : syracuseStep 944777 = 708583) B708583
theorem B748187 : Blo 495792 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B748409 : Blo 495792 748409 := bstep (se 2 (by rfl) ⟨280653, by rfl⟩ : syracuseStep 748409 = 561307) B561307
theorem B748655 : Blo 495792 748655 := bstep (se 1 (by rfl) ⟨561491, by rfl⟩ : syracuseStep 748655 = 1122983) B1122983
theorem B748751 : Blo 495792 748751 := bstep (se 1 (by rfl) ⟨561563, by rfl⟩ : syracuseStep 748751 = 1123127) B1123127
theorem B748871 : Blo 495792 748871 := bstep (se 1 (by rfl) ⟨561653, by rfl⟩ : syracuseStep 748871 = 1123307) B1123307
theorem B5664329 : Blo 495792 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B749159 : Blo 495792 749159 := bstep (se 1 (by rfl) ⟨561869, by rfl⟩ : syracuseStep 749159 = 1123739) B1123739
theorem B2191033 : Blo 495792 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B749543 : Blo 495792 749543 := bstep (se 1 (by rfl) ⟨562157, by rfl⟩ : syracuseStep 749543 = 1124315) B1124315
theorem B749663 : Blo 495792 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B2519261 : Blo 495792 2519261 := bstep (se 3 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 2519261 = 944723) B944723
theorem B2388295 : Blo 495792 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B2552161 : Blo 495792 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B1798793 : Blo 495792 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B15332647 : Blo 495792 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B184251743 : Blo 495792 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B948095 : Blo 495792 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B23066939 : Blo 495792 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B948763 : Blo 495792 948763 := bstep (se 1 (by rfl) ⟨711572, by rfl⟩ : syracuseStep 948763 = 1423145) B1423145
theorem B2685577 : Blo 495792 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B2522015 : Blo 495792 2522015 := bstep (se 1 (by rfl) ⟨1891511, by rfl⟩ : syracuseStep 2522015 = 3783023) B3783023
theorem B48626851 : Blo 495792 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B851623 : Blo 495792 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B4783859 : Blo 495792 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B3768443 : Blo 495792 3768443 := bstep (se 1 (by rfl) ⟨2826332, by rfl⟩ : syracuseStep 3768443 = 5652665) B5652665
theorem B2523473 : Blo 495792 2523473 := bstep (se 2 (by rfl) ⟨946302, by rfl⟩ : syracuseStep 2523473 = 1892605) B1892605
theorem B3802145 : Blo 495792 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B4097243 : Blo 495792 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B1115639 : Blo 495792 1115639 := bstep (se 1 (by rfl) ⟨836729, by rfl⟩ : syracuseStep 1115639 = 1673459) B1673459
theorem B558823 : Blo 495792 558823 := bstep (se 1 (by rfl) ⟨419117, by rfl⟩ : syracuseStep 558823 = 838235) B838235
theorem B4327519 : Blo 495792 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B1116719 : Blo 495792 1116719 := bstep (se 1 (by rfl) ⟨837539, by rfl⟩ : syracuseStep 1116719 = 1675079) B1675079
theorem B10194173 : Blo 495792 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B1413247 : Blo 495792 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B6361253 : Blo 495792 6361253 := bstep (se 4 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 6361253 = 1192735) B1192735
theorem B1118447 : Blo 495792 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B495871 : Blo 495792 495871 := bstep (se 1 (by rfl) ⟨371903, by rfl⟩ : syracuseStep 495871 = 743807) B743807
theorem B495919 : Blo 495792 495919 := bstep (se 1 (by rfl) ⟨371939, by rfl⟩ : syracuseStep 495919 = 743879) B743879
theorem B496063 : Blo 495792 496063 := bstep (se 1 (by rfl) ⟨372047, by rfl⟩ : syracuseStep 496063 = 744095) B744095
theorem B1675727 : Blo 495792 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B1118699 : Blo 495792 1118699 := bstep (se 1 (by rfl) ⟨839024, by rfl⟩ : syracuseStep 1118699 = 1678049) B1678049
theorem B496159 : Blo 495792 496159 := bstep (se 1 (by rfl) ⟨372119, by rfl⟩ : syracuseStep 496159 = 744239) B744239
theorem B496219 : Blo 495792 496219 := bstep (se 1 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 496219 = 744329) B744329
theorem B496239 : Blo 495792 496239 := bstep (se 1 (by rfl) ⟨372179, by rfl⟩ : syracuseStep 496239 = 744359) B744359
theorem B561775 : Blo 495792 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B496359 : Blo 495792 496359 := bstep (se 1 (by rfl) ⟨372269, by rfl⟩ : syracuseStep 496359 = 744539) B744539
theorem B496487 : Blo 495792 496487 := bstep (se 1 (by rfl) ⟨372365, by rfl⟩ : syracuseStep 496487 = 744731) B744731
theorem B7148573 : Blo 495792 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B496799 : Blo 495792 496799 := bstep (se 1 (by rfl) ⟨372599, by rfl⟩ : syracuseStep 496799 = 745199) B745199
theorem B496923 : Blo 495792 496923 := bstep (se 1 (by rfl) ⟨372692, by rfl⟩ : syracuseStep 496923 = 745385) B745385
theorem B1611037 : Blo 495792 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B497023 : Blo 495792 497023 := bstep (se 1 (by rfl) ⟨372767, by rfl⟩ : syracuseStep 497023 = 745535) B745535
theorem B1119743 : Blo 495792 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B497179 : Blo 495792 497179 := bstep (se 1 (by rfl) ⟨372884, by rfl⟩ : syracuseStep 497179 = 745769) B745769
theorem B1513097 : Blo 495792 1513097 := bstep (se 2 (by rfl) ⟨567411, by rfl⟩ : syracuseStep 1513097 = 1134823) B1134823
theorem B497359 : Blo 495792 497359 := bstep (se 1 (by rfl) ⟨373019, by rfl⟩ : syracuseStep 497359 = 746039) B746039
theorem B1119977 : Blo 495792 1119977 := bstep (se 2 (by rfl) ⟨419991, by rfl⟩ : syracuseStep 1119977 = 839983) B839983
theorem B3184393 : Blo 495792 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B4790123 : Blo 495792 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B1677185 : Blo 495792 1677185 := bstep (se 2 (by rfl) ⟨628944, by rfl⟩ : syracuseStep 1677185 = 1257889) B1257889
theorem B497599 : Blo 495792 497599 := bstep (se 1 (by rfl) ⟨373199, by rfl⟩ : syracuseStep 497599 = 746399) B746399
theorem B497791 : Blo 495792 497791 := bstep (se 1 (by rfl) ⟨373343, by rfl⟩ : syracuseStep 497791 = 746687) B746687
theorem B497887 : Blo 495792 497887 := bstep (se 1 (by rfl) ⟨373415, by rfl⟩ : syracuseStep 497887 = 746831) B746831
theorem B497947 : Blo 495792 497947 := bstep (se 1 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 497947 = 746921) B746921
theorem B498047 : Blo 495792 498047 := bstep (se 1 (by rfl) ⟨373535, by rfl⟩ : syracuseStep 498047 = 747071) B747071
theorem B1120751 : Blo 495792 1120751 := bstep (se 1 (by rfl) ⟨840563, by rfl⟩ : syracuseStep 1120751 = 1681127) B1681127
theorem B498287 : Blo 495792 498287 := bstep (se 1 (by rfl) ⟨373715, by rfl⟩ : syracuseStep 498287 = 747431) B747431
theorem B498367 : Blo 495792 498367 := bstep (se 1 (by rfl) ⟨373775, by rfl⟩ : syracuseStep 498367 = 747551) B747551
theorem B498671 : Blo 495792 498671 := bstep (se 1 (by rfl) ⟨374003, by rfl⟩ : syracuseStep 498671 = 748007) B748007
theorem B1121273 : Blo 495792 1121273 := bstep (se 2 (by rfl) ⟨420477, by rfl⟩ : syracuseStep 1121273 = 840955) B840955
theorem B1678427 : Blo 495792 1678427 := bstep (se 1 (by rfl) ⟨1258820, by rfl⟩ : syracuseStep 1678427 = 2517641) B2517641
theorem B629851 : Blo 495792 629851 := bstep (se 1 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 629851 = 944777) B944777
theorem B498791 : Blo 495792 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B498939 : Blo 495792 498939 := bstep (se 1 (by rfl) ⟨374204, by rfl⟩ : syracuseStep 498939 = 748409) B748409
theorem B597295 : Blo 495792 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B1121615 : Blo 495792 1121615 := bstep (se 1 (by rfl) ⟨841211, by rfl⟩ : syracuseStep 1121615 = 1682423) B1682423
theorem B2694487 : Blo 495792 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B499103 : Blo 495792 499103 := bstep (se 1 (by rfl) ⟨374327, by rfl⟩ : syracuseStep 499103 = 748655) B748655
theorem B499167 : Blo 495792 499167 := bstep (se 1 (by rfl) ⟨374375, by rfl⟩ : syracuseStep 499167 = 748751) B748751
theorem B499247 : Blo 495792 499247 := bstep (se 1 (by rfl) ⟨374435, by rfl⟩ : syracuseStep 499247 = 748871) B748871
theorem B3776219 : Blo 495792 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B499439 : Blo 495792 499439 := bstep (se 1 (by rfl) ⟨374579, by rfl⟩ : syracuseStep 499439 = 749159) B749159
theorem B1122191 : Blo 495792 1122191 := bstep (se 1 (by rfl) ⟨841643, by rfl⟩ : syracuseStep 1122191 = 1683287) B1683287
theorem B499695 : Blo 495792 499695 := bstep (se 1 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 499695 = 749543) B749543
theorem B1122299 : Blo 495792 1122299 := bstep (se 1 (by rfl) ⟨841724, by rfl⟩ : syracuseStep 1122299 = 1683449) B1683449
theorem B499775 : Blo 495792 499775 := bstep (se 1 (by rfl) ⟨374831, by rfl⟩ : syracuseStep 499775 = 749663) B749663
theorem B1679507 : Blo 495792 1679507 := bstep (se 1 (by rfl) ⟨1259630, by rfl⟩ : syracuseStep 1679507 = 2519261) B2519261
theorem B1122911 : Blo 495792 1122911 := bstep (se 1 (by rfl) ⟨842183, by rfl⟩ : syracuseStep 1122911 = 1684367) B1684367
theorem B3580769 : Blo 495792 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B1123271 : Blo 495792 1123271 := bstep (se 1 (by rfl) ⟨842453, by rfl⟩ : syracuseStep 1123271 = 1684907) B1684907
theorem B69215269 : Blo 495792 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B632063 : Blo 495792 632063 := bstep (se 1 (by rfl) ⟨474047, by rfl⟩ : syracuseStep 632063 = 948095) B948095
theorem B1123631 : Blo 495792 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B15377959 : Blo 495792 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B1123919 : Blo 495792 1123919 := bstep (se 1 (by rfl) ⟨842939, by rfl⟩ : syracuseStep 1123919 = 1685879) B1685879
theorem B2828155 : Blo 495792 2828155 := bstep (se 1 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 2828155 = 4242233) B4242233
theorem B1681343 : Blo 495792 1681343 := bstep (se 1 (by rfl) ⟨1261007, by rfl⟩ : syracuseStep 1681343 = 2522015) B2522015
theorem B1681505 : Blo 495792 1681505 := bstep (se 2 (by rfl) ⟨630564, by rfl⟩ : syracuseStep 1681505 = 1261129) B1261129
theorem B1058953 : Blo 495792 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B3189239 : Blo 495792 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B1256249 : Blo 495792 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B2829113 : Blo 495792 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B4533083 : Blo 495792 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B1060303 : Blo 495792 1060303 := bstep (se 1 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 1060303 = 1590455) B1590455
theorem B8498681 : Blo 495792 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B1257545 : Blo 495792 1257545 := bstep (se 2 (by rfl) ⟨471579, by rfl⟩ : syracuseStep 1257545 = 943159) B943159
theorem B1061191 : Blo 495792 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1192553 : Blo 495792 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1684097 : Blo 495792 1684097 := bstep (se 2 (by rfl) ⟨631536, by rfl⟩ : syracuseStep 1684097 = 1263073) B1263073
theorem B5681825 : Blo 495792 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B1061687 : Blo 495792 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B2274131 : Blo 495792 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B4043681 : Blo 495792 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B4797731 : Blo 495792 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1685339 : Blo 495792 1685339 := bstep (se 1 (by rfl) ⟨1264004, by rfl⟩ : syracuseStep 1685339 = 2528009) B2528009
theorem B1063019 : Blo 495792 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B2833055 : Blo 495792 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B900031 : Blo 495792 900031 := bstep (se 1 (by rfl) ⟨675023, by rfl⟩ : syracuseStep 900031 = 1350047) B1350047
theorem B1686635 : Blo 495792 1686635 := bstep (se 1 (by rfl) ⟨1264976, by rfl⟩ : syracuseStep 1686635 = 2529953) B2529953
theorem B1260755 : Blo 495792 1260755 := bstep (se 1 (by rfl) ⟨945566, by rfl⟩ : syracuseStep 1260755 = 1891133) B1891133
theorem B34356575 : Blo 495792 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B12959585 : Blo 495792 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B3784967 : Blo 495792 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B1884647 : Blo 495792 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B3589073 : Blo 495792 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1262699 : Blo 495792 1262699 := bstep (se 1 (by rfl) ⟨947024, by rfl⟩ : syracuseStep 1262699 = 1894049) B1894049
theorem B2835719 : Blo 495792 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B43763095 : Blo 495792 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B837175 : Blo 495792 837175 := bstep (se 1 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 837175 = 1255763) B1255763
theorem B5654123 : Blo 495792 5654123 := bstep (se 1 (by rfl) ⟨4240592, by rfl⟩ : syracuseStep 5654123 = 8481185) B8481185
theorem B837263 : Blo 495792 837263 := bstep (se 1 (by rfl) ⟨627947, by rfl⟩ : syracuseStep 837263 = 1255895) B1255895
theorem B706811 : Blo 495792 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B1886591 : Blo 495792 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B1199195 : Blo 495792 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B1265017 : Blo 495792 1265017 := bstep (se 2 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 1265017 = 948763) B948763
theorem B839119 : Blo 495792 839119 := bstep (se 1 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 839119 = 1258679) B1258679
theorem B4541989 : Blo 495792 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B122834495 : Blo 495792 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B3788369 : Blo 495792 3788369 := bstep (se 2 (by rfl) ⟨1420638, by rfl⟩ : syracuseStep 3788369 = 2841277) B2841277
theorem B11685509 : Blo 495792 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B3788855 : Blo 495792 3788855 := bstep (se 1 (by rfl) ⟨2841641, by rfl⟩ : syracuseStep 3788855 = 5683283) B5683283
theorem B64835801 : Blo 495792 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B840091 : Blo 495792 840091 := bstep (se 1 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 840091 = 1260137) B1260137
theorem B3233191 : Blo 495792 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B841279 : Blo 495792 841279 := bstep (se 1 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 841279 = 1261919) B1261919
theorem B2840345 : Blo 495792 2840345 := bstep (se 2 (by rfl) ⟨1065129, by rfl⟩ : syracuseStep 2840345 = 2130259) B2130259
theorem B743783 : Blo 495792 743783 := bstep (se 1 (by rfl) ⟨557837, by rfl⟩ : syracuseStep 743783 = 1115675) B1115675
theorem B743849 : Blo 495792 743849 := bstep (se 2 (by rfl) ⟨278943, by rfl⟩ : syracuseStep 743849 = 557887) B557887
theorem B2841551 : Blo 495792 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B2514077 : Blo 495792 2514077 := bstep (se 3 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 2514077 = 942779) B942779
theorem B941519 : Blo 495792 941519 := bstep (se 1 (by rfl) ⟨706139, by rfl⟩ : syracuseStep 941519 = 1412279) B1412279
theorem B2514401 : Blo 495792 2514401 := bstep (se 2 (by rfl) ⟨942900, by rfl⟩ : syracuseStep 2514401 = 1885801) B1885801
theorem B1892105 : Blo 495792 1892105 := bstep (se 2 (by rfl) ⟨709539, by rfl⟩ : syracuseStep 1892105 = 1419079) B1419079
theorem B2383951 : Blo 495792 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B4022399 : Blo 495792 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B2515373 : Blo 495792 2515373 := bstep (se 3 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 2515373 = 943265) B943265
theorem B4317857 : Blo 495792 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B746267 : Blo 495792 746267 := bstep (se 1 (by rfl) ⟨559700, by rfl⟩ : syracuseStep 746267 = 1119401) B1119401
theorem B4023175 : Blo 495792 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B1008617 : Blo 495792 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B746537 : Blo 495792 746537 := bstep (se 2 (by rfl) ⟨279951, by rfl⟩ : syracuseStep 746537 = 559903) B559903
theorem B11035705 : Blo 495792 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B4777127 : Blo 495792 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B1009007 : Blo 495792 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B1894063 : Blo 495792 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B747239 : Blo 495792 747239 := bstep (se 1 (by rfl) ⟨560429, by rfl⟩ : syracuseStep 747239 = 1120859) B1120859
theorem B4024475 : Blo 495792 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B1075879 : Blo 495792 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B748457 : Blo 495792 748457 := bstep (se 2 (by rfl) ⟨280671, by rfl⟩ : syracuseStep 748457 = 561343) B561343
theorem B748571 : Blo 495792 748571 := bstep (se 1 (by rfl) ⟨561428, by rfl⟩ : syracuseStep 748571 = 1122857) B1122857
theorem B3402881 : Blo 495792 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B748775 : Blo 495792 748775 := bstep (se 1 (by rfl) ⟨561581, by rfl⟩ : syracuseStep 748775 = 1123163) B1123163
theorem B945407 : Blo 495792 945407 := bstep (se 1 (by rfl) ⟨709055, by rfl⟩ : syracuseStep 945407 = 1418111) B1418111
theorem B1699127 : Blo 495792 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B2125217 : Blo 495792 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B748991 : Blo 495792 748991 := bstep (se 1 (by rfl) ⟨561743, by rfl⟩ : syracuseStep 748991 = 1123487) B1123487
theorem B945695 : Blo 495792 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B749423 : Blo 495792 749423 := bstep (se 1 (by rfl) ⟨562067, by rfl⟩ : syracuseStep 749423 = 1124135) B1124135
theorem B946151 : Blo 495792 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B1896479 : Blo 495792 1896479 := bstep (se 1 (by rfl) ⟨1422359, by rfl⟩ : syracuseStep 1896479 = 2844719) B2844719
theorem B749675 : Blo 495792 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B20443529 : Blo 495792 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B2126843 : Blo 495792 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B2390141 : Blo 495792 2390141 := bstep (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) B896303
theorem B1800407 : Blo 495792 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B3178601 : Blo 495792 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B2523311 : Blo 495792 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B2392715 : Blo 495792 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B3769415 : Blo 495792 3769415 := bstep (se 1 (by rfl) ⟨2827061, by rfl⟩ : syracuseStep 3769415 = 5654123) B5654123
theorem B558175 : Blo 495792 558175 := bstep (se 1 (by rfl) ⟨418631, by rfl⟩ : syracuseStep 558175 = 837263) B837263
theorem B14714273 : Blo 495792 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1116233 : Blo 495792 1116233 := bstep (se 2 (by rfl) ⟨418587, by rfl⟩ : syracuseStep 1116233 = 837175) B837175
theorem B2525417 : Blo 495792 2525417 := bstep (se 2 (by rfl) ⟨947031, by rfl⟩ : syracuseStep 2525417 = 1894063) B1894063
theorem B81889663 : Blo 495792 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B2525579 : Blo 495792 2525579 := bstep (se 1 (by rfl) ⟨1894184, by rfl⟩ : syracuseStep 2525579 = 3788369) B3788369
theorem B3770873 : Blo 495792 3770873 := bstep (se 2 (by rfl) ⟨1414077, by rfl⟩ : syracuseStep 3770873 = 2828155) B2828155
theorem B2689645 : Blo 495792 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B2525903 : Blo 495792 2525903 := bstep (se 1 (by rfl) ⟨1894427, by rfl⟩ : syracuseStep 2525903 = 3788855) B3788855
theorem B5770025 : Blo 495792 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B43223867 : Blo 495792 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B1411937 : Blo 495792 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B1117151 : Blo 495792 1117151 := bstep (se 1 (by rfl) ⟨837863, by rfl⟩ : syracuseStep 1117151 = 1675727) B1675727
theorem B1118123 : Blo 495792 1118123 := bstep (se 1 (by rfl) ⟨838592, by rfl⟩ : syracuseStep 1118123 = 1677185) B1677185
theorem B495855 : Blo 495792 495855 := bstep (se 1 (by rfl) ⟨371891, by rfl⟩ : syracuseStep 495855 = 743783) B743783
theorem B495899 : Blo 495792 495899 := bstep (se 1 (by rfl) ⟨371924, by rfl⟩ : syracuseStep 495899 = 743849) B743849
theorem B1413737 : Blo 495792 1413737 := bstep (se 2 (by rfl) ⟨530151, by rfl⟩ : syracuseStep 1413737 = 1060303) B1060303
theorem B1118825 : Blo 495792 1118825 := bstep (se 2 (by rfl) ⟨419559, by rfl⟩ : syracuseStep 1118825 = 839119) B839119
theorem B1118951 : Blo 495792 1118951 := bstep (se 1 (by rfl) ⟨839213, by rfl⟩ : syracuseStep 1118951 = 1678427) B1678427
theorem B1676051 : Blo 495792 1676051 := bstep (se 1 (by rfl) ⟨1257038, by rfl⟩ : syracuseStep 1676051 = 2514077) B2514077
theorem B627679 : Blo 495792 627679 := bstep (se 1 (by rfl) ⟨470759, by rfl⟩ : syracuseStep 627679 = 941519) B941519
theorem B1676267 : Blo 495792 1676267 := bstep (se 1 (by rfl) ⟨1257200, by rfl⟩ : syracuseStep 1676267 = 2514401) B2514401
theorem B1119671 : Blo 495792 1119671 := bstep (se 1 (by rfl) ⟨839753, by rfl⟩ : syracuseStep 1119671 = 1679507) B1679507
theorem B1676915 : Blo 495792 1676915 := bstep (se 1 (by rfl) ⟨1257686, by rfl⟩ : syracuseStep 1676915 = 2515373) B2515373
theorem B1414921 : Blo 495792 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B497511 : Blo 495792 497511 := bstep (se 1 (by rfl) ⟨373133, by rfl⟩ : syracuseStep 497511 = 746267) B746267
theorem B1120121 : Blo 495792 1120121 := bstep (se 2 (by rfl) ⟨420045, by rfl⟩ : syracuseStep 1120121 = 840091) B840091
theorem B497691 : Blo 495792 497691 := bstep (se 1 (by rfl) ⟨373268, by rfl⟩ : syracuseStep 497691 = 746537) B746537
theorem B3184751 : Blo 495792 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B498159 : Blo 495792 498159 := bstep (se 1 (by rfl) ⟨373619, by rfl⟩ : syracuseStep 498159 = 747239) B747239
theorem B1120895 : Blo 495792 1120895 := bstep (se 1 (by rfl) ⟨840671, by rfl⟩ : syracuseStep 1120895 = 1681343) B1681343
theorem B1121003 : Blo 495792 1121003 := bstep (se 1 (by rfl) ⟨840752, by rfl⟩ : syracuseStep 1121003 = 1681505) B1681505
theorem B3022055 : Blo 495792 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B498971 : Blo 495792 498971 := bstep (se 1 (by rfl) ⟨374228, by rfl⟩ : syracuseStep 498971 = 748457) B748457
theorem B499047 : Blo 495792 499047 := bstep (se 1 (by rfl) ⟨374285, by rfl⟩ : syracuseStep 499047 = 748571) B748571
theorem B1121705 : Blo 495792 1121705 := bstep (se 2 (by rfl) ⟨420639, by rfl⟩ : syracuseStep 1121705 = 841279) B841279
theorem B2268587 : Blo 495792 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B499183 : Blo 495792 499183 := bstep (se 1 (by rfl) ⟨374387, by rfl⟩ : syracuseStep 499183 = 748775) B748775
theorem B630271 : Blo 495792 630271 := bstep (se 1 (by rfl) ⟨472703, by rfl⟩ : syracuseStep 630271 = 945407) B945407
theorem B499327 : Blo 495792 499327 := bstep (se 1 (by rfl) ⟨374495, by rfl⟩ : syracuseStep 499327 = 748991) B748991
theorem B499615 : Blo 495792 499615 := bstep (se 1 (by rfl) ⟨374711, by rfl⟩ : syracuseStep 499615 = 749423) B749423
theorem B630767 : Blo 495792 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B499783 : Blo 495792 499783 := bstep (se 1 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 499783 = 749675) B749675
theorem B795035 : Blo 495792 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B1122731 : Blo 495792 1122731 := bstep (se 1 (by rfl) ⟨842048, by rfl⟩ : syracuseStep 1122731 = 1684097) B1684097
theorem B1516087 : Blo 495792 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B2695787 : Blo 495792 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B1417895 : Blo 495792 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B1123559 : Blo 495792 1123559 := bstep (se 1 (by rfl) ⟨842669, by rfl⟩ : syracuseStep 1123559 = 1685339) B1685339
theorem B796393 : Blo 495792 796393 := bstep (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) B597295
theorem B1124423 : Blo 495792 1124423 := bstep (se 1 (by rfl) ⟨843317, by rfl⟩ : syracuseStep 1124423 = 1686635) B1686635
theorem B1682315 : Blo 495792 1682315 := bstep (se 1 (by rfl) ⟨1261736, by rfl⟩ : syracuseStep 1682315 = 2523473) B2523473
theorem B1256431 : Blo 495792 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B2731495 : Blo 495792 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B92287025 : Blo 495792 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B1257727 : Blo 495792 1257727 := bstep (se 1 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 1257727 = 1886591) B1886591
theorem B799463 : Blo 495792 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B6796115 : Blo 495792 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B10139053 : Blo 495792 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B4240835 : Blo 495792 4240835 := bstep (se 1 (by rfl) ⟨3180626, by rfl⟩ : syracuseStep 4240835 = 6361253) B6361253
theorem B1685501 : Blo 495792 1685501 := bstep (se 3 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 1685501 = 632063) B632063
theorem B4765715 : Blo 495792 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B12793949 : Blo 495792 12793949 := bstep (se 3 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 12793949 = 4797731) B4797731
theorem B3193415 : Blo 495792 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B1686689 : Blo 495792 1686689 := bstep (se 2 (by rfl) ⟨632508, by rfl⟩ : syracuseStep 1686689 = 1265017) B1265017
theorem B1261403 : Blo 495792 1261403 := bstep (se 1 (by rfl) ⟨946052, by rfl⟩ : syracuseStep 1261403 = 1892105) B1892105
theorem B1884329 : Blo 495792 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B1884829 : Blo 495792 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B672671 : Blo 495792 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B2148049 : Blo 495792 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B837499 : Blo 495792 837499 := bstep (se 1 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 837499 = 1256249) B1256249
theorem B1886075 : Blo 495792 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B4310921 : Blo 495792 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B1132751 : Blo 495792 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B4245857 : Blo 495792 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B1264319 : Blo 495792 1264319 := bstep (se 1 (by rfl) ⟨948239, by rfl⟩ : syracuseStep 1264319 = 1896479) B1896479
theorem B838363 : Blo 495792 838363 := bstep (se 1 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 838363 = 1257545) B1257545
theorem B3787883 : Blo 495792 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B707791 : Blo 495792 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B1200041 : Blo 495792 1200041 := bstep (se 2 (by rfl) ⟨450015, by rfl⟩ : syracuseStep 1200041 = 900031) B900031
theorem B708679 : Blo 495792 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B1593427 : Blo 495792 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B839801 : Blo 495792 839801 := bstep (se 2 (by rfl) ⟨314925, by rfl⟩ : syracuseStep 839801 = 629851) B629851
theorem B1200271 : Blo 495792 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1888703 : Blo 495792 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B3592649 : Blo 495792 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B840503 : Blo 495792 840503 := bstep (se 1 (by rfl) ⟨630377, by rfl⟩ : syracuseStep 840503 = 1260755) B1260755
theorem B8639723 : Blo 495792 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B2512295 : Blo 495792 2512295 := bstep (se 1 (by rfl) ⟨1884221, by rfl⟩ : syracuseStep 2512295 = 3768443) B3768443
theorem B841799 : Blo 495792 841799 := bstep (se 1 (by rfl) ⟨631349, by rfl⟩ : syracuseStep 841799 = 1262699) B1262699
theorem B1890479 : Blo 495792 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B743759 : Blo 495792 743759 := bstep (se 1 (by rfl) ⟨557819, by rfl⟩ : syracuseStep 743759 = 1115639) B1115639
theorem B5364233 : Blo 495792 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B744479 : Blo 495792 744479 := bstep (se 1 (by rfl) ⟨558359, by rfl⟩ : syracuseStep 744479 = 1116719) B1116719
theorem B58350793 : Blo 495792 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B20503945 : Blo 495792 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B745097 : Blo 495792 745097 := bstep (se 2 (by rfl) ⟨279411, by rfl⟩ : syracuseStep 745097 = 558823) B558823
theorem B7790339 : Blo 495792 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B745631 : Blo 495792 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B745799 : Blo 495792 745799 := bstep (se 1 (by rfl) ⟨559349, by rfl⟩ : syracuseStep 745799 = 1118699) B1118699
theorem B1434505 : Blo 495792 1434505 := bstep (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) B1075879
theorem B746495 : Blo 495792 746495 := bstep (se 1 (by rfl) ⟨559871, by rfl⟩ : syracuseStep 746495 = 1119743) B1119743
theorem B1008731 : Blo 495792 1008731 := bstep (se 1 (by rfl) ⟨756548, by rfl⟩ : syracuseStep 1008731 = 1513097) B1513097
theorem B746651 : Blo 495792 746651 := bstep (se 1 (by rfl) ⟨559988, by rfl⟩ : syracuseStep 746651 = 1119977) B1119977
theorem B1893563 : Blo 495792 1893563 := bstep (se 1 (by rfl) ⟨1420172, by rfl⟩ : syracuseStep 1893563 = 2840345) B2840345
theorem B747167 : Blo 495792 747167 := bstep (se 1 (by rfl) ⟨560375, by rfl⟩ : syracuseStep 747167 = 1120751) B1120751
theorem B1894367 : Blo 495792 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B747515 : Blo 495792 747515 := bstep (se 1 (by rfl) ⟨560636, by rfl⟩ : syracuseStep 747515 = 1121273) B1121273
theorem B6055985 : Blo 495792 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B747743 : Blo 495792 747743 := bstep (se 1 (by rfl) ⟨560807, by rfl⟩ : syracuseStep 747743 = 1121615) B1121615
theorem B2517479 : Blo 495792 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B748127 : Blo 495792 748127 := bstep (se 1 (by rfl) ⟨561095, by rfl⟩ : syracuseStep 748127 = 1122191) B1122191
theorem B748199 : Blo 495792 748199 := bstep (se 1 (by rfl) ⟨561149, by rfl⟩ : syracuseStep 748199 = 1122299) B1122299
theorem B2681599 : Blo 495792 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B748607 : Blo 495792 748607 := bstep (se 1 (by rfl) ⟨561455, by rfl⟩ : syracuseStep 748607 = 1122911) B1122911
theorem B2878571 : Blo 495792 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B2387179 : Blo 495792 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B748847 : Blo 495792 748847 := bstep (se 1 (by rfl) ⟨561635, by rfl⟩ : syracuseStep 748847 = 1123271) B1123271
theorem B749033 : Blo 495792 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B749087 : Blo 495792 749087 := bstep (se 1 (by rfl) ⟨561815, by rfl⟩ : syracuseStep 749087 = 1123631) B1123631
theorem B749279 : Blo 495792 749279 := bstep (se 1 (by rfl) ⟨561959, by rfl⟩ : syracuseStep 749279 = 1123919) B1123919
theorem B2682983 : Blo 495792 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B2126159 : Blo 495792 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B5665787 : Blo 495792 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B13629019 : Blo 495792 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B5667245 : Blo 495792 5667245 := bstep (se 3 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 5667245 = 2125217) B2125217
theorem B2521853 : Blo 495792 2521853 := bstep (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) B945695
theorem B22904383 : Blo 495792 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B2525255 : Blo 495792 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B1116665 : Blo 495792 1116665 := bstep (se 2 (by rfl) ⟨418749, by rfl⟩ : syracuseStep 1116665 = 837499) B837499
theorem B559867 : Blo 495792 559867 := bstep (se 1 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 559867 = 839801) B839801
theorem B2689949 : Blo 495792 2689949 := bstep (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) B1008731
theorem B2395099 : Blo 495792 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B109186217 : Blo 495792 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B1117367 : Blo 495792 1117367 := bstep (se 1 (by rfl) ⟨838025, by rfl⟩ : syracuseStep 1117367 = 1676051) B1676051
theorem B560335 : Blo 495792 560335 := bstep (se 1 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 560335 = 840503) B840503
theorem B23039261 : Blo 495792 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B1117511 : Blo 495792 1117511 := bstep (se 1 (by rfl) ⟨838133, by rfl⟩ : syracuseStep 1117511 = 1676267) B1676267
theorem B1674863 : Blo 495792 1674863 := bstep (se 1 (by rfl) ⟨1256147, by rfl⟩ : syracuseStep 1674863 = 2512295) B2512295
theorem B1117817 : Blo 495792 1117817 := bstep (se 2 (by rfl) ⟨419181, by rfl⟩ : syracuseStep 1117817 = 838363) B838363
theorem B3575465 : Blo 495792 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B1117943 : Blo 495792 1117943 := bstep (se 1 (by rfl) ⟨838457, by rfl⟩ : syracuseStep 1117943 = 1676915) B1676915
theorem B1675241 : Blo 495792 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B561199 : Blo 495792 561199 := bstep (se 1 (by rfl) ⟨420899, by rfl⟩ : syracuseStep 561199 = 841799) B841799
theorem B495839 : Blo 495792 495839 := bstep (se 1 (by rfl) ⟨371879, by rfl⟩ : syracuseStep 495839 = 743759) B743759
theorem B3182905 : Blo 495792 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B3576155 : Blo 495792 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B3641993 : Blo 495792 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B496319 : Blo 495792 496319 := bstep (se 1 (by rfl) ⟨372239, by rfl⟩ : syracuseStep 496319 = 744479) B744479
theorem B1512391 : Blo 495792 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B496731 : Blo 495792 496731 := bstep (se 1 (by rfl) ⟨372548, by rfl⟩ : syracuseStep 496731 = 745097) B745097
theorem B497087 : Blo 495792 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B497199 : Blo 495792 497199 := bstep (se 1 (by rfl) ⟨372899, by rfl⟩ : syracuseStep 497199 = 745799) B745799
theorem B1676969 : Blo 495792 1676969 := bstep (se 2 (by rfl) ⟨628863, by rfl⟩ : syracuseStep 1676969 = 1257727) B1257727
theorem B3020669 : Blo 495792 3020669 := bstep (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) B1132751
theorem B497663 : Blo 495792 497663 := bstep (se 1 (by rfl) ⟨373247, by rfl⟩ : syracuseStep 497663 = 746495) B746495
theorem B497767 : Blo 495792 497767 := bstep (se 1 (by rfl) ⟨373325, by rfl⟩ : syracuseStep 497767 = 746651) B746651
theorem B498111 : Blo 495792 498111 := bstep (se 1 (by rfl) ⟨373583, by rfl⟩ : syracuseStep 498111 = 747167) B747167
theorem B498343 : Blo 495792 498343 := bstep (se 1 (by rfl) ⟨373757, by rfl⟩ : syracuseStep 498343 = 747515) B747515
theorem B4037323 : Blo 495792 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B498495 : Blo 495792 498495 := bstep (se 1 (by rfl) ⟨373871, by rfl⟩ : syracuseStep 498495 = 747743) B747743
theorem B1678319 : Blo 495792 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B498751 : Blo 495792 498751 := bstep (se 1 (by rfl) ⟨374063, by rfl⟩ : syracuseStep 498751 = 748127) B748127
theorem B498799 : Blo 495792 498799 := bstep (se 1 (by rfl) ⟨374099, by rfl⟩ : syracuseStep 498799 = 748199) B748199
theorem B1121543 : Blo 495792 1121543 := bstep (se 1 (by rfl) ⟨841157, by rfl⟩ : syracuseStep 1121543 = 1682315) B1682315
theorem B499071 : Blo 495792 499071 := bstep (se 1 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 499071 = 748607) B748607
theorem B109354373 : Blo 495792 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B499231 : Blo 495792 499231 := bstep (se 1 (by rfl) ⟨374423, by rfl⟩ : syracuseStep 499231 = 748847) B748847
theorem B499355 : Blo 495792 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B499391 : Blo 495792 499391 := bstep (se 1 (by rfl) ⟨374543, by rfl⟩ : syracuseStep 499391 = 749087) B749087
theorem B499519 : Blo 495792 499519 := bstep (se 1 (by rfl) ⟨374639, by rfl⟩ : syracuseStep 499519 = 749279) B749279
theorem B1417439 : Blo 495792 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B532975 : Blo 495792 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B4530743 : Blo 495792 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B3777191 : Blo 495792 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B2827223 : Blo 495792 2827223 := bstep (se 1 (by rfl) ⟨2120417, by rfl⟩ : syracuseStep 2827223 = 4240835) B4240835
theorem B1123667 : Blo 495792 1123667 := bstep (se 1 (by rfl) ⟨842750, by rfl⟩ : syracuseStep 1123667 = 1685501) B1685501
theorem B8529299 : Blo 495792 8529299 := bstep (se 1 (by rfl) ⟨6396974, by rfl⟩ : syracuseStep 8529299 = 12793949) B12793949
theorem B77801057 : Blo 495792 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B3778163 : Blo 495792 3778163 := bstep (se 1 (by rfl) ⟨2833622, by rfl⟩ : syracuseStep 3778163 = 5667245) B5667245
theorem B1681235 : Blo 495792 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B1124459 : Blo 495792 1124459 := bstep (se 1 (by rfl) ⟨843344, by rfl⟩ : syracuseStep 1124459 = 1686689) B1686689
theorem B1682045 : Blo 495792 1682045 := bstep (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) B630767
theorem B1256219 : Blo 495792 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B1682207 : Blo 495792 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B3779621 : Blo 495792 3779621 := bstep (se 4 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 3779621 = 708679) B708679
theorem B9809515 : Blo 495792 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B1912673 : Blo 495792 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B1257383 : Blo 495792 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B1683611 : Blo 495792 1683611 := bstep (se 1 (by rfl) ⟨1262708, by rfl⟩ : syracuseStep 1683611 = 2525417) B2525417
theorem B2830571 : Blo 495792 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B1683719 : Blo 495792 1683719 := bstep (se 1 (by rfl) ⟨1262789, by rfl⟩ : syracuseStep 1683719 = 2525579) B2525579
theorem B1683935 : Blo 495792 1683935 := bstep (se 1 (by rfl) ⟨1262951, by rfl⟩ : syracuseStep 1683935 = 2525903) B2525903
theorem B3846683 : Blo 495792 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B28815911 : Blo 495792 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B2864065 : Blo 495792 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1061857 : Blo 495792 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B800027 : Blo 495792 800027 := bstep (se 1 (by rfl) ⟨600020, by rfl⟩ : syracuseStep 800027 = 1200041) B1200041
theorem B1259135 : Blo 495792 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B3586193 : Blo 495792 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1260319 : Blo 495792 1260319 := bstep (se 1 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 1260319 = 1890479) B1890479
theorem B2014703 : Blo 495792 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B5193559 : Blo 495792 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B1262375 : Blo 495792 1262375 := bstep (se 1 (by rfl) ⟨946781, by rfl⟩ : syracuseStep 1262375 = 1893563) B1893563
theorem B836905 : Blo 495792 836905 := bstep (se 2 (by rfl) ⟨313839, by rfl⟩ : syracuseStep 836905 = 627679) B627679
theorem B1262911 : Blo 495792 1262911 := bstep (se 1 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 1262911 = 1894367) B1894367
theorem B13518737 : Blo 495792 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B1919047 : Blo 495792 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B18172025 : Blo 495792 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1886561 : Blo 495792 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B61524683 : Blo 495792 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B1788655 : Blo 495792 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B840361 : Blo 495792 840361 := bstep (se 2 (by rfl) ⟨315135, by rfl⟩ : syracuseStep 840361 = 630271) B630271
theorem B840935 : Blo 495792 840935 := bstep (se 1 (by rfl) ⟨630701, by rfl⟩ : syracuseStep 840935 = 1261403) B1261403
theorem B2119067 : Blo 495792 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B1595143 : Blo 495792 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B2512943 : Blo 495792 2512943 := bstep (se 1 (by rfl) ⟨1884707, by rfl⟩ : syracuseStep 2512943 = 3769415) B3769415
theorem B2021449 : Blo 495792 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B2513105 : Blo 495792 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B2120093 : Blo 495792 2120093 := bstep (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) B795035
theorem B744155 : Blo 495792 744155 := bstep (se 1 (by rfl) ⟨558116, by rfl⟩ : syracuseStep 744155 = 1116233) B1116233
theorem B744233 : Blo 495792 744233 := bstep (se 2 (by rfl) ⟨279087, by rfl⟩ : syracuseStep 744233 = 558175) B558175
theorem B2513915 : Blo 495792 2513915 := bstep (se 1 (by rfl) ⟨1885436, by rfl⟩ : syracuseStep 2513915 = 3770873) B3770873
theorem B842879 : Blo 495792 842879 := bstep (se 1 (by rfl) ⟨632159, by rfl⟩ : syracuseStep 842879 = 1264319) B1264319
theorem B941291 : Blo 495792 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B744767 : Blo 495792 744767 := bstep (se 1 (by rfl) ⟨558575, by rfl⟩ : syracuseStep 744767 = 1117151) B1117151
theorem B1793789 : Blo 495792 1793789 := bstep (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) B672671
theorem B745415 : Blo 495792 745415 := bstep (se 1 (by rfl) ⟨559061, by rfl⟩ : syracuseStep 745415 = 1118123) B1118123
theorem B942491 : Blo 495792 942491 := bstep (se 1 (by rfl) ⟨706868, by rfl⟩ : syracuseStep 942491 = 1413737) B1413737
theorem B745883 : Blo 495792 745883 := bstep (se 1 (by rfl) ⟨559412, by rfl⟩ : syracuseStep 745883 = 1118825) B1118825
theorem B745967 : Blo 495792 745967 := bstep (se 1 (by rfl) ⟨559475, by rfl⟩ : syracuseStep 745967 = 1118951) B1118951
theorem B746447 : Blo 495792 746447 := bstep (se 1 (by rfl) ⟨559835, by rfl⟩ : syracuseStep 746447 = 1119671) B1119671
theorem B746747 : Blo 495792 746747 := bstep (se 1 (by rfl) ⟨560060, by rfl⟩ : syracuseStep 746747 = 1120121) B1120121
theorem B2123167 : Blo 495792 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B943721 : Blo 495792 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B747263 : Blo 495792 747263 := bstep (se 1 (by rfl) ⟨560447, by rfl⟩ : syracuseStep 747263 = 1120895) B1120895
theorem B747335 : Blo 495792 747335 := bstep (se 1 (by rfl) ⟨560501, by rfl⟩ : syracuseStep 747335 = 1121003) B1121003
theorem B747803 : Blo 495792 747803 := bstep (se 1 (by rfl) ⟨560852, by rfl⟩ : syracuseStep 747803 = 1121705) B1121705
theorem B11495789 : Blo 495792 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B2124569 : Blo 495792 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B1600361 : Blo 495792 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B748487 : Blo 495792 748487 := bstep (se 1 (by rfl) ⟨561365, by rfl⟩ : syracuseStep 748487 = 1122731) B1122731
theorem B1797191 : Blo 495792 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B945263 : Blo 495792 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B749039 : Blo 495792 749039 := bstep (se 1 (by rfl) ⟨561779, by rfl⟩ : syracuseStep 749039 = 1123559) B1123559
theorem B749615 : Blo 495792 749615 := bstep (se 1 (by rfl) ⟨562211, by rfl⟩ : syracuseStep 749615 = 1124423) B1124423
theorem B3177143 : Blo 495792 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B2128943 : Blo 495792 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B30539177 : Blo 495792 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B9536413 : Blo 495792 9536413 := bstep (se 3 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 9536413 = 3576155) B3576155
theorem B9012491 : Blo 495792 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B1115873 : Blo 495792 1115873 := bstep (se 2 (by rfl) ⟨418452, by rfl⟩ : syracuseStep 1115873 = 836905) B836905
theorem B1116575 : Blo 495792 1116575 := bstep (se 1 (by rfl) ⟨837431, by rfl⟩ : syracuseStep 1116575 = 1674863) B1674863
theorem B1116827 : Blo 495792 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B2558729 : Blo 495792 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B2427995 : Blo 495792 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B560623 : Blo 495792 560623 := bstep (se 1 (by rfl) ⟨420467, by rfl⟩ : syracuseStep 560623 = 840935) B840935
theorem B1412711 : Blo 495792 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B1117979 : Blo 495792 1117979 := bstep (se 1 (by rfl) ⟨838484, by rfl⟩ : syracuseStep 1117979 = 1676969) B1676969
theorem B1675295 : Blo 495792 1675295 := bstep (se 1 (by rfl) ⟨1256471, by rfl⟩ : syracuseStep 1675295 = 2512943) B2512943
theorem B1675403 : Blo 495792 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B1413395 : Blo 495792 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B496103 : Blo 495792 496103 := bstep (se 1 (by rfl) ⟨372077, by rfl⟩ : syracuseStep 496103 = 744155) B744155
theorem B496155 : Blo 495792 496155 := bstep (se 1 (by rfl) ⟨372116, by rfl⟩ : syracuseStep 496155 = 744233) B744233
theorem B1118879 : Blo 495792 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B1675943 : Blo 495792 1675943 := bstep (se 1 (by rfl) ⟨1256957, by rfl⟩ : syracuseStep 1675943 = 2513915) B2513915
theorem B561919 : Blo 495792 561919 := bstep (se 1 (by rfl) ⟨421439, by rfl⟩ : syracuseStep 561919 = 842879) B842879
theorem B627527 : Blo 495792 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B496511 : Blo 495792 496511 := bstep (se 1 (by rfl) ⟨372383, by rfl⟩ : syracuseStep 496511 = 744767) B744767
theorem B496943 : Blo 495792 496943 := bstep (se 1 (by rfl) ⟨372707, by rfl⟩ : syracuseStep 496943 = 745415) B745415
theorem B628327 : Blo 495792 628327 := bstep (se 1 (by rfl) ⟨471245, by rfl⟩ : syracuseStep 628327 = 942491) B942491
theorem B497255 : Blo 495792 497255 := bstep (se 1 (by rfl) ⟨372941, by rfl⟩ : syracuseStep 497255 = 745883) B745883
theorem B497311 : Blo 495792 497311 := bstep (se 1 (by rfl) ⟨372983, by rfl⟩ : syracuseStep 497311 = 745967) B745967
theorem B3020495 : Blo 495792 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B497631 : Blo 495792 497631 := bstep (se 1 (by rfl) ⟨373223, by rfl⟩ : syracuseStep 497631 = 746447) B746447
theorem B497831 : Blo 495792 497831 := bstep (se 1 (by rfl) ⟨373373, by rfl⟩ : syracuseStep 497831 = 746747) B746747
theorem B1120481 : Blo 495792 1120481 := bstep (se 2 (by rfl) ⟨420180, by rfl⟩ : syracuseStep 1120481 = 840361) B840361
theorem B629147 : Blo 495792 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B498175 : Blo 495792 498175 := bstep (se 1 (by rfl) ⟨373631, by rfl⟩ : syracuseStep 498175 = 747263) B747263
theorem B498223 : Blo 495792 498223 := bstep (se 1 (by rfl) ⟨373667, by rfl⟩ : syracuseStep 498223 = 747335) B747335
theorem B1120823 : Blo 495792 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B1415809 : Blo 495792 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B498535 : Blo 495792 498535 := bstep (se 1 (by rfl) ⟨373901, by rfl⟩ : syracuseStep 498535 = 747803) B747803
theorem B1121363 : Blo 495792 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B1416379 : Blo 495792 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B1121471 : Blo 495792 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B498991 : Blo 495792 498991 := bstep (se 1 (by rfl) ⟨374243, by rfl⟩ : syracuseStep 498991 = 748487) B748487
theorem B630175 : Blo 495792 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B499359 : Blo 495792 499359 := bstep (se 1 (by rfl) ⟨374519, by rfl⟩ : syracuseStep 499359 = 749039) B749039
theorem B499743 : Blo 495792 499743 := bstep (se 1 (by rfl) ⟨374807, by rfl⟩ : syracuseStep 499743 = 749615) B749615
theorem B2695265 : Blo 495792 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1122407 : Blo 495792 1122407 := bstep (se 1 (by rfl) ⟨841805, by rfl⟩ : syracuseStep 1122407 = 1683611) B1683611
theorem B1122479 : Blo 495792 1122479 := bstep (se 1 (by rfl) ⟨841859, by rfl⟩ : syracuseStep 1122479 = 1683719) B1683719
theorem B1122623 : Blo 495792 1122623 := bstep (se 1 (by rfl) ⟨841967, by rfl⟩ : syracuseStep 1122623 = 1683935) B1683935
theorem B2564455 : Blo 495792 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B19210607 : Blo 495792 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B533351 : Blo 495792 533351 := bstep (se 1 (by rfl) ⟨400013, by rfl⟩ : syracuseStep 533351 = 800027) B800027
theorem B5383097 : Blo 495792 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B1680425 : Blo 495792 1680425 := bstep (se 2 (by rfl) ⟨630159, by rfl⟩ : syracuseStep 1680425 = 1260319) B1260319
theorem B1419295 : Blo 495792 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B20359451 : Blo 495792 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B6924745 : Blo 495792 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B1683503 : Blo 495792 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B1257707 : Blo 495792 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B1683881 : Blo 495792 1683881 := bstep (se 2 (by rfl) ⟨631455, by rfl⟩ : syracuseStep 1683881 = 1262911) B1262911
theorem B2830889 : Blo 495792 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B72790811 : Blo 495792 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B2013779 : Blo 495792 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B3193465 : Blo 495792 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B1195859 : Blo 495792 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B4243873 : Blo 495792 4243873 := bstep (se 2 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 4243873 = 3182905) B3182905
theorem B1884815 : Blo 495792 1884815 := bstep (se 1 (by rfl) ⟨1413611, by rfl⟩ : syracuseStep 1884815 = 2827223) B2827223
theorem B5686199 : Blo 495792 5686199 := bstep (se 1 (by rfl) ⟨4264649, by rfl⟩ : syracuseStep 5686199 = 8529299) B8529299
theorem B3818753 : Blo 495792 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B2016521 : Blo 495792 2016521 := bstep (se 2 (by rfl) ⟨756195, by rfl⟩ : syracuseStep 2016521 = 1512391) B1512391
theorem B837479 : Blo 495792 837479 := bstep (se 1 (by rfl) ⟨628109, by rfl⟩ : syracuseStep 837479 = 1256219) B1256219
theorem B1066907 : Blo 495792 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B1198127 : Blo 495792 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B838255 : Blo 495792 838255 := bstep (se 1 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 838255 = 1257383) B1257383
theorem B1887047 : Blo 495792 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B52317413 : Blo 495792 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B839423 : Blo 495792 839423 := bstep (se 1 (by rfl) ⟨629567, by rfl⟩ : syracuseStep 839423 = 1259135) B1259135
theorem B8507429 : Blo 495792 8507429 := bstep (se 4 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 8507429 = 1595143) B1595143
theorem B2118095 : Blo 495792 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B5100461 : Blo 495792 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B841583 : Blo 495792 841583 := bstep (se 1 (by rfl) ⟨631187, by rfl⟩ : syracuseStep 841583 = 1262375) B1262375
theorem B710633 : Blo 495792 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B12114683 : Blo 495792 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B744443 : Blo 495792 744443 := bstep (se 1 (by rfl) ⟨558332, by rfl⟩ : syracuseStep 744443 = 1116665) B1116665
theorem B41016455 : Blo 495792 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B1793299 : Blo 495792 1793299 := bstep (se 1 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 1793299 = 2689949) B2689949
theorem B744911 : Blo 495792 744911 := bstep (se 1 (by rfl) ⟨558683, by rfl⟩ : syracuseStep 744911 = 1117367) B1117367
theorem B15359507 : Blo 495792 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B745007 : Blo 495792 745007 := bstep (se 1 (by rfl) ⟨558755, by rfl⟩ : syracuseStep 745007 = 1117511) B1117511
theorem B745211 : Blo 495792 745211 := bstep (se 1 (by rfl) ⟨558908, by rfl⟩ : syracuseStep 745211 = 1117817) B1117817
theorem B2383643 : Blo 495792 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B745295 : Blo 495792 745295 := bstep (se 1 (by rfl) ⟨558971, by rfl⟩ : syracuseStep 745295 = 1117943) B1117943
theorem B2384873 : Blo 495792 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B746489 : Blo 495792 746489 := bstep (se 2 (by rfl) ⟨279933, by rfl⟩ : syracuseStep 746489 = 559867) B559867
theorem B747113 : Blo 495792 747113 := bstep (se 2 (by rfl) ⟨280167, by rfl⟩ : syracuseStep 747113 = 560335) B560335
theorem B747695 : Blo 495792 747695 := bstep (se 1 (by rfl) ⟨560771, by rfl⟩ : syracuseStep 747695 = 1121543) B1121543
theorem B72902915 : Blo 495792 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B748265 : Blo 495792 748265 := bstep (se 2 (by rfl) ⟨280599, by rfl⟩ : syracuseStep 748265 = 561199) B561199
theorem B944959 : Blo 495792 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B2518127 : Blo 495792 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B749111 : Blo 495792 749111 := bstep (se 1 (by rfl) ⟨561833, by rfl⟩ : syracuseStep 749111 = 1123667) B1123667
theorem B51867371 : Blo 495792 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B2518775 : Blo 495792 2518775 := bstep (se 1 (by rfl) ⟨1889081, by rfl⟩ : syracuseStep 2518775 = 3778163) B3778163
theorem B749639 : Blo 495792 749639 := bstep (se 1 (by rfl) ⟨562229, by rfl⟩ : syracuseStep 749639 = 1124459) B1124459
theorem B7663859 : Blo 495792 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B2519747 : Blo 495792 2519747 := bstep (se 1 (by rfl) ⟨1889810, by rfl⟩ : syracuseStep 2519747 = 3779621) B3779621
theorem B2390795 : Blo 495792 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B1343135 : Blo 495792 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B1344347 : Blo 495792 1344347 := bstep (se 1 (by rfl) ⟨1008260, by rfl⟩ : syracuseStep 1344347 = 2016521) B2016521
theorem B12715217 : Blo 495792 12715217 := bstep (se 2 (by rfl) ⟨4768206, by rfl⟩ : syracuseStep 12715217 = 9536413) B9536413
theorem B558319 : Blo 495792 558319 := bstep (se 1 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 558319 = 837479) B837479
theorem B1705819 : Blo 495792 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B1673405 : Blo 495792 1673405 := bstep (se 3 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 1673405 = 627527) B627527
theorem B559615 : Blo 495792 559615 := bstep (se 1 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 559615 = 839423) B839423
theorem B1116863 : Blo 495792 1116863 := bstep (se 1 (by rfl) ⟨837647, by rfl⟩ : syracuseStep 1116863 = 1675295) B1675295
theorem B5671619 : Blo 495792 5671619 := bstep (se 1 (by rfl) ⟨4253714, by rfl⟩ : syracuseStep 5671619 = 8507429) B8507429
theorem B1116935 : Blo 495792 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B1412063 : Blo 495792 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B1117295 : Blo 495792 1117295 := bstep (se 1 (by rfl) ⟨837971, by rfl⟩ : syracuseStep 1117295 = 1675943) B1675943
theorem B1117673 : Blo 495792 1117673 := bstep (se 2 (by rfl) ⟨419127, by rfl⟩ : syracuseStep 1117673 = 838255) B838255
theorem B561055 : Blo 495792 561055 := bstep (se 1 (by rfl) ⟨420791, by rfl⟩ : syracuseStep 561055 = 841583) B841583
theorem B496295 : Blo 495792 496295 := bstep (se 1 (by rfl) ⟨372221, by rfl⟩ : syracuseStep 496295 = 744443) B744443
theorem B496607 : Blo 495792 496607 := bstep (se 1 (by rfl) ⟨372455, by rfl⟩ : syracuseStep 496607 = 744911) B744911
theorem B496671 : Blo 495792 496671 := bstep (se 1 (by rfl) ⟨372503, by rfl⟩ : syracuseStep 496671 = 745007) B745007
theorem B496807 : Blo 495792 496807 := bstep (se 1 (by rfl) ⟨372605, by rfl⟩ : syracuseStep 496807 = 745211) B745211
theorem B496863 : Blo 495792 496863 := bstep (se 1 (by rfl) ⟨372647, by rfl⟩ : syracuseStep 496863 = 745295) B745295
theorem B497659 : Blo 495792 497659 := bstep (se 1 (by rfl) ⟨373244, by rfl⟩ : syracuseStep 497659 = 746489) B746489
theorem B1120283 : Blo 495792 1120283 := bstep (se 1 (by rfl) ⟨840212, by rfl⟩ : syracuseStep 1120283 = 1680425) B1680425
theorem B498075 : Blo 495792 498075 := bstep (se 1 (by rfl) ⟨373556, by rfl⟩ : syracuseStep 498075 = 747113) B747113
theorem B1677725 : Blo 495792 1677725 := bstep (se 3 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 1677725 = 629147) B629147
theorem B498463 : Blo 495792 498463 := bstep (se 1 (by rfl) ⟨373847, by rfl⟩ : syracuseStep 498463 = 747695) B747695
theorem B48601943 : Blo 495792 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B13572967 : Blo 495792 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B498843 : Blo 495792 498843 := bstep (se 1 (by rfl) ⟨374132, by rfl⟩ : syracuseStep 498843 = 748265) B748265
theorem B1678751 : Blo 495792 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B499407 : Blo 495792 499407 := bstep (se 1 (by rfl) ⟨374555, by rfl⟩ : syracuseStep 499407 = 749111) B749111
theorem B34578247 : Blo 495792 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B1679183 : Blo 495792 1679183 := bstep (se 1 (by rfl) ⟨1259387, by rfl⟩ : syracuseStep 1679183 = 2518775) B2518775
theorem B1122335 : Blo 495792 1122335 := bstep (se 1 (by rfl) ⟨841751, by rfl⟩ : syracuseStep 1122335 = 1683503) B1683503
theorem B499759 : Blo 495792 499759 := bstep (se 1 (by rfl) ⟨374819, by rfl⟩ : syracuseStep 499759 = 749639) B749639
theorem B1122587 : Blo 495792 1122587 := bstep (se 1 (by rfl) ⟨841940, by rfl⟩ : syracuseStep 1122587 = 1683881) B1683881
theorem B1679831 : Blo 495792 1679831 := bstep (se 1 (by rfl) ⟨1259873, by rfl⟩ : syracuseStep 1679831 = 2519747) B2519747
theorem B895423 : Blo 495792 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B797239 : Blo 495792 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B1256543 : Blo 495792 1256543 := bstep (se 1 (by rfl) ⟨942407, by rfl⟩ : syracuseStep 1256543 = 1884815) B1884815
theorem B3419273 : Blo 495792 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B6008327 : Blo 495792 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B798751 : Blo 495792 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B1258031 : Blo 495792 1258031 := bstep (se 1 (by rfl) ⟨943523, by rfl⟩ : syracuseStep 1258031 = 1887047) B1887047
theorem B1618663 : Blo 495792 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B34878275 : Blo 495792 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B1422269 : Blo 495792 1422269 := bstep (se 3 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 1422269 = 533351) B533351
theorem B1259945 : Blo 495792 1259945 := bstep (se 2 (by rfl) ⟨472479, by rfl⟩ : syracuseStep 1259945 = 944959) B944959
theorem B8076455 : Blo 495792 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B27344303 : Blo 495792 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B10239671 : Blo 495792 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B1589095 : Blo 495792 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B3588731 : Blo 495792 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B1589915 : Blo 495792 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B837769 : Blo 495792 837769 := bstep (se 2 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 837769 = 628327) B628327
theorem B838471 : Blo 495792 838471 := bstep (se 1 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 838471 = 1257707) B1257707
theorem B1887259 : Blo 495792 1887259 := bstep (se 1 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 1887259 = 2830889) B2830889
theorem B1887745 : Blo 495792 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B1888505 : Blo 495792 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B1593863 : Blo 495792 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B840233 : Blo 495792 840233 := bstep (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) B630175
theorem B5658497 : Blo 495792 5658497 := bstep (se 2 (by rfl) ⟨2121936, by rfl⟩ : syracuseStep 5658497 = 4243873) B4243873
theorem B3790799 : Blo 495792 3790799 := bstep (se 1 (by rfl) ⟨2843099, by rfl⟩ : syracuseStep 3790799 = 5686199) B5686199
theorem B2545835 : Blo 495792 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B743915 : Blo 495792 743915 := bstep (se 1 (by rfl) ⟨557936, by rfl⟩ : syracuseStep 743915 = 1115873) B1115873
theorem B711271 : Blo 495792 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B744383 : Blo 495792 744383 := bstep (se 1 (by rfl) ⟨558287, by rfl⟩ : syracuseStep 744383 = 1116575) B1116575
theorem B744551 : Blo 495792 744551 := bstep (se 1 (by rfl) ⟨558413, by rfl⟩ : syracuseStep 744551 = 1116827) B1116827
theorem B941807 : Blo 495792 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B745319 : Blo 495792 745319 := bstep (se 1 (by rfl) ⟨558989, by rfl⟩ : syracuseStep 745319 = 1117979) B1117979
theorem B1892393 : Blo 495792 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B942263 : Blo 495792 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B745919 : Blo 495792 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B9232993 : Blo 495792 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B3400307 : Blo 495792 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B746987 : Blo 495792 746987 := bstep (se 1 (by rfl) ⟨560240, by rfl⟩ : syracuseStep 746987 = 1120481) B1120481
theorem B747215 : Blo 495792 747215 := bstep (se 1 (by rfl) ⟨560411, by rfl⟩ : syracuseStep 747215 = 1120823) B1120823
theorem B8054653 : Blo 495792 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B747497 : Blo 495792 747497 := bstep (se 2 (by rfl) ⟨280311, by rfl⟩ : syracuseStep 747497 = 560623) B560623
theorem B747575 : Blo 495792 747575 := bstep (se 1 (by rfl) ⟨560681, by rfl⟩ : syracuseStep 747575 = 1121363) B1121363
theorem B747647 : Blo 495792 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B1895021 : Blo 495792 1895021 := bstep (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) B710633
theorem B1796843 : Blo 495792 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B748271 : Blo 495792 748271 := bstep (se 1 (by rfl) ⟨561203, by rfl⟩ : syracuseStep 748271 = 1122407) B1122407
theorem B748319 : Blo 495792 748319 := bstep (se 1 (by rfl) ⟨561239, by rfl⟩ : syracuseStep 748319 = 1122479) B1122479
theorem B748415 : Blo 495792 748415 := bstep (se 1 (by rfl) ⟨561311, by rfl⟩ : syracuseStep 748415 = 1122623) B1122623
theorem B12807071 : Blo 495792 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B749225 : Blo 495792 749225 := bstep (se 2 (by rfl) ⟨280959, by rfl⟩ : syracuseStep 749225 = 561919) B561919
theorem B5370077 : Blo 495792 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B5109239 : Blo 495792 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B48527207 : Blo 495792 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B4257953 : Blo 495792 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B2391065 : Blo 495792 2391065 := bstep (se 2 (by rfl) ⟨896649, by rfl⟩ : syracuseStep 2391065 = 1793299) B1793299
theorem B2392487 : Blo 495792 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B1115603 : Blo 495792 1115603 := bstep (se 1 (by rfl) ⟨836702, by rfl⟩ : syracuseStep 1115603 = 1673405) B1673405
theorem B1117025 : Blo 495792 1117025 := bstep (se 2 (by rfl) ⟨418884, by rfl⟩ : syracuseStep 1117025 = 837769) B837769
theorem B560155 : Blo 495792 560155 := bstep (se 1 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 560155 = 840233) B840233
theorem B1117961 : Blo 495792 1117961 := bstep (se 2 (by rfl) ⟨419235, by rfl⟩ : syracuseStep 1117961 = 838471) B838471
theorem B3772331 : Blo 495792 3772331 := bstep (se 1 (by rfl) ⟨2829248, by rfl⟩ : syracuseStep 3772331 = 5658497) B5658497
theorem B2527199 : Blo 495792 2527199 := bstep (se 1 (by rfl) ⟨1895399, by rfl⟩ : syracuseStep 2527199 = 3790799) B3790799
theorem B1118483 : Blo 495792 1118483 := bstep (se 1 (by rfl) ⟨838862, by rfl⟩ : syracuseStep 1118483 = 1677725) B1677725
theorem B495943 : Blo 495792 495943 := bstep (se 1 (by rfl) ⟨371957, by rfl⟩ : syracuseStep 495943 = 743915) B743915
theorem B496255 : Blo 495792 496255 := bstep (se 1 (by rfl) ⟨372191, by rfl⟩ : syracuseStep 496255 = 744383) B744383
theorem B496367 : Blo 495792 496367 := bstep (se 1 (by rfl) ⟨372275, by rfl⟩ : syracuseStep 496367 = 744551) B744551
theorem B1119167 : Blo 495792 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B1119455 : Blo 495792 1119455 := bstep (se 1 (by rfl) ⟨839591, by rfl⟩ : syracuseStep 1119455 = 1679183) B1679183
theorem B496879 : Blo 495792 496879 := bstep (se 1 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 496879 = 745319) B745319
theorem B628175 : Blo 495792 628175 := bstep (se 1 (by rfl) ⟨471131, by rfl⟩ : syracuseStep 628175 = 942263) B942263
theorem B497279 : Blo 495792 497279 := bstep (se 1 (by rfl) ⟨372959, by rfl⟩ : syracuseStep 497279 = 745919) B745919
theorem B1119887 : Blo 495792 1119887 := bstep (se 1 (by rfl) ⟨839915, by rfl⟩ : syracuseStep 1119887 = 1679831) B1679831
theorem B2266871 : Blo 495792 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B6788893 : Blo 495792 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B497991 : Blo 495792 497991 := bstep (se 1 (by rfl) ⟨373493, by rfl⟩ : syracuseStep 497991 = 746987) B746987
theorem B498143 : Blo 495792 498143 := bstep (se 1 (by rfl) ⟨373607, by rfl⟩ : syracuseStep 498143 = 747215) B747215
theorem B498331 : Blo 495792 498331 := bstep (se 1 (by rfl) ⟨373748, by rfl⟩ : syracuseStep 498331 = 747497) B747497
theorem B498383 : Blo 495792 498383 := bstep (se 1 (by rfl) ⟨373787, by rfl⟩ : syracuseStep 498383 = 747575) B747575
theorem B498431 : Blo 495792 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B498847 : Blo 495792 498847 := bstep (se 1 (by rfl) ⟨374135, by rfl⟩ : syracuseStep 498847 = 748271) B748271
theorem B498879 : Blo 495792 498879 := bstep (se 1 (by rfl) ⟨374159, by rfl⟩ : syracuseStep 498879 = 748319) B748319
theorem B498943 : Blo 495792 498943 := bstep (se 1 (by rfl) ⟨374207, by rfl⟩ : syracuseStep 498943 = 748415) B748415
theorem B4791581 : Blo 495792 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B4005551 : Blo 495792 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B499483 : Blo 495792 499483 := bstep (se 1 (by rfl) ⟨374612, by rfl⟩ : syracuseStep 499483 = 749225) B749225
theorem B3580051 : Blo 495792 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B18097289 : Blo 495792 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B32351471 : Blo 495792 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B5384303 : Blo 495792 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B18229535 : Blo 495792 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B6826447 : Blo 495792 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B896231 : Blo 495792 896231 := bstep (se 1 (by rfl) ⟨672173, by rfl⟩ : syracuseStep 896231 = 1344347) B1344347
theorem B4239773 : Blo 495792 4239773 := bstep (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) B1589915
theorem B3781079 : Blo 495792 3781079 := bstep (se 1 (by rfl) ⟨2835809, by rfl⟩ : syracuseStep 3781079 = 5671619) B5671619
theorem B2274425 : Blo 495792 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B1259003 : Blo 495792 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B1062575 : Blo 495792 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B1193897 : Blo 495792 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1062985 : Blo 495792 1062985 := bstep (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) B797239
theorem B1261595 : Blo 495792 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B1065001 : Blo 495792 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B1263347 : Blo 495792 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B8538047 : Blo 495792 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B837695 : Blo 495792 837695 := bstep (se 1 (by rfl) ⟨628271, by rfl⟩ : syracuseStep 837695 = 1256543) B1256543
theorem B2279515 : Blo 495792 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B838687 : Blo 495792 838687 := bstep (se 1 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 838687 = 1258031) B1258031
theorem B23252183 : Blo 495792 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B2838635 : Blo 495792 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B839963 : Blo 495792 839963 := bstep (se 1 (by rfl) ⟨629972, by rfl⟩ : syracuseStep 839963 = 1259945) B1259945
theorem B2511485 : Blo 495792 2511485 := bstep (se 3 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 2511485 = 941807) B941807
theorem B1594043 : Blo 495792 1594043 := bstep (se 1 (by rfl) ⟨1195532, by rfl⟩ : syracuseStep 1594043 = 2391065) B2391065
theorem B2118793 : Blo 495792 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B8476811 : Blo 495792 8476811 := bstep (se 1 (by rfl) ⟨6357608, by rfl⟩ : syracuseStep 8476811 = 12715217) B12715217
theorem B744425 : Blo 495792 744425 := bstep (se 2 (by rfl) ⟨279159, by rfl⟩ : syracuseStep 744425 = 558319) B558319
theorem B744575 : Blo 495792 744575 := bstep (se 1 (by rfl) ⟨558431, by rfl⟩ : syracuseStep 744575 = 1116863) B1116863
theorem B744623 : Blo 495792 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B941375 : Blo 495792 941375 := bstep (se 1 (by rfl) ⟨706031, by rfl⟩ : syracuseStep 941375 = 1412063) B1412063
theorem B744863 : Blo 495792 744863 := bstep (se 1 (by rfl) ⟨558647, by rfl⟩ : syracuseStep 744863 = 1117295) B1117295
theorem B745115 : Blo 495792 745115 := bstep (se 1 (by rfl) ⟨558836, by rfl⟩ : syracuseStep 745115 = 1117673) B1117673
theorem B10739537 : Blo 495792 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B49242629 : Blo 495792 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B746153 : Blo 495792 746153 := bstep (se 2 (by rfl) ⟨279807, by rfl⟩ : syracuseStep 746153 = 559615) B559615
theorem B746855 : Blo 495792 746855 := bstep (se 1 (by rfl) ⟨560141, by rfl⟩ : syracuseStep 746855 = 1120283) B1120283
theorem B2516345 : Blo 495792 2516345 := bstep (se 2 (by rfl) ⟨943629, by rfl⟩ : syracuseStep 2516345 = 1887259) B1887259
theorem B32401295 : Blo 495792 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B2516993 : Blo 495792 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B748073 : Blo 495792 748073 := bstep (se 2 (by rfl) ⟨280527, by rfl⟩ : syracuseStep 748073 = 561055) B561055
theorem B748223 : Blo 495792 748223 := bstep (se 1 (by rfl) ⟨561167, by rfl⟩ : syracuseStep 748223 = 1122335) B1122335
theorem B748391 : Blo 495792 748391 := bstep (se 1 (by rfl) ⟨561293, by rfl⟩ : syracuseStep 748391 = 1122587) B1122587
theorem B2158217 : Blo 495792 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B948179 : Blo 495792 948179 := bstep (se 1 (by rfl) ⟨711134, by rfl⟩ : syracuseStep 948179 = 1422269) B1422269
theorem B948361 : Blo 495792 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B3406159 : Blo 495792 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B46104329 : Blo 495792 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B558463 : Blo 495792 558463 := bstep (se 1 (by rfl) ⟨418847, by rfl⟩ : syracuseStep 558463 = 837695) B837695
theorem B15501455 : Blo 495792 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B559975 : Blo 495792 559975 := bstep (se 1 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 559975 = 839963) B839963
theorem B1674323 : Blo 495792 1674323 := bstep (se 1 (by rfl) ⟨1255742, by rfl⟩ : syracuseStep 1674323 = 2511485) B2511485
theorem B1675133 : Blo 495792 1675133 := bstep (se 3 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 1675133 = 628175) B628175
theorem B1118249 : Blo 495792 1118249 := bstep (se 2 (by rfl) ⟨419343, by rfl⟩ : syracuseStep 1118249 = 838687) B838687
theorem B496283 : Blo 495792 496283 := bstep (se 1 (by rfl) ⟨372212, by rfl⟩ : syracuseStep 496283 = 744425) B744425
theorem B496383 : Blo 495792 496383 := bstep (se 1 (by rfl) ⟨372287, by rfl⟩ : syracuseStep 496383 = 744575) B744575
theorem B496415 : Blo 495792 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B627583 : Blo 495792 627583 := bstep (se 1 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 627583 = 941375) B941375
theorem B496575 : Blo 495792 496575 := bstep (se 1 (by rfl) ⟨372431, by rfl⟩ : syracuseStep 496575 = 744863) B744863
theorem B496743 : Blo 495792 496743 := bstep (se 1 (by rfl) ⟨372557, by rfl⟩ : syracuseStep 496743 = 745115) B745115
theorem B3183725 : Blo 495792 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B497435 : Blo 495792 497435 := bstep (se 1 (by rfl) ⟨373076, by rfl⟩ : syracuseStep 497435 = 746153) B746153
theorem B12064859 : Blo 495792 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B21567647 : Blo 495792 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B497903 : Blo 495792 497903 := bstep (se 1 (by rfl) ⟨373427, by rfl⟩ : syracuseStep 497903 = 746855) B746855
theorem B1677563 : Blo 495792 1677563 := bstep (se 1 (by rfl) ⟨1258172, by rfl⟩ : syracuseStep 1677563 = 2516345) B2516345
theorem B21600863 : Blo 495792 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B1677995 : Blo 495792 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B2825057 : Blo 495792 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B498715 : Blo 495792 498715 := bstep (se 1 (by rfl) ⟨374036, by rfl⟩ : syracuseStep 498715 = 748073) B748073
theorem B498815 : Blo 495792 498815 := bstep (se 1 (by rfl) ⟨374111, by rfl⟩ : syracuseStep 498815 = 748223) B748223
theorem B498927 : Blo 495792 498927 := bstep (se 1 (by rfl) ⟨374195, by rfl⟩ : syracuseStep 498927 = 748391) B748391
theorem B597487 : Blo 495792 597487 := bstep (se 1 (by rfl) ⟨448115, by rfl⟩ : syracuseStep 597487 = 896231) B896231
theorem B9051857 : Blo 495792 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B1417313 : Blo 495792 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B2826515 : Blo 495792 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B1516283 : Blo 495792 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B632119 : Blo 495792 632119 := bstep (se 1 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 632119 = 948179) B948179
theorem B1420001 : Blo 495792 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B1684799 : Blo 495792 1684799 := bstep (se 1 (by rfl) ⟨1263599, by rfl⟩ : syracuseStep 1684799 = 2527199) B2527199
theorem B1062695 : Blo 495792 1062695 := bstep (se 1 (by rfl) ⟨797021, by rfl⟩ : syracuseStep 1062695 = 1594043) B1594043
theorem B5651207 : Blo 495792 5651207 := bstep (se 1 (by rfl) ⟨4238405, by rfl⟩ : syracuseStep 5651207 = 8476811) B8476811
theorem B6044989 : Blo 495792 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B3194387 : Blo 495792 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B7159691 : Blo 495792 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B3589535 : Blo 495792 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1264481 : Blo 495792 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B4541545 : Blo 495792 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B839335 : Blo 495792 839335 := bstep (se 1 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 839335 = 1259003) B1259003
theorem B708383 : Blo 495792 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B841063 : Blo 495792 841063 := bstep (se 1 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 841063 = 1261595) B1261595
theorem B4773401 : Blo 495792 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B1594991 : Blo 495792 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B743735 : Blo 495792 743735 := bstep (se 1 (by rfl) ⟨557801, by rfl⟩ : syracuseStep 743735 = 1115603) B1115603
theorem B842231 : Blo 495792 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B5692031 : Blo 495792 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B744683 : Blo 495792 744683 := bstep (se 1 (by rfl) ⟨558512, by rfl⟩ : syracuseStep 744683 = 1117025) B1117025
theorem B745307 : Blo 495792 745307 := bstep (se 1 (by rfl) ⟨558980, by rfl⟩ : syracuseStep 745307 = 1117961) B1117961
theorem B2514887 : Blo 495792 2514887 := bstep (se 1 (by rfl) ⟨1886165, by rfl⟩ : syracuseStep 2514887 = 3772331) B3772331
theorem B1892423 : Blo 495792 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B3039353 : Blo 495792 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B745655 : Blo 495792 745655 := bstep (se 1 (by rfl) ⟨559241, by rfl⟩ : syracuseStep 745655 = 1118483) B1118483
theorem B9101929 : Blo 495792 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B746111 : Blo 495792 746111 := bstep (se 1 (by rfl) ⟨559583, by rfl⟩ : syracuseStep 746111 = 1119167) B1119167
theorem B746303 : Blo 495792 746303 := bstep (se 1 (by rfl) ⟨559727, by rfl⟩ : syracuseStep 746303 = 1119455) B1119455
theorem B746591 : Blo 495792 746591 := bstep (se 1 (by rfl) ⟨559943, by rfl⟩ : syracuseStep 746591 = 1119887) B1119887
theorem B746873 : Blo 495792 746873 := bstep (se 2 (by rfl) ⟨280077, by rfl⟩ : syracuseStep 746873 = 560155) B560155
theorem B32828419 : Blo 495792 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B12153023 : Blo 495792 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B1438811 : Blo 495792 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B2520719 : Blo 495792 2520719 := bstep (se 1 (by rfl) ⟨1890539, by rfl⟩ : syracuseStep 2520719 = 3781079) B3781079
theorem B10681469 : Blo 495792 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B30736219 : Blo 495792 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B2393023 : Blo 495792 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B1116215 : Blo 495792 1116215 := bstep (se 1 (by rfl) ⟨837161, by rfl⟩ : syracuseStep 1116215 = 1674323) B1674323
theorem B1116755 : Blo 495792 1116755 := bstep (se 1 (by rfl) ⟨837566, by rfl⟩ : syracuseStep 1116755 = 1675133) B1675133
theorem B8489933 : Blo 495792 8489933 := bstep (se 3 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 8489933 = 3183725) B3183725
theorem B3182267 : Blo 495792 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B1118375 : Blo 495792 1118375 := bstep (se 1 (by rfl) ⟨838781, by rfl⟩ : syracuseStep 1118375 = 1677563) B1677563
theorem B495823 : Blo 495792 495823 := bstep (se 1 (by rfl) ⟨371867, by rfl⟩ : syracuseStep 495823 = 743735) B743735
theorem B561487 : Blo 495792 561487 := bstep (se 1 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 561487 = 842231) B842231
theorem B1118663 : Blo 495792 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B496455 : Blo 495792 496455 := bstep (se 1 (by rfl) ⟨372341, by rfl⟩ : syracuseStep 496455 = 744683) B744683
theorem B1119113 : Blo 495792 1119113 := bstep (se 2 (by rfl) ⟨419667, by rfl⟩ : syracuseStep 1119113 = 839335) B839335
theorem B6034571 : Blo 495792 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B496871 : Blo 495792 496871 := bstep (se 1 (by rfl) ⟨372653, by rfl⟩ : syracuseStep 496871 = 745307) B745307
theorem B1676591 : Blo 495792 1676591 := bstep (se 1 (by rfl) ⟨1257443, by rfl⟩ : syracuseStep 1676591 = 2514887) B2514887
theorem B175084901 : Blo 495792 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B497103 : Blo 495792 497103 := bstep (se 1 (by rfl) ⟨372827, by rfl⟩ : syracuseStep 497103 = 745655) B745655
theorem B497407 : Blo 495792 497407 := bstep (se 1 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 497407 = 746111) B746111
theorem B497535 : Blo 495792 497535 := bstep (se 1 (by rfl) ⟨373151, by rfl⟩ : syracuseStep 497535 = 746303) B746303
theorem B497727 : Blo 495792 497727 := bstep (se 1 (by rfl) ⟨373295, by rfl⟩ : syracuseStep 497727 = 746591) B746591
theorem B497915 : Blo 495792 497915 := bstep (se 1 (by rfl) ⟨373436, by rfl⟩ : syracuseStep 497915 = 746873) B746873
theorem B1121417 : Blo 495792 1121417 := bstep (se 2 (by rfl) ⟨420531, by rfl⟩ : syracuseStep 1121417 = 841063) B841063
theorem B8102015 : Blo 495792 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B959207 : Blo 495792 959207 := bstep (se 1 (by rfl) ⟨719405, by rfl⟩ : syracuseStep 959207 = 1438811) B1438811
theorem B1123199 : Blo 495792 1123199 := bstep (se 1 (by rfl) ⟨842399, by rfl⟩ : syracuseStep 1123199 = 1684799) B1684799
theorem B1680479 : Blo 495792 1680479 := bstep (se 1 (by rfl) ⟨1260359, by rfl⟩ : syracuseStep 1680479 = 2520719) B2520719
theorem B796649 : Blo 495792 796649 := bstep (se 2 (by rfl) ⟨298743, by rfl⟩ : syracuseStep 796649 = 597487) B597487
theorem B7120979 : Blo 495792 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B12135905 : Blo 495792 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B10334303 : Blo 495792 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B1063327 : Blo 495792 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B8043239 : Blo 495792 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B14400575 : Blo 495792 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B1883371 : Blo 495792 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B1261615 : Blo 495792 1261615 := bstep (se 1 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 1261615 = 1892423) B1892423
theorem B1884343 : Blo 495792 1884343 := bstep (se 1 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 1884343 = 2826515) B2826515
theorem B836777 : Blo 495792 836777 := bstep (se 2 (by rfl) ⟨313791, by rfl⟩ : syracuseStep 836777 = 627583) B627583
theorem B708463 : Blo 495792 708463 := bstep (se 1 (by rfl) ⟨531347, by rfl⟩ : syracuseStep 708463 = 1062695) B1062695
theorem B1889021 : Blo 495792 1889021 := bstep (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) B708383
theorem B19092509 : Blo 495792 19092509 := bstep (se 3 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 19092509 = 7159691) B7159691
theorem B40981625 : Blo 495792 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B842825 : Blo 495792 842825 := bstep (se 2 (by rfl) ⟨316059, by rfl⟩ : syracuseStep 842825 = 632119) B632119
theorem B744617 : Blo 495792 744617 := bstep (se 2 (by rfl) ⟨279231, by rfl⟩ : syracuseStep 744617 = 558463) B558463
theorem B842987 : Blo 495792 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B745499 : Blo 495792 745499 := bstep (se 1 (by rfl) ⟨559124, by rfl⟩ : syracuseStep 745499 = 1118249) B1118249
theorem B746633 : Blo 495792 746633 := bstep (se 2 (by rfl) ⟨279987, by rfl⟩ : syracuseStep 746633 = 559975) B559975
theorem B14378431 : Blo 495792 14378431 := bstep (se 1 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 14378431 = 21567647) B21567647
theorem B6055393 : Blo 495792 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B3794687 : Blo 495792 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B944875 : Blo 495792 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B2026235 : Blo 495792 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B1010855 : Blo 495792 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B946667 : Blo 495792 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B8059985 : Blo 495792 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B3767471 : Blo 495792 3767471 := bstep (se 1 (by rfl) ⟨2825603, by rfl⟩ : syracuseStep 3767471 = 5651207) B5651207
theorem B2129591 : Blo 495792 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B557851 : Blo 495792 557851 := bstep (se 1 (by rfl) ⟨418388, by rfl⟩ : syracuseStep 557851 = 836777) B836777
theorem B2524445 : Blo 495792 2524445 := bstep (se 3 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 2524445 = 946667) B946667
theorem B19171241 : Blo 495792 19171241 := bstep (se 2 (by rfl) ⟨7189215, by rfl⟩ : syracuseStep 19171241 = 14378431) B14378431
theorem B2557885 : Blo 495792 2557885 := bstep (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) B959207
theorem B1117727 : Blo 495792 1117727 := bstep (se 1 (by rfl) ⟨838295, by rfl⟩ : syracuseStep 1117727 = 1676591) B1676591
theorem B116723267 : Blo 495792 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B561883 : Blo 495792 561883 := bstep (se 1 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 561883 = 842825) B842825
theorem B496411 : Blo 495792 496411 := bstep (se 1 (by rfl) ⟨372308, by rfl⟩ : syracuseStep 496411 = 744617) B744617
theorem B561991 : Blo 495792 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B496999 : Blo 495792 496999 := bstep (se 1 (by rfl) ⟨372749, by rfl⟩ : syracuseStep 496999 = 745499) B745499
theorem B1120319 : Blo 495792 1120319 := bstep (se 1 (by rfl) ⟨840239, by rfl⟩ : syracuseStep 1120319 = 1680479) B1680479
theorem B497755 : Blo 495792 497755 := bstep (se 1 (by rfl) ⟨373316, by rfl⟩ : syracuseStep 497755 = 746633) B746633
theorem B2529791 : Blo 495792 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B6889535 : Blo 495792 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1417769 : Blo 495792 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B5678909 : Blo 495792 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B1682153 : Blo 495792 1682153 := bstep (se 2 (by rfl) ⟨630807, by rfl⟩ : syracuseStep 1682153 = 1261615) B1261615
theorem B3190697 : Blo 495792 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B8073857 : Blo 495792 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B1259347 : Blo 495792 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B12728339 : Blo 495792 12728339 := bstep (se 1 (by rfl) ⟨9546254, by rfl⟩ : syracuseStep 12728339 = 19092509) B19092509
theorem B1259833 : Blo 495792 1259833 := bstep (se 2 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 1259833 = 944875) B944875
theorem B673903 : Blo 495792 673903 := bstep (se 1 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 673903 = 1010855) B1010855
theorem B2511161 : Blo 495792 2511161 := bstep (se 2 (by rfl) ⟨941685, by rfl⟩ : syracuseStep 2511161 = 1883371) B1883371
theorem B5362159 : Blo 495792 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B2511647 : Blo 495792 2511647 := bstep (se 1 (by rfl) ⟨1883735, by rfl⟩ : syracuseStep 2511647 = 3767471) B3767471
theorem B2512457 : Blo 495792 2512457 := bstep (se 2 (by rfl) ⟨942171, by rfl⟩ : syracuseStep 2512457 = 1884343) B1884343
theorem B744143 : Blo 495792 744143 := bstep (se 1 (by rfl) ⟨558107, by rfl⟩ : syracuseStep 744143 = 1116215) B1116215
theorem B744503 : Blo 495792 744503 := bstep (se 1 (by rfl) ⟨558377, by rfl⟩ : syracuseStep 744503 = 1116755) B1116755
theorem B5659955 : Blo 495792 5659955 := bstep (se 1 (by rfl) ⟨4244966, by rfl⟩ : syracuseStep 5659955 = 8489933) B8489933
theorem B2121511 : Blo 495792 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B745583 : Blo 495792 745583 := bstep (se 1 (by rfl) ⟨559187, by rfl⟩ : syracuseStep 745583 = 1118375) B1118375
theorem B745775 : Blo 495792 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B746075 : Blo 495792 746075 := bstep (se 1 (by rfl) ⟨559556, by rfl⟩ : syracuseStep 746075 = 1119113) B1119113
theorem B27321083 : Blo 495792 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B4023047 : Blo 495792 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B747611 : Blo 495792 747611 := bstep (se 1 (by rfl) ⟨560708, by rfl⟩ : syracuseStep 747611 = 1121417) B1121417
theorem B944617 : Blo 495792 944617 := bstep (se 2 (by rfl) ⟨354231, by rfl⟩ : syracuseStep 944617 = 708463) B708463
theorem B2124397 : Blo 495792 2124397 := bstep (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) B796649
theorem B5401343 : Blo 495792 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B748649 : Blo 495792 748649 := bstep (se 2 (by rfl) ⟨280743, by rfl⟩ : syracuseStep 748649 = 561487) B561487
theorem B748799 : Blo 495792 748799 := bstep (se 1 (by rfl) ⟨561599, by rfl⟩ : syracuseStep 748799 = 1123199) B1123199
theorem B4747319 : Blo 495792 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B5403293 : Blo 495792 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B8090603 : Blo 495792 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B9600383 : Blo 495792 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B5373323 : Blo 495792 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B12780827 : Blo 495792 12780827 := bstep (se 1 (by rfl) ⟨9585620, by rfl⟩ : syracuseStep 12780827 = 19171241) B19171241
theorem B21530285 : Blo 495792 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B3410513 : Blo 495792 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B1674107 : Blo 495792 1674107 := bstep (se 1 (by rfl) ⟨1255580, by rfl⟩ : syracuseStep 1674107 = 2511161) B2511161
theorem B1674431 : Blo 495792 1674431 := bstep (se 1 (by rfl) ⟨1255823, by rfl⟩ : syracuseStep 1674431 = 2511647) B2511647
theorem B1674971 : Blo 495792 1674971 := bstep (se 1 (by rfl) ⟨1256228, by rfl⟩ : syracuseStep 1674971 = 2512457) B2512457
theorem B496095 : Blo 495792 496095 := bstep (se 1 (by rfl) ⟨372071, by rfl⟩ : syracuseStep 496095 = 744143) B744143
theorem B496335 : Blo 495792 496335 := bstep (se 1 (by rfl) ⟨372251, by rfl⟩ : syracuseStep 496335 = 744503) B744503
theorem B3773303 : Blo 495792 3773303 := bstep (se 1 (by rfl) ⟨2829977, by rfl⟩ : syracuseStep 3773303 = 5659955) B5659955
theorem B4593023 : Blo 495792 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B497055 : Blo 495792 497055 := bstep (se 1 (by rfl) ⟨372791, by rfl⟩ : syracuseStep 497055 = 745583) B745583
theorem B497183 : Blo 495792 497183 := bstep (se 1 (by rfl) ⟨372887, by rfl⟩ : syracuseStep 497183 = 745775) B745775
theorem B497383 : Blo 495792 497383 := bstep (se 1 (by rfl) ⟨373037, by rfl⟩ : syracuseStep 497383 = 746075) B746075
theorem B7149545 : Blo 495792 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B498407 : Blo 495792 498407 := bstep (se 1 (by rfl) ⟨373805, by rfl⟩ : syracuseStep 498407 = 747611) B747611
theorem B1121435 : Blo 495792 1121435 := bstep (se 1 (by rfl) ⟨841076, by rfl⟩ : syracuseStep 1121435 = 1682153) B1682153
theorem B499099 : Blo 495792 499099 := bstep (se 1 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 499099 = 748649) B748649
theorem B499199 : Blo 495792 499199 := bstep (se 1 (by rfl) ⟨374399, by rfl⟩ : syracuseStep 499199 = 748799) B748799
theorem B1679129 : Blo 495792 1679129 := bstep (se 2 (by rfl) ⟨629673, by rfl⟩ : syracuseStep 1679129 = 1259347) B1259347
theorem B1679777 : Blo 495792 1679777 := bstep (se 2 (by rfl) ⟨629916, by rfl⟩ : syracuseStep 1679777 = 1259833) B1259833
theorem B6400255 : Blo 495792 6400255 := bstep (se 1 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 6400255 = 9600383) B9600383
theorem B3582215 : Blo 495792 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B2828681 : Blo 495792 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B1682963 : Blo 495792 1682963 := bstep (se 1 (by rfl) ⟨1262222, by rfl⟩ : syracuseStep 1682963 = 2524445) B2524445
theorem B10728125 : Blo 495792 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B898537 : Blo 495792 898537 := bstep (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) B673903
theorem B1259489 : Blo 495792 1259489 := bstep (se 2 (by rfl) ⟨472308, by rfl⟩ : syracuseStep 1259489 = 944617) B944617
theorem B2832529 : Blo 495792 2832529 := bstep (se 2 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 2832529 = 2124397) B2124397
theorem B1686527 : Blo 495792 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B3785939 : Blo 495792 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B14403581 : Blo 495792 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B3164879 : Blo 495792 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B5393735 : Blo 495792 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B743801 : Blo 495792 743801 := bstep (se 2 (by rfl) ⟨278925, by rfl⟩ : syracuseStep 743801 = 557851) B557851
theorem B745151 : Blo 495792 745151 := bstep (se 1 (by rfl) ⟨558863, by rfl⟩ : syracuseStep 745151 = 1117727) B1117727
theorem B77815511 : Blo 495792 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B746879 : Blo 495792 746879 := bstep (se 1 (by rfl) ⟨560159, by rfl⟩ : syracuseStep 746879 = 1120319) B1120319
theorem B945179 : Blo 495792 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B18214055 : Blo 495792 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B749177 : Blo 495792 749177 := bstep (se 2 (by rfl) ⟨280941, by rfl⟩ : syracuseStep 749177 = 561883) B561883
theorem B749321 : Blo 495792 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B2127131 : Blo 495792 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B3602195 : Blo 495792 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B8485559 : Blo 495792 8485559 := bstep (se 1 (by rfl) ⟨6364169, by rfl⟩ : syracuseStep 8485559 = 12728339) B12728339
theorem B2523959 : Blo 495792 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B8520551 : Blo 495792 8520551 := bstep (se 1 (by rfl) ⟨6390413, by rfl⟩ : syracuseStep 8520551 = 12780827) B12780827
theorem B14353523 : Blo 495792 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B9602387 : Blo 495792 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B1116071 : Blo 495792 1116071 := bstep (se 1 (by rfl) ⟨837053, by rfl⟩ : syracuseStep 1116071 = 1674107) B1674107
theorem B1116287 : Blo 495792 1116287 := bstep (se 1 (by rfl) ⟨837215, by rfl⟩ : syracuseStep 1116287 = 1674431) B1674431
theorem B1116647 : Blo 495792 1116647 := bstep (se 1 (by rfl) ⟨837485, by rfl⟩ : syracuseStep 1116647 = 1674971) B1674971
theorem B495867 : Blo 495792 495867 := bstep (se 1 (by rfl) ⟨371900, by rfl⟩ : syracuseStep 495867 = 743801) B743801
theorem B496767 : Blo 495792 496767 := bstep (se 1 (by rfl) ⟨372575, by rfl⟩ : syracuseStep 496767 = 745151) B745151
theorem B51877007 : Blo 495792 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B1119419 : Blo 495792 1119419 := bstep (se 1 (by rfl) ⟨839564, by rfl⟩ : syracuseStep 1119419 = 1679129) B1679129
theorem B1119851 : Blo 495792 1119851 := bstep (se 1 (by rfl) ⟨839888, by rfl⟩ : syracuseStep 1119851 = 1679777) B1679777
theorem B497919 : Blo 495792 497919 := bstep (se 1 (by rfl) ⟨373439, by rfl⟩ : syracuseStep 497919 = 746879) B746879
theorem B630119 : Blo 495792 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B1121975 : Blo 495792 1121975 := bstep (se 1 (by rfl) ⟨841481, by rfl⟩ : syracuseStep 1121975 = 1682963) B1682963
theorem B499451 : Blo 495792 499451 := bstep (se 1 (by rfl) ⟨374588, by rfl⟩ : syracuseStep 499451 = 749177) B749177
theorem B499547 : Blo 495792 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B3776705 : Blo 495792 3776705 := bstep (se 2 (by rfl) ⟨1416264, by rfl⟩ : syracuseStep 3776705 = 2832529) B2832529
theorem B7152083 : Blo 495792 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B1418087 : Blo 495792 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B2401463 : Blo 495792 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B1124351 : Blo 495792 1124351 := bstep (se 1 (by rfl) ⟨843263, by rfl⟩ : syracuseStep 1124351 = 1686527) B1686527
theorem B2273675 : Blo 495792 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B8533673 : Blo 495792 8533673 := bstep (se 2 (by rfl) ⟨3200127, by rfl⟩ : syracuseStep 8533673 = 6400255) B6400255
theorem B3062015 : Blo 495792 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B4766363 : Blo 495792 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B1885787 : Blo 495792 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B8439677 : Blo 495792 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B1198049 : Blo 495792 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B12142703 : Blo 495792 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B839659 : Blo 495792 839659 := bstep (se 1 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 839659 = 1259489) B1259489
theorem B5657039 : Blo 495792 5657039 := bstep (se 1 (by rfl) ⟨4242779, by rfl⟩ : syracuseStep 5657039 = 8485559) B8485559
theorem B3595823 : Blo 495792 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B2515535 : Blo 495792 2515535 := bstep (se 1 (by rfl) ⟨1886651, by rfl⟩ : syracuseStep 2515535 = 3773303) B3773303
theorem B747623 : Blo 495792 747623 := bstep (se 1 (by rfl) ⟨560717, by rfl⟩ : syracuseStep 747623 = 1121435) B1121435
theorem B2388143 : Blo 495792 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B9569015 : Blo 495792 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B8095135 : Blo 495792 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B3771359 : Blo 495792 3771359 := bstep (se 1 (by rfl) ⟨2828519, by rfl⟩ : syracuseStep 3771359 = 5657039) B5657039
theorem B24252533 : Blo 495792 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B2397215 : Blo 495792 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B1119545 : Blo 495792 1119545 := bstep (se 2 (by rfl) ⟨419829, by rfl⟩ : syracuseStep 1119545 = 839659) B839659
theorem B1677023 : Blo 495792 1677023 := bstep (se 1 (by rfl) ⟨1257767, by rfl⟩ : syracuseStep 1677023 = 2515535) B2515535
theorem B498415 : Blo 495792 498415 := bstep (se 1 (by rfl) ⟨373811, by rfl⟩ : syracuseStep 498415 = 747623) B747623
theorem B1680317 : Blo 495792 1680317 := bstep (se 3 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 1680317 = 630119) B630119
theorem B2041343 : Blo 495792 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B1682639 : Blo 495792 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B5680367 : Blo 495792 5680367 := bstep (se 1 (by rfl) ⟨4260275, by rfl⟩ : syracuseStep 5680367 = 8520551) B8520551
theorem B6401591 : Blo 495792 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B1257191 : Blo 495792 1257191 := bstep (se 1 (by rfl) ⟨942893, by rfl⟩ : syracuseStep 1257191 = 1885787) B1885787
theorem B3781565 : Blo 495792 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B34584671 : Blo 495792 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B3194797 : Blo 495792 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B4768055 : Blo 495792 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B1592095 : Blo 495792 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B5689115 : Blo 495792 5689115 := bstep (se 1 (by rfl) ⟨4266836, by rfl⟩ : syracuseStep 5689115 = 8533673) B8533673
theorem B5626451 : Blo 495792 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B744047 : Blo 495792 744047 := bstep (se 1 (by rfl) ⟨558035, by rfl⟩ : syracuseStep 744047 = 1116071) B1116071
theorem B744191 : Blo 495792 744191 := bstep (se 1 (by rfl) ⟨558143, by rfl⟩ : syracuseStep 744191 = 1116287) B1116287
theorem B744431 : Blo 495792 744431 := bstep (se 1 (by rfl) ⟨558323, by rfl⟩ : syracuseStep 744431 = 1116647) B1116647
theorem B746279 : Blo 495792 746279 := bstep (se 1 (by rfl) ⟨559709, by rfl⟩ : syracuseStep 746279 = 1119419) B1119419
theorem B746567 : Blo 495792 746567 := bstep (se 1 (by rfl) ⟨559925, by rfl⟩ : syracuseStep 746567 = 1119851) B1119851
theorem B747983 : Blo 495792 747983 := bstep (se 1 (by rfl) ⟨560987, by rfl⟩ : syracuseStep 747983 = 1121975) B1121975
theorem B2517803 : Blo 495792 2517803 := bstep (se 1 (by rfl) ⟨1888352, by rfl⟩ : syracuseStep 2517803 = 3776705) B3776705
theorem B1600975 : Blo 495792 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B749567 : Blo 495792 749567 := bstep (se 1 (by rfl) ⟨562175, by rfl⟩ : syracuseStep 749567 = 1124351) B1124351
theorem B3177575 : Blo 495792 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B3178703 : Blo 495792 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B1118015 : Blo 495792 1118015 := bstep (se 1 (by rfl) ⟨838511, by rfl⟩ : syracuseStep 1118015 = 1677023) B1677023
theorem B496031 : Blo 495792 496031 := bstep (se 1 (by rfl) ⟨372023, by rfl⟩ : syracuseStep 496031 = 744047) B744047
theorem B496127 : Blo 495792 496127 := bstep (se 1 (by rfl) ⟨372095, by rfl⟩ : syracuseStep 496127 = 744191) B744191
theorem B2134633 : Blo 495792 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B496287 : Blo 495792 496287 := bstep (se 1 (by rfl) ⟨372215, by rfl⟩ : syracuseStep 496287 = 744431) B744431
theorem B497519 : Blo 495792 497519 := bstep (se 1 (by rfl) ⟨373139, by rfl⟩ : syracuseStep 497519 = 746279) B746279
theorem B1120211 : Blo 495792 1120211 := bstep (se 1 (by rfl) ⟨840158, by rfl⟩ : syracuseStep 1120211 = 1680317) B1680317
theorem B497711 : Blo 495792 497711 := bstep (se 1 (by rfl) ⟨373283, by rfl⟩ : syracuseStep 497711 = 746567) B746567
theorem B498655 : Blo 495792 498655 := bstep (se 1 (by rfl) ⟨373991, by rfl⟩ : syracuseStep 498655 = 747983) B747983
theorem B1678535 : Blo 495792 1678535 := bstep (se 1 (by rfl) ⟨1258901, by rfl⟩ : syracuseStep 1678535 = 2517803) B2517803
theorem B1121759 : Blo 495792 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B4267727 : Blo 495792 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B499711 : Blo 495792 499711 := bstep (se 1 (by rfl) ⟨374783, by rfl⟩ : syracuseStep 499711 = 749567) B749567
theorem B10793513 : Blo 495792 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B16168355 : Blo 495792 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B3750967 : Blo 495792 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B1360895 : Blo 495792 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B3786911 : Blo 495792 3786911 := bstep (se 1 (by rfl) ⟨2840183, by rfl⟩ : syracuseStep 3786911 = 5680367) B5680367
theorem B838127 : Blo 495792 838127 := bstep (se 1 (by rfl) ⟨628595, by rfl⟩ : syracuseStep 838127 = 1257191) B1257191
theorem B23056447 : Blo 495792 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B2118383 : Blo 495792 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B6379343 : Blo 495792 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B2514239 : Blo 495792 2514239 := bstep (se 1 (by rfl) ⟨1885679, by rfl⟩ : syracuseStep 2514239 = 3771359) B3771359
theorem B3792743 : Blo 495792 3792743 := bstep (se 1 (by rfl) ⟨2844557, by rfl⟩ : syracuseStep 3792743 = 5689115) B5689115
theorem B1598143 : Blo 495792 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B746363 : Blo 495792 746363 := bstep (se 1 (by rfl) ⟨559772, by rfl⟩ : syracuseStep 746363 = 1119545) B1119545
theorem B2122793 : Blo 495792 2122793 := bstep (se 2 (by rfl) ⟨796047, by rfl⟩ : syracuseStep 2122793 = 1592095) B1592095
theorem B2521043 : Blo 495792 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B4259729 : Blo 495792 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B2130857 : Blo 495792 2130857 := bstep (se 2 (by rfl) ⟨799071, by rfl⟩ : syracuseStep 2130857 = 1598143) B1598143
theorem B2524607 : Blo 495792 2524607 := bstep (se 1 (by rfl) ⟨1893455, by rfl⟩ : syracuseStep 2524607 = 3786911) B3786911
theorem B558751 : Blo 495792 558751 := bstep (se 1 (by rfl) ⟨419063, by rfl⟩ : syracuseStep 558751 = 838127) B838127
theorem B1412255 : Blo 495792 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1119023 : Blo 495792 1119023 := bstep (se 1 (by rfl) ⟨839267, by rfl⟩ : syracuseStep 1119023 = 1678535) B1678535
theorem B1676159 : Blo 495792 1676159 := bstep (se 1 (by rfl) ⟨1257119, by rfl⟩ : syracuseStep 1676159 = 2514239) B2514239
theorem B2528495 : Blo 495792 2528495 := bstep (se 1 (by rfl) ⟨1896371, by rfl⟩ : syracuseStep 2528495 = 3792743) B3792743
theorem B30741929 : Blo 495792 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B497575 : Blo 495792 497575 := bstep (se 1 (by rfl) ⟨373181, by rfl⟩ : syracuseStep 497575 = 746363) B746363
theorem B1415195 : Blo 495792 1415195 := bstep (se 1 (by rfl) ⟨1061396, by rfl⟩ : syracuseStep 1415195 = 2122793) B2122793
theorem B1680695 : Blo 495792 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B20005157 : Blo 495792 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B7195675 : Blo 495792 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B2839819 : Blo 495792 2839819 := bstep (se 1 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 2839819 = 4259729) B4259729
theorem B2119135 : Blo 495792 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B745343 : Blo 495792 745343 := bstep (se 1 (by rfl) ⟨559007, by rfl⟩ : syracuseStep 745343 = 1118015) B1118015
theorem B3629053 : Blo 495792 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B4252895 : Blo 495792 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B746807 : Blo 495792 746807 := bstep (se 1 (by rfl) ⟨560105, by rfl⟩ : syracuseStep 746807 = 1120211) B1120211
theorem B747839 : Blo 495792 747839 := bstep (se 1 (by rfl) ⟨560879, by rfl⟩ : syracuseStep 747839 = 1121759) B1121759
theorem B2845151 : Blo 495792 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B2846177 : Blo 495792 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B10778903 : Blo 495792 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B13336771 : Blo 495792 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B1117439 : Blo 495792 1117439 := bstep (se 1 (by rfl) ⟨838079, by rfl⟩ : syracuseStep 1117439 = 1676159) B1676159
theorem B496895 : Blo 495792 496895 := bstep (se 1 (by rfl) ⟨372671, by rfl⟩ : syracuseStep 496895 = 745343) B745343
theorem B497871 : Blo 495792 497871 := bstep (se 1 (by rfl) ⟨373403, by rfl⟩ : syracuseStep 497871 = 746807) B746807
theorem B1120463 : Blo 495792 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B498559 : Blo 495792 498559 := bstep (se 1 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 498559 = 747839) B747839
theorem B2825513 : Blo 495792 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B7185935 : Blo 495792 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B1420571 : Blo 495792 1420571 := bstep (se 1 (by rfl) ⟨1065428, by rfl⟩ : syracuseStep 1420571 = 2130857) B2130857
theorem B1683071 : Blo 495792 1683071 := bstep (se 1 (by rfl) ⟨1262303, by rfl⟩ : syracuseStep 1683071 = 2524607) B2524607
theorem B1685663 : Blo 495792 1685663 := bstep (se 1 (by rfl) ⟨1264247, by rfl⟩ : syracuseStep 1685663 = 2528495) B2528495
theorem B20494619 : Blo 495792 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B2835263 : Blo 495792 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B3786425 : Blo 495792 3786425 := bstep (se 2 (by rfl) ⟨1419909, by rfl⟩ : syracuseStep 3786425 = 2839819) B2839819
theorem B4838737 : Blo 495792 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B745001 : Blo 495792 745001 := bstep (se 2 (by rfl) ⟨279375, by rfl⟩ : syracuseStep 745001 = 558751) B558751
theorem B746015 : Blo 495792 746015 := bstep (se 1 (by rfl) ⟨559511, by rfl⟩ : syracuseStep 746015 = 1119023) B1119023
theorem B943463 : Blo 495792 943463 := bstep (se 1 (by rfl) ⟨707597, by rfl⟩ : syracuseStep 943463 = 1415195) B1415195
theorem B9594233 : Blo 495792 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B1896767 : Blo 495792 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B1897451 : Blo 495792 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B3766013 : Blo 495792 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B2524283 : Blo 495792 2524283 := bstep (se 1 (by rfl) ⟨1893212, by rfl⟩ : syracuseStep 2524283 = 3786425) B3786425
theorem B496667 : Blo 495792 496667 := bstep (se 1 (by rfl) ⟨372500, by rfl⟩ : syracuseStep 496667 = 745001) B745001
theorem B497343 : Blo 495792 497343 := bstep (se 1 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 497343 = 746015) B746015
theorem B628975 : Blo 495792 628975 := bstep (se 1 (by rfl) ⟨471731, by rfl⟩ : syracuseStep 628975 = 943463) B943463
theorem B6396155 : Blo 495792 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B4790623 : Blo 495792 4790623 := bstep (se 1 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 4790623 = 7185935) B7185935
theorem B1122047 : Blo 495792 1122047 := bstep (se 1 (by rfl) ⟨841535, by rfl⟩ : syracuseStep 1122047 = 1683071) B1683071
theorem B1123775 : Blo 495792 1123775 := bstep (se 1 (by rfl) ⟨842831, by rfl⟩ : syracuseStep 1123775 = 1685663) B1685663
theorem B1883675 : Blo 495792 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B1264511 : Blo 495792 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B1264967 : Blo 495792 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B2510675 : Blo 495792 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B17782361 : Blo 495792 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B1890175 : Blo 495792 1890175 := bstep (se 1 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 1890175 = 2835263) B2835263
theorem B744959 : Blo 495792 744959 := bstep (se 1 (by rfl) ⟨558719, by rfl⟩ : syracuseStep 744959 = 1117439) B1117439
theorem B746975 : Blo 495792 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B6451649 : Blo 495792 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B947047 : Blo 495792 947047 := bstep (se 1 (by rfl) ⟨710285, by rfl⟩ : syracuseStep 947047 = 1420571) B1420571
theorem B13663079 : Blo 495792 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B1673783 : Blo 495792 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B4264103 : Blo 495792 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B496639 : Blo 495792 496639 := bstep (se 1 (by rfl) ⟨372479, by rfl⟩ : syracuseStep 496639 = 744959) B744959
theorem B497983 : Blo 495792 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B4301099 : Blo 495792 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B1255783 : Blo 495792 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B1682855 : Blo 495792 1682855 := bstep (se 1 (by rfl) ⟨1262141, by rfl⟩ : syracuseStep 1682855 = 2524283) B2524283
theorem B1262729 : Blo 495792 1262729 := bstep (se 2 (by rfl) ⟨473523, by rfl⟩ : syracuseStep 1262729 = 947047) B947047
theorem B838633 : Blo 495792 838633 := bstep (se 2 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 838633 = 628975) B628975
theorem B843007 : Blo 495792 843007 := bstep (se 1 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 843007 = 1264511) B1264511
theorem B843311 : Blo 495792 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B11854907 : Blo 495792 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B748031 : Blo 495792 748031 := bstep (se 1 (by rfl) ⟨561023, by rfl⟩ : syracuseStep 748031 = 1122047) B1122047
theorem B749183 : Blo 495792 749183 := bstep (se 1 (by rfl) ⟨561887, by rfl⟩ : syracuseStep 749183 = 1123775) B1123775
theorem B2520233 : Blo 495792 2520233 := bstep (se 2 (by rfl) ⟨945087, by rfl⟩ : syracuseStep 2520233 = 1890175) B1890175
theorem B6387497 : Blo 495792 6387497 := bstep (se 2 (by rfl) ⟨2395311, by rfl⟩ : syracuseStep 6387497 = 4790623) B4790623
theorem B9108719 : Blo 495792 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B1115855 : Blo 495792 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B1674377 : Blo 495792 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B1118177 : Blo 495792 1118177 := bstep (se 2 (by rfl) ⟨419316, by rfl⟩ : syracuseStep 1118177 = 838633) B838633
theorem B562207 : Blo 495792 562207 := bstep (se 1 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 562207 = 843311) B843311
theorem B7903271 : Blo 495792 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B498687 : Blo 495792 498687 := bstep (se 1 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 498687 = 748031) B748031
theorem B1121903 : Blo 495792 1121903 := bstep (se 1 (by rfl) ⟨841427, by rfl⟩ : syracuseStep 1121903 = 1682855) B1682855
theorem B499455 : Blo 495792 499455 := bstep (se 1 (by rfl) ⟨374591, by rfl⟩ : syracuseStep 499455 = 749183) B749183
theorem B1680155 : Blo 495792 1680155 := bstep (se 1 (by rfl) ⟨1260116, by rfl⟩ : syracuseStep 1680155 = 2520233) B2520233
theorem B1124009 : Blo 495792 1124009 := bstep (se 2 (by rfl) ⟨421503, by rfl⟩ : syracuseStep 1124009 = 843007) B843007
theorem B6072479 : Blo 495792 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B2867399 : Blo 495792 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B841819 : Blo 495792 841819 := bstep (se 1 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 841819 = 1262729) B1262729
theorem B2842735 : Blo 495792 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B4258331 : Blo 495792 4258331 := bstep (se 1 (by rfl) ⟨3193748, by rfl⟩ : syracuseStep 4258331 = 6387497) B6387497
theorem B1116251 : Blo 495792 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B1120103 : Blo 495792 1120103 := bstep (se 1 (by rfl) ⟨840077, by rfl⟩ : syracuseStep 1120103 = 1680155) B1680155
theorem B1122425 : Blo 495792 1122425 := bstep (se 2 (by rfl) ⟨420909, by rfl⟩ : syracuseStep 1122425 = 841819) B841819
theorem B1911599 : Blo 495792 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B4048319 : Blo 495792 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B2838887 : Blo 495792 2838887 := bstep (se 1 (by rfl) ⟨2129165, by rfl⟩ : syracuseStep 2838887 = 4258331) B4258331
theorem B3790313 : Blo 495792 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B743903 : Blo 495792 743903 := bstep (se 1 (by rfl) ⟨557927, by rfl⟩ : syracuseStep 743903 = 1115855) B1115855
theorem B745451 : Blo 495792 745451 := bstep (se 1 (by rfl) ⟨559088, by rfl⟩ : syracuseStep 745451 = 1118177) B1118177
theorem B5268847 : Blo 495792 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B747935 : Blo 495792 747935 := bstep (se 1 (by rfl) ⟨560951, by rfl⟩ : syracuseStep 747935 = 1121903) B1121903
theorem B749339 : Blo 495792 749339 := bstep (se 1 (by rfl) ⟨562004, by rfl⟩ : syracuseStep 749339 = 1124009) B1124009
theorem B749609 : Blo 495792 749609 := bstep (se 2 (by rfl) ⟨281103, by rfl⟩ : syracuseStep 749609 = 562207) B562207
theorem B2526875 : Blo 495792 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B495935 : Blo 495792 495935 := bstep (se 1 (by rfl) ⟨371951, by rfl⟩ : syracuseStep 495935 = 743903) B743903
theorem B496967 : Blo 495792 496967 := bstep (se 1 (by rfl) ⟨372725, by rfl⟩ : syracuseStep 496967 = 745451) B745451
theorem B498623 : Blo 495792 498623 := bstep (se 1 (by rfl) ⟨373967, by rfl⟩ : syracuseStep 498623 = 747935) B747935
theorem B499559 : Blo 495792 499559 := bstep (se 1 (by rfl) ⟨374669, by rfl⟩ : syracuseStep 499559 = 749339) B749339
theorem B499739 : Blo 495792 499739 := bstep (se 1 (by rfl) ⟨374804, by rfl⟩ : syracuseStep 499739 = 749609) B749609
theorem B2698879 : Blo 495792 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B7025129 : Blo 495792 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B744167 : Blo 495792 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B1892591 : Blo 495792 1892591 := bstep (se 1 (by rfl) ⟨1419443, by rfl⟩ : syracuseStep 1892591 = 2838887) B2838887
theorem B746735 : Blo 495792 746735 := bstep (se 1 (by rfl) ⟨560051, by rfl⟩ : syracuseStep 746735 = 1120103) B1120103
theorem B748283 : Blo 495792 748283 := bstep (se 1 (by rfl) ⟨561212, by rfl⟩ : syracuseStep 748283 = 1122425) B1122425
theorem B1274399 : Blo 495792 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B496111 : Blo 495792 496111 := bstep (se 1 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 496111 = 744167) B744167
theorem B497823 : Blo 495792 497823 := bstep (se 1 (by rfl) ⟨373367, by rfl⟩ : syracuseStep 497823 = 746735) B746735
theorem B498855 : Blo 495792 498855 := bstep (se 1 (by rfl) ⟨374141, by rfl⟩ : syracuseStep 498855 = 748283) B748283
theorem B1684583 : Blo 495792 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B1261727 : Blo 495792 1261727 := bstep (se 1 (by rfl) ⟨946295, by rfl⟩ : syracuseStep 1261727 = 1892591) B1892591
theorem B3598505 : Blo 495792 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B4683419 : Blo 495792 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B849599 : Blo 495792 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B2399003 : Blo 495792 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B1123055 : Blo 495792 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B3122279 : Blo 495792 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B566399 : Blo 495792 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B841151 : Blo 495792 841151 := bstep (se 1 (by rfl) ⟨630863, by rfl⟩ : syracuseStep 841151 = 1261727) B1261727
theorem B1510397 : Blo 495792 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B560767 : Blo 495792 560767 := bstep (se 1 (by rfl) ⟨420575, by rfl⟩ : syracuseStep 560767 = 841151) B841151
theorem B2081519 : Blo 495792 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B1599335 : Blo 495792 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B748703 : Blo 495792 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B499135 : Blo 495792 499135 := bstep (se 1 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 499135 = 748703) B748703
theorem B1066223 : Blo 495792 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B22202869 : Blo 495792 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B1006931 : Blo 495792 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B747689 : Blo 495792 747689 := bstep (se 2 (by rfl) ⟨280383, by rfl⟩ : syracuseStep 747689 = 560767) B560767
theorem B498459 : Blo 495792 498459 := bstep (se 1 (by rfl) ⟨373844, by rfl⟩ : syracuseStep 498459 = 747689) B747689
theorem B29603825 : Blo 495792 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B2843261 : Blo 495792 2843261 := bstep (se 3 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 2843261 = 1066223) B1066223
theorem B2685149 : Blo 495792 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B19735883 : Blo 495792 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B1790099 : Blo 495792 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B1895507 : Blo 495792 1895507 := bstep (se 1 (by rfl) ⟨1421630, by rfl⟩ : syracuseStep 1895507 = 2843261) B2843261
theorem B1193399 : Blo 495792 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B13157255 : Blo 495792 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B1263671 : Blo 495792 1263671 := bstep (se 1 (by rfl) ⟨947753, by rfl⟩ : syracuseStep 1263671 = 1895507) B1895507
theorem B795599 : Blo 495792 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B8771503 : Blo 495792 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B842447 : Blo 495792 842447 := bstep (se 1 (by rfl) ⟨631835, by rfl⟩ : syracuseStep 842447 = 1263671) B1263671
theorem B561631 : Blo 495792 561631 := bstep (se 1 (by rfl) ⟨421223, by rfl⟩ : syracuseStep 561631 = 842447) B842447
theorem B530399 : Blo 495792 530399 := bstep (se 1 (by rfl) ⟨397799, by rfl⟩ : syracuseStep 530399 = 795599) B795599
theorem B11695337 : Blo 495792 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B1414397 : Blo 495792 1414397 := bstep (se 3 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 1414397 = 530399) B530399
theorem B748841 : Blo 495792 748841 := bstep (se 2 (by rfl) ⟨280815, by rfl⟩ : syracuseStep 748841 = 561631) B561631
theorem B7796891 : Blo 495792 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B499227 : Blo 495792 499227 := bstep (se 1 (by rfl) ⟨374420, by rfl⟩ : syracuseStep 499227 = 748841) B748841
theorem B5197927 : Blo 495792 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B942931 : Blo 495792 942931 := bstep (se 1 (by rfl) ⟨707198, by rfl⟩ : syracuseStep 942931 = 1414397) B1414397
theorem B1257241 : Blo 495792 1257241 := bstep (se 2 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 1257241 = 942931) B942931
theorem B6930569 : Blo 495792 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B18481517 : Blo 495792 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B1676321 : Blo 495792 1676321 := bstep (se 2 (by rfl) ⟨628620, by rfl⟩ : syracuseStep 1676321 = 1257241) B1257241
theorem B12321011 : Blo 495792 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B1117547 : Blo 495792 1117547 := bstep (se 1 (by rfl) ⟨838160, by rfl⟩ : syracuseStep 1117547 = 1676321) B1676321
theorem B8214007 : Blo 495792 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B745031 : Blo 495792 745031 := bstep (se 1 (by rfl) ⟨558773, by rfl⟩ : syracuseStep 745031 = 1117547) B1117547
theorem B496687 : Blo 495792 496687 := bstep (se 1 (by rfl) ⟨372515, by rfl⟩ : syracuseStep 496687 = 745031) B745031
theorem B10952009 : Blo 495792 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B7301339 : Blo 495792 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B4867559 : Blo 495792 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B3245039 : Blo 495792 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B2163359 : Blo 495792 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B5768957 : Blo 495792 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B3845971 : Blo 495792 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B5127961 : Blo 495792 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B6837281 : Blo 495792 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B4558187 : Blo 495792 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B3038791 : Blo 495792 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 495792 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B2701147 : Blo 495792 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B3601529 : Blo 495792 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B2401019 : Blo 495792 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B1600679 : Blo 495792 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B4268477 : Blo 495792 4268477 := bstep (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) B1600679
theorem B2845651 : Blo 495792 2845651 := bstep (se 1 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 2845651 = 4268477) B4268477
theorem B3794201 : Blo 495792 3794201 := bstep (se 2 (by rfl) ⟨1422825, by rfl⟩ : syracuseStep 3794201 = 2845651) B2845651
theorem B2529467 : Blo 495792 2529467 := bstep (se 1 (by rfl) ⟨1897100, by rfl⟩ : syracuseStep 2529467 = 3794201) B3794201
theorem B1686311 : Blo 495792 1686311 := bstep (se 1 (by rfl) ⟨1264733, by rfl⟩ : syracuseStep 1686311 = 2529467) B2529467
theorem B1124207 : Blo 495792 1124207 := bstep (se 1 (by rfl) ⟨843155, by rfl⟩ : syracuseStep 1124207 = 1686311) B1686311
theorem B749471 : Blo 495792 749471 := bstep (se 1 (by rfl) ⟨562103, by rfl⟩ : syracuseStep 749471 = 1124207) B1124207
theorem B499647 : Blo 495792 499647 := bstep (se 1 (by rfl) ⟨374735, by rfl⟩ : syracuseStep 499647 = 749471) B749471

theorem C0 (j : ℕ) (h1 : 123948 ≤ j) (h2 : j ≤ 124647) : Blo 495792 (4 * j + 3) := by
  interval_cases j
  · exact B495795
  · exact B495799
  · exact B495803
  · exact B495807
  · exact B495811
  · exact B495815
  · exact B495819
  · exact B495823
  · exact B495827
  · exact B495831
  · exact B495835
  · exact B495839
  · exact B495843
  · exact B495847
  · exact B495851
  · exact B495855
  · exact B495859
  · exact B495863
  · exact B495867
  · exact B495871
  · exact B495875
  · exact B495879
  · exact B495883
  · exact B495887
  · exact B495891
  · exact B495895
  · exact B495899
  · exact B495903
  · exact B495907
  · exact B495911
  · exact B495915
  · exact B495919
  · exact B495923
  · exact B495927
  · exact B495931
  · exact B495935
  · exact B495939
  · exact B495943
  · exact B495947
  · exact B495951
  · exact B495955
  · exact B495959
  · exact B495963
  · exact B495967
  · exact B495971
  · exact B495975
  · exact B495979
  · exact B495983
  · exact B495987
  · exact B495991
  · exact B495995
  · exact B495999
  · exact B496003
  · exact B496007
  · exact B496011
  · exact B496015
  · exact B496019
  · exact B496023
  · exact B496027
  · exact B496031
  · exact B496035
  · exact B496039
  · exact B496043
  · exact B496047
  · exact B496051
  · exact B496055
  · exact B496059
  · exact B496063
  · exact B496067
  · exact B496071
  · exact B496075
  · exact B496079
  · exact B496083
  · exact B496087
  · exact B496091
  · exact B496095
  · exact B496099
  · exact B496103
  · exact B496107
  · exact B496111
  · exact B496115
  · exact B496119
  · exact B496123
  · exact B496127
  · exact B496131
  · exact B496135
  · exact B496139
  · exact B496143
  · exact B496147
  · exact B496151
  · exact B496155
  · exact B496159
  · exact B496163
  · exact B496167
  · exact B496171
  · exact B496175
  · exact B496179
  · exact B496183
  · exact B496187
  · exact B496191
  · exact B496195
  · exact B496199
  · exact B496203
  · exact B496207
  · exact B496211
  · exact B496215
  · exact B496219
  · exact B496223
  · exact B496227
  · exact B496231
  · exact B496235
  · exact B496239
  · exact B496243
  · exact B496247
  · exact B496251
  · exact B496255
  · exact B496259
  · exact B496263
  · exact B496267
  · exact B496271
  · exact B496275
  · exact B496279
  · exact B496283
  · exact B496287
  · exact B496291
  · exact B496295
  · exact B496299
  · exact B496303
  · exact B496307
  · exact B496311
  · exact B496315
  · exact B496319
  · exact B496323
  · exact B496327
  · exact B496331
  · exact B496335
  · exact B496339
  · exact B496343
  · exact B496347
  · exact B496351
  · exact B496355
  · exact B496359
  · exact B496363
  · exact B496367
  · exact B496371
  · exact B496375
  · exact B496379
  · exact B496383
  · exact B496387
  · exact B496391
  · exact B496395
  · exact B496399
  · exact B496403
  · exact B496407
  · exact B496411
  · exact B496415
  · exact B496419
  · exact B496423
  · exact B496427
  · exact B496431
  · exact B496435
  · exact B496439
  · exact B496443
  · exact B496447
  · exact B496451
  · exact B496455
  · exact B496459
  · exact B496463
  · exact B496467
  · exact B496471
  · exact B496475
  · exact B496479
  · exact B496483
  · exact B496487
  · exact B496491
  · exact B496495
  · exact B496499
  · exact B496503
  · exact B496507
  · exact B496511
  · exact B496515
  · exact B496519
  · exact B496523
  · exact B496527
  · exact B496531
  · exact B496535
  · exact B496539
  · exact B496543
  · exact B496547
  · exact B496551
  · exact B496555
  · exact B496559
  · exact B496563
  · exact B496567
  · exact B496571
  · exact B496575
  · exact B496579
  · exact B496583
  · exact B496587
  · exact B496591
  · exact B496595
  · exact B496599
  · exact B496603
  · exact B496607
  · exact B496611
  · exact B496615
  · exact B496619
  · exact B496623
  · exact B496627
  · exact B496631
  · exact B496635
  · exact B496639
  · exact B496643
  · exact B496647
  · exact B496651
  · exact B496655
  · exact B496659
  · exact B496663
  · exact B496667
  · exact B496671
  · exact B496675
  · exact B496679
  · exact B496683
  · exact B496687
  · exact B496691
  · exact B496695
  · exact B496699
  · exact B496703
  · exact B496707
  · exact B496711
  · exact B496715
  · exact B496719
  · exact B496723
  · exact B496727
  · exact B496731
  · exact B496735
  · exact B496739
  · exact B496743
  · exact B496747
  · exact B496751
  · exact B496755
  · exact B496759
  · exact B496763
  · exact B496767
  · exact B496771
  · exact B496775
  · exact B496779
  · exact B496783
  · exact B496787
  · exact B496791
  · exact B496795
  · exact B496799
  · exact B496803
  · exact B496807
  · exact B496811
  · exact B496815
  · exact B496819
  · exact B496823
  · exact B496827
  · exact B496831
  · exact B496835
  · exact B496839
  · exact B496843
  · exact B496847
  · exact B496851
  · exact B496855
  · exact B496859
  · exact B496863
  · exact B496867
  · exact B496871
  · exact B496875
  · exact B496879
  · exact B496883
  · exact B496887
  · exact B496891
  · exact B496895
  · exact B496899
  · exact B496903
  · exact B496907
  · exact B496911
  · exact B496915
  · exact B496919
  · exact B496923
  · exact B496927
  · exact B496931
  · exact B496935
  · exact B496939
  · exact B496943
  · exact B496947
  · exact B496951
  · exact B496955
  · exact B496959
  · exact B496963
  · exact B496967
  · exact B496971
  · exact B496975
  · exact B496979
  · exact B496983
  · exact B496987
  · exact B496991
  · exact B496995
  · exact B496999
  · exact B497003
  · exact B497007
  · exact B497011
  · exact B497015
  · exact B497019
  · exact B497023
  · exact B497027
  · exact B497031
  · exact B497035
  · exact B497039
  · exact B497043
  · exact B497047
  · exact B497051
  · exact B497055
  · exact B497059
  · exact B497063
  · exact B497067
  · exact B497071
  · exact B497075
  · exact B497079
  · exact B497083
  · exact B497087
  · exact B497091
  · exact B497095
  · exact B497099
  · exact B497103
  · exact B497107
  · exact B497111
  · exact B497115
  · exact B497119
  · exact B497123
  · exact B497127
  · exact B497131
  · exact B497135
  · exact B497139
  · exact B497143
  · exact B497147
  · exact B497151
  · exact B497155
  · exact B497159
  · exact B497163
  · exact B497167
  · exact B497171
  · exact B497175
  · exact B497179
  · exact B497183
  · exact B497187
  · exact B497191
  · exact B497195
  · exact B497199
  · exact B497203
  · exact B497207
  · exact B497211
  · exact B497215
  · exact B497219
  · exact B497223
  · exact B497227
  · exact B497231
  · exact B497235
  · exact B497239
  · exact B497243
  · exact B497247
  · exact B497251
  · exact B497255
  · exact B497259
  · exact B497263
  · exact B497267
  · exact B497271
  · exact B497275
  · exact B497279
  · exact B497283
  · exact B497287
  · exact B497291
  · exact B497295
  · exact B497299
  · exact B497303
  · exact B497307
  · exact B497311
  · exact B497315
  · exact B497319
  · exact B497323
  · exact B497327
  · exact B497331
  · exact B497335
  · exact B497339
  · exact B497343
  · exact B497347
  · exact B497351
  · exact B497355
  · exact B497359
  · exact B497363
  · exact B497367
  · exact B497371
  · exact B497375
  · exact B497379
  · exact B497383
  · exact B497387
  · exact B497391
  · exact B497395
  · exact B497399
  · exact B497403
  · exact B497407
  · exact B497411
  · exact B497415
  · exact B497419
  · exact B497423
  · exact B497427
  · exact B497431
  · exact B497435
  · exact B497439
  · exact B497443
  · exact B497447
  · exact B497451
  · exact B497455
  · exact B497459
  · exact B497463
  · exact B497467
  · exact B497471
  · exact B497475
  · exact B497479
  · exact B497483
  · exact B497487
  · exact B497491
  · exact B497495
  · exact B497499
  · exact B497503
  · exact B497507
  · exact B497511
  · exact B497515
  · exact B497519
  · exact B497523
  · exact B497527
  · exact B497531
  · exact B497535
  · exact B497539
  · exact B497543
  · exact B497547
  · exact B497551
  · exact B497555
  · exact B497559
  · exact B497563
  · exact B497567
  · exact B497571
  · exact B497575
  · exact B497579
  · exact B497583
  · exact B497587
  · exact B497591
  · exact B497595
  · exact B497599
  · exact B497603
  · exact B497607
  · exact B497611
  · exact B497615
  · exact B497619
  · exact B497623
  · exact B497627
  · exact B497631
  · exact B497635
  · exact B497639
  · exact B497643
  · exact B497647
  · exact B497651
  · exact B497655
  · exact B497659
  · exact B497663
  · exact B497667
  · exact B497671
  · exact B497675
  · exact B497679
  · exact B497683
  · exact B497687
  · exact B497691
  · exact B497695
  · exact B497699
  · exact B497703
  · exact B497707
  · exact B497711
  · exact B497715
  · exact B497719
  · exact B497723
  · exact B497727
  · exact B497731
  · exact B497735
  · exact B497739
  · exact B497743
  · exact B497747
  · exact B497751
  · exact B497755
  · exact B497759
  · exact B497763
  · exact B497767
  · exact B497771
  · exact B497775
  · exact B497779
  · exact B497783
  · exact B497787
  · exact B497791
  · exact B497795
  · exact B497799
  · exact B497803
  · exact B497807
  · exact B497811
  · exact B497815
  · exact B497819
  · exact B497823
  · exact B497827
  · exact B497831
  · exact B497835
  · exact B497839
  · exact B497843
  · exact B497847
  · exact B497851
  · exact B497855
  · exact B497859
  · exact B497863
  · exact B497867
  · exact B497871
  · exact B497875
  · exact B497879
  · exact B497883
  · exact B497887
  · exact B497891
  · exact B497895
  · exact B497899
  · exact B497903
  · exact B497907
  · exact B497911
  · exact B497915
  · exact B497919
  · exact B497923
  · exact B497927
  · exact B497931
  · exact B497935
  · exact B497939
  · exact B497943
  · exact B497947
  · exact B497951
  · exact B497955
  · exact B497959
  · exact B497963
  · exact B497967
  · exact B497971
  · exact B497975
  · exact B497979
  · exact B497983
  · exact B497987
  · exact B497991
  · exact B497995
  · exact B497999
  · exact B498003
  · exact B498007
  · exact B498011
  · exact B498015
  · exact B498019
  · exact B498023
  · exact B498027
  · exact B498031
  · exact B498035
  · exact B498039
  · exact B498043
  · exact B498047
  · exact B498051
  · exact B498055
  · exact B498059
  · exact B498063
  · exact B498067
  · exact B498071
  · exact B498075
  · exact B498079
  · exact B498083
  · exact B498087
  · exact B498091
  · exact B498095
  · exact B498099
  · exact B498103
  · exact B498107
  · exact B498111
  · exact B498115
  · exact B498119
  · exact B498123
  · exact B498127
  · exact B498131
  · exact B498135
  · exact B498139
  · exact B498143
  · exact B498147
  · exact B498151
  · exact B498155
  · exact B498159
  · exact B498163
  · exact B498167
  · exact B498171
  · exact B498175
  · exact B498179
  · exact B498183
  · exact B498187
  · exact B498191
  · exact B498195
  · exact B498199
  · exact B498203
  · exact B498207
  · exact B498211
  · exact B498215
  · exact B498219
  · exact B498223
  · exact B498227
  · exact B498231
  · exact B498235
  · exact B498239
  · exact B498243
  · exact B498247
  · exact B498251
  · exact B498255
  · exact B498259
  · exact B498263
  · exact B498267
  · exact B498271
  · exact B498275
  · exact B498279
  · exact B498283
  · exact B498287
  · exact B498291
  · exact B498295
  · exact B498299
  · exact B498303
  · exact B498307
  · exact B498311
  · exact B498315
  · exact B498319
  · exact B498323
  · exact B498327
  · exact B498331
  · exact B498335
  · exact B498339
  · exact B498343
  · exact B498347
  · exact B498351
  · exact B498355
  · exact B498359
  · exact B498363
  · exact B498367
  · exact B498371
  · exact B498375
  · exact B498379
  · exact B498383
  · exact B498387
  · exact B498391
  · exact B498395
  · exact B498399
  · exact B498403
  · exact B498407
  · exact B498411
  · exact B498415
  · exact B498419
  · exact B498423
  · exact B498427
  · exact B498431
  · exact B498435
  · exact B498439
  · exact B498443
  · exact B498447
  · exact B498451
  · exact B498455
  · exact B498459
  · exact B498463
  · exact B498467
  · exact B498471
  · exact B498475
  · exact B498479
  · exact B498483
  · exact B498487
  · exact B498491
  · exact B498495
  · exact B498499
  · exact B498503
  · exact B498507
  · exact B498511
  · exact B498515
  · exact B498519
  · exact B498523
  · exact B498527
  · exact B498531
  · exact B498535
  · exact B498539
  · exact B498543
  · exact B498547
  · exact B498551
  · exact B498555
  · exact B498559
  · exact B498563
  · exact B498567
  · exact B498571
  · exact B498575
  · exact B498579
  · exact B498583
  · exact B498587
  · exact B498591

theorem C1 (j : ℕ) (h1 : 124648 ≤ j) (h2 : j ≤ 124947) : Blo 495792 (4 * j + 3) := by
  interval_cases j
  · exact B498595
  · exact B498599
  · exact B498603
  · exact B498607
  · exact B498611
  · exact B498615
  · exact B498619
  · exact B498623
  · exact B498627
  · exact B498631
  · exact B498635
  · exact B498639
  · exact B498643
  · exact B498647
  · exact B498651
  · exact B498655
  · exact B498659
  · exact B498663
  · exact B498667
  · exact B498671
  · exact B498675
  · exact B498679
  · exact B498683
  · exact B498687
  · exact B498691
  · exact B498695
  · exact B498699
  · exact B498703
  · exact B498707
  · exact B498711
  · exact B498715
  · exact B498719
  · exact B498723
  · exact B498727
  · exact B498731
  · exact B498735
  · exact B498739
  · exact B498743
  · exact B498747
  · exact B498751
  · exact B498755
  · exact B498759
  · exact B498763
  · exact B498767
  · exact B498771
  · exact B498775
  · exact B498779
  · exact B498783
  · exact B498787
  · exact B498791
  · exact B498795
  · exact B498799
  · exact B498803
  · exact B498807
  · exact B498811
  · exact B498815
  · exact B498819
  · exact B498823
  · exact B498827
  · exact B498831
  · exact B498835
  · exact B498839
  · exact B498843
  · exact B498847
  · exact B498851
  · exact B498855
  · exact B498859
  · exact B498863
  · exact B498867
  · exact B498871
  · exact B498875
  · exact B498879
  · exact B498883
  · exact B498887
  · exact B498891
  · exact B498895
  · exact B498899
  · exact B498903
  · exact B498907
  · exact B498911
  · exact B498915
  · exact B498919
  · exact B498923
  · exact B498927
  · exact B498931
  · exact B498935
  · exact B498939
  · exact B498943
  · exact B498947
  · exact B498951
  · exact B498955
  · exact B498959
  · exact B498963
  · exact B498967
  · exact B498971
  · exact B498975
  · exact B498979
  · exact B498983
  · exact B498987
  · exact B498991
  · exact B498995
  · exact B498999
  · exact B499003
  · exact B499007
  · exact B499011
  · exact B499015
  · exact B499019
  · exact B499023
  · exact B499027
  · exact B499031
  · exact B499035
  · exact B499039
  · exact B499043
  · exact B499047
  · exact B499051
  · exact B499055
  · exact B499059
  · exact B499063
  · exact B499067
  · exact B499071
  · exact B499075
  · exact B499079
  · exact B499083
  · exact B499087
  · exact B499091
  · exact B499095
  · exact B499099
  · exact B499103
  · exact B499107
  · exact B499111
  · exact B499115
  · exact B499119
  · exact B499123
  · exact B499127
  · exact B499131
  · exact B499135
  · exact B499139
  · exact B499143
  · exact B499147
  · exact B499151
  · exact B499155
  · exact B499159
  · exact B499163
  · exact B499167
  · exact B499171
  · exact B499175
  · exact B499179
  · exact B499183
  · exact B499187
  · exact B499191
  · exact B499195
  · exact B499199
  · exact B499203
  · exact B499207
  · exact B499211
  · exact B499215
  · exact B499219
  · exact B499223
  · exact B499227
  · exact B499231
  · exact B499235
  · exact B499239
  · exact B499243
  · exact B499247
  · exact B499251
  · exact B499255
  · exact B499259
  · exact B499263
  · exact B499267
  · exact B499271
  · exact B499275
  · exact B499279
  · exact B499283
  · exact B499287
  · exact B499291
  · exact B499295
  · exact B499299
  · exact B499303
  · exact B499307
  · exact B499311
  · exact B499315
  · exact B499319
  · exact B499323
  · exact B499327
  · exact B499331
  · exact B499335
  · exact B499339
  · exact B499343
  · exact B499347
  · exact B499351
  · exact B499355
  · exact B499359
  · exact B499363
  · exact B499367
  · exact B499371
  · exact B499375
  · exact B499379
  · exact B499383
  · exact B499387
  · exact B499391
  · exact B499395
  · exact B499399
  · exact B499403
  · exact B499407
  · exact B499411
  · exact B499415
  · exact B499419
  · exact B499423
  · exact B499427
  · exact B499431
  · exact B499435
  · exact B499439
  · exact B499443
  · exact B499447
  · exact B499451
  · exact B499455
  · exact B499459
  · exact B499463
  · exact B499467
  · exact B499471
  · exact B499475
  · exact B499479
  · exact B499483
  · exact B499487
  · exact B499491
  · exact B499495
  · exact B499499
  · exact B499503
  · exact B499507
  · exact B499511
  · exact B499515
  · exact B499519
  · exact B499523
  · exact B499527
  · exact B499531
  · exact B499535
  · exact B499539
  · exact B499543
  · exact B499547
  · exact B499551
  · exact B499555
  · exact B499559
  · exact B499563
  · exact B499567
  · exact B499571
  · exact B499575
  · exact B499579
  · exact B499583
  · exact B499587
  · exact B499591
  · exact B499595
  · exact B499599
  · exact B499603
  · exact B499607
  · exact B499611
  · exact B499615
  · exact B499619
  · exact B499623
  · exact B499627
  · exact B499631
  · exact B499635
  · exact B499639
  · exact B499643
  · exact B499647
  · exact B499651
  · exact B499655
  · exact B499659
  · exact B499663
  · exact B499667
  · exact B499671
  · exact B499675
  · exact B499679
  · exact B499683
  · exact B499687
  · exact B499691
  · exact B499695
  · exact B499699
  · exact B499703
  · exact B499707
  · exact B499711
  · exact B499715
  · exact B499719
  · exact B499723
  · exact B499727
  · exact B499731
  · exact B499735
  · exact B499739
  · exact B499743
  · exact B499747
  · exact B499751
  · exact B499755
  · exact B499759
  · exact B499763
  · exact B499767
  · exact B499771
  · exact B499775
  · exact B499779
  · exact B499783
  · exact B499787
  · exact B499791

theorem solution (m : ℕ) (hlo : 495792 ≤ m) (hhi : m ≤ 499792) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 123948 ≤ j := by omega
    have hj2 : j ≤ 124947 := by omega
    have hb : Blo 495792 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 124648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
