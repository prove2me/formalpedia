-- Prove2me | solution 1 for syracuse_descends_range_439778_443778
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:56.547638+00:00
-- url     : https://prove2.me/submissions/8f513113-829a-41a1-9542-5c2082de5a35

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


theorem B557057 : Blo 439778 557057 := bbase (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) (by norm_num)
theorem B557113 : Blo 439778 557113 := bbase (se 2 (by rfl) ⟨208917, by rfl⟩ : syracuseStep 557113 = 417835) (by norm_num)
theorem B2228309 : Blo 439778 2228309 := bbase (se 8 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 2228309 = 26113) (by norm_num)
theorem B557209 : Blo 439778 557209 := bbase (se 2 (by rfl) ⟨208953, by rfl⟩ : syracuseStep 557209 = 417907) (by norm_num)
theorem B1114357 : Blo 439778 1114357 := bbase (se 5 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 1114357 = 104471) (by norm_num)
theorem B1671461 : Blo 439778 1671461 := bbase (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) (by norm_num)
theorem B557381 : Blo 439778 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B1114469 : Blo 439778 1114469 := bbase (se 4 (by rfl) ⟨104481, by rfl⟩ : syracuseStep 1114469 = 208963) (by norm_num)
theorem B557437 : Blo 439778 557437 := bbase (se 3 (by rfl) ⟨104519, by rfl⟩ : syracuseStep 557437 = 209039) (by norm_num)
theorem B557533 : Blo 439778 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B1114661 : Blo 439778 1114661 := bbase (se 4 (by rfl) ⟨104499, by rfl⟩ : syracuseStep 1114661 = 208999) (by norm_num)
theorem B1671749 : Blo 439778 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B2130533 : Blo 439778 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B557705 : Blo 439778 557705 := bbase (se 2 (by rfl) ⟨209139, by rfl⟩ : syracuseStep 557705 = 418279) (by norm_num)
theorem B5374613 : Blo 439778 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B557761 : Blo 439778 557761 := bbase (se 2 (by rfl) ⟨209160, by rfl⟩ : syracuseStep 557761 = 418321) (by norm_num)
theorem B557857 : Blo 439778 557857 := bbase (se 2 (by rfl) ⟨209196, by rfl⟩ : syracuseStep 557857 = 418393) (by norm_num)
theorem B1115005 : Blo 439778 1115005 := bbase (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) (by norm_num)
theorem B852925 : Blo 439778 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B558029 : Blo 439778 558029 := bbase (se 3 (by rfl) ⟨104630, by rfl⟩ : syracuseStep 558029 = 209261) (by norm_num)
theorem B1115117 : Blo 439778 1115117 := bbase (se 3 (by rfl) ⟨209084, by rfl⟩ : syracuseStep 1115117 = 418169) (by norm_num)
theorem B558085 : Blo 439778 558085 := bbase (se 4 (by rfl) ⟨52320, by rfl⟩ : syracuseStep 558085 = 104641) (by norm_num)
theorem B2688085 : Blo 439778 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B558181 : Blo 439778 558181 := bbase (se 4 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 558181 = 104659) (by norm_num)
theorem B1115309 : Blo 439778 1115309 := bbase (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) (by norm_num)
theorem B2819285 : Blo 439778 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B754925 : Blo 439778 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B853237 : Blo 439778 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B558353 : Blo 439778 558353 := bbase (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) (by norm_num)
theorem B558409 : Blo 439778 558409 := bbase (se 2 (by rfl) ⟨209403, by rfl⟩ : syracuseStep 558409 = 418807) (by norm_num)
theorem B2229605 : Blo 439778 2229605 := bbase (se 4 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 2229605 = 418051) (by norm_num)
theorem B558505 : Blo 439778 558505 := bbase (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) (by norm_num)
theorem B1115653 : Blo 439778 1115653 := bbase (se 4 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 1115653 = 209185) (by norm_num)
theorem B558677 : Blo 439778 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B788077 : Blo 439778 788077 := bbase (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) (by norm_num)
theorem B1115765 : Blo 439778 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B558733 : Blo 439778 558733 := bbase (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) (by norm_num)
theorem B1672933 : Blo 439778 1672933 := bbase (se 4 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 1672933 = 313675) (by norm_num)
theorem B558829 : Blo 439778 558829 := bbase (se 3 (by rfl) ⟨104780, by rfl⟩ : syracuseStep 558829 = 209561) (by norm_num)
theorem B1410821 : Blo 439778 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B1115957 : Blo 439778 1115957 := bbase (se 5 (by rfl) ⟨52310, by rfl⟩ : syracuseStep 1115957 = 104621) (by norm_num)
theorem B1509205 : Blo 439778 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B7767893 : Blo 439778 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B1410949 : Blo 439778 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B559001 : Blo 439778 559001 := bbase (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) (by norm_num)
theorem B559057 : Blo 439778 559057 := bbase (se 2 (by rfl) ⟨209646, by rfl⟩ : syracuseStep 559057 = 419293) (by norm_num)
theorem B1345493 : Blo 439778 1345493 := bbase (se 7 (by rfl) ⟨15767, by rfl⟩ : syracuseStep 1345493 = 31535) (by norm_num)
theorem B1673237 : Blo 439778 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B559153 : Blo 439778 559153 := bbase (se 2 (by rfl) ⟨209682, by rfl⟩ : syracuseStep 559153 = 419365) (by norm_num)
theorem B1116301 : Blo 439778 1116301 := bbase (se 3 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 1116301 = 418613) (by norm_num)
theorem B9537749 : Blo 439778 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B559325 : Blo 439778 559325 := bbase (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) (by norm_num)
theorem B821485 : Blo 439778 821485 := bbase (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) (by norm_num)
theorem B1116413 : Blo 439778 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B559381 : Blo 439778 559381 := bbase (se 6 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 559381 = 26221) (by norm_num)
theorem B559477 : Blo 439778 559477 := bbase (se 5 (by rfl) ⟨26225, by rfl⟩ : syracuseStep 559477 = 52451) (by norm_num)
theorem B2263477 : Blo 439778 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1116605 : Blo 439778 1116605 := bbase (se 3 (by rfl) ⟨209363, by rfl⟩ : syracuseStep 1116605 = 418727) (by norm_num)
theorem B559649 : Blo 439778 559649 := bbase (se 2 (by rfl) ⟨209868, by rfl⟩ : syracuseStep 559649 = 419737) (by norm_num)
theorem B2263621 : Blo 439778 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B559705 : Blo 439778 559705 := bbase (se 2 (by rfl) ⟨209889, by rfl⟩ : syracuseStep 559705 = 419779) (by norm_num)
theorem B2230901 : Blo 439778 2230901 := bbase (se 5 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 2230901 = 209147) (by norm_num)
theorem B559801 : Blo 439778 559801 := bbase (se 2 (by rfl) ⟨209925, by rfl⟩ : syracuseStep 559801 = 419851) (by norm_num)
theorem B1116949 : Blo 439778 1116949 := bbase (se 6 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 1116949 = 52357) (by norm_num)
theorem B559973 : Blo 439778 559973 := bbase (se 4 (by rfl) ⟨52497, by rfl⟩ : syracuseStep 559973 = 104995) (by norm_num)
theorem B1117061 : Blo 439778 1117061 := bbase (se 4 (by rfl) ⟨104724, by rfl⟩ : syracuseStep 1117061 = 209449) (by norm_num)
theorem B560029 : Blo 439778 560029 := bbase (se 3 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 560029 = 210011) (by norm_num)
theorem B756677 : Blo 439778 756677 := bbase (se 4 (by rfl) ⟨70938, by rfl⟩ : syracuseStep 756677 = 141877) (by norm_num)
theorem B560125 : Blo 439778 560125 := bbase (se 3 (by rfl) ⟨105023, by rfl⟩ : syracuseStep 560125 = 210047) (by norm_num)
theorem B1117253 : Blo 439778 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B1510517 : Blo 439778 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B494761 : Blo 439778 494761 := bbase (se 2 (by rfl) ⟨185535, by rfl⟩ : syracuseStep 494761 = 371071) (by norm_num)
theorem B560297 : Blo 439778 560297 := bbase (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) (by norm_num)
theorem B494797 : Blo 439778 494797 := bbase (se 3 (by rfl) ⟨92774, by rfl⟩ : syracuseStep 494797 = 185549) (by norm_num)
theorem B560353 : Blo 439778 560353 := bbase (se 2 (by rfl) ⟨210132, by rfl⟩ : syracuseStep 560353 = 420265) (by norm_num)
theorem B494833 : Blo 439778 494833 := bbase (se 2 (by rfl) ⟨185562, by rfl⟩ : syracuseStep 494833 = 371125) (by norm_num)
theorem B494869 : Blo 439778 494869 := bbase (se 6 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 494869 = 23197) (by norm_num)
theorem B494905 : Blo 439778 494905 := bbase (se 2 (by rfl) ⟨185589, by rfl⟩ : syracuseStep 494905 = 371179) (by norm_num)
theorem B560449 : Blo 439778 560449 := bbase (se 2 (by rfl) ⟨210168, by rfl⟩ : syracuseStep 560449 = 420337) (by norm_num)
theorem B494941 : Blo 439778 494941 := bbase (se 3 (by rfl) ⟨92801, by rfl⟩ : syracuseStep 494941 = 185603) (by norm_num)
theorem B494977 : Blo 439778 494977 := bbase (se 2 (by rfl) ⟨185616, by rfl⟩ : syracuseStep 494977 = 371233) (by norm_num)
theorem B1117597 : Blo 439778 1117597 := bbase (se 3 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 1117597 = 419099) (by norm_num)
theorem B495013 : Blo 439778 495013 := bbase (se 4 (by rfl) ⟨46407, by rfl⟩ : syracuseStep 495013 = 92815) (by norm_num)
theorem B495049 : Blo 439778 495049 := bbase (se 2 (by rfl) ⟨185643, by rfl⟩ : syracuseStep 495049 = 371287) (by norm_num)
theorem B495085 : Blo 439778 495085 := bbase (se 3 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 495085 = 185657) (by norm_num)
theorem B560621 : Blo 439778 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B2395637 : Blo 439778 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1117709 : Blo 439778 1117709 := bbase (se 3 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 1117709 = 419141) (by norm_num)
theorem B495121 : Blo 439778 495121 := bbase (se 2 (by rfl) ⟨185670, by rfl⟩ : syracuseStep 495121 = 371341) (by norm_num)
theorem B560677 : Blo 439778 560677 := bbase (se 4 (by rfl) ⟨52563, by rfl⟩ : syracuseStep 560677 = 105127) (by norm_num)
theorem B495157 : Blo 439778 495157 := bbase (se 5 (by rfl) ⟨23210, by rfl⟩ : syracuseStep 495157 = 46421) (by norm_num)
theorem B495193 : Blo 439778 495193 := bbase (se 2 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 495193 = 371395) (by norm_num)
theorem B495229 : Blo 439778 495229 := bbase (se 3 (by rfl) ⟨92855, by rfl⟩ : syracuseStep 495229 = 185711) (by norm_num)
theorem B560773 : Blo 439778 560773 := bbase (se 4 (by rfl) ⟨52572, by rfl⟩ : syracuseStep 560773 = 105145) (by norm_num)
theorem B495265 : Blo 439778 495265 := bbase (se 2 (by rfl) ⟨185724, by rfl⟩ : syracuseStep 495265 = 371449) (by norm_num)
theorem B495301 : Blo 439778 495301 := bbase (se 4 (by rfl) ⟨46434, by rfl⟩ : syracuseStep 495301 = 92869) (by norm_num)
theorem B1117901 : Blo 439778 1117901 := bbase (se 3 (by rfl) ⟨209606, by rfl⟩ : syracuseStep 1117901 = 419213) (by norm_num)
theorem B495337 : Blo 439778 495337 := bbase (se 2 (by rfl) ⟨185751, by rfl⟩ : syracuseStep 495337 = 371503) (by norm_num)
theorem B495373 : Blo 439778 495373 := bbase (se 3 (by rfl) ⟨92882, by rfl⟩ : syracuseStep 495373 = 185765) (by norm_num)
theorem B495409 : Blo 439778 495409 := bbase (se 2 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 495409 = 371557) (by norm_num)
theorem B560945 : Blo 439778 560945 := bbase (se 2 (by rfl) ⟨210354, by rfl⟩ : syracuseStep 560945 = 420709) (by norm_num)
theorem B495445 : Blo 439778 495445 := bbase (se 9 (by rfl) ⟨1451, by rfl⟩ : syracuseStep 495445 = 2903) (by norm_num)
theorem B561001 : Blo 439778 561001 := bbase (se 2 (by rfl) ⟨210375, by rfl⟩ : syracuseStep 561001 = 420751) (by norm_num)
theorem B495481 : Blo 439778 495481 := bbase (se 2 (by rfl) ⟨185805, by rfl⟩ : syracuseStep 495481 = 371611) (by norm_num)
theorem B2232197 : Blo 439778 2232197 := bbase (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) (by norm_num)
theorem B495517 : Blo 439778 495517 := bbase (se 3 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 495517 = 185819) (by norm_num)
theorem B626621 : Blo 439778 626621 := bbase (se 3 (by rfl) ⟨117491, by rfl⟩ : syracuseStep 626621 = 234983) (by norm_num)
theorem B495553 : Blo 439778 495553 := bbase (se 2 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 495553 = 371665) (by norm_num)
theorem B561097 : Blo 439778 561097 := bbase (se 2 (by rfl) ⟨210411, by rfl⟩ : syracuseStep 561097 = 420823) (by norm_num)
theorem B495589 : Blo 439778 495589 := bbase (se 4 (by rfl) ⟨46461, by rfl⟩ : syracuseStep 495589 = 92923) (by norm_num)
theorem B495625 : Blo 439778 495625 := bbase (se 2 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 495625 = 371719) (by norm_num)
theorem B1118245 : Blo 439778 1118245 := bbase (se 4 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 1118245 = 209671) (by norm_num)
theorem B495661 : Blo 439778 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B495697 : Blo 439778 495697 := bbase (se 2 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 495697 = 371773) (by norm_num)
theorem B1675349 : Blo 439778 1675349 := bbase (se 8 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 1675349 = 19633) (by norm_num)
theorem B495733 : Blo 439778 495733 := bbase (se 5 (by rfl) ⟨23237, by rfl⟩ : syracuseStep 495733 = 46475) (by norm_num)
theorem B561269 : Blo 439778 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B1118357 : Blo 439778 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B495769 : Blo 439778 495769 := bbase (se 2 (by rfl) ⟨185913, by rfl⟩ : syracuseStep 495769 = 371827) (by norm_num)
theorem B561325 : Blo 439778 561325 := bbase (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) (by norm_num)
theorem B495805 : Blo 439778 495805 := bbase (se 3 (by rfl) ⟨92963, by rfl⟩ : syracuseStep 495805 = 185927) (by norm_num)
theorem B659669 : Blo 439778 659669 := bbase (se 7 (by rfl) ⟨7730, by rfl⟩ : syracuseStep 659669 = 15461) (by norm_num)
theorem B495841 : Blo 439778 495841 := bbase (se 2 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 495841 = 371881) (by norm_num)
theorem B659693 : Blo 439778 659693 := bbase (se 3 (by rfl) ⟨123692, by rfl⟩ : syracuseStep 659693 = 247385) (by norm_num)
theorem B659717 : Blo 439778 659717 := bbase (se 4 (by rfl) ⟨61848, by rfl⟩ : syracuseStep 659717 = 123697) (by norm_num)
theorem B495877 : Blo 439778 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B561421 : Blo 439778 561421 := bbase (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) (by norm_num)
theorem B2265365 : Blo 439778 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B659741 : Blo 439778 659741 := bbase (se 3 (by rfl) ⟨123701, by rfl⟩ : syracuseStep 659741 = 247403) (by norm_num)
theorem B495913 : Blo 439778 495913 := bbase (se 2 (by rfl) ⟨185967, by rfl⟩ : syracuseStep 495913 = 371935) (by norm_num)
theorem B659765 : Blo 439778 659765 := bbase (se 5 (by rfl) ⟨30926, by rfl⟩ : syracuseStep 659765 = 61853) (by norm_num)
theorem B659789 : Blo 439778 659789 := bbase (se 3 (by rfl) ⟨123710, by rfl⟩ : syracuseStep 659789 = 247421) (by norm_num)
theorem B495949 : Blo 439778 495949 := bbase (se 3 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 495949 = 185981) (by norm_num)
theorem B4297045 : Blo 439778 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B1118549 : Blo 439778 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B659813 : Blo 439778 659813 := bbase (se 4 (by rfl) ⟨61857, by rfl⟩ : syracuseStep 659813 = 123715) (by norm_num)
theorem B495985 : Blo 439778 495985 := bbase (se 2 (by rfl) ⟨185994, by rfl⟩ : syracuseStep 495985 = 371989) (by norm_num)
theorem B1675637 : Blo 439778 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B659837 : Blo 439778 659837 := bbase (se 3 (by rfl) ⟨123719, by rfl⟩ : syracuseStep 659837 = 247439) (by norm_num)
theorem B659861 : Blo 439778 659861 := bbase (se 6 (by rfl) ⟨15465, by rfl⟩ : syracuseStep 659861 = 30931) (by norm_num)
theorem B496021 : Blo 439778 496021 := bbase (se 6 (by rfl) ⟨11625, by rfl⟩ : syracuseStep 496021 = 23251) (by norm_num)
theorem B659885 : Blo 439778 659885 := bbase (se 3 (by rfl) ⟨123728, by rfl⟩ : syracuseStep 659885 = 247457) (by norm_num)
theorem B496057 : Blo 439778 496057 := bbase (se 2 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 496057 = 372043) (by norm_num)
theorem B561593 : Blo 439778 561593 := bbase (se 2 (by rfl) ⟨210597, by rfl⟩ : syracuseStep 561593 = 421195) (by norm_num)
theorem B659909 : Blo 439778 659909 := bbase (se 4 (by rfl) ⟨61866, by rfl⟩ : syracuseStep 659909 = 123733) (by norm_num)
theorem B659933 : Blo 439778 659933 := bbase (se 3 (by rfl) ⟨123737, by rfl⟩ : syracuseStep 659933 = 247475) (by norm_num)
theorem B496093 : Blo 439778 496093 := bbase (se 3 (by rfl) ⟨93017, by rfl⟩ : syracuseStep 496093 = 186035) (by norm_num)
theorem B561649 : Blo 439778 561649 := bbase (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) (by norm_num)
theorem B659957 : Blo 439778 659957 := bbase (se 5 (by rfl) ⟨30935, by rfl⟩ : syracuseStep 659957 = 61871) (by norm_num)
theorem B496129 : Blo 439778 496129 := bbase (se 2 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 496129 = 372097) (by norm_num)
theorem B659981 : Blo 439778 659981 := bbase (se 3 (by rfl) ⟨123746, by rfl⟩ : syracuseStep 659981 = 247493) (by norm_num)
theorem B660005 : Blo 439778 660005 := bbase (se 4 (by rfl) ⟨61875, by rfl⟩ : syracuseStep 660005 = 123751) (by norm_num)
theorem B496165 : Blo 439778 496165 := bbase (se 4 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 496165 = 93031) (by norm_num)
theorem B660029 : Blo 439778 660029 := bbase (se 3 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 660029 = 247511) (by norm_num)
theorem B496201 : Blo 439778 496201 := bbase (se 2 (by rfl) ⟨186075, by rfl⟩ : syracuseStep 496201 = 372151) (by norm_num)
theorem B528977 : Blo 439778 528977 := bbase (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) (by norm_num)
theorem B660053 : Blo 439778 660053 := bbase (se 8 (by rfl) ⟨3867, by rfl⟩ : syracuseStep 660053 = 7735) (by norm_num)
theorem B660077 : Blo 439778 660077 := bbase (se 3 (by rfl) ⟨123764, by rfl⟩ : syracuseStep 660077 = 247529) (by norm_num)
theorem B496237 : Blo 439778 496237 := bbase (se 3 (by rfl) ⟨93044, by rfl⟩ : syracuseStep 496237 = 186089) (by norm_num)
theorem B660101 : Blo 439778 660101 := bbase (se 4 (by rfl) ⟨61884, by rfl⟩ : syracuseStep 660101 = 123769) (by norm_num)
theorem B496273 : Blo 439778 496273 := bbase (se 2 (by rfl) ⟨186102, by rfl⟩ : syracuseStep 496273 = 372205) (by norm_num)
theorem B660125 : Blo 439778 660125 := bbase (se 3 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 660125 = 247547) (by norm_num)
theorem B627373 : Blo 439778 627373 := bbase (se 3 (by rfl) ⟨117632, by rfl⟩ : syracuseStep 627373 = 235265) (by norm_num)
theorem B1118893 : Blo 439778 1118893 := bbase (se 3 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 1118893 = 419585) (by norm_num)
theorem B660149 : Blo 439778 660149 := bbase (se 5 (by rfl) ⟨30944, by rfl⟩ : syracuseStep 660149 = 61889) (by norm_num)
theorem B496309 : Blo 439778 496309 := bbase (se 5 (by rfl) ⟨23264, by rfl⟩ : syracuseStep 496309 = 46529) (by norm_num)
theorem B660173 : Blo 439778 660173 := bbase (se 3 (by rfl) ⟨123782, by rfl⟩ : syracuseStep 660173 = 247565) (by norm_num)
theorem B1413845 : Blo 439778 1413845 := bbase (se 7 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 1413845 = 33137) (by norm_num)
theorem B496345 : Blo 439778 496345 := bbase (se 2 (by rfl) ⟨186129, by rfl⟩ : syracuseStep 496345 = 372259) (by norm_num)
theorem B660197 : Blo 439778 660197 := bbase (se 4 (by rfl) ⟨61893, by rfl⟩ : syracuseStep 660197 = 123787) (by norm_num)
theorem B660221 : Blo 439778 660221 := bbase (se 3 (by rfl) ⟨123791, by rfl⟩ : syracuseStep 660221 = 247583) (by norm_num)
theorem B496381 : Blo 439778 496381 := bbase (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) (by norm_num)
theorem B660245 : Blo 439778 660245 := bbase (se 6 (by rfl) ⟨15474, by rfl⟩ : syracuseStep 660245 = 30949) (by norm_num)
theorem B1119005 : Blo 439778 1119005 := bbase (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) (by norm_num)
theorem B496417 : Blo 439778 496417 := bbase (se 2 (by rfl) ⟨186156, by rfl⟩ : syracuseStep 496417 = 372313) (by norm_num)
theorem B660269 : Blo 439778 660269 := bbase (se 3 (by rfl) ⟨123800, by rfl⟩ : syracuseStep 660269 = 247601) (by norm_num)
theorem B660293 : Blo 439778 660293 := bbase (se 4 (by rfl) ⟨61902, by rfl⟩ : syracuseStep 660293 = 123805) (by norm_num)
theorem B496453 : Blo 439778 496453 := bbase (se 4 (by rfl) ⟨46542, by rfl⟩ : syracuseStep 496453 = 93085) (by norm_num)
theorem B660317 : Blo 439778 660317 := bbase (se 3 (by rfl) ⟨123809, by rfl⟩ : syracuseStep 660317 = 247619) (by norm_num)
theorem B496489 : Blo 439778 496489 := bbase (se 2 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 496489 = 372367) (by norm_num)
theorem B660341 : Blo 439778 660341 := bbase (se 5 (by rfl) ⟨30953, by rfl⟩ : syracuseStep 660341 = 61907) (by norm_num)
theorem B660365 : Blo 439778 660365 := bbase (se 3 (by rfl) ⟨123818, by rfl⟩ : syracuseStep 660365 = 247637) (by norm_num)
theorem B496525 : Blo 439778 496525 := bbase (se 3 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 496525 = 186197) (by norm_num)
theorem B660389 : Blo 439778 660389 := bbase (se 4 (by rfl) ⟨61911, by rfl⟩ : syracuseStep 660389 = 123823) (by norm_num)
theorem B496561 : Blo 439778 496561 := bbase (se 2 (by rfl) ⟨186210, by rfl⟩ : syracuseStep 496561 = 372421) (by norm_num)
theorem B660413 : Blo 439778 660413 := bbase (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) (by norm_num)
theorem B660437 : Blo 439778 660437 := bbase (se 7 (by rfl) ⟨7739, by rfl⟩ : syracuseStep 660437 = 15479) (by norm_num)
theorem B496597 : Blo 439778 496597 := bbase (se 7 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 496597 = 11639) (by norm_num)
theorem B1119197 : Blo 439778 1119197 := bbase (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) (by norm_num)
theorem B660461 : Blo 439778 660461 := bbase (se 3 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 660461 = 247673) (by norm_num)
theorem B496633 : Blo 439778 496633 := bbase (se 2 (by rfl) ⟨186237, by rfl⟩ : syracuseStep 496633 = 372475) (by norm_num)
theorem B660485 : Blo 439778 660485 := bbase (se 4 (by rfl) ⟨61920, by rfl⟩ : syracuseStep 660485 = 123841) (by norm_num)
theorem B660509 : Blo 439778 660509 := bbase (se 3 (by rfl) ⟨123845, by rfl⟩ : syracuseStep 660509 = 247691) (by norm_num)
theorem B496669 : Blo 439778 496669 := bbase (se 3 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 496669 = 186251) (by norm_num)
theorem B660533 : Blo 439778 660533 := bbase (se 5 (by rfl) ⟨30962, by rfl⟩ : syracuseStep 660533 = 61925) (by norm_num)
theorem B496705 : Blo 439778 496705 := bbase (se 2 (by rfl) ⟨186264, by rfl⟩ : syracuseStep 496705 = 372529) (by norm_num)
theorem B660557 : Blo 439778 660557 := bbase (se 3 (by rfl) ⟨123854, by rfl⟩ : syracuseStep 660557 = 247709) (by norm_num)
theorem B660581 : Blo 439778 660581 := bbase (se 4 (by rfl) ⟨61929, by rfl⟩ : syracuseStep 660581 = 123859) (by norm_num)
theorem B496741 : Blo 439778 496741 := bbase (se 4 (by rfl) ⟨46569, by rfl⟩ : syracuseStep 496741 = 93139) (by norm_num)
theorem B660605 : Blo 439778 660605 := bbase (se 3 (by rfl) ⟨123863, by rfl⟩ : syracuseStep 660605 = 247727) (by norm_num)
theorem B496777 : Blo 439778 496777 := bbase (se 2 (by rfl) ⟨186291, by rfl⟩ : syracuseStep 496777 = 372583) (by norm_num)
theorem B660629 : Blo 439778 660629 := bbase (se 6 (by rfl) ⟨15483, by rfl⟩ : syracuseStep 660629 = 30967) (by norm_num)
theorem B2233493 : Blo 439778 2233493 := bbase (se 6 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 2233493 = 104695) (by norm_num)
theorem B660653 : Blo 439778 660653 := bbase (se 3 (by rfl) ⟨123872, by rfl⟩ : syracuseStep 660653 = 247745) (by norm_num)
theorem B496813 : Blo 439778 496813 := bbase (se 3 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 496813 = 186305) (by norm_num)
theorem B1152173 : Blo 439778 1152173 := bbase (se 3 (by rfl) ⟨216032, by rfl⟩ : syracuseStep 1152173 = 432065) (by norm_num)
theorem B660677 : Blo 439778 660677 := bbase (se 4 (by rfl) ⟨61938, by rfl⟩ : syracuseStep 660677 = 123877) (by norm_num)
theorem B496849 : Blo 439778 496849 := bbase (se 2 (by rfl) ⟨186318, by rfl⟩ : syracuseStep 496849 = 372637) (by norm_num)
theorem B660701 : Blo 439778 660701 := bbase (se 3 (by rfl) ⟨123881, by rfl⟩ : syracuseStep 660701 = 247763) (by norm_num)
theorem B660725 : Blo 439778 660725 := bbase (se 5 (by rfl) ⟨30971, by rfl⟩ : syracuseStep 660725 = 61943) (by norm_num)
theorem B496885 : Blo 439778 496885 := bbase (se 5 (by rfl) ⟨23291, by rfl⟩ : syracuseStep 496885 = 46583) (by norm_num)
theorem B660749 : Blo 439778 660749 := bbase (se 3 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 660749 = 247781) (by norm_num)
theorem B496921 : Blo 439778 496921 := bbase (se 2 (by rfl) ⟨186345, by rfl⟩ : syracuseStep 496921 = 372691) (by norm_num)
theorem B660773 : Blo 439778 660773 := bbase (se 4 (by rfl) ⟨61947, by rfl⟩ : syracuseStep 660773 = 123895) (by norm_num)
theorem B955685 : Blo 439778 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B1119541 : Blo 439778 1119541 := bbase (se 5 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 1119541 = 104957) (by norm_num)
theorem B660797 : Blo 439778 660797 := bbase (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) (by norm_num)
theorem B496957 : Blo 439778 496957 := bbase (se 3 (by rfl) ⟨93179, by rfl⟩ : syracuseStep 496957 = 186359) (by norm_num)
theorem B660821 : Blo 439778 660821 := bbase (se 14 (by rfl) ⟨60, by rfl⟩ : syracuseStep 660821 = 121) (by norm_num)
theorem B496993 : Blo 439778 496993 := bbase (se 2 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 496993 = 372745) (by norm_num)
theorem B660845 : Blo 439778 660845 := bbase (se 3 (by rfl) ⟨123908, by rfl⟩ : syracuseStep 660845 = 247817) (by norm_num)
theorem B660869 : Blo 439778 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B497029 : Blo 439778 497029 := bbase (se 4 (by rfl) ⟨46596, by rfl⟩ : syracuseStep 497029 = 93193) (by norm_num)
theorem B660893 : Blo 439778 660893 := bbase (se 3 (by rfl) ⟨123917, by rfl⟩ : syracuseStep 660893 = 247835) (by norm_num)
theorem B1119653 : Blo 439778 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B497065 : Blo 439778 497065 := bbase (se 2 (by rfl) ⟨186399, by rfl⟩ : syracuseStep 497065 = 372799) (by norm_num)
theorem B660917 : Blo 439778 660917 := bbase (se 5 (by rfl) ⟨30980, by rfl⟩ : syracuseStep 660917 = 61961) (by norm_num)
theorem B628165 : Blo 439778 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B660941 : Blo 439778 660941 := bbase (se 3 (by rfl) ⟨123926, by rfl⟩ : syracuseStep 660941 = 247853) (by norm_num)
theorem B497101 : Blo 439778 497101 := bbase (se 3 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 497101 = 186413) (by norm_num)
theorem B660965 : Blo 439778 660965 := bbase (se 4 (by rfl) ⟨61965, by rfl⟩ : syracuseStep 660965 = 123931) (by norm_num)
theorem B497137 : Blo 439778 497137 := bbase (se 2 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 497137 = 372853) (by norm_num)
theorem B595445 : Blo 439778 595445 := bbase (se 5 (by rfl) ⟨27911, by rfl⟩ : syracuseStep 595445 = 55823) (by norm_num)
theorem B660989 : Blo 439778 660989 := bbase (se 3 (by rfl) ⟨123935, by rfl⟩ : syracuseStep 660989 = 247871) (by norm_num)
theorem B661013 : Blo 439778 661013 := bbase (se 6 (by rfl) ⟨15492, by rfl⟩ : syracuseStep 661013 = 30985) (by norm_num)
theorem B1676821 : Blo 439778 1676821 := bbase (se 6 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 1676821 = 78601) (by norm_num)
theorem B497173 : Blo 439778 497173 := bbase (se 6 (by rfl) ⟨11652, by rfl⟩ : syracuseStep 497173 = 23305) (by norm_num)
theorem B661037 : Blo 439778 661037 := bbase (se 3 (by rfl) ⟨123944, by rfl⟩ : syracuseStep 661037 = 247889) (by norm_num)
theorem B497209 : Blo 439778 497209 := bbase (se 2 (by rfl) ⟨186453, by rfl⟩ : syracuseStep 497209 = 372907) (by norm_num)
theorem B661061 : Blo 439778 661061 := bbase (se 4 (by rfl) ⟨61974, by rfl⟩ : syracuseStep 661061 = 123949) (by norm_num)
theorem B3348053 : Blo 439778 3348053 := bbase (se 8 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 3348053 = 39235) (by norm_num)
theorem B661085 : Blo 439778 661085 := bbase (se 3 (by rfl) ⟨123953, by rfl⟩ : syracuseStep 661085 = 247907) (by norm_num)
theorem B497245 : Blo 439778 497245 := bbase (se 3 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 497245 = 186467) (by norm_num)
theorem B1119845 : Blo 439778 1119845 := bbase (se 4 (by rfl) ⟨104985, by rfl⟩ : syracuseStep 1119845 = 209971) (by norm_num)
theorem B661109 : Blo 439778 661109 := bbase (se 5 (by rfl) ⟨30989, by rfl⟩ : syracuseStep 661109 = 61979) (by norm_num)
theorem B497281 : Blo 439778 497281 := bbase (se 2 (by rfl) ⟨186480, by rfl⟩ : syracuseStep 497281 = 372961) (by norm_num)
theorem B661133 : Blo 439778 661133 := bbase (se 3 (by rfl) ⟨123962, by rfl⟩ : syracuseStep 661133 = 247925) (by norm_num)
theorem B661157 : Blo 439778 661157 := bbase (se 4 (by rfl) ⟨61983, by rfl⟩ : syracuseStep 661157 = 123967) (by norm_num)
theorem B497317 : Blo 439778 497317 := bbase (se 4 (by rfl) ⟨46623, by rfl⟩ : syracuseStep 497317 = 93247) (by norm_num)
theorem B661181 : Blo 439778 661181 := bbase (se 3 (by rfl) ⟨123971, by rfl⟩ : syracuseStep 661181 = 247943) (by norm_num)
theorem B497353 : Blo 439778 497353 := bbase (se 2 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 497353 = 373015) (by norm_num)
theorem B661205 : Blo 439778 661205 := bbase (se 7 (by rfl) ⟨7748, by rfl⟩ : syracuseStep 661205 = 15497) (by norm_num)
theorem B661229 : Blo 439778 661229 := bbase (se 3 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 661229 = 247961) (by norm_num)
theorem B497389 : Blo 439778 497389 := bbase (se 3 (by rfl) ⟨93260, by rfl⟩ : syracuseStep 497389 = 186521) (by norm_num)
theorem B530173 : Blo 439778 530173 := bbase (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) (by norm_num)
theorem B661253 : Blo 439778 661253 := bbase (se 4 (by rfl) ⟨61992, by rfl⟩ : syracuseStep 661253 = 123985) (by norm_num)
theorem B497425 : Blo 439778 497425 := bbase (se 2 (by rfl) ⟨186534, by rfl⟩ : syracuseStep 497425 = 373069) (by norm_num)
theorem B628501 : Blo 439778 628501 := bbase (se 6 (by rfl) ⟨14730, by rfl⟩ : syracuseStep 628501 = 29461) (by norm_num)
theorem B661277 : Blo 439778 661277 := bbase (se 3 (by rfl) ⟨123989, by rfl⟩ : syracuseStep 661277 = 247979) (by norm_num)
theorem B661301 : Blo 439778 661301 := bbase (se 5 (by rfl) ⟨30998, by rfl⟩ : syracuseStep 661301 = 61997) (by norm_num)
theorem B3020597 : Blo 439778 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B497461 : Blo 439778 497461 := bbase (se 5 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 497461 = 46637) (by norm_num)
theorem B530245 : Blo 439778 530245 := bbase (se 4 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 530245 = 99421) (by norm_num)
theorem B1677125 : Blo 439778 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B661325 : Blo 439778 661325 := bbase (se 3 (by rfl) ⟨123998, by rfl⟩ : syracuseStep 661325 = 247997) (by norm_num)
theorem B497497 : Blo 439778 497497 := bbase (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) (by norm_num)
theorem B661349 : Blo 439778 661349 := bbase (se 4 (by rfl) ⟨62001, by rfl⟩ : syracuseStep 661349 = 124003) (by norm_num)
theorem B661373 : Blo 439778 661373 := bbase (se 3 (by rfl) ⟨124007, by rfl⟩ : syracuseStep 661373 = 248015) (by norm_num)
theorem B497533 : Blo 439778 497533 := bbase (se 3 (by rfl) ⟨93287, by rfl⟩ : syracuseStep 497533 = 186575) (by norm_num)
theorem B661397 : Blo 439778 661397 := bbase (se 6 (by rfl) ⟨15501, by rfl⟩ : syracuseStep 661397 = 31003) (by norm_num)
theorem B497569 : Blo 439778 497569 := bbase (se 2 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 497569 = 373177) (by norm_num)
theorem B661421 : Blo 439778 661421 := bbase (se 3 (by rfl) ⟨124016, by rfl⟩ : syracuseStep 661421 = 248033) (by norm_num)
theorem B1120189 : Blo 439778 1120189 := bbase (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) (by norm_num)
theorem B661445 : Blo 439778 661445 := bbase (se 4 (by rfl) ⟨62010, by rfl⟩ : syracuseStep 661445 = 124021) (by norm_num)
theorem B497605 : Blo 439778 497605 := bbase (se 4 (by rfl) ⟨46650, by rfl⟩ : syracuseStep 497605 = 93301) (by norm_num)
theorem B661469 : Blo 439778 661469 := bbase (se 3 (by rfl) ⟨124025, by rfl⟩ : syracuseStep 661469 = 248051) (by norm_num)
theorem B497641 : Blo 439778 497641 := bbase (se 2 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 497641 = 373231) (by norm_num)
theorem B628717 : Blo 439778 628717 := bbase (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) (by norm_num)
theorem B661493 : Blo 439778 661493 := bbase (se 5 (by rfl) ⟨31007, by rfl⟩ : syracuseStep 661493 = 62015) (by norm_num)
theorem B661517 : Blo 439778 661517 := bbase (se 3 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 661517 = 248069) (by norm_num)
theorem B497677 : Blo 439778 497677 := bbase (se 3 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 497677 = 186629) (by norm_num)
theorem B661541 : Blo 439778 661541 := bbase (se 4 (by rfl) ⟨62019, by rfl⟩ : syracuseStep 661541 = 124039) (by norm_num)
theorem B1120301 : Blo 439778 1120301 := bbase (se 3 (by rfl) ⟨210056, by rfl⟩ : syracuseStep 1120301 = 420113) (by norm_num)
theorem B497713 : Blo 439778 497713 := bbase (se 2 (by rfl) ⟨186642, by rfl⟩ : syracuseStep 497713 = 373285) (by norm_num)
theorem B661565 : Blo 439778 661565 := bbase (se 3 (by rfl) ⟨124043, by rfl⟩ : syracuseStep 661565 = 248087) (by norm_num)
theorem B661589 : Blo 439778 661589 := bbase (se 8 (by rfl) ⟨3876, by rfl⟩ : syracuseStep 661589 = 7753) (by norm_num)
theorem B497749 : Blo 439778 497749 := bbase (se 8 (by rfl) ⟨2916, by rfl⟩ : syracuseStep 497749 = 5833) (by norm_num)
theorem B661613 : Blo 439778 661613 := bbase (se 3 (by rfl) ⟨124052, by rfl⟩ : syracuseStep 661613 = 248105) (by norm_num)
theorem B497785 : Blo 439778 497785 := bbase (se 2 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 497785 = 373339) (by norm_num)
theorem B661637 : Blo 439778 661637 := bbase (se 4 (by rfl) ⟨62028, by rfl⟩ : syracuseStep 661637 = 124057) (by norm_num)
theorem B661661 : Blo 439778 661661 := bbase (se 3 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 661661 = 248123) (by norm_num)
theorem B497821 : Blo 439778 497821 := bbase (se 3 (by rfl) ⟨93341, by rfl⟩ : syracuseStep 497821 = 186683) (by norm_num)
theorem B661685 : Blo 439778 661685 := bbase (se 5 (by rfl) ⟨31016, by rfl⟩ : syracuseStep 661685 = 62033) (by norm_num)
theorem B497857 : Blo 439778 497857 := bbase (se 2 (by rfl) ⟨186696, by rfl⟩ : syracuseStep 497857 = 373393) (by norm_num)
theorem B1022149 : Blo 439778 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B661709 : Blo 439778 661709 := bbase (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) (by norm_num)
theorem B661733 : Blo 439778 661733 := bbase (se 4 (by rfl) ⟨62037, by rfl⟩ : syracuseStep 661733 = 124075) (by norm_num)
theorem B497893 : Blo 439778 497893 := bbase (se 4 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 497893 = 93355) (by norm_num)
theorem B1120493 : Blo 439778 1120493 := bbase (se 3 (by rfl) ⟨210092, by rfl⟩ : syracuseStep 1120493 = 420185) (by norm_num)
theorem B661757 : Blo 439778 661757 := bbase (se 3 (by rfl) ⟨124079, by rfl⟩ : syracuseStep 661757 = 248159) (by norm_num)
theorem B497929 : Blo 439778 497929 := bbase (se 2 (by rfl) ⟨186723, by rfl⟩ : syracuseStep 497929 = 373447) (by norm_num)
theorem B661781 : Blo 439778 661781 := bbase (se 6 (by rfl) ⟨15510, by rfl⟩ : syracuseStep 661781 = 31021) (by norm_num)
theorem B661805 : Blo 439778 661805 := bbase (se 3 (by rfl) ⟨124088, by rfl⟩ : syracuseStep 661805 = 248177) (by norm_num)
theorem B497965 : Blo 439778 497965 := bbase (se 3 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 497965 = 186737) (by norm_num)
theorem B661829 : Blo 439778 661829 := bbase (se 4 (by rfl) ⟨62046, by rfl⟩ : syracuseStep 661829 = 124093) (by norm_num)
theorem B498001 : Blo 439778 498001 := bbase (se 2 (by rfl) ⟨186750, by rfl⟩ : syracuseStep 498001 = 373501) (by norm_num)
theorem B661853 : Blo 439778 661853 := bbase (se 3 (by rfl) ⟨124097, by rfl⟩ : syracuseStep 661853 = 248195) (by norm_num)
theorem B629093 : Blo 439778 629093 := bbase (se 4 (by rfl) ⟨58977, by rfl⟩ : syracuseStep 629093 = 117955) (by norm_num)
theorem B989549 : Blo 439778 989549 := bbase (se 3 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 989549 = 371081) (by norm_num)
theorem B661877 : Blo 439778 661877 := bbase (se 5 (by rfl) ⟨31025, by rfl⟩ : syracuseStep 661877 = 62051) (by norm_num)
theorem B498037 : Blo 439778 498037 := bbase (se 5 (by rfl) ⟨23345, by rfl⟩ : syracuseStep 498037 = 46691) (by norm_num)
theorem B661901 : Blo 439778 661901 := bbase (se 3 (by rfl) ⟨124106, by rfl⟩ : syracuseStep 661901 = 248213) (by norm_num)
theorem B498073 : Blo 439778 498073 := bbase (se 2 (by rfl) ⟨186777, by rfl⟩ : syracuseStep 498073 = 373555) (by norm_num)
theorem B661925 : Blo 439778 661925 := bbase (se 4 (by rfl) ⟨62055, by rfl⟩ : syracuseStep 661925 = 124111) (by norm_num)
theorem B2234789 : Blo 439778 2234789 := bbase (se 4 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 2234789 = 419023) (by norm_num)
theorem B1022381 : Blo 439778 1022381 := bbase (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) (by norm_num)
theorem B989621 : Blo 439778 989621 := bbase (se 5 (by rfl) ⟨46388, by rfl⟩ : syracuseStep 989621 = 92777) (by norm_num)
theorem B661949 : Blo 439778 661949 := bbase (se 3 (by rfl) ⟨124115, by rfl⟩ : syracuseStep 661949 = 248231) (by norm_num)
theorem B498109 : Blo 439778 498109 := bbase (se 3 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 498109 = 186791) (by norm_num)
theorem B661973 : Blo 439778 661973 := bbase (se 7 (by rfl) ⟨7757, by rfl⟩ : syracuseStep 661973 = 15515) (by norm_num)
theorem B498145 : Blo 439778 498145 := bbase (se 2 (by rfl) ⟨186804, by rfl⟩ : syracuseStep 498145 = 373609) (by norm_num)
theorem B661997 : Blo 439778 661997 := bbase (se 3 (by rfl) ⟨124124, by rfl⟩ : syracuseStep 661997 = 248249) (by norm_num)
theorem B989693 : Blo 439778 989693 := bbase (se 3 (by rfl) ⟨185567, by rfl⟩ : syracuseStep 989693 = 371135) (by norm_num)
theorem B662021 : Blo 439778 662021 := bbase (se 4 (by rfl) ⟨62064, by rfl⟩ : syracuseStep 662021 = 124129) (by norm_num)
theorem B498181 : Blo 439778 498181 := bbase (se 4 (by rfl) ⟨46704, by rfl⟩ : syracuseStep 498181 = 93409) (by norm_num)
theorem B662045 : Blo 439778 662045 := bbase (se 3 (by rfl) ⟨124133, by rfl⟩ : syracuseStep 662045 = 248267) (by norm_num)
theorem B498217 : Blo 439778 498217 := bbase (se 2 (by rfl) ⟨186831, by rfl⟩ : syracuseStep 498217 = 373663) (by norm_num)
theorem B662069 : Blo 439778 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B989765 : Blo 439778 989765 := bbase (se 4 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 989765 = 185581) (by norm_num)
theorem B1120837 : Blo 439778 1120837 := bbase (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) (by norm_num)
theorem B662093 : Blo 439778 662093 := bbase (se 3 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 662093 = 248285) (by norm_num)
theorem B498253 : Blo 439778 498253 := bbase (se 3 (by rfl) ⟨93422, by rfl⟩ : syracuseStep 498253 = 186845) (by norm_num)
theorem B662117 : Blo 439778 662117 := bbase (se 4 (by rfl) ⟨62073, by rfl⟩ : syracuseStep 662117 = 124147) (by norm_num)
theorem B498289 : Blo 439778 498289 := bbase (se 2 (by rfl) ⟨186858, by rfl⟩ : syracuseStep 498289 = 373717) (by norm_num)
theorem B662141 : Blo 439778 662141 := bbase (se 3 (by rfl) ⟨124151, by rfl⟩ : syracuseStep 662141 = 248303) (by norm_num)
theorem B989837 : Blo 439778 989837 := bbase (se 3 (by rfl) ⟨185594, by rfl⟩ : syracuseStep 989837 = 371189) (by norm_num)
theorem B662165 : Blo 439778 662165 := bbase (se 6 (by rfl) ⟨15519, by rfl⟩ : syracuseStep 662165 = 31039) (by norm_num)
theorem B498325 : Blo 439778 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B662189 : Blo 439778 662189 := bbase (se 3 (by rfl) ⟨124160, by rfl⟩ : syracuseStep 662189 = 248321) (by norm_num)
theorem B1120949 : Blo 439778 1120949 := bbase (se 5 (by rfl) ⟨52544, by rfl⟩ : syracuseStep 1120949 = 105089) (by norm_num)
theorem B498361 : Blo 439778 498361 := bbase (se 2 (by rfl) ⟨186885, by rfl⟩ : syracuseStep 498361 = 373771) (by norm_num)
theorem B662213 : Blo 439778 662213 := bbase (se 4 (by rfl) ⟨62082, by rfl⟩ : syracuseStep 662213 = 124165) (by norm_num)
theorem B989909 : Blo 439778 989909 := bbase (se 7 (by rfl) ⟨11600, by rfl⟩ : syracuseStep 989909 = 23201) (by norm_num)
theorem B662237 : Blo 439778 662237 := bbase (se 3 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 662237 = 248339) (by norm_num)
theorem B498397 : Blo 439778 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B662261 : Blo 439778 662261 := bbase (se 5 (by rfl) ⟨31043, by rfl⟩ : syracuseStep 662261 = 62087) (by norm_num)
theorem B498433 : Blo 439778 498433 := bbase (se 2 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 498433 = 373825) (by norm_num)
theorem B662285 : Blo 439778 662285 := bbase (se 3 (by rfl) ⟨124178, by rfl⟩ : syracuseStep 662285 = 248357) (by norm_num)
theorem B989981 : Blo 439778 989981 := bbase (se 3 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 989981 = 371243) (by norm_num)
theorem B662309 : Blo 439778 662309 := bbase (se 4 (by rfl) ⟨62091, by rfl⟩ : syracuseStep 662309 = 124183) (by norm_num)
theorem B498469 : Blo 439778 498469 := bbase (se 4 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 498469 = 93463) (by norm_num)
theorem B531245 : Blo 439778 531245 := bbase (se 3 (by rfl) ⟨99608, by rfl⟩ : syracuseStep 531245 = 199217) (by norm_num)
theorem B662333 : Blo 439778 662333 := bbase (se 3 (by rfl) ⟨124187, by rfl⟩ : syracuseStep 662333 = 248375) (by norm_num)
theorem B498505 : Blo 439778 498505 := bbase (se 2 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 498505 = 373879) (by norm_num)
theorem B662357 : Blo 439778 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B990053 : Blo 439778 990053 := bbase (se 4 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 990053 = 185635) (by norm_num)
theorem B1416037 : Blo 439778 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B662381 : Blo 439778 662381 := bbase (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) (by norm_num)
theorem B498541 : Blo 439778 498541 := bbase (se 3 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 498541 = 186953) (by norm_num)
theorem B1121141 : Blo 439778 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B662405 : Blo 439778 662405 := bbase (se 4 (by rfl) ⟨62100, by rfl⟩ : syracuseStep 662405 = 124201) (by norm_num)
theorem B498577 : Blo 439778 498577 := bbase (se 2 (by rfl) ⟨186966, by rfl⟩ : syracuseStep 498577 = 373933) (by norm_num)
theorem B662429 : Blo 439778 662429 := bbase (se 3 (by rfl) ⟨124205, by rfl⟩ : syracuseStep 662429 = 248411) (by norm_num)
theorem B990125 : Blo 439778 990125 := bbase (se 3 (by rfl) ⟨185648, by rfl⟩ : syracuseStep 990125 = 371297) (by norm_num)
theorem B3218357 : Blo 439778 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B662453 : Blo 439778 662453 := bbase (se 5 (by rfl) ⟨31052, by rfl⟩ : syracuseStep 662453 = 62105) (by norm_num)
theorem B498613 : Blo 439778 498613 := bbase (se 5 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 498613 = 46745) (by norm_num)
theorem B662477 : Blo 439778 662477 := bbase (se 3 (by rfl) ⟨124214, by rfl⟩ : syracuseStep 662477 = 248429) (by norm_num)
theorem B498649 : Blo 439778 498649 := bbase (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) (by norm_num)
theorem B891877 : Blo 439778 891877 := bbase (se 4 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 891877 = 167227) (by norm_num)
theorem B662501 : Blo 439778 662501 := bbase (se 4 (by rfl) ⟨62109, by rfl⟩ : syracuseStep 662501 = 124219) (by norm_num)
theorem B990197 : Blo 439778 990197 := bbase (se 5 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 990197 = 92831) (by norm_num)
theorem B662525 : Blo 439778 662525 := bbase (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) (by norm_num)
theorem B498685 : Blo 439778 498685 := bbase (se 3 (by rfl) ⟨93503, by rfl⟩ : syracuseStep 498685 = 187007) (by norm_num)
theorem B662549 : Blo 439778 662549 := bbase (se 6 (by rfl) ⟨15528, by rfl⟩ : syracuseStep 662549 = 31057) (by norm_num)
theorem B498721 : Blo 439778 498721 := bbase (se 2 (by rfl) ⟨187020, by rfl⟩ : syracuseStep 498721 = 374041) (by norm_num)
theorem B662573 : Blo 439778 662573 := bbase (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) (by norm_num)
theorem B990269 : Blo 439778 990269 := bbase (se 3 (by rfl) ⟨185675, by rfl⟩ : syracuseStep 990269 = 371351) (by norm_num)
theorem B662597 : Blo 439778 662597 := bbase (se 4 (by rfl) ⟨62118, by rfl⟩ : syracuseStep 662597 = 124237) (by norm_num)
theorem B498757 : Blo 439778 498757 := bbase (se 4 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 498757 = 93517) (by norm_num)
theorem B662621 : Blo 439778 662621 := bbase (se 3 (by rfl) ⟨124241, by rfl⟩ : syracuseStep 662621 = 248483) (by norm_num)
theorem B498793 : Blo 439778 498793 := bbase (se 2 (by rfl) ⟨187047, by rfl⟩ : syracuseStep 498793 = 374095) (by norm_num)
theorem B662645 : Blo 439778 662645 := bbase (se 5 (by rfl) ⟨31061, by rfl⟩ : syracuseStep 662645 = 62123) (by norm_num)
theorem B990341 : Blo 439778 990341 := bbase (se 4 (by rfl) ⟨92844, by rfl⟩ : syracuseStep 990341 = 185689) (by norm_num)
theorem B662669 : Blo 439778 662669 := bbase (se 3 (by rfl) ⟨124250, by rfl⟩ : syracuseStep 662669 = 248501) (by norm_num)
theorem B498829 : Blo 439778 498829 := bbase (se 3 (by rfl) ⟨93530, by rfl⟩ : syracuseStep 498829 = 187061) (by norm_num)
theorem B662693 : Blo 439778 662693 := bbase (se 4 (by rfl) ⟨62127, by rfl⟩ : syracuseStep 662693 = 124255) (by norm_num)
theorem B498865 : Blo 439778 498865 := bbase (se 2 (by rfl) ⟨187074, by rfl⟩ : syracuseStep 498865 = 374149) (by norm_num)
theorem B662717 : Blo 439778 662717 := bbase (se 3 (by rfl) ⟨124259, by rfl⟩ : syracuseStep 662717 = 248519) (by norm_num)
theorem B1121485 : Blo 439778 1121485 := bbase (se 3 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 1121485 = 420557) (by norm_num)
theorem B990413 : Blo 439778 990413 := bbase (se 3 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 990413 = 371405) (by norm_num)
theorem B662741 : Blo 439778 662741 := bbase (se 7 (by rfl) ⟨7766, by rfl⟩ : syracuseStep 662741 = 15533) (by norm_num)
theorem B498901 : Blo 439778 498901 := bbase (se 7 (by rfl) ⟨5846, by rfl⟩ : syracuseStep 498901 = 11693) (by norm_num)
theorem B662765 : Blo 439778 662765 := bbase (se 3 (by rfl) ⟨124268, by rfl⟩ : syracuseStep 662765 = 248537) (by norm_num)
theorem B498937 : Blo 439778 498937 := bbase (se 2 (by rfl) ⟨187101, by rfl⟩ : syracuseStep 498937 = 374203) (by norm_num)
theorem B662789 : Blo 439778 662789 := bbase (se 4 (by rfl) ⟨62136, by rfl⟩ : syracuseStep 662789 = 124273) (by norm_num)
theorem B990485 : Blo 439778 990485 := bbase (se 6 (by rfl) ⟨23214, by rfl⟩ : syracuseStep 990485 = 46429) (by norm_num)
theorem B662813 : Blo 439778 662813 := bbase (se 3 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 662813 = 248555) (by norm_num)
theorem B498973 : Blo 439778 498973 := bbase (se 3 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 498973 = 187115) (by norm_num)
theorem B662837 : Blo 439778 662837 := bbase (se 5 (by rfl) ⟨31070, by rfl⟩ : syracuseStep 662837 = 62141) (by norm_num)
theorem B1121597 : Blo 439778 1121597 := bbase (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) (by norm_num)
theorem B499009 : Blo 439778 499009 := bbase (se 2 (by rfl) ⟨187128, by rfl⟩ : syracuseStep 499009 = 374257) (by norm_num)
theorem B662861 : Blo 439778 662861 := bbase (se 3 (by rfl) ⟨124286, by rfl⟩ : syracuseStep 662861 = 248573) (by norm_num)
theorem B990557 : Blo 439778 990557 := bbase (se 3 (by rfl) ⟨185729, by rfl⟩ : syracuseStep 990557 = 371459) (by norm_num)
theorem B662885 : Blo 439778 662885 := bbase (se 4 (by rfl) ⟨62145, by rfl⟩ : syracuseStep 662885 = 124291) (by norm_num)
theorem B499045 : Blo 439778 499045 := bbase (se 4 (by rfl) ⟨46785, by rfl⟩ : syracuseStep 499045 = 93571) (by norm_num)
theorem B662909 : Blo 439778 662909 := bbase (se 3 (by rfl) ⟨124295, by rfl⟩ : syracuseStep 662909 = 248591) (by norm_num)
theorem B1252741 : Blo 439778 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B499081 : Blo 439778 499081 := bbase (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) (by norm_num)
theorem B662933 : Blo 439778 662933 := bbase (se 6 (by rfl) ⟨15537, by rfl⟩ : syracuseStep 662933 = 31075) (by norm_num)
theorem B990629 : Blo 439778 990629 := bbase (se 4 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 990629 = 185743) (by norm_num)
theorem B662957 : Blo 439778 662957 := bbase (se 3 (by rfl) ⟨124304, by rfl⟩ : syracuseStep 662957 = 248609) (by norm_num)
theorem B499117 : Blo 439778 499117 := bbase (se 3 (by rfl) ⟨93584, by rfl⟩ : syracuseStep 499117 = 187169) (by norm_num)
theorem B662981 : Blo 439778 662981 := bbase (se 4 (by rfl) ⟨62154, by rfl⟩ : syracuseStep 662981 = 124309) (by norm_num)
theorem B564689 : Blo 439778 564689 := bbase (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) (by norm_num)
theorem B499153 : Blo 439778 499153 := bbase (se 2 (by rfl) ⟨187182, by rfl⟩ : syracuseStep 499153 = 374365) (by norm_num)
theorem B597461 : Blo 439778 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B663005 : Blo 439778 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B531937 : Blo 439778 531937 := bbase (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) (by norm_num)
theorem B531941 : Blo 439778 531941 := bbase (se 4 (by rfl) ⟨49869, by rfl⟩ : syracuseStep 531941 = 99739) (by norm_num)
theorem B892397 : Blo 439778 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B990701 : Blo 439778 990701 := bbase (se 3 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 990701 = 371513) (by norm_num)
theorem B663029 : Blo 439778 663029 := bbase (se 5 (by rfl) ⟨31079, by rfl⟩ : syracuseStep 663029 = 62159) (by norm_num)
theorem B499189 : Blo 439778 499189 := bbase (se 5 (by rfl) ⟨23399, by rfl⟩ : syracuseStep 499189 = 46799) (by norm_num)
theorem B1121789 : Blo 439778 1121789 := bbase (se 3 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 1121789 = 420671) (by norm_num)
theorem B663053 : Blo 439778 663053 := bbase (se 3 (by rfl) ⟨124322, by rfl⟩ : syracuseStep 663053 = 248645) (by norm_num)
theorem B499225 : Blo 439778 499225 := bbase (se 2 (by rfl) ⟨187209, by rfl⟩ : syracuseStep 499225 = 374419) (by norm_num)
theorem B1252901 : Blo 439778 1252901 := bbase (se 4 (by rfl) ⟨117459, by rfl⟩ : syracuseStep 1252901 = 234919) (by norm_num)
theorem B663077 : Blo 439778 663077 := bbase (se 4 (by rfl) ⟨62163, by rfl⟩ : syracuseStep 663077 = 124327) (by norm_num)
theorem B990773 : Blo 439778 990773 := bbase (se 5 (by rfl) ⟨46442, by rfl⟩ : syracuseStep 990773 = 92885) (by norm_num)
theorem B663101 : Blo 439778 663101 := bbase (se 3 (by rfl) ⟨124331, by rfl⟩ : syracuseStep 663101 = 248663) (by norm_num)
theorem B663125 : Blo 439778 663125 := bbase (se 8 (by rfl) ⟨3885, by rfl⟩ : syracuseStep 663125 = 7771) (by norm_num)
theorem B663149 : Blo 439778 663149 := bbase (se 3 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 663149 = 248681) (by norm_num)
theorem B597613 : Blo 439778 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B990845 : Blo 439778 990845 := bbase (se 3 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 990845 = 371567) (by norm_num)
theorem B663173 : Blo 439778 663173 := bbase (se 4 (by rfl) ⟨62172, by rfl⟩ : syracuseStep 663173 = 124345) (by norm_num)
theorem B663197 : Blo 439778 663197 := bbase (se 3 (by rfl) ⟨124349, by rfl⟩ : syracuseStep 663197 = 248699) (by norm_num)
theorem B1416869 : Blo 439778 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B2236085 : Blo 439778 2236085 := bbase (se 5 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 2236085 = 209633) (by norm_num)
theorem B663221 : Blo 439778 663221 := bbase (se 5 (by rfl) ⟨31088, by rfl⟩ : syracuseStep 663221 = 62177) (by norm_num)
theorem B990917 : Blo 439778 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B663245 : Blo 439778 663245 := bbase (se 3 (by rfl) ⟨124358, by rfl⟩ : syracuseStep 663245 = 248717) (by norm_num)
theorem B663269 : Blo 439778 663269 := bbase (se 4 (by rfl) ⟨62181, by rfl⟩ : syracuseStep 663269 = 124363) (by norm_num)
theorem B630517 : Blo 439778 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B663293 : Blo 439778 663293 := bbase (se 3 (by rfl) ⟨124367, by rfl⟩ : syracuseStep 663293 = 248735) (by norm_num)
theorem B990989 : Blo 439778 990989 := bbase (se 3 (by rfl) ⟨185810, by rfl⟩ : syracuseStep 990989 = 371621) (by norm_num)
theorem B1253141 : Blo 439778 1253141 := bbase (se 6 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 1253141 = 58741) (by norm_num)
theorem B663317 : Blo 439778 663317 := bbase (se 6 (by rfl) ⟨15546, by rfl⟩ : syracuseStep 663317 = 31093) (by norm_num)
theorem B663341 : Blo 439778 663341 := bbase (se 3 (by rfl) ⟨124376, by rfl⟩ : syracuseStep 663341 = 248753) (by norm_num)
theorem B663365 : Blo 439778 663365 := bbase (se 4 (by rfl) ⟨62190, by rfl⟩ : syracuseStep 663365 = 124381) (by norm_num)
theorem B991061 : Blo 439778 991061 := bbase (se 9 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 991061 = 5807) (by norm_num)
theorem B1122133 : Blo 439778 1122133 := bbase (se 9 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 1122133 = 6575) (by norm_num)
theorem B663389 : Blo 439778 663389 := bbase (se 3 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 663389 = 248771) (by norm_num)
theorem B663413 : Blo 439778 663413 := bbase (se 5 (by rfl) ⟨31097, by rfl⟩ : syracuseStep 663413 = 62195) (by norm_num)
theorem B1679237 : Blo 439778 1679237 := bbase (se 4 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 1679237 = 314857) (by norm_num)
theorem B663437 : Blo 439778 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B991133 : Blo 439778 991133 := bbase (se 3 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 991133 = 371675) (by norm_num)
theorem B663461 : Blo 439778 663461 := bbase (se 4 (by rfl) ⟨62199, by rfl⟩ : syracuseStep 663461 = 124399) (by norm_num)
theorem B663485 : Blo 439778 663485 := bbase (se 3 (by rfl) ⟨124403, by rfl⟩ : syracuseStep 663485 = 248807) (by norm_num)
theorem B1122245 : Blo 439778 1122245 := bbase (se 4 (by rfl) ⟨105210, by rfl⟩ : syracuseStep 1122245 = 210421) (by norm_num)
theorem B663509 : Blo 439778 663509 := bbase (se 7 (by rfl) ⟨7775, by rfl⟩ : syracuseStep 663509 = 15551) (by norm_num)
theorem B1253333 : Blo 439778 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B532441 : Blo 439778 532441 := bbase (se 2 (by rfl) ⟨199665, by rfl⟩ : syracuseStep 532441 = 399331) (by norm_num)
theorem B565213 : Blo 439778 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B991205 : Blo 439778 991205 := bbase (se 4 (by rfl) ⟨92925, by rfl⟩ : syracuseStep 991205 = 185851) (by norm_num)
theorem B663533 : Blo 439778 663533 := bbase (se 3 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 663533 = 248825) (by norm_num)
theorem B663557 : Blo 439778 663557 := bbase (se 4 (by rfl) ⟨62208, by rfl⟩ : syracuseStep 663557 = 124417) (by norm_num)
theorem B663581 : Blo 439778 663581 := bbase (se 3 (by rfl) ⟨124421, by rfl⟩ : syracuseStep 663581 = 248843) (by norm_num)
theorem B598045 : Blo 439778 598045 := bbase (se 3 (by rfl) ⟨112133, by rfl⟩ : syracuseStep 598045 = 224267) (by norm_num)
theorem B991277 : Blo 439778 991277 := bbase (se 3 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 991277 = 371729) (by norm_num)
theorem B663605 : Blo 439778 663605 := bbase (se 5 (by rfl) ⟨31106, by rfl⟩ : syracuseStep 663605 = 62213) (by norm_num)
theorem B663629 : Blo 439778 663629 := bbase (se 3 (by rfl) ⟨124430, by rfl⟩ : syracuseStep 663629 = 248861) (by norm_num)
theorem B663653 : Blo 439778 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B991349 : Blo 439778 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B663677 : Blo 439778 663677 := bbase (se 3 (by rfl) ⟨124439, by rfl⟩ : syracuseStep 663677 = 248879) (by norm_num)
theorem B1122437 : Blo 439778 1122437 := bbase (se 4 (by rfl) ⟨105228, by rfl⟩ : syracuseStep 1122437 = 210457) (by norm_num)
theorem B663701 : Blo 439778 663701 := bbase (se 6 (by rfl) ⟨15555, by rfl⟩ : syracuseStep 663701 = 31111) (by norm_num)
theorem B1679525 : Blo 439778 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B663725 : Blo 439778 663725 := bbase (se 3 (by rfl) ⟨124448, by rfl⟩ : syracuseStep 663725 = 248897) (by norm_num)
theorem B991421 : Blo 439778 991421 := bbase (se 3 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 991421 = 371783) (by norm_num)
theorem B663749 : Blo 439778 663749 := bbase (se 4 (by rfl) ⟨62226, by rfl⟩ : syracuseStep 663749 = 124453) (by norm_num)
theorem B598213 : Blo 439778 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B663773 : Blo 439778 663773 := bbase (se 3 (by rfl) ⟨124457, by rfl⟩ : syracuseStep 663773 = 248915) (by norm_num)
theorem B663797 : Blo 439778 663797 := bbase (se 5 (by rfl) ⟨31115, by rfl⟩ : syracuseStep 663797 = 62231) (by norm_num)
theorem B991493 : Blo 439778 991493 := bbase (se 4 (by rfl) ⟨92952, by rfl⟩ : syracuseStep 991493 = 185905) (by norm_num)
theorem B663821 : Blo 439778 663821 := bbase (se 3 (by rfl) ⟨124466, by rfl⟩ : syracuseStep 663821 = 248933) (by norm_num)
theorem B663845 : Blo 439778 663845 := bbase (se 4 (by rfl) ⟨62235, by rfl⟩ : syracuseStep 663845 = 124471) (by norm_num)
theorem B663869 : Blo 439778 663869 := bbase (se 3 (by rfl) ⟨124475, by rfl⟩ : syracuseStep 663869 = 248951) (by norm_num)
theorem B631109 : Blo 439778 631109 := bbase (se 4 (by rfl) ⟨59166, by rfl⟩ : syracuseStep 631109 = 118333) (by norm_num)
theorem B991565 : Blo 439778 991565 := bbase (se 3 (by rfl) ⟨185918, by rfl⟩ : syracuseStep 991565 = 371837) (by norm_num)
theorem B663893 : Blo 439778 663893 := bbase (se 10 (by rfl) ⟨972, by rfl⟩ : syracuseStep 663893 = 1945) (by norm_num)
theorem B532825 : Blo 439778 532825 := bbase (se 2 (by rfl) ⟨199809, by rfl⟩ : syracuseStep 532825 = 399619) (by norm_num)
theorem B663917 : Blo 439778 663917 := bbase (se 3 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 663917 = 248969) (by norm_num)
theorem B663941 : Blo 439778 663941 := bbase (se 4 (by rfl) ⟨62244, by rfl⟩ : syracuseStep 663941 = 124489) (by norm_num)
theorem B991637 : Blo 439778 991637 := bbase (se 6 (by rfl) ⟨23241, by rfl⟩ : syracuseStep 991637 = 46483) (by norm_num)
theorem B631189 : Blo 439778 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B663965 : Blo 439778 663965 := bbase (se 3 (by rfl) ⟨124493, by rfl⟩ : syracuseStep 663965 = 248987) (by norm_num)
theorem B663989 : Blo 439778 663989 := bbase (se 5 (by rfl) ⟨31124, by rfl⟩ : syracuseStep 663989 = 62249) (by norm_num)
theorem B664013 : Blo 439778 664013 := bbase (se 3 (by rfl) ⟨124502, by rfl⟩ : syracuseStep 664013 = 249005) (by norm_num)
theorem B598477 : Blo 439778 598477 := bbase (se 3 (by rfl) ⟨112214, by rfl⟩ : syracuseStep 598477 = 224429) (by norm_num)
theorem B991709 : Blo 439778 991709 := bbase (se 3 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 991709 = 371891) (by norm_num)
theorem B1122781 : Blo 439778 1122781 := bbase (se 3 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 1122781 = 421043) (by norm_num)
theorem B664037 : Blo 439778 664037 := bbase (se 4 (by rfl) ⟨62253, by rfl⟩ : syracuseStep 664037 = 124507) (by norm_num)
theorem B664061 : Blo 439778 664061 := bbase (se 3 (by rfl) ⟨124511, by rfl⟩ : syracuseStep 664061 = 249023) (by norm_num)
theorem B631309 : Blo 439778 631309 := bbase (se 3 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 631309 = 236741) (by norm_num)
theorem B664085 : Blo 439778 664085 := bbase (se 6 (by rfl) ⟨15564, by rfl⟩ : syracuseStep 664085 = 31129) (by norm_num)
theorem B991781 : Blo 439778 991781 := bbase (se 4 (by rfl) ⟨92979, by rfl⟩ : syracuseStep 991781 = 185959) (by norm_num)
theorem B664109 : Blo 439778 664109 := bbase (se 3 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 664109 = 249041) (by norm_num)
theorem B3875381 : Blo 439778 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B664133 : Blo 439778 664133 := bbase (se 4 (by rfl) ⟨62262, by rfl⟩ : syracuseStep 664133 = 124525) (by norm_num)
theorem B1122893 : Blo 439778 1122893 := bbase (se 3 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 1122893 = 421085) (by norm_num)
theorem B664157 : Blo 439778 664157 := bbase (se 3 (by rfl) ⟨124529, by rfl⟩ : syracuseStep 664157 = 249059) (by norm_num)
theorem B991853 : Blo 439778 991853 := bbase (se 3 (by rfl) ⟨185972, by rfl⟩ : syracuseStep 991853 = 371945) (by norm_num)
theorem B631405 : Blo 439778 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B664181 : Blo 439778 664181 := bbase (se 5 (by rfl) ⟨31133, by rfl⟩ : syracuseStep 664181 = 62267) (by norm_num)
theorem B664205 : Blo 439778 664205 := bbase (se 3 (by rfl) ⟨124538, by rfl⟩ : syracuseStep 664205 = 249077) (by norm_num)
theorem B664229 : Blo 439778 664229 := bbase (se 4 (by rfl) ⟨62271, by rfl⟩ : syracuseStep 664229 = 124543) (by norm_num)
theorem B991925 : Blo 439778 991925 := bbase (se 5 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 991925 = 92993) (by norm_num)
theorem B893629 : Blo 439778 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B664253 : Blo 439778 664253 := bbase (se 3 (by rfl) ⟨124547, by rfl⟩ : syracuseStep 664253 = 249095) (by norm_num)
theorem B664277 : Blo 439778 664277 := bbase (se 7 (by rfl) ⟨7784, by rfl⟩ : syracuseStep 664277 = 15569) (by norm_num)
theorem B664301 : Blo 439778 664301 := bbase (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) (by norm_num)
theorem B991997 : Blo 439778 991997 := bbase (se 3 (by rfl) ⟨185999, by rfl⟩ : syracuseStep 991997 = 371999) (by norm_num)
theorem B664325 : Blo 439778 664325 := bbase (se 4 (by rfl) ⟨62280, by rfl⟩ : syracuseStep 664325 = 124561) (by norm_num)
theorem B1123085 : Blo 439778 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B566033 : Blo 439778 566033 := bbase (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) (by norm_num)
theorem B664349 : Blo 439778 664349 := bbase (se 3 (by rfl) ⟨124565, by rfl⟩ : syracuseStep 664349 = 249131) (by norm_num)
theorem B664373 : Blo 439778 664373 := bbase (se 5 (by rfl) ⟨31142, by rfl⟩ : syracuseStep 664373 = 62285) (by norm_num)
theorem B992069 : Blo 439778 992069 := bbase (se 4 (by rfl) ⟨93006, by rfl⟩ : syracuseStep 992069 = 186013) (by norm_num)
theorem B664397 : Blo 439778 664397 := bbase (se 3 (by rfl) ⟨124574, by rfl⟩ : syracuseStep 664397 = 249149) (by norm_num)
theorem B664421 : Blo 439778 664421 := bbase (se 4 (by rfl) ⟨62289, by rfl⟩ : syracuseStep 664421 = 124579) (by norm_num)
theorem B664445 : Blo 439778 664445 := bbase (se 3 (by rfl) ⟨124583, by rfl⟩ : syracuseStep 664445 = 249167) (by norm_num)
theorem B992141 : Blo 439778 992141 := bbase (se 3 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 992141 = 372053) (by norm_num)
theorem B664469 : Blo 439778 664469 := bbase (se 6 (by rfl) ⟨15573, by rfl⟩ : syracuseStep 664469 = 31147) (by norm_num)
theorem B664493 : Blo 439778 664493 := bbase (se 3 (by rfl) ⟨124592, by rfl⟩ : syracuseStep 664493 = 249185) (by norm_num)
theorem B1254325 : Blo 439778 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B566197 : Blo 439778 566197 := bbase (se 5 (by rfl) ⟨26540, by rfl⟩ : syracuseStep 566197 = 53081) (by norm_num)
theorem B2237381 : Blo 439778 2237381 := bbase (se 4 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 2237381 = 419509) (by norm_num)
theorem B664517 : Blo 439778 664517 := bbase (se 4 (by rfl) ⟨62298, by rfl⟩ : syracuseStep 664517 = 124597) (by norm_num)
theorem B992213 : Blo 439778 992213 := bbase (se 7 (by rfl) ⟨11627, by rfl⟩ : syracuseStep 992213 = 23255) (by norm_num)
theorem B664541 : Blo 439778 664541 := bbase (se 3 (by rfl) ⟨124601, by rfl⟩ : syracuseStep 664541 = 249203) (by norm_num)
theorem B664565 : Blo 439778 664565 := bbase (se 5 (by rfl) ⟨31151, by rfl⟩ : syracuseStep 664565 = 62303) (by norm_num)
theorem B566281 : Blo 439778 566281 := bbase (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) (by norm_num)
theorem B664589 : Blo 439778 664589 := bbase (se 3 (by rfl) ⟨124610, by rfl⟩ : syracuseStep 664589 = 249221) (by norm_num)
theorem B992285 : Blo 439778 992285 := bbase (se 3 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 992285 = 372107) (by norm_num)
theorem B664613 : Blo 439778 664613 := bbase (se 4 (by rfl) ⟨62307, by rfl⟩ : syracuseStep 664613 = 124615) (by norm_num)
theorem B664637 : Blo 439778 664637 := bbase (se 3 (by rfl) ⟨124619, by rfl⟩ : syracuseStep 664637 = 249239) (by norm_num)
theorem B664661 : Blo 439778 664661 := bbase (se 8 (by rfl) ⟨3894, by rfl⟩ : syracuseStep 664661 = 7789) (by norm_num)
theorem B992357 : Blo 439778 992357 := bbase (se 4 (by rfl) ⟨93033, by rfl⟩ : syracuseStep 992357 = 186067) (by norm_num)
theorem B795749 : Blo 439778 795749 := bbase (se 4 (by rfl) ⟨74601, by rfl⟩ : syracuseStep 795749 = 149203) (by norm_num)
theorem B664685 : Blo 439778 664685 := bbase (se 3 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 664685 = 249257) (by norm_num)
theorem B2827381 : Blo 439778 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B664709 : Blo 439778 664709 := bbase (se 4 (by rfl) ⟨62316, by rfl⟩ : syracuseStep 664709 = 124633) (by norm_num)
theorem B664733 : Blo 439778 664733 := bbase (se 3 (by rfl) ⟨124637, by rfl⟩ : syracuseStep 664733 = 249275) (by norm_num)
theorem B992429 : Blo 439778 992429 := bbase (se 3 (by rfl) ⟨186080, by rfl⟩ : syracuseStep 992429 = 372161) (by norm_num)
theorem B795829 : Blo 439778 795829 := bbase (se 5 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 795829 = 74609) (by norm_num)
theorem B664757 : Blo 439778 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B828613 : Blo 439778 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B664781 : Blo 439778 664781 := bbase (se 3 (by rfl) ⟨124646, by rfl⟩ : syracuseStep 664781 = 249293) (by norm_num)
theorem B664805 : Blo 439778 664805 := bbase (se 4 (by rfl) ⟨62325, by rfl⟩ : syracuseStep 664805 = 124651) (by norm_num)
theorem B992501 : Blo 439778 992501 := bbase (se 5 (by rfl) ⟨46523, by rfl⟩ : syracuseStep 992501 = 93047) (by norm_num)
theorem B664829 : Blo 439778 664829 := bbase (se 3 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 664829 = 249311) (by norm_num)
theorem B664853 : Blo 439778 664853 := bbase (se 6 (by rfl) ⟨15582, by rfl⟩ : syracuseStep 664853 = 31165) (by norm_num)
theorem B664877 : Blo 439778 664877 := bbase (se 3 (by rfl) ⟨124664, by rfl⟩ : syracuseStep 664877 = 249329) (by norm_num)
theorem B992573 : Blo 439778 992573 := bbase (se 3 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 992573 = 372215) (by norm_num)
theorem B1680709 : Blo 439778 1680709 := bbase (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) (by norm_num)
theorem B664901 : Blo 439778 664901 := bbase (se 4 (by rfl) ⟨62334, by rfl⟩ : syracuseStep 664901 = 124669) (by norm_num)
theorem B664925 : Blo 439778 664925 := bbase (se 3 (by rfl) ⟨124673, by rfl⟩ : syracuseStep 664925 = 249347) (by norm_num)
theorem B664949 : Blo 439778 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B992645 : Blo 439778 992645 := bbase (se 4 (by rfl) ⟨93060, by rfl⟩ : syracuseStep 992645 = 186121) (by norm_num)
theorem B664973 : Blo 439778 664973 := bbase (se 3 (by rfl) ⟨124682, by rfl⟩ : syracuseStep 664973 = 249365) (by norm_num)
theorem B796061 : Blo 439778 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B664997 : Blo 439778 664997 := bbase (se 4 (by rfl) ⟨62343, by rfl⟩ : syracuseStep 664997 = 124687) (by norm_num)
theorem B665021 : Blo 439778 665021 := bbase (se 3 (by rfl) ⟨124691, by rfl⟩ : syracuseStep 665021 = 249383) (by norm_num)
theorem B992717 : Blo 439778 992717 := bbase (se 3 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 992717 = 372269) (by norm_num)
theorem B665045 : Blo 439778 665045 := bbase (se 7 (by rfl) ⟨7793, by rfl⟩ : syracuseStep 665045 = 15587) (by norm_num)
theorem B1058269 : Blo 439778 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B665069 : Blo 439778 665069 := bbase (se 3 (by rfl) ⟨124700, by rfl⟩ : syracuseStep 665069 = 249401) (by norm_num)
theorem B1418741 : Blo 439778 1418741 := bbase (se 5 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 1418741 = 133007) (by norm_num)
theorem B665093 : Blo 439778 665093 := bbase (se 4 (by rfl) ⟨62352, by rfl⟩ : syracuseStep 665093 = 124705) (by norm_num)
theorem B992789 : Blo 439778 992789 := bbase (se 6 (by rfl) ⟨23268, by rfl⟩ : syracuseStep 992789 = 46537) (by norm_num)
theorem B665117 : Blo 439778 665117 := bbase (se 3 (by rfl) ⟨124709, by rfl⟩ : syracuseStep 665117 = 249419) (by norm_num)
theorem B1123877 : Blo 439778 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B665141 : Blo 439778 665141 := bbase (se 5 (by rfl) ⟨31178, by rfl⟩ : syracuseStep 665141 = 62357) (by norm_num)
theorem B665165 : Blo 439778 665165 := bbase (se 3 (by rfl) ⟨124718, by rfl⟩ : syracuseStep 665165 = 249437) (by norm_num)
theorem B992861 : Blo 439778 992861 := bbase (se 3 (by rfl) ⟨186161, by rfl⟩ : syracuseStep 992861 = 372323) (by norm_num)
theorem B665189 : Blo 439778 665189 := bbase (se 4 (by rfl) ⟨62361, by rfl⟩ : syracuseStep 665189 = 124723) (by norm_num)
theorem B1484405 : Blo 439778 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B1681013 : Blo 439778 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B665213 : Blo 439778 665213 := bbase (se 3 (by rfl) ⟨124727, by rfl⟩ : syracuseStep 665213 = 249455) (by norm_num)
theorem B665237 : Blo 439778 665237 := bbase (se 6 (by rfl) ⟨15591, by rfl⟩ : syracuseStep 665237 = 31183) (by norm_num)
theorem B992933 : Blo 439778 992933 := bbase (se 4 (by rfl) ⟨93087, by rfl⟩ : syracuseStep 992933 = 186175) (by norm_num)
theorem B665261 : Blo 439778 665261 := bbase (se 3 (by rfl) ⟨124736, by rfl⟩ : syracuseStep 665261 = 249473) (by norm_num)
theorem B1058501 : Blo 439778 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B665285 : Blo 439778 665285 := bbase (se 4 (by rfl) ⟨62370, by rfl⟩ : syracuseStep 665285 = 124741) (by norm_num)
theorem B665309 : Blo 439778 665309 := bbase (se 3 (by rfl) ⟨124745, by rfl⟩ : syracuseStep 665309 = 249491) (by norm_num)
theorem B993005 : Blo 439778 993005 := bbase (se 3 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 993005 = 372377) (by norm_num)
theorem B665333 : Blo 439778 665333 := bbase (se 5 (by rfl) ⟨31187, by rfl⟩ : syracuseStep 665333 = 62375) (by norm_num)
theorem B861949 : Blo 439778 861949 := bbase (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) (by norm_num)
theorem B665357 : Blo 439778 665357 := bbase (se 3 (by rfl) ⟨124754, by rfl⟩ : syracuseStep 665357 = 249509) (by norm_num)
theorem B665381 : Blo 439778 665381 := bbase (se 4 (by rfl) ⟨62379, by rfl⟩ : syracuseStep 665381 = 124759) (by norm_num)
theorem B993077 : Blo 439778 993077 := bbase (se 5 (by rfl) ⟨46550, by rfl⟩ : syracuseStep 993077 = 93101) (by norm_num)
theorem B665405 : Blo 439778 665405 := bbase (se 3 (by rfl) ⟨124763, by rfl⟩ : syracuseStep 665405 = 249527) (by norm_num)
theorem B894797 : Blo 439778 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B1058645 : Blo 439778 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B665429 : Blo 439778 665429 := bbase (se 9 (by rfl) ⟨1949, by rfl⟩ : syracuseStep 665429 = 3899) (by norm_num)
theorem B665453 : Blo 439778 665453 := bbase (se 3 (by rfl) ⟨124772, by rfl⟩ : syracuseStep 665453 = 249545) (by norm_num)
theorem B993149 : Blo 439778 993149 := bbase (se 3 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 993149 = 372431) (by norm_num)
theorem B665477 : Blo 439778 665477 := bbase (se 4 (by rfl) ⟨62388, by rfl⟩ : syracuseStep 665477 = 124777) (by norm_num)
theorem B665501 : Blo 439778 665501 := bbase (se 3 (by rfl) ⟨124781, by rfl⟩ : syracuseStep 665501 = 249563) (by norm_num)
theorem B665525 : Blo 439778 665525 := bbase (se 5 (by rfl) ⟨31196, by rfl⟩ : syracuseStep 665525 = 62393) (by norm_num)
theorem B993221 : Blo 439778 993221 := bbase (se 4 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 993221 = 186229) (by norm_num)
theorem B665549 : Blo 439778 665549 := bbase (se 3 (by rfl) ⟨124790, by rfl⟩ : syracuseStep 665549 = 249581) (by norm_num)
theorem B665573 : Blo 439778 665573 := bbase (se 4 (by rfl) ⟨62397, by rfl⟩ : syracuseStep 665573 = 124795) (by norm_num)
theorem B665597 : Blo 439778 665597 := bbase (se 3 (by rfl) ⟨124799, by rfl⟩ : syracuseStep 665597 = 249599) (by norm_num)
theorem B1255429 : Blo 439778 1255429 := bbase (se 4 (by rfl) ⟨117696, by rfl⟩ : syracuseStep 1255429 = 235393) (by norm_num)
theorem B993293 : Blo 439778 993293 := bbase (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) (by norm_num)
theorem B665621 : Blo 439778 665621 := bbase (se 6 (by rfl) ⟨15600, by rfl⟩ : syracuseStep 665621 = 31201) (by norm_num)
theorem B1484837 : Blo 439778 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B665645 : Blo 439778 665645 := bbase (se 3 (by rfl) ⟨124808, by rfl⟩ : syracuseStep 665645 = 249617) (by norm_num)
theorem B1058885 : Blo 439778 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B993365 : Blo 439778 993365 := bbase (se 8 (by rfl) ⟨5820, by rfl⟩ : syracuseStep 993365 = 11641) (by norm_num)
theorem B993437 : Blo 439778 993437 := bbase (se 3 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 993437 = 372539) (by norm_num)
theorem B2238677 : Blo 439778 2238677 := bbase (se 7 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 2238677 = 52469) (by norm_num)
theorem B993509 : Blo 439778 993509 := bbase (se 4 (by rfl) ⟨93141, by rfl⟩ : syracuseStep 993509 = 186283) (by norm_num)
theorem B993581 : Blo 439778 993581 := bbase (se 3 (by rfl) ⟨186296, by rfl⟩ : syracuseStep 993581 = 372593) (by norm_num)
theorem B993653 : Blo 439778 993653 := bbase (se 5 (by rfl) ⟨46577, by rfl⟩ : syracuseStep 993653 = 93155) (by norm_num)
theorem B895349 : Blo 439778 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B993725 : Blo 439778 993725 := bbase (se 3 (by rfl) ⟨186323, by rfl⟩ : syracuseStep 993725 = 372647) (by norm_num)
theorem B1485269 : Blo 439778 1485269 := bbase (se 7 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 1485269 = 34811) (by norm_num)
theorem B993797 : Blo 439778 993797 := bbase (se 4 (by rfl) ⟨93168, by rfl⟩ : syracuseStep 993797 = 186337) (by norm_num)
theorem B797213 : Blo 439778 797213 := bbase (se 3 (by rfl) ⟨149477, by rfl⟩ : syracuseStep 797213 = 298955) (by norm_num)
theorem B1878565 : Blo 439778 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B993869 : Blo 439778 993869 := bbase (se 3 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 993869 = 372701) (by norm_num)
theorem B502357 : Blo 439778 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B797293 : Blo 439778 797293 := bbase (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) (by norm_num)
theorem B469633 : Blo 439778 469633 := bbase (se 2 (by rfl) ⟨176112, by rfl⟩ : syracuseStep 469633 = 352225) (by norm_num)
theorem B993941 : Blo 439778 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B994013 : Blo 439778 994013 := bbase (se 3 (by rfl) ⟨186377, by rfl⟩ : syracuseStep 994013 = 372755) (by norm_num)
theorem B469757 : Blo 439778 469757 := bbase (se 3 (by rfl) ⟨88079, by rfl⟩ : syracuseStep 469757 = 176159) (by norm_num)
theorem B3025685 : Blo 439778 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B994085 : Blo 439778 994085 := bbase (se 4 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 994085 = 186391) (by norm_num)
theorem B1059653 : Blo 439778 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B994157 : Blo 439778 994157 := bbase (se 3 (by rfl) ⟨186404, by rfl⟩ : syracuseStep 994157 = 372809) (by norm_num)
theorem B1485701 : Blo 439778 1485701 := bbase (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) (by norm_num)
theorem B994229 : Blo 439778 994229 := bbase (se 5 (by rfl) ⟨46604, by rfl⟩ : syracuseStep 994229 = 93209) (by norm_num)
theorem B470009 : Blo 439778 470009 := bbase (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) (by norm_num)
theorem B994301 : Blo 439778 994301 := bbase (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) (by norm_num)
theorem B502849 : Blo 439778 502849 := bbase (se 2 (by rfl) ⟨188568, by rfl⟩ : syracuseStep 502849 = 377137) (by norm_num)
theorem B994373 : Blo 439778 994373 := bbase (se 4 (by rfl) ⟨93222, by rfl⟩ : syracuseStep 994373 = 186445) (by norm_num)
theorem B994445 : Blo 439778 994445 := bbase (se 3 (by rfl) ⟨186458, by rfl⟩ : syracuseStep 994445 = 372917) (by norm_num)
theorem B994517 : Blo 439778 994517 := bbase (se 7 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 994517 = 23309) (by norm_num)
theorem B1879301 : Blo 439778 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B994589 : Blo 439778 994589 := bbase (se 3 (by rfl) ⟨186485, by rfl⟩ : syracuseStep 994589 = 372971) (by norm_num)
theorem B1486133 : Blo 439778 1486133 := bbase (se 5 (by rfl) ⟨69662, by rfl⟩ : syracuseStep 1486133 = 139325) (by norm_num)
theorem B994661 : Blo 439778 994661 := bbase (se 4 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 994661 = 186499) (by norm_num)
theorem B994733 : Blo 439778 994733 := bbase (se 3 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 994733 = 373025) (by norm_num)
theorem B470453 : Blo 439778 470453 := bbase (se 5 (by rfl) ⟨22052, by rfl⟩ : syracuseStep 470453 = 44105) (by norm_num)
theorem B1256933 : Blo 439778 1256933 := bbase (se 4 (by rfl) ⟨117837, by rfl⟩ : syracuseStep 1256933 = 235675) (by norm_num)
theorem B2239973 : Blo 439778 2239973 := bbase (se 4 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 2239973 = 419995) (by norm_num)
theorem B994805 : Blo 439778 994805 := bbase (se 5 (by rfl) ⟨46631, by rfl⟩ : syracuseStep 994805 = 93263) (by norm_num)
theorem B994877 : Blo 439778 994877 := bbase (se 3 (by rfl) ⟨186539, by rfl⟩ : syracuseStep 994877 = 373079) (by norm_num)
theorem B994949 : Blo 439778 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B798373 : Blo 439778 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B470701 : Blo 439778 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B1683125 : Blo 439778 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B995021 : Blo 439778 995021 := bbase (se 3 (by rfl) ⟨186566, by rfl⟩ : syracuseStep 995021 = 373133) (by norm_num)
theorem B1486565 : Blo 439778 1486565 := bbase (se 4 (by rfl) ⟨139365, by rfl⟩ : syracuseStep 1486565 = 278731) (by norm_num)
theorem B1093349 : Blo 439778 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B995093 : Blo 439778 995093 := bbase (se 6 (by rfl) ⟨23322, by rfl⟩ : syracuseStep 995093 = 46645) (by norm_num)
theorem B798517 : Blo 439778 798517 := bbase (se 5 (by rfl) ⟨37430, by rfl⟩ : syracuseStep 798517 = 74861) (by norm_num)
theorem B995165 : Blo 439778 995165 := bbase (se 3 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 995165 = 373187) (by norm_num)
theorem B995237 : Blo 439778 995237 := bbase (se 4 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 995237 = 186607) (by norm_num)
theorem B3583925 : Blo 439778 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B798677 : Blo 439778 798677 := bbase (se 7 (by rfl) ⟨9359, by rfl⟩ : syracuseStep 798677 = 18719) (by norm_num)
theorem B1683413 : Blo 439778 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B995309 : Blo 439778 995309 := bbase (se 3 (by rfl) ⟨186620, by rfl⟩ : syracuseStep 995309 = 373241) (by norm_num)
theorem B995381 : Blo 439778 995381 := bbase (se 5 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 995381 = 93317) (by norm_num)
theorem B471145 : Blo 439778 471145 := bbase (se 2 (by rfl) ⟨176679, by rfl⟩ : syracuseStep 471145 = 353359) (by norm_num)
theorem B995453 : Blo 439778 995453 := bbase (se 3 (by rfl) ⟨186647, by rfl⟩ : syracuseStep 995453 = 373295) (by norm_num)
theorem B1486997 : Blo 439778 1486997 := bbase (se 6 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 1486997 = 69703) (by norm_num)
theorem B471205 : Blo 439778 471205 := bbase (se 4 (by rfl) ⟨44175, by rfl⟩ : syracuseStep 471205 = 88351) (by norm_num)
theorem B1061029 : Blo 439778 1061029 := bbase (se 4 (by rfl) ⟨99471, by rfl⟩ : syracuseStep 1061029 = 198943) (by norm_num)
theorem B995525 : Blo 439778 995525 := bbase (se 4 (by rfl) ⟨93330, by rfl⟩ : syracuseStep 995525 = 186661) (by norm_num)
theorem B1421509 : Blo 439778 1421509 := bbase (se 4 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 1421509 = 266533) (by norm_num)
theorem B995597 : Blo 439778 995597 := bbase (se 3 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 995597 = 373349) (by norm_num)
theorem B995669 : Blo 439778 995669 := bbase (se 10 (by rfl) ⟨1458, by rfl⟩ : syracuseStep 995669 = 2917) (by norm_num)
theorem B995741 : Blo 439778 995741 := bbase (se 3 (by rfl) ⟨186701, by rfl⟩ : syracuseStep 995741 = 373403) (by norm_num)
theorem B471521 : Blo 439778 471521 := bbase (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) (by norm_num)
theorem B995813 : Blo 439778 995813 := bbase (se 4 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 995813 = 186715) (by norm_num)
theorem B995885 : Blo 439778 995885 := bbase (se 3 (by rfl) ⟨186728, by rfl⟩ : syracuseStep 995885 = 373457) (by norm_num)
theorem B1487429 : Blo 439778 1487429 := bbase (se 4 (by rfl) ⟨139446, by rfl⟩ : syracuseStep 1487429 = 278893) (by norm_num)
theorem B1192565 : Blo 439778 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B995957 : Blo 439778 995957 := bbase (se 5 (by rfl) ⟨46685, by rfl⟩ : syracuseStep 995957 = 93371) (by norm_num)
theorem B996029 : Blo 439778 996029 := bbase (se 3 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 996029 = 373511) (by norm_num)
theorem B2241269 : Blo 439778 2241269 := bbase (se 5 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 2241269 = 210119) (by norm_num)
theorem B996101 : Blo 439778 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B996173 : Blo 439778 996173 := bbase (se 3 (by rfl) ⟨186782, by rfl⟩ : syracuseStep 996173 = 373565) (by norm_num)
theorem B996245 : Blo 439778 996245 := bbase (se 6 (by rfl) ⟨23349, by rfl⟩ : syracuseStep 996245 = 46699) (by norm_num)
theorem B471965 : Blo 439778 471965 := bbase (se 3 (by rfl) ⟨88493, by rfl⟩ : syracuseStep 471965 = 176987) (by norm_num)
theorem B472025 : Blo 439778 472025 := bbase (se 2 (by rfl) ⟨177009, by rfl⟩ : syracuseStep 472025 = 354019) (by norm_num)
theorem B996317 : Blo 439778 996317 := bbase (se 3 (by rfl) ⟨186809, by rfl⟩ : syracuseStep 996317 = 373619) (by norm_num)
theorem B1487861 : Blo 439778 1487861 := bbase (se 5 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 1487861 = 139487) (by norm_num)
theorem B2831381 : Blo 439778 2831381 := bbase (se 6 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 2831381 = 132721) (by norm_num)
theorem B1258517 : Blo 439778 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B996389 : Blo 439778 996389 := bbase (se 4 (by rfl) ⟨93411, by rfl⟩ : syracuseStep 996389 = 186823) (by norm_num)
theorem B472153 : Blo 439778 472153 := bbase (se 2 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 472153 = 354115) (by norm_num)
theorem B996461 : Blo 439778 996461 := bbase (se 3 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 996461 = 373673) (by norm_num)
theorem B1684597 : Blo 439778 1684597 := bbase (se 5 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 1684597 = 157931) (by norm_num)
theorem B3355829 : Blo 439778 3355829 := bbase (se 5 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 3355829 = 314609) (by norm_num)
theorem B996533 : Blo 439778 996533 := bbase (se 5 (by rfl) ⟨46712, by rfl⟩ : syracuseStep 996533 = 93425) (by norm_num)
theorem B996605 : Blo 439778 996605 := bbase (se 3 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 996605 = 373727) (by norm_num)
theorem B996677 : Blo 439778 996677 := bbase (se 4 (by rfl) ⟨93438, by rfl⟩ : syracuseStep 996677 = 186877) (by norm_num)
theorem B1062229 : Blo 439778 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B996749 : Blo 439778 996749 := bbase (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) (by norm_num)
theorem B1488293 : Blo 439778 1488293 := bbase (se 4 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 1488293 = 279055) (by norm_num)
theorem B1684901 : Blo 439778 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B996821 : Blo 439778 996821 := bbase (se 7 (by rfl) ⟨11681, by rfl⟩ : syracuseStep 996821 = 23363) (by norm_num)
theorem B472597 : Blo 439778 472597 := bbase (se 6 (by rfl) ⟨11076, by rfl⟩ : syracuseStep 472597 = 22153) (by norm_num)
theorem B6829589 : Blo 439778 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B996893 : Blo 439778 996893 := bbase (se 3 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 996893 = 373835) (by norm_num)
theorem B996965 : Blo 439778 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B472717 : Blo 439778 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B997037 : Blo 439778 997037 := bbase (se 3 (by rfl) ⟨186944, by rfl⟩ : syracuseStep 997037 = 373889) (by norm_num)
theorem B1259189 : Blo 439778 1259189 := bbase (se 5 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 1259189 = 118049) (by norm_num)
theorem B505549 : Blo 439778 505549 := bbase (se 3 (by rfl) ⟨94790, by rfl⟩ : syracuseStep 505549 = 189581) (by norm_num)
theorem B997109 : Blo 439778 997109 := bbase (se 5 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 997109 = 93479) (by norm_num)
theorem B997181 : Blo 439778 997181 := bbase (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) (by norm_num)
theorem B1488725 : Blo 439778 1488725 := bbase (se 9 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 1488725 = 8723) (by norm_num)
theorem B669541 : Blo 439778 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B997253 : Blo 439778 997253 := bbase (se 4 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 997253 = 186985) (by norm_num)
theorem B472969 : Blo 439778 472969 := bbase (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) (by norm_num)
theorem B472973 : Blo 439778 472973 := bbase (se 3 (by rfl) ⟨88682, by rfl⟩ : syracuseStep 472973 = 177365) (by norm_num)
theorem B1062845 : Blo 439778 1062845 := bbase (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) (by norm_num)
theorem B505801 : Blo 439778 505801 := bbase (se 2 (by rfl) ⟨189675, by rfl⟩ : syracuseStep 505801 = 379351) (by norm_num)
theorem B997325 : Blo 439778 997325 := bbase (se 3 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 997325 = 373997) (by norm_num)
theorem B604157 : Blo 439778 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B2242565 : Blo 439778 2242565 := bbase (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) (by norm_num)
theorem B997397 : Blo 439778 997397 := bbase (se 6 (by rfl) ⟨23376, by rfl⟩ : syracuseStep 997397 = 46753) (by norm_num)
theorem B997469 : Blo 439778 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B1259621 : Blo 439778 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B2275445 : Blo 439778 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B1063037 : Blo 439778 1063037 := bbase (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) (by norm_num)
theorem B997541 : Blo 439778 997541 := bbase (se 4 (by rfl) ⟨93519, by rfl⟩ : syracuseStep 997541 = 187039) (by norm_num)
theorem B1063133 : Blo 439778 1063133 := bbase (se 3 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 1063133 = 398675) (by norm_num)
theorem B997613 : Blo 439778 997613 := bbase (se 3 (by rfl) ⟨187052, by rfl⟩ : syracuseStep 997613 = 374105) (by norm_num)
theorem B1489157 : Blo 439778 1489157 := bbase (se 4 (by rfl) ⟨139608, by rfl⟩ : syracuseStep 1489157 = 279217) (by norm_num)
theorem B1128725 : Blo 439778 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B997685 : Blo 439778 997685 := bbase (se 5 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 997685 = 93533) (by norm_num)
theorem B997757 : Blo 439778 997757 := bbase (se 3 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 997757 = 374159) (by norm_num)
theorem B473537 : Blo 439778 473537 := bbase (se 2 (by rfl) ⟨177576, by rfl⟩ : syracuseStep 473537 = 355153) (by norm_num)
theorem B997829 : Blo 439778 997829 := bbase (se 4 (by rfl) ⟨93546, by rfl⟩ : syracuseStep 997829 = 187093) (by norm_num)
theorem B1882597 : Blo 439778 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B997901 : Blo 439778 997901 := bbase (se 3 (by rfl) ⟨187106, by rfl⟩ : syracuseStep 997901 = 374213) (by norm_num)
theorem B2767445 : Blo 439778 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B997973 : Blo 439778 997973 := bbase (se 8 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 997973 = 11695) (by norm_num)
theorem B473725 : Blo 439778 473725 := bbase (se 3 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 473725 = 177647) (by norm_num)
theorem B998045 : Blo 439778 998045 := bbase (se 3 (by rfl) ⟨187133, by rfl⟩ : syracuseStep 998045 = 374267) (by norm_num)
theorem B1489589 : Blo 439778 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B998117 : Blo 439778 998117 := bbase (se 4 (by rfl) ⟨93573, by rfl⟩ : syracuseStep 998117 = 187147) (by norm_num)
theorem B998189 : Blo 439778 998189 := bbase (se 3 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 998189 = 374321) (by norm_num)
theorem B1260373 : Blo 439778 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B998261 : Blo 439778 998261 := bbase (se 5 (by rfl) ⟨46793, by rfl⟩ : syracuseStep 998261 = 93587) (by norm_num)
theorem B998333 : Blo 439778 998333 := bbase (se 3 (by rfl) ⟨187187, by rfl⟩ : syracuseStep 998333 = 374375) (by norm_num)
theorem B670709 : Blo 439778 670709 := bbase (se 5 (by rfl) ⟨31439, by rfl⟩ : syracuseStep 670709 = 62879) (by norm_num)
theorem B998405 : Blo 439778 998405 := bbase (se 4 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 998405 = 187201) (by norm_num)
theorem B998477 : Blo 439778 998477 := bbase (se 3 (by rfl) ⟨187214, by rfl⟩ : syracuseStep 998477 = 374429) (by norm_num)
theorem B1490021 : Blo 439778 1490021 := bbase (se 4 (by rfl) ⟨139689, by rfl⟩ : syracuseStep 1490021 = 279379) (by norm_num)
theorem B2243861 : Blo 439778 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B834941 : Blo 439778 834941 := bbase (se 3 (by rfl) ⟨156551, by rfl⟩ : syracuseStep 834941 = 313103) (by norm_num)
theorem B835085 : Blo 439778 835085 := bbase (se 3 (by rfl) ⟨156578, by rfl⟩ : syracuseStep 835085 = 313157) (by norm_num)
theorem B1490453 : Blo 439778 1490453 := bbase (se 6 (by rfl) ⟨34932, by rfl⟩ : syracuseStep 1490453 = 69865) (by norm_num)
theorem B2014789 : Blo 439778 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B1785509 : Blo 439778 1785509 := bbase (se 4 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 1785509 = 334783) (by norm_num)
theorem B2014901 : Blo 439778 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B835373 : Blo 439778 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B835525 : Blo 439778 835525 := bbase (se 4 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 835525 = 156661) (by norm_num)
theorem B1490885 : Blo 439778 1490885 := bbase (se 4 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 1490885 = 279541) (by norm_num)
theorem B2015189 : Blo 439778 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B704533 : Blo 439778 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B835829 : Blo 439778 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B1491317 : Blo 439778 1491317 := bbase (se 5 (by rfl) ⟨69905, by rfl⟩ : syracuseStep 1491317 = 139811) (by norm_num)
theorem B1589653 : Blo 439778 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1130917 : Blo 439778 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B2245157 : Blo 439778 2245157 := bbase (se 4 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 2245157 = 420967) (by norm_num)
theorem B1065565 : Blo 439778 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B705205 : Blo 439778 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B672509 : Blo 439778 672509 := bbase (se 3 (by rfl) ⟨126095, by rfl⟩ : syracuseStep 672509 = 252191) (by norm_num)
theorem B1491749 : Blo 439778 1491749 := bbase (se 4 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 1491749 = 279703) (by norm_num)
theorem B2507669 : Blo 439778 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B1065901 : Blo 439778 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B836581 : Blo 439778 836581 := bbase (se 4 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 836581 = 156859) (by norm_num)
theorem B574465 : Blo 439778 574465 := bbase (se 2 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 574465 = 430849) (by norm_num)
theorem B967717 : Blo 439778 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B836725 : Blo 439778 836725 := bbase (se 5 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 836725 = 78443) (by norm_num)
theorem B1492181 : Blo 439778 1492181 := bbase (se 7 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 1492181 = 34973) (by norm_num)
theorem B836885 : Blo 439778 836885 := bbase (se 6 (by rfl) ⟨19614, by rfl⟩ : syracuseStep 836885 = 39229) (by norm_num)
theorem B1885589 : Blo 439778 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B837029 : Blo 439778 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B574921 : Blo 439778 574921 := bbase (se 2 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 574921 = 431191) (by norm_num)
theorem B10765781 : Blo 439778 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B1263221 : Blo 439778 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B1492613 : Blo 439778 1492613 := bbase (se 4 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 1492613 = 279865) (by norm_num)
theorem B706205 : Blo 439778 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B837317 : Blo 439778 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B673525 : Blo 439778 673525 := bbase (se 5 (by rfl) ⟨31571, by rfl⟩ : syracuseStep 673525 = 63143) (by norm_num)
theorem B2246453 : Blo 439778 2246453 := bbase (se 5 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 2246453 = 210605) (by norm_num)
theorem B837469 : Blo 439778 837469 := bbase (se 3 (by rfl) ⟨157025, by rfl⟩ : syracuseStep 837469 = 314051) (by norm_num)
theorem B2508853 : Blo 439778 2508853 := bbase (se 5 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 2508853 = 235205) (by norm_num)
theorem B1493045 : Blo 439778 1493045 := bbase (se 5 (by rfl) ⟨69986, by rfl⟩ : syracuseStep 1493045 = 139973) (by norm_num)
theorem B1198165 : Blo 439778 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B837773 : Blo 439778 837773 := bbase (se 3 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 837773 = 314165) (by norm_num)
theorem B1886597 : Blo 439778 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B1198469 : Blo 439778 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B1493477 : Blo 439778 1493477 := bbase (se 4 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 1493477 = 280027) (by norm_num)
theorem B1198709 : Blo 439778 1198709 := bbase (se 5 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 1198709 = 112379) (by norm_num)
theorem B8506133 : Blo 439778 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B838525 : Blo 439778 838525 := bbase (se 3 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 838525 = 314447) (by norm_num)
theorem B543629 : Blo 439778 543629 := bbase (se 3 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 543629 = 203861) (by norm_num)
theorem B1493909 : Blo 439778 1493909 := bbase (se 6 (by rfl) ⟨35013, by rfl⟩ : syracuseStep 1493909 = 70027) (by norm_num)
theorem B2837429 : Blo 439778 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B838669 : Blo 439778 838669 := bbase (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) (by norm_num)
theorem B707717 : Blo 439778 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B838829 : Blo 439778 838829 := bbase (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) (by norm_num)
theorem B2018533 : Blo 439778 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B1592581 : Blo 439778 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B2379029 : Blo 439778 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B838973 : Blo 439778 838973 := bbase (se 3 (by rfl) ⟨157307, by rfl⟩ : syracuseStep 838973 = 314615) (by norm_num)
theorem B1494341 : Blo 439778 1494341 := bbase (se 4 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 1494341 = 280189) (by norm_num)
theorem B2870741 : Blo 439778 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B708173 : Blo 439778 708173 := bbase (se 3 (by rfl) ⟨132782, by rfl⟩ : syracuseStep 708173 = 265565) (by norm_num)
theorem B839261 : Blo 439778 839261 := bbase (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) (by norm_num)
theorem B839413 : Blo 439778 839413 := bbase (se 5 (by rfl) ⟨39347, by rfl⟩ : syracuseStep 839413 = 78695) (by norm_num)
theorem B1494773 : Blo 439778 1494773 := bbase (se 5 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 1494773 = 140135) (by norm_num)
theorem B2117461 : Blo 439778 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B5820245 : Blo 439778 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B479081 : Blo 439778 479081 := bbase (se 2 (by rfl) ⟨179655, by rfl⟩ : syracuseStep 479081 = 359311) (by norm_num)
theorem B905069 : Blo 439778 905069 := bbase (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) (by norm_num)
theorem B446357 : Blo 439778 446357 := bbase (se 6 (by rfl) ⟨10461, by rfl⟩ : syracuseStep 446357 = 20923) (by norm_num)
theorem B2510837 : Blo 439778 2510837 := bbase (se 5 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 2510837 = 235391) (by norm_num)
theorem B8572949 : Blo 439778 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B839717 : Blo 439778 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B1888373 : Blo 439778 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B1495205 : Blo 439778 1495205 := bbase (se 4 (by rfl) ⟨140175, by rfl⟩ : syracuseStep 1495205 = 280351) (by norm_num)
theorem B446693 : Blo 439778 446693 := bbase (se 4 (by rfl) ⟨41877, by rfl⟩ : syracuseStep 446693 = 83755) (by norm_num)
theorem B512345 : Blo 439778 512345 := bbase (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) (by norm_num)
theorem B446953 : Blo 439778 446953 := bbase (se 2 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 446953 = 335215) (by norm_num)
theorem B709165 : Blo 439778 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B1495637 : Blo 439778 1495637 := bbase (se 8 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 1495637 = 17527) (by norm_num)
theorem B840469 : Blo 439778 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B3363605 : Blo 439778 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B742189 : Blo 439778 742189 := bbase (se 3 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 742189 = 278321) (by norm_num)
theorem B742277 : Blo 439778 742277 := bbase (se 4 (by rfl) ⟨69588, by rfl⟩ : syracuseStep 742277 = 139177) (by norm_num)
theorem B840613 : Blo 439778 840613 := bbase (se 4 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 840613 = 157615) (by norm_num)
theorem B742405 : Blo 439778 742405 := bbase (se 4 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 742405 = 139201) (by norm_num)
theorem B1496069 : Blo 439778 1496069 := bbase (se 4 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 1496069 = 280513) (by norm_num)
theorem B2020373 : Blo 439778 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B840773 : Blo 439778 840773 := bbase (se 4 (by rfl) ⟨78822, by rfl⟩ : syracuseStep 840773 = 157645) (by norm_num)
theorem B742493 : Blo 439778 742493 := bbase (se 3 (by rfl) ⟨139217, by rfl⟩ : syracuseStep 742493 = 278435) (by norm_num)
theorem B447625 : Blo 439778 447625 := bbase (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) (by norm_num)
theorem B709813 : Blo 439778 709813 := bbase (se 5 (by rfl) ⟨33272, by rfl⟩ : syracuseStep 709813 = 66545) (by norm_num)
theorem B840917 : Blo 439778 840917 := bbase (se 7 (by rfl) ⟨9854, by rfl⟩ : syracuseStep 840917 = 19709) (by norm_num)
theorem B742621 : Blo 439778 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B742709 : Blo 439778 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B447869 : Blo 439778 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B742837 : Blo 439778 742837 := bbase (se 5 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 742837 = 69641) (by norm_num)
theorem B1496501 : Blo 439778 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B841205 : Blo 439778 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B742925 : Blo 439778 742925 := bbase (se 3 (by rfl) ⟨139298, by rfl⟩ : syracuseStep 742925 = 278597) (by norm_num)
theorem B743053 : Blo 439778 743053 := bbase (se 3 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 743053 = 278645) (by norm_num)
theorem B841357 : Blo 439778 841357 := bbase (se 3 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 841357 = 315509) (by norm_num)
theorem B743141 : Blo 439778 743141 := bbase (se 4 (by rfl) ⟨69669, by rfl⟩ : syracuseStep 743141 = 139339) (by norm_num)
theorem B1595189 : Blo 439778 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B743269 : Blo 439778 743269 := bbase (se 4 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 743269 = 139363) (by norm_num)
theorem B1496933 : Blo 439778 1496933 := bbase (se 4 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 1496933 = 280675) (by norm_num)
theorem B743357 : Blo 439778 743357 := bbase (se 3 (by rfl) ⟨139379, by rfl⟩ : syracuseStep 743357 = 278759) (by norm_num)
theorem B841661 : Blo 439778 841661 := bbase (se 3 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 841661 = 315623) (by norm_num)
theorem B448453 : Blo 439778 448453 := bbase (se 4 (by rfl) ⟨42042, by rfl⟩ : syracuseStep 448453 = 84085) (by norm_num)
theorem B1366021 : Blo 439778 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B940061 : Blo 439778 940061 := bbase (se 3 (by rfl) ⟨176261, by rfl⟩ : syracuseStep 940061 = 352523) (by norm_num)
theorem B743485 : Blo 439778 743485 := bbase (se 3 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 743485 = 278807) (by norm_num)
theorem B1595477 : Blo 439778 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710741 : Blo 439778 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B743573 : Blo 439778 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B2513045 : Blo 439778 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B940205 : Blo 439778 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B743701 : Blo 439778 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B1497365 : Blo 439778 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B1136933 : Blo 439778 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B809261 : Blo 439778 809261 := bbase (se 3 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 809261 = 303473) (by norm_num)
theorem B1431893 : Blo 439778 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B743789 : Blo 439778 743789 := bbase (se 3 (by rfl) ⟨139460, by rfl⟩ : syracuseStep 743789 = 278921) (by norm_num)
theorem B743917 : Blo 439778 743917 := bbase (se 3 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 743917 = 278969) (by norm_num)
theorem B940565 : Blo 439778 940565 := bbase (se 6 (by rfl) ⟨22044, by rfl⟩ : syracuseStep 940565 = 44089) (by norm_num)
theorem B744005 : Blo 439778 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B842413 : Blo 439778 842413 := bbase (se 3 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 842413 = 315905) (by norm_num)
theorem B744133 : Blo 439778 744133 := bbase (se 4 (by rfl) ⟨69762, by rfl⟩ : syracuseStep 744133 = 139525) (by norm_num)
theorem B744221 : Blo 439778 744221 := bbase (se 3 (by rfl) ⟨139541, by rfl⟩ : syracuseStep 744221 = 279083) (by norm_num)
theorem B449345 : Blo 439778 449345 := bbase (se 2 (by rfl) ⟨168504, by rfl⟩ : syracuseStep 449345 = 337009) (by norm_num)
theorem B1694533 : Blo 439778 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B744349 : Blo 439778 744349 := bbase (se 3 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 744349 = 279131) (by norm_num)
theorem B744437 : Blo 439778 744437 := bbase (se 5 (by rfl) ⟨34895, by rfl⟩ : syracuseStep 744437 = 69791) (by norm_num)
theorem B744565 : Blo 439778 744565 := bbase (se 5 (by rfl) ⟨34901, by rfl⟩ : syracuseStep 744565 = 69803) (by norm_num)
theorem B449701 : Blo 439778 449701 := bbase (se 4 (by rfl) ⟨42159, by rfl⟩ : syracuseStep 449701 = 84319) (by norm_num)
theorem B744653 : Blo 439778 744653 := bbase (se 3 (by rfl) ⟨139622, by rfl⟩ : syracuseStep 744653 = 279245) (by norm_num)
theorem B3759317 : Blo 439778 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B679133 : Blo 439778 679133 := bbase (se 3 (by rfl) ⟨127337, by rfl⟩ : syracuseStep 679133 = 254675) (by norm_num)
theorem B744781 : Blo 439778 744781 := bbase (se 3 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 744781 = 279293) (by norm_num)
theorem B941453 : Blo 439778 941453 := bbase (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) (by norm_num)
theorem B744869 : Blo 439778 744869 := bbase (se 4 (by rfl) ⟨69831, by rfl⟩ : syracuseStep 744869 = 139663) (by norm_num)
theorem B482737 : Blo 439778 482737 := bbase (se 2 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 482737 = 362053) (by norm_num)
theorem B744997 : Blo 439778 744997 := bbase (se 4 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 744997 = 139687) (by norm_num)
theorem B2022965 : Blo 439778 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B745085 : Blo 439778 745085 := bbase (se 3 (by rfl) ⟨139703, by rfl⟩ : syracuseStep 745085 = 279407) (by norm_num)
theorem B941701 : Blo 439778 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B745213 : Blo 439778 745213 := bbase (se 3 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 745213 = 279455) (by norm_num)
theorem B1072981 : Blo 439778 1072981 := bbase (se 9 (by rfl) ⟨3143, by rfl⟩ : syracuseStep 1072981 = 6287) (by norm_num)
theorem B745301 : Blo 439778 745301 := bbase (se 9 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 745301 = 4367) (by norm_num)
theorem B1269605 : Blo 439778 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B2121653 : Blo 439778 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B1138637 : Blo 439778 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B745429 : Blo 439778 745429 := bbase (se 7 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 745429 = 17471) (by norm_num)
theorem B745517 : Blo 439778 745517 := bbase (se 3 (by rfl) ⟨139784, by rfl⟩ : syracuseStep 745517 = 279569) (by norm_num)
theorem B942205 : Blo 439778 942205 := bbase (se 3 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 942205 = 353327) (by norm_num)
theorem B745645 : Blo 439778 745645 := bbase (se 3 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 745645 = 279617) (by norm_num)
theorem B745733 : Blo 439778 745733 := bbase (se 4 (by rfl) ⟨69912, by rfl⟩ : syracuseStep 745733 = 139825) (by norm_num)
theorem B1892645 : Blo 439778 1892645 := bbase (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) (by norm_num)
theorem B745861 : Blo 439778 745861 := bbase (se 4 (by rfl) ⟨69924, by rfl⟩ : syracuseStep 745861 = 139849) (by norm_num)
theorem B2384309 : Blo 439778 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B745949 : Blo 439778 745949 := bbase (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) (by norm_num)
theorem B1073645 : Blo 439778 1073645 := bbase (se 3 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 1073645 = 402617) (by norm_num)
theorem B2843221 : Blo 439778 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B746077 : Blo 439778 746077 := bbase (se 3 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 746077 = 279779) (by norm_num)
theorem B746165 : Blo 439778 746165 := bbase (se 5 (by rfl) ⟨34976, by rfl⟩ : syracuseStep 746165 = 69953) (by norm_num)
theorem B746293 : Blo 439778 746293 := bbase (se 5 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 746293 = 69965) (by norm_num)
theorem B746381 : Blo 439778 746381 := bbase (se 3 (by rfl) ⟨139946, by rfl⟩ : syracuseStep 746381 = 279893) (by norm_num)
theorem B943093 : Blo 439778 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B746509 : Blo 439778 746509 := bbase (se 3 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 746509 = 279941) (by norm_num)
theorem B746597 : Blo 439778 746597 := bbase (se 4 (by rfl) ⟨69993, by rfl⟩ : syracuseStep 746597 = 139987) (by norm_num)
theorem B746725 : Blo 439778 746725 := bbase (se 4 (by rfl) ⟨70005, by rfl⟩ : syracuseStep 746725 = 140011) (by norm_num)
theorem B746813 : Blo 439778 746813 := bbase (se 3 (by rfl) ⟨140027, by rfl⟩ : syracuseStep 746813 = 280055) (by norm_num)
theorem B714101 : Blo 439778 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B7562645 : Blo 439778 7562645 := bbase (se 6 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 7562645 = 354499) (by norm_num)
theorem B746941 : Blo 439778 746941 := bbase (se 3 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 746941 = 280103) (by norm_num)
theorem B943589 : Blo 439778 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B747029 : Blo 439778 747029 := bbase (se 6 (by rfl) ⟨17508, by rfl⟩ : syracuseStep 747029 = 35017) (by norm_num)
theorem B747157 : Blo 439778 747157 := bbase (se 6 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 747157 = 35023) (by norm_num)
theorem B1271477 : Blo 439778 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B747245 : Blo 439778 747245 := bbase (se 3 (by rfl) ⟨140108, by rfl⟩ : syracuseStep 747245 = 280217) (by norm_num)
theorem B747373 : Blo 439778 747373 := bbase (se 3 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 747373 = 280265) (by norm_num)
theorem B747461 : Blo 439778 747461 := bbase (se 4 (by rfl) ⟨70074, by rfl⟩ : syracuseStep 747461 = 140149) (by norm_num)
theorem B1894421 : Blo 439778 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B747589 : Blo 439778 747589 := bbase (se 4 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 747589 = 140173) (by norm_num)
theorem B911477 : Blo 439778 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B747677 : Blo 439778 747677 := bbase (se 3 (by rfl) ⟨140189, by rfl⟩ : syracuseStep 747677 = 280379) (by norm_num)
theorem B1337573 : Blo 439778 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1894661 : Blo 439778 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B747805 : Blo 439778 747805 := bbase (se 3 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 747805 = 280427) (by norm_num)
theorem B944477 : Blo 439778 944477 := bbase (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) (by norm_num)
theorem B1272181 : Blo 439778 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B747893 : Blo 439778 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B944597 : Blo 439778 944597 := bbase (se 7 (by rfl) ⟨11069, by rfl⟩ : syracuseStep 944597 = 22139) (by norm_num)
theorem B748021 : Blo 439778 748021 := bbase (se 5 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 748021 = 70127) (by norm_num)
theorem B748109 : Blo 439778 748109 := bbase (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) (by norm_num)
theorem B748237 : Blo 439778 748237 := bbase (se 3 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 748237 = 280589) (by norm_num)
theorem B1338133 : Blo 439778 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B748325 : Blo 439778 748325 := bbase (se 4 (by rfl) ⟨70155, by rfl⟩ : syracuseStep 748325 = 140311) (by norm_num)
theorem B748453 : Blo 439778 748453 := bbase (se 4 (by rfl) ⟨70167, by rfl⟩ : syracuseStep 748453 = 140335) (by norm_num)
theorem B748541 : Blo 439778 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1534997 : Blo 439778 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B945229 : Blo 439778 945229 := bbase (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) (by norm_num)
theorem B748669 : Blo 439778 748669 := bbase (se 3 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 748669 = 280751) (by norm_num)
theorem B748757 : Blo 439778 748757 := bbase (se 7 (by rfl) ⟨8774, by rfl⟩ : syracuseStep 748757 = 17549) (by norm_num)
theorem B847325 : Blo 439778 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B946117 : Blo 439778 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B946237 : Blo 439778 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B946493 : Blo 439778 946493 := bbase (se 3 (by rfl) ⟨177467, by rfl⟩ : syracuseStep 946493 = 354935) (by norm_num)
theorem B1274869 : Blo 439778 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B5043221 : Blo 439778 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B947381 : Blo 439778 947381 := bbase (se 5 (by rfl) ⟨44408, by rfl⟩ : syracuseStep 947381 = 88817) (by norm_num)
theorem B947621 : Blo 439778 947621 := bbase (se 4 (by rfl) ⟨88839, by rfl⟩ : syracuseStep 947621 = 177679) (by norm_num)
theorem B718309 : Blo 439778 718309 := bbase (se 4 (by rfl) ⟨67341, by rfl⟩ : syracuseStep 718309 = 134683) (by norm_num)
theorem B3340277 : Blo 439778 3340277 := bbase (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) (by norm_num)
theorem B1079957 : Blo 439778 1079957 := bbase (se 6 (by rfl) ⟨25311, by rfl⟩ : syracuseStep 1079957 = 50623) (by norm_num)
theorem B2227013 : Blo 439778 2227013 := bbase (se 4 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 2227013 = 417565) (by norm_num)
theorem B1440661 : Blo 439778 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B3177461 : Blo 439778 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B3767381 : Blo 439778 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B752789 : Blo 439778 752789 := bbase (se 6 (by rfl) ⟨17643, by rfl⟩ : syracuseStep 752789 = 35287) (by norm_num)
theorem B1113365 : Blo 439778 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B752933 : Blo 439778 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B753029 : Blo 439778 753029 := bbase (se 4 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 753029 = 141193) (by norm_num)
theorem B1113709 : Blo 439778 1113709 := bbase (se 3 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 1113709 = 417641) (by norm_num)
theorem B556733 : Blo 439778 556733 := bbase (se 3 (by rfl) ⟨104387, by rfl⟩ : syracuseStep 556733 = 208775) (by norm_num)
theorem B1113821 : Blo 439778 1113821 := bbase (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) (by norm_num)
theorem B556789 : Blo 439778 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B2522933 : Blo 439778 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B556885 : Blo 439778 556885 := bbase (se 9 (by rfl) ⟨1631, by rfl⟩ : syracuseStep 556885 = 3263) (by norm_num)
theorem B1703797 : Blo 439778 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B1114013 : Blo 439778 1114013 := bbase (se 3 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 1114013 = 417755) (by norm_num)
theorem B557219 : Blo 439778 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B1114307 : Blo 439778 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B1114499 : Blo 439778 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1507889 : Blo 439778 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1671779 : Blo 439778 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B557923 : Blo 439778 557923 := bstep (se 1 (by rfl) ⟨418442, by rfl⟩ : syracuseStep 557923 = 836885) B836885
theorem B558019 : Blo 439778 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B7177187 : Blo 439778 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B8487989 : Blo 439778 8487989 := bstep (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) B795749
theorem B5178595 : Blo 439778 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B1672433 : Blo 439778 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1115441 : Blo 439778 1115441 := bstep (se 2 (by rfl) ⟨418290, by rfl⟩ : syracuseStep 1115441 = 836581) B836581
theorem B1115491 : Blo 439778 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B558515 : Blo 439778 558515 := bstep (se 1 (by rfl) ⟨418886, by rfl⟩ : syracuseStep 558515 = 837773) B837773
theorem B6358499 : Blo 439778 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B1115633 : Blo 439778 1115633 := bstep (se 2 (by rfl) ⟨418362, by rfl⟩ : syracuseStep 1115633 = 836725) B836725
theorem B3769841 : Blo 439778 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B1410605 : Blo 439778 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B5670755 : Blo 439778 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B1411025 : Blo 439778 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B559219 : Blo 439778 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B1050769 : Blo 439778 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B559315 : Blo 439778 559315 := bstep (se 1 (by rfl) ⟨419486, by rfl⟩ : syracuseStep 559315 = 838973) B838973
theorem B2230577 : Blo 439778 2230577 := bstep (se 2 (by rfl) ⟨836466, by rfl⟩ : syracuseStep 2230577 = 1672933) B1672933
theorem B1149265 : Blo 439778 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B1116625 : Blo 439778 1116625 := bstep (se 2 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 1116625 = 837469) B837469
theorem B1673891 : Blo 439778 1673891 := bstep (se 1 (by rfl) ⟨1255418, by rfl⟩ : syracuseStep 1673891 = 2510837) B2510837
theorem B1673905 : Blo 439778 1673905 := bstep (se 2 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 1673905 = 1255429) B1255429
theorem B559811 : Blo 439778 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B1116899 : Blo 439778 1116899 := bstep (se 1 (by rfl) ⟨837674, by rfl⟩ : syracuseStep 1116899 = 1675349) B1675349
theorem B3345137 : Blo 439778 3345137 := bstep (se 2 (by rfl) ⟨1254426, by rfl⟩ : syracuseStep 3345137 = 2508853) B2508853
theorem B1117091 : Blo 439778 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B2526349 : Blo 439778 2526349 := bstep (se 3 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 2526349 = 947381) B947381
theorem B3017969 : Blo 439778 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B494851 : Blo 439778 494851 := bstep (se 1 (by rfl) ⟨371138, by rfl⟩ : syracuseStep 494851 = 742277) B742277
theorem B1346915 : Blo 439778 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B560515 : Blo 439778 560515 := bstep (se 1 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 560515 = 840773) B840773
theorem B494995 : Blo 439778 494995 := bstep (se 1 (by rfl) ⟨371246, by rfl⟩ : syracuseStep 494995 = 742493) B742493
theorem B3018161 : Blo 439778 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B560611 : Blo 439778 560611 := bstep (se 1 (by rfl) ⟨420458, by rfl⟩ : syracuseStep 560611 = 840917) B840917
theorem B626177 : Blo 439778 626177 := bstep (se 2 (by rfl) ⟨234816, by rfl⟩ : syracuseStep 626177 = 469633) B469633
theorem B495139 : Blo 439778 495139 := bstep (se 1 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 495139 = 742709) B742709
theorem B1904269 : Blo 439778 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B495283 : Blo 439778 495283 := bstep (se 1 (by rfl) ⟨371462, by rfl⟩ : syracuseStep 495283 = 742925) B742925
theorem B2232035 : Blo 439778 2232035 := bstep (se 1 (by rfl) ⟨1674026, by rfl⟩ : syracuseStep 2232035 = 3348053) B3348053
theorem B495427 : Blo 439778 495427 := bstep (se 1 (by rfl) ⟨371570, by rfl⟩ : syracuseStep 495427 = 743141) B743141
theorem B1118033 : Blo 439778 1118033 := bstep (se 2 (by rfl) ⟨419262, by rfl⟩ : syracuseStep 1118033 = 838525) B838525
theorem B1118083 : Blo 439778 1118083 := bstep (se 1 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 1118083 = 1677125) B1677125
theorem B495571 : Blo 439778 495571 := bstep (se 1 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 495571 = 743357) B743357
theorem B561107 : Blo 439778 561107 := bstep (se 1 (by rfl) ⟨420830, by rfl⟩ : syracuseStep 561107 = 841661) B841661
theorem B1118225 : Blo 439778 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B626707 : Blo 439778 626707 := bstep (se 1 (by rfl) ⟨470030, by rfl⟩ : syracuseStep 626707 = 940061) B940061
theorem B495715 : Blo 439778 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B1675363 : Blo 439778 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B757955 : Blo 439778 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B659681 : Blo 439778 659681 := bstep (se 2 (by rfl) ⟨247380, by rfl⟩ : syracuseStep 659681 = 494761) B494761
theorem B954595 : Blo 439778 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B659699 : Blo 439778 659699 := bstep (se 1 (by rfl) ⟨494774, by rfl⟩ : syracuseStep 659699 = 989549) B989549
theorem B495859 : Blo 439778 495859 := bstep (se 1 (by rfl) ⟨371894, by rfl⟩ : syracuseStep 495859 = 743789) B743789
theorem B659729 : Blo 439778 659729 := bstep (se 2 (by rfl) ⟨247398, by rfl⟩ : syracuseStep 659729 = 494797) B494797
theorem B659747 : Blo 439778 659747 := bstep (se 1 (by rfl) ⟨494810, by rfl⟩ : syracuseStep 659747 = 989621) B989621
theorem B2691377 : Blo 439778 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B659777 : Blo 439778 659777 := bstep (se 2 (by rfl) ⟨247416, by rfl⟩ : syracuseStep 659777 = 494833) B494833
theorem B659795 : Blo 439778 659795 := bstep (se 1 (by rfl) ⟨494846, by rfl⟩ : syracuseStep 659795 = 989693) B989693
theorem B627043 : Blo 439778 627043 := bstep (se 1 (by rfl) ⟨470282, by rfl⟩ : syracuseStep 627043 = 940565) B940565
theorem B659825 : Blo 439778 659825 := bstep (se 2 (by rfl) ⟨247434, by rfl⟩ : syracuseStep 659825 = 494869) B494869
theorem B659843 : Blo 439778 659843 := bstep (se 1 (by rfl) ⟨494882, by rfl⟩ : syracuseStep 659843 = 989765) B989765
theorem B496003 : Blo 439778 496003 := bstep (se 1 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 496003 = 744005) B744005
theorem B659873 : Blo 439778 659873 := bstep (se 2 (by rfl) ⟨247452, by rfl⟩ : syracuseStep 659873 = 494905) B494905
theorem B659891 : Blo 439778 659891 := bstep (se 1 (by rfl) ⟨494918, by rfl⟩ : syracuseStep 659891 = 989837) B989837
theorem B659921 : Blo 439778 659921 := bstep (se 2 (by rfl) ⟨247470, by rfl⟩ : syracuseStep 659921 = 494941) B494941
theorem B659939 : Blo 439778 659939 := bstep (se 1 (by rfl) ⟨494954, by rfl⟩ : syracuseStep 659939 = 989909) B989909
theorem B659969 : Blo 439778 659969 := bstep (se 2 (by rfl) ⟨247488, by rfl⟩ : syracuseStep 659969 = 494977) B494977
theorem B2232845 : Blo 439778 2232845 := bstep (se 3 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 2232845 = 837317) B837317
theorem B659987 : Blo 439778 659987 := bstep (se 1 (by rfl) ⟨494990, by rfl⟩ : syracuseStep 659987 = 989981) B989981
theorem B496147 : Blo 439778 496147 := bstep (se 1 (by rfl) ⟨372110, by rfl⟩ : syracuseStep 496147 = 744221) B744221
theorem B660017 : Blo 439778 660017 := bstep (se 2 (by rfl) ⟨247506, by rfl⟩ : syracuseStep 660017 = 495013) B495013
theorem B660035 : Blo 439778 660035 := bstep (se 1 (by rfl) ⟨495026, by rfl⟩ : syracuseStep 660035 = 990053) B990053
theorem B660065 : Blo 439778 660065 := bstep (se 2 (by rfl) ⟨247524, by rfl⟩ : syracuseStep 660065 = 495049) B495049
theorem B660083 : Blo 439778 660083 := bstep (se 1 (by rfl) ⟨495062, by rfl⟩ : syracuseStep 660083 = 990125) B990125
theorem B660113 : Blo 439778 660113 := bstep (se 2 (by rfl) ⟨247542, by rfl⟩ : syracuseStep 660113 = 495085) B495085
theorem B660131 : Blo 439778 660131 := bstep (se 1 (by rfl) ⟨495098, by rfl⟩ : syracuseStep 660131 = 990197) B990197
theorem B496291 : Blo 439778 496291 := bstep (se 1 (by rfl) ⟨372218, by rfl⟩ : syracuseStep 496291 = 744437) B744437
theorem B660161 : Blo 439778 660161 := bstep (se 2 (by rfl) ⟨247560, by rfl⟩ : syracuseStep 660161 = 495121) B495121
theorem B660179 : Blo 439778 660179 := bstep (se 1 (by rfl) ⟨495134, by rfl⟩ : syracuseStep 660179 = 990269) B990269
theorem B660209 : Blo 439778 660209 := bstep (se 2 (by rfl) ⟨247578, by rfl⟩ : syracuseStep 660209 = 495157) B495157
theorem B660227 : Blo 439778 660227 := bstep (se 1 (by rfl) ⟨495170, by rfl⟩ : syracuseStep 660227 = 990341) B990341
theorem B660257 : Blo 439778 660257 := bstep (se 2 (by rfl) ⟨247596, by rfl⟩ : syracuseStep 660257 = 495193) B495193
theorem B660275 : Blo 439778 660275 := bstep (se 1 (by rfl) ⟨495206, by rfl⟩ : syracuseStep 660275 = 990413) B990413
theorem B496435 : Blo 439778 496435 := bstep (se 1 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 496435 = 744653) B744653
theorem B660305 : Blo 439778 660305 := bstep (se 2 (by rfl) ⟨247614, by rfl⟩ : syracuseStep 660305 = 495229) B495229
theorem B660323 : Blo 439778 660323 := bstep (se 1 (by rfl) ⟨495242, by rfl⟩ : syracuseStep 660323 = 990485) B990485
theorem B660353 : Blo 439778 660353 := bstep (se 2 (by rfl) ⟨247632, by rfl⟩ : syracuseStep 660353 = 495265) B495265
theorem B627601 : Blo 439778 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B660371 : Blo 439778 660371 := bstep (se 1 (by rfl) ⟨495278, by rfl⟩ : syracuseStep 660371 = 990557) B990557
theorem B660401 : Blo 439778 660401 := bstep (se 2 (by rfl) ⟨247650, by rfl⟩ : syracuseStep 660401 = 495301) B495301
theorem B627635 : Blo 439778 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B660419 : Blo 439778 660419 := bstep (se 1 (by rfl) ⟨495314, by rfl⟩ : syracuseStep 660419 = 990629) B990629
theorem B496579 : Blo 439778 496579 := bstep (se 1 (by rfl) ⟨372434, by rfl⟩ : syracuseStep 496579 = 744869) B744869
theorem B3019717 : Blo 439778 3019717 := bstep (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) B566197
theorem B660449 : Blo 439778 660449 := bstep (se 2 (by rfl) ⟨247668, by rfl⟩ : syracuseStep 660449 = 495337) B495337
theorem B1119217 : Blo 439778 1119217 := bstep (se 2 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 1119217 = 839413) B839413
theorem B594931 : Blo 439778 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B660467 : Blo 439778 660467 := bstep (se 1 (by rfl) ⟨495350, by rfl⟩ : syracuseStep 660467 = 990701) B990701
theorem B660497 : Blo 439778 660497 := bstep (se 2 (by rfl) ⟨247686, by rfl⟩ : syracuseStep 660497 = 495373) B495373
theorem B660515 : Blo 439778 660515 := bstep (se 1 (by rfl) ⟨495386, by rfl⟩ : syracuseStep 660515 = 990773) B990773
theorem B1348643 : Blo 439778 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B660545 : Blo 439778 660545 := bstep (se 2 (by rfl) ⟨247704, by rfl⟩ : syracuseStep 660545 = 495409) B495409
theorem B660563 : Blo 439778 660563 := bstep (se 1 (by rfl) ⟨495422, by rfl⟩ : syracuseStep 660563 = 990845) B990845
theorem B496723 : Blo 439778 496723 := bstep (se 1 (by rfl) ⟨372542, by rfl⟩ : syracuseStep 496723 = 745085) B745085
theorem B660593 : Blo 439778 660593 := bstep (se 2 (by rfl) ⟨247722, by rfl⟩ : syracuseStep 660593 = 495445) B495445
theorem B2823281 : Blo 439778 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B660611 : Blo 439778 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B660641 : Blo 439778 660641 := bstep (se 2 (by rfl) ⟨247740, by rfl⟩ : syracuseStep 660641 = 495481) B495481
theorem B660659 : Blo 439778 660659 := bstep (se 1 (by rfl) ⟨495494, by rfl⟩ : syracuseStep 660659 = 990989) B990989
theorem B660689 : Blo 439778 660689 := bstep (se 2 (by rfl) ⟨247758, by rfl⟩ : syracuseStep 660689 = 495517) B495517
theorem B660707 : Blo 439778 660707 := bstep (se 1 (by rfl) ⟨495530, by rfl⟩ : syracuseStep 660707 = 991061) B991061
theorem B496867 : Blo 439778 496867 := bstep (se 1 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 496867 = 745301) B745301
theorem B660737 : Blo 439778 660737 := bstep (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) B495553
theorem B1119491 : Blo 439778 1119491 := bstep (se 1 (by rfl) ⟨839618, by rfl⟩ : syracuseStep 1119491 = 1679237) B1679237
theorem B660755 : Blo 439778 660755 := bstep (se 1 (by rfl) ⟨495566, by rfl⟩ : syracuseStep 660755 = 991133) B991133
theorem B1414435 : Blo 439778 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B660785 : Blo 439778 660785 := bstep (se 2 (by rfl) ⟨247794, by rfl⟩ : syracuseStep 660785 = 495589) B495589
theorem B759091 : Blo 439778 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B660803 : Blo 439778 660803 := bstep (se 1 (by rfl) ⟨495602, by rfl⟩ : syracuseStep 660803 = 991205) B991205
theorem B1611085 : Blo 439778 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B660833 : Blo 439778 660833 := bstep (se 2 (by rfl) ⟨247812, by rfl⟩ : syracuseStep 660833 = 495625) B495625
theorem B660851 : Blo 439778 660851 := bstep (se 1 (by rfl) ⟨495638, by rfl⟩ : syracuseStep 660851 = 991277) B991277
theorem B497011 : Blo 439778 497011 := bstep (se 1 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 497011 = 745517) B745517
theorem B3020165 : Blo 439778 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B660881 : Blo 439778 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B660899 : Blo 439778 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B660929 : Blo 439778 660929 := bstep (se 2 (by rfl) ⟨247848, by rfl⟩ : syracuseStep 660929 = 495697) B495697
theorem B1119683 : Blo 439778 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B660947 : Blo 439778 660947 := bstep (se 1 (by rfl) ⟨495710, by rfl⟩ : syracuseStep 660947 = 991421) B991421
theorem B628193 : Blo 439778 628193 := bstep (se 2 (by rfl) ⟨235572, by rfl⟩ : syracuseStep 628193 = 471145) B471145
theorem B660977 : Blo 439778 660977 := bstep (se 2 (by rfl) ⟨247866, by rfl⟩ : syracuseStep 660977 = 495733) B495733
theorem B660995 : Blo 439778 660995 := bstep (se 1 (by rfl) ⟨495746, by rfl⟩ : syracuseStep 660995 = 991493) B991493
theorem B497155 : Blo 439778 497155 := bstep (se 1 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 497155 = 745733) B745733
theorem B661025 : Blo 439778 661025 := bstep (se 2 (by rfl) ⟨247884, by rfl⟩ : syracuseStep 661025 = 495769) B495769
theorem B628273 : Blo 439778 628273 := bstep (se 2 (by rfl) ⟨235602, by rfl⟩ : syracuseStep 628273 = 471205) B471205
theorem B1414705 : Blo 439778 1414705 := bstep (se 2 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 1414705 = 1061029) B1061029
theorem B661043 : Blo 439778 661043 := bstep (se 1 (by rfl) ⟨495782, by rfl⟩ : syracuseStep 661043 = 991565) B991565
theorem B661073 : Blo 439778 661073 := bstep (se 2 (by rfl) ⟨247902, by rfl⟩ : syracuseStep 661073 = 495805) B495805
theorem B661091 : Blo 439778 661091 := bstep (se 1 (by rfl) ⟨495818, by rfl⟩ : syracuseStep 661091 = 991637) B991637
theorem B661121 : Blo 439778 661121 := bstep (se 2 (by rfl) ⟨247920, by rfl⟩ : syracuseStep 661121 = 495841) B495841
theorem B661139 : Blo 439778 661139 := bstep (se 1 (by rfl) ⟨495854, by rfl⟩ : syracuseStep 661139 = 991709) B991709
theorem B497299 : Blo 439778 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B661169 : Blo 439778 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B661187 : Blo 439778 661187 := bstep (se 1 (by rfl) ⟨495890, by rfl⟩ : syracuseStep 661187 = 991781) B991781
theorem B661217 : Blo 439778 661217 := bstep (se 2 (by rfl) ⟨247956, by rfl⟩ : syracuseStep 661217 = 495913) B495913
theorem B661235 : Blo 439778 661235 := bstep (se 1 (by rfl) ⟨495926, by rfl⟩ : syracuseStep 661235 = 991853) B991853
theorem B661265 : Blo 439778 661265 := bstep (se 2 (by rfl) ⟨247974, by rfl⟩ : syracuseStep 661265 = 495949) B495949
theorem B661283 : Blo 439778 661283 := bstep (se 1 (by rfl) ⟨495962, by rfl⟩ : syracuseStep 661283 = 991925) B991925
theorem B497443 : Blo 439778 497443 := bstep (se 1 (by rfl) ⟨373082, by rfl⟩ : syracuseStep 497443 = 746165) B746165
theorem B661313 : Blo 439778 661313 := bstep (se 2 (by rfl) ⟨247992, by rfl⟩ : syracuseStep 661313 = 495985) B495985
theorem B661331 : Blo 439778 661331 := bstep (se 1 (by rfl) ⟨495998, by rfl⟩ : syracuseStep 661331 = 991997) B991997
theorem B661361 : Blo 439778 661361 := bstep (se 2 (by rfl) ⟨248010, by rfl⟩ : syracuseStep 661361 = 496021) B496021
theorem B661379 : Blo 439778 661379 := bstep (se 1 (by rfl) ⟨496034, by rfl⟩ : syracuseStep 661379 = 992069) B992069
theorem B661409 : Blo 439778 661409 := bstep (se 2 (by rfl) ⟨248028, by rfl⟩ : syracuseStep 661409 = 496057) B496057
theorem B661427 : Blo 439778 661427 := bstep (se 1 (by rfl) ⟨496070, by rfl⟩ : syracuseStep 661427 = 992141) B992141
theorem B497587 : Blo 439778 497587 := bstep (se 1 (by rfl) ⟨373190, by rfl⟩ : syracuseStep 497587 = 746381) B746381
theorem B661457 : Blo 439778 661457 := bstep (se 2 (by rfl) ⟨248046, by rfl⟩ : syracuseStep 661457 = 496093) B496093
theorem B595937 : Blo 439778 595937 := bstep (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) B446953
theorem B661475 : Blo 439778 661475 := bstep (se 1 (by rfl) ⟨496106, by rfl⟩ : syracuseStep 661475 = 992213) B992213
theorem B661505 : Blo 439778 661505 := bstep (se 2 (by rfl) ⟨248064, by rfl⟩ : syracuseStep 661505 = 496129) B496129
theorem B661523 : Blo 439778 661523 := bstep (se 1 (by rfl) ⟨496142, by rfl⟩ : syracuseStep 661523 = 992285) B992285
theorem B661553 : Blo 439778 661553 := bstep (se 2 (by rfl) ⟨248082, by rfl⟩ : syracuseStep 661553 = 496165) B496165
theorem B661571 : Blo 439778 661571 := bstep (se 1 (by rfl) ⟨496178, by rfl⟩ : syracuseStep 661571 = 992357) B992357
theorem B497731 : Blo 439778 497731 := bstep (se 1 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 497731 = 746597) B746597
theorem B661601 : Blo 439778 661601 := bstep (se 2 (by rfl) ⟨248100, by rfl⟩ : syracuseStep 661601 = 496201) B496201
theorem B661619 : Blo 439778 661619 := bstep (se 1 (by rfl) ⟨496214, by rfl⟩ : syracuseStep 661619 = 992429) B992429
theorem B661649 : Blo 439778 661649 := bstep (se 2 (by rfl) ⟨248118, by rfl⟩ : syracuseStep 661649 = 496237) B496237
theorem B661667 : Blo 439778 661667 := bstep (se 1 (by rfl) ⟨496250, by rfl⟩ : syracuseStep 661667 = 992501) B992501
theorem B661697 : Blo 439778 661697 := bstep (se 2 (by rfl) ⟨248136, by rfl⟩ : syracuseStep 661697 = 496273) B496273
theorem B2398405 : Blo 439778 2398405 := bstep (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) B449701
theorem B661715 : Blo 439778 661715 := bstep (se 1 (by rfl) ⟨496286, by rfl⟩ : syracuseStep 661715 = 992573) B992573
theorem B497875 : Blo 439778 497875 := bstep (se 1 (by rfl) ⟨373406, by rfl⟩ : syracuseStep 497875 = 746813) B746813
theorem B661745 : Blo 439778 661745 := bstep (se 2 (by rfl) ⟨248154, by rfl⟩ : syracuseStep 661745 = 496309) B496309
theorem B661763 : Blo 439778 661763 := bstep (se 1 (by rfl) ⟨496322, by rfl⟩ : syracuseStep 661763 = 992645) B992645
theorem B1677581 : Blo 439778 1677581 := bstep (se 3 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 1677581 = 629093) B629093
theorem B530707 : Blo 439778 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B661793 : Blo 439778 661793 := bstep (se 2 (by rfl) ⟨248172, by rfl⟩ : syracuseStep 661793 = 496345) B496345
theorem B661811 : Blo 439778 661811 := bstep (se 1 (by rfl) ⟨496358, by rfl⟩ : syracuseStep 661811 = 992717) B992717
theorem B629059 : Blo 439778 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B661841 : Blo 439778 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B661859 : Blo 439778 661859 := bstep (se 1 (by rfl) ⟨496394, by rfl⟩ : syracuseStep 661859 = 992789) B992789
theorem B498019 : Blo 439778 498019 := bstep (se 1 (by rfl) ⟨373514, by rfl⟩ : syracuseStep 498019 = 747029) B747029
theorem B1120625 : Blo 439778 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B661889 : Blo 439778 661889 := bstep (se 2 (by rfl) ⟨248208, by rfl⟩ : syracuseStep 661889 = 496417) B496417
theorem B989585 : Blo 439778 989585 := bstep (se 2 (by rfl) ⟨371094, by rfl⟩ : syracuseStep 989585 = 742189) B742189
theorem B661907 : Blo 439778 661907 := bstep (se 1 (by rfl) ⟨496430, by rfl⟩ : syracuseStep 661907 = 992861) B992861
theorem B1120675 : Blo 439778 1120675 := bstep (se 1 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 1120675 = 1681013) B1681013
theorem B989603 : Blo 439778 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B661937 : Blo 439778 661937 := bstep (se 2 (by rfl) ⟨248226, by rfl⟩ : syracuseStep 661937 = 496453) B496453
theorem B661955 : Blo 439778 661955 := bstep (se 1 (by rfl) ⟨496466, by rfl⟩ : syracuseStep 661955 = 992933) B992933
theorem B661985 : Blo 439778 661985 := bstep (se 2 (by rfl) ⟨248244, by rfl⟩ : syracuseStep 661985 = 496489) B496489
theorem B662003 : Blo 439778 662003 := bstep (se 1 (by rfl) ⟨496502, by rfl⟩ : syracuseStep 662003 = 993005) B993005
theorem B498163 : Blo 439778 498163 := bstep (se 1 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 498163 = 747245) B747245
theorem B662033 : Blo 439778 662033 := bstep (se 2 (by rfl) ⟨248262, by rfl⟩ : syracuseStep 662033 = 496525) B496525
theorem B662051 : Blo 439778 662051 := bstep (se 1 (by rfl) ⟨496538, by rfl⟩ : syracuseStep 662051 = 993077) B993077
theorem B1120817 : Blo 439778 1120817 := bstep (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) B840613
theorem B596531 : Blo 439778 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B662081 : Blo 439778 662081 := bstep (se 2 (by rfl) ⟨248280, by rfl⟩ : syracuseStep 662081 = 496561) B496561
theorem B662099 : Blo 439778 662099 := bstep (se 1 (by rfl) ⟨496574, by rfl⟩ : syracuseStep 662099 = 993149) B993149
theorem B662129 : Blo 439778 662129 := bstep (se 2 (by rfl) ⟨248298, by rfl⟩ : syracuseStep 662129 = 496597) B496597
theorem B662147 : Blo 439778 662147 := bstep (se 1 (by rfl) ⟨496610, by rfl⟩ : syracuseStep 662147 = 993221) B993221
theorem B498307 : Blo 439778 498307 := bstep (se 1 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 498307 = 747461) B747461
theorem B662177 : Blo 439778 662177 := bstep (se 2 (by rfl) ⟨248316, by rfl⟩ : syracuseStep 662177 = 496633) B496633
theorem B989873 : Blo 439778 989873 := bstep (se 2 (by rfl) ⟨371202, by rfl⟩ : syracuseStep 989873 = 742405) B742405
theorem B662195 : Blo 439778 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B989891 : Blo 439778 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B662225 : Blo 439778 662225 := bstep (se 2 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 662225 = 496669) B496669
theorem B662243 : Blo 439778 662243 := bstep (se 1 (by rfl) ⟨496682, by rfl⟩ : syracuseStep 662243 = 993365) B993365
theorem B662273 : Blo 439778 662273 := bstep (se 2 (by rfl) ⟨248352, by rfl⟩ : syracuseStep 662273 = 496705) B496705
theorem B662291 : Blo 439778 662291 := bstep (se 1 (by rfl) ⟨496718, by rfl⟩ : syracuseStep 662291 = 993437) B993437
theorem B498451 : Blo 439778 498451 := bstep (se 1 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 498451 = 747677) B747677
theorem B629537 : Blo 439778 629537 := bstep (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) B472153
theorem B662321 : Blo 439778 662321 := bstep (se 2 (by rfl) ⟨248370, by rfl⟩ : syracuseStep 662321 = 496741) B496741
theorem B662339 : Blo 439778 662339 := bstep (se 1 (by rfl) ⟨496754, by rfl⟩ : syracuseStep 662339 = 993509) B993509
theorem B662369 : Blo 439778 662369 := bstep (se 2 (by rfl) ⟨248388, by rfl⟩ : syracuseStep 662369 = 496777) B496777
theorem B662387 : Blo 439778 662387 := bstep (se 1 (by rfl) ⟨496790, by rfl⟩ : syracuseStep 662387 = 993581) B993581
theorem B662417 : Blo 439778 662417 := bstep (se 2 (by rfl) ⟨248406, by rfl⟩ : syracuseStep 662417 = 496813) B496813
theorem B629651 : Blo 439778 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B662435 : Blo 439778 662435 := bstep (se 1 (by rfl) ⟨496826, by rfl⟩ : syracuseStep 662435 = 993653) B993653
theorem B596899 : Blo 439778 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B498595 : Blo 439778 498595 := bstep (se 1 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 498595 = 747893) B747893
theorem B662465 : Blo 439778 662465 := bstep (se 2 (by rfl) ⟨248424, by rfl⟩ : syracuseStep 662465 = 496849) B496849
theorem B990161 : Blo 439778 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B662483 : Blo 439778 662483 := bstep (se 1 (by rfl) ⟨496862, by rfl⟩ : syracuseStep 662483 = 993725) B993725
theorem B990179 : Blo 439778 990179 := bstep (se 1 (by rfl) ⟨742634, by rfl⟩ : syracuseStep 990179 = 1485269) B1485269
theorem B629731 : Blo 439778 629731 := bstep (se 1 (by rfl) ⟨472298, by rfl⟩ : syracuseStep 629731 = 944597) B944597
theorem B662513 : Blo 439778 662513 := bstep (se 2 (by rfl) ⟨248442, by rfl⟩ : syracuseStep 662513 = 496885) B496885
theorem B662531 : Blo 439778 662531 := bstep (se 1 (by rfl) ⟨496898, by rfl⟩ : syracuseStep 662531 = 993797) B993797
theorem B662561 : Blo 439778 662561 := bstep (se 2 (by rfl) ⟨248460, by rfl⟩ : syracuseStep 662561 = 496921) B496921
theorem B662579 : Blo 439778 662579 := bstep (se 1 (by rfl) ⟨496934, by rfl⟩ : syracuseStep 662579 = 993869) B993869
theorem B498739 : Blo 439778 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B662609 : Blo 439778 662609 := bstep (se 2 (by rfl) ⟨248478, by rfl⟩ : syracuseStep 662609 = 496957) B496957
theorem B662627 : Blo 439778 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B1416305 : Blo 439778 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B662657 : Blo 439778 662657 := bstep (se 2 (by rfl) ⟨248496, by rfl⟩ : syracuseStep 662657 = 496993) B496993
theorem B662675 : Blo 439778 662675 := bstep (se 1 (by rfl) ⟨497006, by rfl⟩ : syracuseStep 662675 = 994013) B994013
theorem B662705 : Blo 439778 662705 := bstep (se 2 (by rfl) ⟨248514, by rfl⟩ : syracuseStep 662705 = 497029) B497029
theorem B662723 : Blo 439778 662723 := bstep (se 1 (by rfl) ⟨497042, by rfl⟩ : syracuseStep 662723 = 994085) B994085
theorem B498883 : Blo 439778 498883 := bstep (se 1 (by rfl) ⟨374162, by rfl⟩ : syracuseStep 498883 = 748325) B748325
theorem B662753 : Blo 439778 662753 := bstep (se 2 (by rfl) ⟨248532, by rfl⟩ : syracuseStep 662753 = 497065) B497065
theorem B990449 : Blo 439778 990449 := bstep (se 2 (by rfl) ⟨371418, by rfl⟩ : syracuseStep 990449 = 742837) B742837
theorem B662771 : Blo 439778 662771 := bstep (se 1 (by rfl) ⟨497078, by rfl⟩ : syracuseStep 662771 = 994157) B994157
theorem B990467 : Blo 439778 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B662801 : Blo 439778 662801 := bstep (se 2 (by rfl) ⟨248550, by rfl⟩ : syracuseStep 662801 = 497101) B497101
theorem B662819 : Blo 439778 662819 := bstep (se 1 (by rfl) ⟨497114, by rfl⟩ : syracuseStep 662819 = 994229) B994229
theorem B957745 : Blo 439778 957745 := bstep (se 2 (by rfl) ⟨359154, by rfl⟩ : syracuseStep 957745 = 718309) B718309
theorem B662849 : Blo 439778 662849 := bstep (se 2 (by rfl) ⟨248568, by rfl⟩ : syracuseStep 662849 = 497137) B497137
theorem B1252685 : Blo 439778 1252685 := bstep (se 3 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 1252685 = 469757) B469757
theorem B662867 : Blo 439778 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B499027 : Blo 439778 499027 := bstep (se 1 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 499027 = 748541) B748541
theorem B1023331 : Blo 439778 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B2235761 : Blo 439778 2235761 := bstep (se 2 (by rfl) ⟨838410, by rfl⟩ : syracuseStep 2235761 = 1676821) B1676821
theorem B662897 : Blo 439778 662897 := bstep (se 2 (by rfl) ⟨248586, by rfl⟩ : syracuseStep 662897 = 497173) B497173
theorem B662915 : Blo 439778 662915 := bstep (se 1 (by rfl) ⟨497186, by rfl⟩ : syracuseStep 662915 = 994373) B994373
theorem B8068493 : Blo 439778 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B662945 : Blo 439778 662945 := bstep (se 2 (by rfl) ⟨248604, by rfl⟩ : syracuseStep 662945 = 497209) B497209
theorem B662963 : Blo 439778 662963 := bstep (se 1 (by rfl) ⟨497222, by rfl⟩ : syracuseStep 662963 = 994445) B994445
theorem B1416653 : Blo 439778 1416653 := bstep (se 3 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 1416653 = 531245) B531245
theorem B662993 : Blo 439778 662993 := bstep (se 2 (by rfl) ⟨248622, by rfl⟩ : syracuseStep 662993 = 497245) B497245
theorem B663011 : Blo 439778 663011 := bstep (se 1 (by rfl) ⟨497258, by rfl⟩ : syracuseStep 663011 = 994517) B994517
theorem B499171 : Blo 439778 499171 := bstep (se 1 (by rfl) ⟨374378, by rfl⟩ : syracuseStep 499171 = 748757) B748757
theorem B663041 : Blo 439778 663041 := bstep (se 2 (by rfl) ⟨248640, by rfl⟩ : syracuseStep 663041 = 497281) B497281
theorem B1252867 : Blo 439778 1252867 := bstep (se 1 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 1252867 = 1879301) B1879301
theorem B2825741 : Blo 439778 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B990737 : Blo 439778 990737 := bstep (se 2 (by rfl) ⟨371526, by rfl⟩ : syracuseStep 990737 = 743053) B743053
theorem B630289 : Blo 439778 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B663059 : Blo 439778 663059 := bstep (se 1 (by rfl) ⟨497294, by rfl⟩ : syracuseStep 663059 = 994589) B994589
theorem B1121809 : Blo 439778 1121809 := bstep (se 2 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 1121809 = 841357) B841357
theorem B990755 : Blo 439778 990755 := bstep (se 1 (by rfl) ⟨743066, by rfl⟩ : syracuseStep 990755 = 1486133) B1486133
theorem B663089 : Blo 439778 663089 := bstep (se 2 (by rfl) ⟨248658, by rfl⟩ : syracuseStep 663089 = 497317) B497317
theorem B663107 : Blo 439778 663107 := bstep (se 1 (by rfl) ⟨497330, by rfl⟩ : syracuseStep 663107 = 994661) B994661
theorem B663137 : Blo 439778 663137 := bstep (se 2 (by rfl) ⟨248676, by rfl⟩ : syracuseStep 663137 = 497353) B497353
theorem B663155 : Blo 439778 663155 := bstep (se 1 (by rfl) ⟨497366, by rfl⟩ : syracuseStep 663155 = 994733) B994733
theorem B663185 : Blo 439778 663185 := bstep (se 2 (by rfl) ⟨248694, by rfl⟩ : syracuseStep 663185 = 497389) B497389
theorem B663203 : Blo 439778 663203 := bstep (se 1 (by rfl) ⟨497402, by rfl⟩ : syracuseStep 663203 = 994805) B994805
theorem B663233 : Blo 439778 663233 := bstep (se 2 (by rfl) ⟨248712, by rfl⟩ : syracuseStep 663233 = 497425) B497425
theorem B1449677 : Blo 439778 1449677 := bstep (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) B543629
theorem B663251 : Blo 439778 663251 := bstep (se 1 (by rfl) ⟨497438, by rfl⟩ : syracuseStep 663251 = 994877) B994877
theorem B663281 : Blo 439778 663281 := bstep (se 2 (by rfl) ⟨248730, by rfl⟩ : syracuseStep 663281 = 497461) B497461
theorem B663299 : Blo 439778 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B663329 : Blo 439778 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B1122083 : Blo 439778 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B892721 : Blo 439778 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B991025 : Blo 439778 991025 := bstep (se 2 (by rfl) ⟨371634, by rfl⟩ : syracuseStep 991025 = 743269) B743269
theorem B663347 : Blo 439778 663347 := bstep (se 1 (by rfl) ⟨497510, by rfl⟩ : syracuseStep 663347 = 995021) B995021
theorem B991043 : Blo 439778 991043 := bstep (se 1 (by rfl) ⟨743282, by rfl⟩ : syracuseStep 991043 = 1486565) B1486565
theorem B728899 : Blo 439778 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B663377 : Blo 439778 663377 := bstep (se 2 (by rfl) ⟨248766, by rfl⟩ : syracuseStep 663377 = 497533) B497533
theorem B663395 : Blo 439778 663395 := bstep (se 1 (by rfl) ⟨497546, by rfl⟩ : syracuseStep 663395 = 995093) B995093
theorem B663425 : Blo 439778 663425 := bstep (se 2 (by rfl) ⟨248784, by rfl⟩ : syracuseStep 663425 = 497569) B497569
theorem B663443 : Blo 439778 663443 := bstep (se 1 (by rfl) ⟨497582, by rfl⟩ : syracuseStep 663443 = 995165) B995165
theorem B663473 : Blo 439778 663473 := bstep (se 2 (by rfl) ⟨248802, by rfl⟩ : syracuseStep 663473 = 497605) B497605
theorem B597937 : Blo 439778 597937 := bstep (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) B448453
theorem B663491 : Blo 439778 663491 := bstep (se 1 (by rfl) ⟨497618, by rfl⟩ : syracuseStep 663491 = 995237) B995237
theorem B663521 : Blo 439778 663521 := bstep (se 2 (by rfl) ⟨248820, by rfl⟩ : syracuseStep 663521 = 497641) B497641
theorem B532451 : Blo 439778 532451 := bstep (se 1 (by rfl) ⟨399338, by rfl⟩ : syracuseStep 532451 = 798677) B798677
theorem B1122275 : Blo 439778 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B1253357 : Blo 439778 1253357 := bstep (se 3 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 1253357 = 470009) B470009
theorem B663539 : Blo 439778 663539 := bstep (se 1 (by rfl) ⟨497654, by rfl⟩ : syracuseStep 663539 = 995309) B995309
theorem B663569 : Blo 439778 663569 := bstep (se 2 (by rfl) ⟨248838, by rfl⟩ : syracuseStep 663569 = 497677) B497677
theorem B663587 : Blo 439778 663587 := bstep (se 1 (by rfl) ⟨497690, by rfl⟩ : syracuseStep 663587 = 995381) B995381
theorem B663617 : Blo 439778 663617 := bstep (se 2 (by rfl) ⟨248856, by rfl⟩ : syracuseStep 663617 = 497713) B497713
theorem B991313 : Blo 439778 991313 := bstep (se 2 (by rfl) ⟨371742, by rfl⟩ : syracuseStep 991313 = 743485) B743485
theorem B663635 : Blo 439778 663635 := bstep (se 1 (by rfl) ⟨497726, by rfl⟩ : syracuseStep 663635 = 995453) B995453
theorem B991331 : Blo 439778 991331 := bstep (se 1 (by rfl) ⟨743498, by rfl⟩ : syracuseStep 991331 = 1486997) B1486997
theorem B663665 : Blo 439778 663665 := bstep (se 2 (by rfl) ⟨248874, by rfl⟩ : syracuseStep 663665 = 497749) B497749
theorem B663683 : Blo 439778 663683 := bstep (se 1 (by rfl) ⟨497762, by rfl⟩ : syracuseStep 663683 = 995525) B995525
theorem B663713 : Blo 439778 663713 := bstep (se 2 (by rfl) ⟨248892, by rfl⟩ : syracuseStep 663713 = 497785) B497785
theorem B663731 : Blo 439778 663731 := bstep (se 1 (by rfl) ⟨497798, by rfl⟩ : syracuseStep 663731 = 995597) B995597
theorem B6037685 : Blo 439778 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B663761 : Blo 439778 663761 := bstep (se 2 (by rfl) ⟨248910, by rfl⟩ : syracuseStep 663761 = 497821) B497821
theorem B630995 : Blo 439778 630995 := bstep (se 1 (by rfl) ⟨473246, by rfl⟩ : syracuseStep 630995 = 946493) B946493
theorem B663779 : Blo 439778 663779 := bstep (se 1 (by rfl) ⟨497834, by rfl⟩ : syracuseStep 663779 = 995669) B995669
theorem B663809 : Blo 439778 663809 := bstep (se 2 (by rfl) ⟨248928, by rfl⟩ : syracuseStep 663809 = 497857) B497857
theorem B663827 : Blo 439778 663827 := bstep (se 1 (by rfl) ⟨497870, by rfl⟩ : syracuseStep 663827 = 995741) B995741
theorem B663857 : Blo 439778 663857 := bstep (se 2 (by rfl) ⟨248946, by rfl⟩ : syracuseStep 663857 = 497893) B497893
theorem B663875 : Blo 439778 663875 := bstep (se 1 (by rfl) ⟨497906, by rfl⟩ : syracuseStep 663875 = 995813) B995813
theorem B663905 : Blo 439778 663905 := bstep (se 2 (by rfl) ⟨248964, by rfl⟩ : syracuseStep 663905 = 497929) B497929
theorem B991601 : Blo 439778 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B663923 : Blo 439778 663923 := bstep (se 1 (by rfl) ⟨497942, by rfl⟩ : syracuseStep 663923 = 995885) B995885
theorem B991619 : Blo 439778 991619 := bstep (se 1 (by rfl) ⟨743714, by rfl⟩ : syracuseStep 991619 = 1487429) B1487429
theorem B663953 : Blo 439778 663953 := bstep (se 2 (by rfl) ⟨248982, by rfl⟩ : syracuseStep 663953 = 497965) B497965
theorem B795043 : Blo 439778 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B663971 : Blo 439778 663971 := bstep (se 1 (by rfl) ⟨497978, by rfl⟩ : syracuseStep 663971 = 995957) B995957
theorem B664001 : Blo 439778 664001 := bstep (se 2 (by rfl) ⟨249000, by rfl⟩ : syracuseStep 664001 = 498001) B498001
theorem B664019 : Blo 439778 664019 := bstep (se 1 (by rfl) ⟨498014, by rfl⟩ : syracuseStep 664019 = 996029) B996029
theorem B664049 : Blo 439778 664049 := bstep (se 2 (by rfl) ⟨249018, by rfl⟩ : syracuseStep 664049 = 498037) B498037
theorem B664067 : Blo 439778 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B664097 : Blo 439778 664097 := bstep (se 2 (by rfl) ⟨249036, by rfl⟩ : syracuseStep 664097 = 498073) B498073
theorem B664115 : Blo 439778 664115 := bstep (se 1 (by rfl) ⟨498086, by rfl⟩ : syracuseStep 664115 = 996173) B996173
theorem B664145 : Blo 439778 664145 := bstep (se 2 (by rfl) ⟨249054, by rfl⟩ : syracuseStep 664145 = 498109) B498109
theorem B664163 : Blo 439778 664163 := bstep (se 1 (by rfl) ⟨498122, by rfl⟩ : syracuseStep 664163 = 996245) B996245
theorem B664193 : Blo 439778 664193 := bstep (se 2 (by rfl) ⟨249072, by rfl⟩ : syracuseStep 664193 = 498145) B498145
theorem B991889 : Blo 439778 991889 := bstep (se 2 (by rfl) ⟨371958, by rfl⟩ : syracuseStep 991889 = 743917) B743917
theorem B664211 : Blo 439778 664211 := bstep (se 1 (by rfl) ⟨498158, by rfl⟩ : syracuseStep 664211 = 996317) B996317
theorem B991907 : Blo 439778 991907 := bstep (se 1 (by rfl) ⟨743930, by rfl⟩ : syracuseStep 991907 = 1487861) B1487861
theorem B664241 : Blo 439778 664241 := bstep (se 2 (by rfl) ⟨249090, by rfl⟩ : syracuseStep 664241 = 498181) B498181
theorem B664259 : Blo 439778 664259 := bstep (se 1 (by rfl) ⟨498194, by rfl⟩ : syracuseStep 664259 = 996389) B996389
theorem B664289 : Blo 439778 664289 := bstep (se 2 (by rfl) ⟨249108, by rfl⟩ : syracuseStep 664289 = 498217) B498217
theorem B664307 : Blo 439778 664307 := bstep (se 1 (by rfl) ⟨498230, by rfl⟩ : syracuseStep 664307 = 996461) B996461
theorem B2007821 : Blo 439778 2007821 := bstep (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) B752933
theorem B664337 : Blo 439778 664337 := bstep (se 2 (by rfl) ⟨249126, by rfl⟩ : syracuseStep 664337 = 498253) B498253
theorem B2237219 : Blo 439778 2237219 := bstep (se 1 (by rfl) ⟨1677914, by rfl⟩ : syracuseStep 2237219 = 3355829) B3355829
theorem B664355 : Blo 439778 664355 := bstep (se 1 (by rfl) ⟨498266, by rfl⟩ : syracuseStep 664355 = 996533) B996533
theorem B664385 : Blo 439778 664385 := bstep (se 2 (by rfl) ⟨249144, by rfl⟩ : syracuseStep 664385 = 498289) B498289
theorem B631633 : Blo 439778 631633 := bstep (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) B473725
theorem B664403 : Blo 439778 664403 := bstep (se 1 (by rfl) ⟨498302, by rfl⟩ : syracuseStep 664403 = 996605) B996605
theorem B664433 : Blo 439778 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B664451 : Blo 439778 664451 := bstep (se 1 (by rfl) ⟨498338, by rfl⟩ : syracuseStep 664451 = 996677) B996677
theorem B1123217 : Blo 439778 1123217 := bstep (se 2 (by rfl) ⟨421206, by rfl⟩ : syracuseStep 1123217 = 842413) B842413
theorem B664481 : Blo 439778 664481 := bstep (se 2 (by rfl) ⟨249180, by rfl⟩ : syracuseStep 664481 = 498361) B498361
theorem B992177 : Blo 439778 992177 := bstep (se 2 (by rfl) ⟨372066, by rfl⟩ : syracuseStep 992177 = 744133) B744133
theorem B664499 : Blo 439778 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B992195 : Blo 439778 992195 := bstep (se 1 (by rfl) ⟨744146, by rfl⟩ : syracuseStep 992195 = 1488293) B1488293
theorem B631747 : Blo 439778 631747 := bstep (se 1 (by rfl) ⟨473810, by rfl⟩ : syracuseStep 631747 = 947621) B947621
theorem B1123267 : Blo 439778 1123267 := bstep (se 1 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 1123267 = 1684901) B1684901
theorem B664529 : Blo 439778 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B664547 : Blo 439778 664547 := bstep (se 1 (by rfl) ⟨498410, by rfl⟩ : syracuseStep 664547 = 996821) B996821
theorem B664577 : Blo 439778 664577 := bstep (se 2 (by rfl) ⟨249216, by rfl⟩ : syracuseStep 664577 = 498433) B498433
theorem B664595 : Blo 439778 664595 := bstep (se 1 (by rfl) ⟨498446, by rfl⟩ : syracuseStep 664595 = 996893) B996893
theorem B10298389 : Blo 439778 10298389 := bstep (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) B482737
theorem B664625 : Blo 439778 664625 := bstep (se 2 (by rfl) ⟨249234, by rfl⟩ : syracuseStep 664625 = 498469) B498469
theorem B664643 : Blo 439778 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B664673 : Blo 439778 664673 := bstep (se 2 (by rfl) ⟨249252, by rfl⟩ : syracuseStep 664673 = 498505) B498505
theorem B1680497 : Blo 439778 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B664691 : Blo 439778 664691 := bstep (se 1 (by rfl) ⟨498518, by rfl⟩ : syracuseStep 664691 = 997037) B997037
theorem B1254541 : Blo 439778 1254541 := bstep (se 3 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 1254541 = 470453) B470453
theorem B664721 : Blo 439778 664721 := bstep (se 2 (by rfl) ⟨249270, by rfl⟩ : syracuseStep 664721 = 498541) B498541
theorem B664739 : Blo 439778 664739 := bstep (se 1 (by rfl) ⟨498554, by rfl⟩ : syracuseStep 664739 = 997109) B997109
theorem B664769 : Blo 439778 664769 := bstep (se 2 (by rfl) ⟨249288, by rfl⟩ : syracuseStep 664769 = 498577) B498577
theorem B992465 : Blo 439778 992465 := bstep (se 2 (by rfl) ⟨372174, by rfl⟩ : syracuseStep 992465 = 744349) B744349
theorem B664787 : Blo 439778 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B992483 : Blo 439778 992483 := bstep (se 1 (by rfl) ⟨744362, by rfl⟩ : syracuseStep 992483 = 1488725) B1488725
theorem B664817 : Blo 439778 664817 := bstep (se 2 (by rfl) ⟨249306, by rfl⟩ : syracuseStep 664817 = 498613) B498613
theorem B664835 : Blo 439778 664835 := bstep (se 1 (by rfl) ⟨498626, by rfl⟩ : syracuseStep 664835 = 997253) B997253
theorem B1418509 : Blo 439778 1418509 := bstep (se 3 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 1418509 = 531941) B531941
theorem B664865 : Blo 439778 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B1189169 : Blo 439778 1189169 := bstep (se 2 (by rfl) ⟨445938, by rfl⟩ : syracuseStep 1189169 = 891877) B891877
theorem B664883 : Blo 439778 664883 := bstep (se 1 (by rfl) ⟨498662, by rfl⟩ : syracuseStep 664883 = 997325) B997325
theorem B664913 : Blo 439778 664913 := bstep (se 2 (by rfl) ⟨249342, by rfl⟩ : syracuseStep 664913 = 498685) B498685
theorem B664931 : Blo 439778 664931 := bstep (se 1 (by rfl) ⟨498698, by rfl⟩ : syracuseStep 664931 = 997397) B997397
theorem B664961 : Blo 439778 664961 := bstep (se 2 (by rfl) ⟨249360, by rfl⟩ : syracuseStep 664961 = 498721) B498721
theorem B664979 : Blo 439778 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B1516963 : Blo 439778 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B665009 : Blo 439778 665009 := bstep (se 2 (by rfl) ⟨249378, by rfl⟩ : syracuseStep 665009 = 498757) B498757
theorem B665027 : Blo 439778 665027 := bstep (se 1 (by rfl) ⟨498770, by rfl⟩ : syracuseStep 665027 = 997541) B997541
theorem B665057 : Blo 439778 665057 := bstep (se 2 (by rfl) ⟨249396, by rfl⟩ : syracuseStep 665057 = 498793) B498793
theorem B992753 : Blo 439778 992753 := bstep (se 2 (by rfl) ⟨372282, by rfl⟩ : syracuseStep 992753 = 744565) B744565
theorem B665075 : Blo 439778 665075 := bstep (se 1 (by rfl) ⟨498806, by rfl⟩ : syracuseStep 665075 = 997613) B997613
theorem B992771 : Blo 439778 992771 := bstep (se 1 (by rfl) ⟨744578, by rfl⟩ : syracuseStep 992771 = 1489157) B1489157
theorem B665105 : Blo 439778 665105 := bstep (se 2 (by rfl) ⟨249414, by rfl⟩ : syracuseStep 665105 = 498829) B498829
theorem B665123 : Blo 439778 665123 := bstep (se 1 (by rfl) ⟨498842, by rfl⟩ : syracuseStep 665123 = 997685) B997685
theorem B665153 : Blo 439778 665153 := bstep (se 2 (by rfl) ⟨249432, by rfl⟩ : syracuseStep 665153 = 498865) B498865
theorem B2238029 : Blo 439778 2238029 := bstep (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) B839261
theorem B665171 : Blo 439778 665171 := bstep (se 1 (by rfl) ⟨498878, by rfl⟩ : syracuseStep 665171 = 997757) B997757
theorem B665201 : Blo 439778 665201 := bstep (se 2 (by rfl) ⟨249450, by rfl⟩ : syracuseStep 665201 = 498901) B498901
theorem B665219 : Blo 439778 665219 := bstep (se 1 (by rfl) ⟨498914, by rfl⟩ : syracuseStep 665219 = 997829) B997829
theorem B665249 : Blo 439778 665249 := bstep (se 2 (by rfl) ⟨249468, by rfl⟩ : syracuseStep 665249 = 498937) B498937
theorem B665267 : Blo 439778 665267 := bstep (se 1 (by rfl) ⟨498950, by rfl⟩ : syracuseStep 665267 = 997901) B997901
theorem B2827973 : Blo 439778 2827973 := bstep (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) B530245
theorem B665297 : Blo 439778 665297 := bstep (se 2 (by rfl) ⟨249486, by rfl⟩ : syracuseStep 665297 = 498973) B498973
theorem B1844963 : Blo 439778 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B665315 : Blo 439778 665315 := bstep (se 1 (by rfl) ⟨498986, by rfl⟩ : syracuseStep 665315 = 997973) B997973
theorem B665345 : Blo 439778 665345 := bstep (se 2 (by rfl) ⟨249504, by rfl⟩ : syracuseStep 665345 = 499009) B499009
theorem B993041 : Blo 439778 993041 := bstep (se 2 (by rfl) ⟨372390, by rfl⟩ : syracuseStep 993041 = 744781) B744781
theorem B665363 : Blo 439778 665363 := bstep (se 1 (by rfl) ⟨499022, by rfl⟩ : syracuseStep 665363 = 998045) B998045
theorem B993059 : Blo 439778 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B665393 : Blo 439778 665393 := bstep (se 2 (by rfl) ⟨249522, by rfl⟩ : syracuseStep 665393 = 499045) B499045
theorem B665411 : Blo 439778 665411 := bstep (se 1 (by rfl) ⟨499058, by rfl⟩ : syracuseStep 665411 = 998117) B998117
theorem B1484621 : Blo 439778 1484621 := bstep (se 3 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 1484621 = 556733) B556733
theorem B665441 : Blo 439778 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B665459 : Blo 439778 665459 := bstep (se 1 (by rfl) ⟨499094, by rfl⟩ : syracuseStep 665459 = 998189) B998189
theorem B1484675 : Blo 439778 1484675 := bstep (se 1 (by rfl) ⟨1113506, by rfl⟩ : syracuseStep 1484675 = 2227013) B2227013
theorem B665489 : Blo 439778 665489 := bstep (se 2 (by rfl) ⟨249558, by rfl⟩ : syracuseStep 665489 = 499117) B499117
theorem B665507 : Blo 439778 665507 := bstep (se 1 (by rfl) ⟨499130, by rfl⟩ : syracuseStep 665507 = 998261) B998261
theorem B665537 : Blo 439778 665537 := bstep (se 2 (by rfl) ⟨249576, by rfl⟩ : syracuseStep 665537 = 499153) B499153
theorem B9086917 : Blo 439778 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B665555 : Blo 439778 665555 := bstep (se 1 (by rfl) ⟨499166, by rfl⟩ : syracuseStep 665555 = 998333) B998333
theorem B665585 : Blo 439778 665585 := bstep (se 2 (by rfl) ⟨249594, by rfl⟩ : syracuseStep 665585 = 499189) B499189
theorem B665603 : Blo 439778 665603 := bstep (se 1 (by rfl) ⟨499202, by rfl⟩ : syracuseStep 665603 = 998405) B998405
theorem B665633 : Blo 439778 665633 := bstep (se 2 (by rfl) ⟨249612, by rfl⟩ : syracuseStep 665633 = 499225) B499225
theorem B993329 : Blo 439778 993329 := bstep (se 2 (by rfl) ⟨372498, by rfl⟩ : syracuseStep 993329 = 744997) B744997
theorem B665651 : Blo 439778 665651 := bstep (se 1 (by rfl) ⟨499238, by rfl⟩ : syracuseStep 665651 = 998477) B998477
theorem B993347 : Blo 439778 993347 := bstep (se 1 (by rfl) ⟨745010, by rfl⟩ : syracuseStep 993347 = 1490021) B1490021
theorem B501859 : Blo 439778 501859 := bstep (se 1 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 501859 = 752789) B752789
theorem B1484945 : Blo 439778 1484945 := bstep (se 2 (by rfl) ⟨556854, by rfl⟩ : syracuseStep 1484945 = 1113709) B1113709
theorem B796817 : Blo 439778 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B1255601 : Blo 439778 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B502019 : Blo 439778 502019 := bstep (se 1 (by rfl) ⟨376514, by rfl⟩ : syracuseStep 502019 = 753029) B753029
theorem B3385613 : Blo 439778 3385613 := bstep (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) B1269605
theorem B993617 : Blo 439778 993617 := bstep (se 2 (by rfl) ⟨372606, by rfl⟩ : syracuseStep 993617 = 745213) B745213
theorem B993635 : Blo 439778 993635 := bstep (se 1 (by rfl) ⟨745226, by rfl⟩ : syracuseStep 993635 = 1490453) B1490453
theorem B1190285 : Blo 439778 1190285 := bstep (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) B446357
theorem B1190339 : Blo 439778 1190339 := bstep (se 1 (by rfl) ⟨892754, by rfl⟩ : syracuseStep 1190339 = 1785509) B1785509
theorem B1681955 : Blo 439778 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B993905 : Blo 439778 993905 := bstep (se 2 (by rfl) ⟨372714, by rfl⟩ : syracuseStep 993905 = 745429) B745429
theorem B993923 : Blo 439778 993923 := bstep (se 1 (by rfl) ⟨745442, by rfl⟩ : syracuseStep 993923 = 1490885) B1490885
theorem B1485485 : Blo 439778 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B797393 : Blo 439778 797393 := bstep (se 2 (by rfl) ⟨299022, by rfl⟩ : syracuseStep 797393 = 598045) B598045
theorem B1485539 : Blo 439778 1485539 := bstep (se 1 (by rfl) ⟨1114154, by rfl⟩ : syracuseStep 1485539 = 2228309) B2228309
theorem B1256273 : Blo 439778 1256273 := bstep (se 2 (by rfl) ⟨471102, by rfl⟩ : syracuseStep 1256273 = 942205) B942205
theorem B994193 : Blo 439778 994193 := bstep (se 2 (by rfl) ⟨372822, by rfl⟩ : syracuseStep 994193 = 745645) B745645
theorem B994211 : Blo 439778 994211 := bstep (se 1 (by rfl) ⟨745658, by rfl⟩ : syracuseStep 994211 = 1491317) B1491317
theorem B797617 : Blo 439778 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B1485809 : Blo 439778 1485809 := bstep (se 2 (by rfl) ⟨557178, by rfl⟩ : syracuseStep 1485809 = 1114357) B1114357
theorem B1420355 : Blo 439778 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B994481 : Blo 439778 994481 := bstep (se 2 (by rfl) ⟨372930, by rfl⟩ : syracuseStep 994481 = 745861) B745861
theorem B994499 : Blo 439778 994499 := bstep (se 1 (by rfl) ⟨745874, by rfl⟩ : syracuseStep 994499 = 1491749) B1491749
theorem B1191181 : Blo 439778 1191181 := bstep (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) B446693
theorem B797969 : Blo 439778 797969 := bstep (se 2 (by rfl) ⟨299238, by rfl⟩ : syracuseStep 797969 = 598477) B598477
theorem B6040973 : Blo 439778 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B994769 : Blo 439778 994769 := bstep (se 2 (by rfl) ⟨373038, by rfl⟩ : syracuseStep 994769 = 746077) B746077
theorem B1420753 : Blo 439778 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B1879523 : Blo 439778 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B994787 : Blo 439778 994787 := bstep (se 1 (by rfl) ⟨746090, by rfl⟩ : syracuseStep 994787 = 1492181) B1492181
theorem B1486349 : Blo 439778 1486349 := bstep (se 3 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 1486349 = 557381) B557381
theorem B1682957 : Blo 439778 1682957 := bstep (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) B631109
theorem B1486403 : Blo 439778 1486403 := bstep (se 1 (by rfl) ⟨1114802, by rfl⟩ : syracuseStep 1486403 = 2229605) B2229605
theorem B1191505 : Blo 439778 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1257059 : Blo 439778 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B5451461 : Blo 439778 5451461 := bstep (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) B1022149
theorem B995057 : Blo 439778 995057 := bstep (se 2 (by rfl) ⟨373146, by rfl⟩ : syracuseStep 995057 = 746293) B746293
theorem B995075 : Blo 439778 995075 := bstep (se 1 (by rfl) ⟨746306, by rfl⟩ : syracuseStep 995075 = 1492613) B1492613
theorem B1486673 : Blo 439778 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B1421201 : Blo 439778 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B1257389 : Blo 439778 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B896995 : Blo 439778 896995 := bstep (se 1 (by rfl) ⟨672746, by rfl⟩ : syracuseStep 896995 = 1345493) B1345493
theorem B1257457 : Blo 439778 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B765953 : Blo 439778 765953 := bstep (se 2 (by rfl) ⟨287232, by rfl⟩ : syracuseStep 765953 = 574465) B574465
theorem B995345 : Blo 439778 995345 := bstep (se 2 (by rfl) ⟨373254, by rfl⟩ : syracuseStep 995345 = 746509) B746509
theorem B995363 : Blo 439778 995363 := bstep (se 1 (by rfl) ⟨746522, by rfl⟩ : syracuseStep 995363 = 1493045) B1493045
theorem B1290289 : Blo 439778 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B1061105 : Blo 439778 1061105 := bstep (se 2 (by rfl) ⟨397914, by rfl⟩ : syracuseStep 1061105 = 795829) B795829
theorem B1257731 : Blo 439778 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B798979 : Blo 439778 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B995633 : Blo 439778 995633 := bstep (se 2 (by rfl) ⟨373362, by rfl⟩ : syracuseStep 995633 = 746725) B746725
theorem B995651 : Blo 439778 995651 := bstep (se 1 (by rfl) ⟨746738, by rfl⟩ : syracuseStep 995651 = 1493477) B1493477
theorem B1487213 : Blo 439778 1487213 := bstep (se 3 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 1487213 = 557705) B557705
theorem B14332301 : Blo 439778 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1487267 : Blo 439778 1487267 := bstep (se 1 (by rfl) ⟨1115450, by rfl⟩ : syracuseStep 1487267 = 2230901) B2230901
theorem B799139 : Blo 439778 799139 := bstep (se 1 (by rfl) ⟨599354, by rfl⟩ : syracuseStep 799139 = 1198709) B1198709
theorem B2240945 : Blo 439778 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B995921 : Blo 439778 995921 := bstep (se 2 (by rfl) ⟨373470, by rfl⟩ : syracuseStep 995921 = 746941) B746941
theorem B766561 : Blo 439778 766561 := bstep (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) B574921
theorem B995939 : Blo 439778 995939 := bstep (se 1 (by rfl) ⟨746954, by rfl⟩ : syracuseStep 995939 = 1493909) B1493909
theorem B504451 : Blo 439778 504451 := bstep (se 1 (by rfl) ⟨378338, by rfl⟩ : syracuseStep 504451 = 756677) B756677
theorem B1487537 : Blo 439778 1487537 := bstep (se 2 (by rfl) ⟨557826, by rfl⟩ : syracuseStep 1487537 = 1115653) B1115653
theorem B996209 : Blo 439778 996209 := bstep (se 2 (by rfl) ⟨373578, by rfl⟩ : syracuseStep 996209 = 747157) B747157
theorem B996227 : Blo 439778 996227 := bstep (se 1 (by rfl) ⟨747170, by rfl⟩ : syracuseStep 996227 = 1494341) B1494341
theorem B1913827 : Blo 439778 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B472115 : Blo 439778 472115 := bstep (se 1 (by rfl) ⟨354086, by rfl⟩ : syracuseStep 472115 = 708173) B708173
theorem B1258573 : Blo 439778 1258573 := bstep (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) B471965
theorem B2012273 : Blo 439778 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B996497 : Blo 439778 996497 := bstep (se 2 (by rfl) ⟨373686, by rfl⟩ : syracuseStep 996497 = 747373) B747373
theorem B996515 : Blo 439778 996515 := bstep (se 1 (by rfl) ⟨747386, by rfl⟩ : syracuseStep 996515 = 1494773) B1494773
theorem B1881265 : Blo 439778 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1488077 : Blo 439778 1488077 := bstep (se 3 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 1488077 = 558029) B558029
theorem B3880163 : Blo 439778 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B1258733 : Blo 439778 1258733 := bstep (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) B472025
theorem B603379 : Blo 439778 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B1488131 : Blo 439778 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B5715299 : Blo 439778 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B1258915 : Blo 439778 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B996785 : Blo 439778 996785 := bstep (se 2 (by rfl) ⟨373794, by rfl⟩ : syracuseStep 996785 = 747589) B747589
theorem B996803 : Blo 439778 996803 := bstep (se 1 (by rfl) ⟨747602, by rfl⟩ : syracuseStep 996803 = 1495205) B1495205
theorem B439779 : Blo 439778 439779 := bstep (se 1 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 439779 = 659669) B659669
theorem B439795 : Blo 439778 439795 := bstep (se 1 (by rfl) ⟨329846, by rfl⟩ : syracuseStep 439795 = 659693) B659693
theorem B439811 : Blo 439778 439811 := bstep (se 1 (by rfl) ⟨329858, by rfl⟩ : syracuseStep 439811 = 659717) B659717
theorem B1488401 : Blo 439778 1488401 := bstep (se 2 (by rfl) ⟨558150, by rfl⟩ : syracuseStep 1488401 = 1116301) B1116301
theorem B439827 : Blo 439778 439827 := bstep (se 1 (by rfl) ⟨329870, by rfl⟩ : syracuseStep 439827 = 659741) B659741
theorem B439843 : Blo 439778 439843 := bstep (se 1 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 439843 = 659765) B659765
theorem B439859 : Blo 439778 439859 := bstep (se 1 (by rfl) ⟨329894, by rfl⟩ : syracuseStep 439859 = 659789) B659789
theorem B439875 : Blo 439778 439875 := bstep (se 1 (by rfl) ⟨329906, by rfl⟩ : syracuseStep 439875 = 659813) B659813
theorem B3782213 : Blo 439778 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B439891 : Blo 439778 439891 := bstep (se 1 (by rfl) ⟨329918, by rfl⟩ : syracuseStep 439891 = 659837) B659837
theorem B439907 : Blo 439778 439907 := bstep (se 1 (by rfl) ⟨329930, by rfl⟩ : syracuseStep 439907 = 659861) B659861
theorem B439923 : Blo 439778 439923 := bstep (se 1 (by rfl) ⟨329942, by rfl⟩ : syracuseStep 439923 = 659885) B659885
theorem B439939 : Blo 439778 439939 := bstep (se 1 (by rfl) ⟨329954, by rfl⟩ : syracuseStep 439939 = 659909) B659909
theorem B439955 : Blo 439778 439955 := bstep (se 1 (by rfl) ⟨329966, by rfl⟩ : syracuseStep 439955 = 659933) B659933
theorem B439971 : Blo 439778 439971 := bstep (se 1 (by rfl) ⟨329978, by rfl⟩ : syracuseStep 439971 = 659957) B659957
theorem B439987 : Blo 439778 439987 := bstep (se 1 (by rfl) ⟨329990, by rfl⟩ : syracuseStep 439987 = 659981) B659981
theorem B440003 : Blo 439778 440003 := bstep (se 1 (by rfl) ⟨330002, by rfl⟩ : syracuseStep 440003 = 660005) B660005
theorem B997073 : Blo 439778 997073 := bstep (se 2 (by rfl) ⟨373902, by rfl⟩ : syracuseStep 997073 = 747805) B747805
theorem B440019 : Blo 439778 440019 := bstep (se 1 (by rfl) ⟨330014, by rfl⟩ : syracuseStep 440019 = 660029) B660029
theorem B440035 : Blo 439778 440035 := bstep (se 1 (by rfl) ⟨330026, by rfl⟩ : syracuseStep 440035 = 660053) B660053
theorem B997091 : Blo 439778 997091 := bstep (se 1 (by rfl) ⟨747818, by rfl⟩ : syracuseStep 997091 = 1495637) B1495637
theorem B440051 : Blo 439778 440051 := bstep (se 1 (by rfl) ⟨330038, by rfl⟩ : syracuseStep 440051 = 660077) B660077
theorem B440067 : Blo 439778 440067 := bstep (se 1 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 440067 = 660101) B660101
theorem B440083 : Blo 439778 440083 := bstep (se 1 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 440083 = 660125) B660125
theorem B440099 : Blo 439778 440099 := bstep (se 1 (by rfl) ⟨330074, by rfl⟩ : syracuseStep 440099 = 660149) B660149
theorem B440115 : Blo 439778 440115 := bstep (se 1 (by rfl) ⟨330086, by rfl⟩ : syracuseStep 440115 = 660173) B660173
theorem B440131 : Blo 439778 440131 := bstep (se 1 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 440131 = 660197) B660197
theorem B440147 : Blo 439778 440147 := bstep (se 1 (by rfl) ⟨330110, by rfl⟩ : syracuseStep 440147 = 660221) B660221
theorem B440163 : Blo 439778 440163 := bstep (se 1 (by rfl) ⟨330122, by rfl⟩ : syracuseStep 440163 = 660245) B660245
theorem B2242403 : Blo 439778 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B440179 : Blo 439778 440179 := bstep (se 1 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 440179 = 660269) B660269
theorem B440195 : Blo 439778 440195 := bstep (se 1 (by rfl) ⟨330146, by rfl⟩ : syracuseStep 440195 = 660293) B660293
theorem B440211 : Blo 439778 440211 := bstep (se 1 (by rfl) ⟨330158, by rfl⟩ : syracuseStep 440211 = 660317) B660317
theorem B440227 : Blo 439778 440227 := bstep (se 1 (by rfl) ⟨330170, by rfl⟩ : syracuseStep 440227 = 660341) B660341
theorem B440243 : Blo 439778 440243 := bstep (se 1 (by rfl) ⟨330182, by rfl⟩ : syracuseStep 440243 = 660365) B660365
theorem B440259 : Blo 439778 440259 := bstep (se 1 (by rfl) ⟨330194, by rfl⟩ : syracuseStep 440259 = 660389) B660389
theorem B440275 : Blo 439778 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B440291 : Blo 439778 440291 := bstep (se 1 (by rfl) ⟨330218, by rfl⟩ : syracuseStep 440291 = 660437) B660437
theorem B997361 : Blo 439778 997361 := bstep (se 2 (by rfl) ⟨374010, by rfl⟩ : syracuseStep 997361 = 748021) B748021
theorem B440307 : Blo 439778 440307 := bstep (se 1 (by rfl) ⟨330230, by rfl⟩ : syracuseStep 440307 = 660461) B660461
theorem B440323 : Blo 439778 440323 := bstep (se 1 (by rfl) ⟨330242, by rfl⟩ : syracuseStep 440323 = 660485) B660485
theorem B997379 : Blo 439778 997379 := bstep (se 1 (by rfl) ⟨748034, by rfl⟩ : syracuseStep 997379 = 1496069) B1496069
theorem B440339 : Blo 439778 440339 := bstep (se 1 (by rfl) ⟨330254, by rfl⟩ : syracuseStep 440339 = 660509) B660509
theorem B440355 : Blo 439778 440355 := bstep (se 1 (by rfl) ⟨330266, by rfl⟩ : syracuseStep 440355 = 660533) B660533
theorem B1488941 : Blo 439778 1488941 := bstep (se 3 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 1488941 = 558353) B558353
theorem B2504753 : Blo 439778 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B440371 : Blo 439778 440371 := bstep (se 1 (by rfl) ⟨330278, by rfl⟩ : syracuseStep 440371 = 660557) B660557
theorem B440387 : Blo 439778 440387 := bstep (se 1 (by rfl) ⟨330290, by rfl⟩ : syracuseStep 440387 = 660581) B660581
theorem B440403 : Blo 439778 440403 := bstep (se 1 (by rfl) ⟨330302, by rfl⟩ : syracuseStep 440403 = 660605) B660605
theorem B440419 : Blo 439778 440419 := bstep (se 1 (by rfl) ⟨330314, by rfl⟩ : syracuseStep 440419 = 660629) B660629
theorem B1488995 : Blo 439778 1488995 := bstep (se 1 (by rfl) ⟨1116746, by rfl⟩ : syracuseStep 1488995 = 2233493) B2233493
theorem B669809 : Blo 439778 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B440435 : Blo 439778 440435 := bstep (se 1 (by rfl) ⟨330326, by rfl⟩ : syracuseStep 440435 = 660653) B660653
theorem B768115 : Blo 439778 768115 := bstep (se 1 (by rfl) ⟨576086, by rfl⟩ : syracuseStep 768115 = 1152173) B1152173
theorem B440451 : Blo 439778 440451 := bstep (se 1 (by rfl) ⟨330338, by rfl⟩ : syracuseStep 440451 = 660677) B660677
theorem B1063057 : Blo 439778 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B440467 : Blo 439778 440467 := bstep (se 1 (by rfl) ⟨330350, by rfl⟩ : syracuseStep 440467 = 660701) B660701
theorem B440483 : Blo 439778 440483 := bstep (se 1 (by rfl) ⟨330362, by rfl⟩ : syracuseStep 440483 = 660725) B660725
theorem B440499 : Blo 439778 440499 := bstep (se 1 (by rfl) ⟨330374, by rfl⟩ : syracuseStep 440499 = 660749) B660749
theorem B440515 : Blo 439778 440515 := bstep (se 1 (by rfl) ⟨330386, by rfl⟩ : syracuseStep 440515 = 660773) B660773
theorem B440531 : Blo 439778 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B440547 : Blo 439778 440547 := bstep (se 1 (by rfl) ⟨330410, by rfl⟩ : syracuseStep 440547 = 660821) B660821
theorem B440563 : Blo 439778 440563 := bstep (se 1 (by rfl) ⟨330422, by rfl⟩ : syracuseStep 440563 = 660845) B660845
theorem B440579 : Blo 439778 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B997649 : Blo 439778 997649 := bstep (se 2 (by rfl) ⟨374118, by rfl⟩ : syracuseStep 997649 = 748237) B748237
theorem B440595 : Blo 439778 440595 := bstep (se 1 (by rfl) ⟨330446, by rfl⟩ : syracuseStep 440595 = 660893) B660893
theorem B440611 : Blo 439778 440611 := bstep (se 1 (by rfl) ⟨330458, by rfl⟩ : syracuseStep 440611 = 660917) B660917
theorem B997667 : Blo 439778 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B440627 : Blo 439778 440627 := bstep (se 1 (by rfl) ⟨330470, by rfl⟩ : syracuseStep 440627 = 660941) B660941
theorem B440643 : Blo 439778 440643 := bstep (se 1 (by rfl) ⟨330482, by rfl⟩ : syracuseStep 440643 = 660965) B660965
theorem B1194317 : Blo 439778 1194317 := bstep (se 3 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 1194317 = 447869) B447869
theorem B440659 : Blo 439778 440659 := bstep (se 1 (by rfl) ⟨330494, by rfl⟩ : syracuseStep 440659 = 660989) B660989
theorem B440675 : Blo 439778 440675 := bstep (se 1 (by rfl) ⟨330506, by rfl⟩ : syracuseStep 440675 = 661013) B661013
theorem B1784177 : Blo 439778 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1489265 : Blo 439778 1489265 := bstep (se 2 (by rfl) ⟨558474, by rfl⟩ : syracuseStep 1489265 = 1116949) B1116949
theorem B440691 : Blo 439778 440691 := bstep (se 1 (by rfl) ⟨330518, by rfl⟩ : syracuseStep 440691 = 661037) B661037
theorem B440707 : Blo 439778 440707 := bstep (se 1 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 440707 = 661061) B661061
theorem B440723 : Blo 439778 440723 := bstep (se 1 (by rfl) ⟨330542, by rfl⟩ : syracuseStep 440723 = 661085) B661085
theorem B440739 : Blo 439778 440739 := bstep (se 1 (by rfl) ⟨330554, by rfl⟩ : syracuseStep 440739 = 661109) B661109
theorem B440755 : Blo 439778 440755 := bstep (se 1 (by rfl) ⟨330566, by rfl⟩ : syracuseStep 440755 = 661133) B661133
theorem B440771 : Blo 439778 440771 := bstep (se 1 (by rfl) ⟨330578, by rfl⟩ : syracuseStep 440771 = 661157) B661157
theorem B440787 : Blo 439778 440787 := bstep (se 1 (by rfl) ⟨330590, by rfl⟩ : syracuseStep 440787 = 661181) B661181
theorem B440803 : Blo 439778 440803 := bstep (se 1 (by rfl) ⟨330602, by rfl⟩ : syracuseStep 440803 = 661205) B661205
theorem B440819 : Blo 439778 440819 := bstep (se 1 (by rfl) ⟨330614, by rfl⟩ : syracuseStep 440819 = 661229) B661229
theorem B440835 : Blo 439778 440835 := bstep (se 1 (by rfl) ⟨330626, by rfl⟩ : syracuseStep 440835 = 661253) B661253
theorem B440851 : Blo 439778 440851 := bstep (se 1 (by rfl) ⟨330638, by rfl⟩ : syracuseStep 440851 = 661277) B661277
theorem B1063459 : Blo 439778 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B440867 : Blo 439778 440867 := bstep (se 1 (by rfl) ⟨330650, by rfl⟩ : syracuseStep 440867 = 661301) B661301
theorem B2013731 : Blo 439778 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B997937 : Blo 439778 997937 := bstep (se 2 (by rfl) ⟨374226, by rfl⟩ : syracuseStep 997937 = 748453) B748453
theorem B440883 : Blo 439778 440883 := bstep (se 1 (by rfl) ⟨330662, by rfl⟩ : syracuseStep 440883 = 661325) B661325
theorem B440899 : Blo 439778 440899 := bstep (se 1 (by rfl) ⟨330674, by rfl⟩ : syracuseStep 440899 = 661349) B661349
theorem B997955 : Blo 439778 997955 := bstep (se 1 (by rfl) ⟨748466, by rfl⟩ : syracuseStep 997955 = 1496933) B1496933
theorem B440915 : Blo 439778 440915 := bstep (se 1 (by rfl) ⟨330686, by rfl⟩ : syracuseStep 440915 = 661373) B661373
theorem B440931 : Blo 439778 440931 := bstep (se 1 (by rfl) ⟨330698, by rfl⟩ : syracuseStep 440931 = 661397) B661397
theorem B440947 : Blo 439778 440947 := bstep (se 1 (by rfl) ⟨330710, by rfl⟩ : syracuseStep 440947 = 661421) B661421
theorem B440963 : Blo 439778 440963 := bstep (se 1 (by rfl) ⟨330722, by rfl⟩ : syracuseStep 440963 = 661445) B661445
theorem B1587853 : Blo 439778 1587853 := bstep (se 3 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 1587853 = 595445) B595445
theorem B2243213 : Blo 439778 2243213 := bstep (se 3 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 2243213 = 841205) B841205
theorem B440979 : Blo 439778 440979 := bstep (se 1 (by rfl) ⟨330734, by rfl⟩ : syracuseStep 440979 = 661469) B661469
theorem B440995 : Blo 439778 440995 := bstep (se 1 (by rfl) ⟨330746, by rfl⟩ : syracuseStep 440995 = 661493) B661493
theorem B441011 : Blo 439778 441011 := bstep (se 1 (by rfl) ⟨330758, by rfl⟩ : syracuseStep 441011 = 661517) B661517
theorem B441027 : Blo 439778 441027 := bstep (se 1 (by rfl) ⟨330770, by rfl⟩ : syracuseStep 441027 = 661541) B661541
theorem B441043 : Blo 439778 441043 := bstep (se 1 (by rfl) ⟨330782, by rfl⟩ : syracuseStep 441043 = 661565) B661565
theorem B441059 : Blo 439778 441059 := bstep (se 1 (by rfl) ⟨330794, by rfl⟩ : syracuseStep 441059 = 661589) B661589
theorem B441075 : Blo 439778 441075 := bstep (se 1 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 441075 = 661613) B661613
theorem B670465 : Blo 439778 670465 := bstep (se 2 (by rfl) ⟨251424, by rfl⟩ : syracuseStep 670465 = 502849) B502849
theorem B441091 : Blo 439778 441091 := bstep (se 1 (by rfl) ⟨330818, by rfl⟩ : syracuseStep 441091 = 661637) B661637
theorem B1260305 : Blo 439778 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B441107 : Blo 439778 441107 := bstep (se 1 (by rfl) ⟨330830, by rfl⟩ : syracuseStep 441107 = 661661) B661661
theorem B441123 : Blo 439778 441123 := bstep (se 1 (by rfl) ⟨330842, by rfl⟩ : syracuseStep 441123 = 661685) B661685
theorem B441139 : Blo 439778 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B441155 : Blo 439778 441155 := bstep (se 1 (by rfl) ⟨330866, by rfl⟩ : syracuseStep 441155 = 661733) B661733
theorem B998225 : Blo 439778 998225 := bstep (se 2 (by rfl) ⟨374334, by rfl⟩ : syracuseStep 998225 = 748669) B748669
theorem B441171 : Blo 439778 441171 := bstep (se 1 (by rfl) ⟨330878, by rfl⟩ : syracuseStep 441171 = 661757) B661757
theorem B441187 : Blo 439778 441187 := bstep (se 1 (by rfl) ⟨330890, by rfl⟩ : syracuseStep 441187 = 661781) B661781
theorem B998243 : Blo 439778 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B539507 : Blo 439778 539507 := bstep (se 1 (by rfl) ⟨404630, by rfl⟩ : syracuseStep 539507 = 809261) B809261
theorem B441203 : Blo 439778 441203 := bstep (se 1 (by rfl) ⟨330902, by rfl⟩ : syracuseStep 441203 = 661805) B661805
theorem B441219 : Blo 439778 441219 := bstep (se 1 (by rfl) ⟨330914, by rfl⟩ : syracuseStep 441219 = 661829) B661829
theorem B1489805 : Blo 439778 1489805 := bstep (se 3 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 1489805 = 558677) B558677
theorem B441235 : Blo 439778 441235 := bstep (se 1 (by rfl) ⟨330926, by rfl⟩ : syracuseStep 441235 = 661853) B661853
theorem B441251 : Blo 439778 441251 := bstep (se 1 (by rfl) ⟨330938, by rfl⟩ : syracuseStep 441251 = 661877) B661877
theorem B441267 : Blo 439778 441267 := bstep (se 1 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 441267 = 661901) B661901
theorem B441283 : Blo 439778 441283 := bstep (se 1 (by rfl) ⟨330962, by rfl⟩ : syracuseStep 441283 = 661925) B661925
theorem B1489859 : Blo 439778 1489859 := bstep (se 1 (by rfl) ⟨1117394, by rfl⟩ : syracuseStep 1489859 = 2234789) B2234789
theorem B441299 : Blo 439778 441299 := bstep (se 1 (by rfl) ⟨330974, by rfl⟩ : syracuseStep 441299 = 661949) B661949
theorem B441315 : Blo 439778 441315 := bstep (se 1 (by rfl) ⟨330986, by rfl⟩ : syracuseStep 441315 = 661973) B661973
theorem B441331 : Blo 439778 441331 := bstep (se 1 (by rfl) ⟨330998, by rfl⟩ : syracuseStep 441331 = 661997) B661997
theorem B441347 : Blo 439778 441347 := bstep (se 1 (by rfl) ⟨331010, by rfl⟩ : syracuseStep 441347 = 662021) B662021
theorem B441363 : Blo 439778 441363 := bstep (se 1 (by rfl) ⟨331022, by rfl⟩ : syracuseStep 441363 = 662045) B662045
theorem B441379 : Blo 439778 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B441395 : Blo 439778 441395 := bstep (se 1 (by rfl) ⟨331046, by rfl⟩ : syracuseStep 441395 = 662093) B662093
theorem B441411 : Blo 439778 441411 := bstep (se 1 (by rfl) ⟨331058, by rfl⟩ : syracuseStep 441411 = 662117) B662117
theorem B1883213 : Blo 439778 1883213 := bstep (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) B706205
theorem B441427 : Blo 439778 441427 := bstep (se 1 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 441427 = 662141) B662141
theorem B441443 : Blo 439778 441443 := bstep (se 1 (by rfl) ⟨331082, by rfl⟩ : syracuseStep 441443 = 662165) B662165
theorem B441459 : Blo 439778 441459 := bstep (se 1 (by rfl) ⟨331094, by rfl⟩ : syracuseStep 441459 = 662189) B662189
theorem B441475 : Blo 439778 441475 := bstep (se 1 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 441475 = 662213) B662213
theorem B441491 : Blo 439778 441491 := bstep (se 1 (by rfl) ⟨331118, by rfl⟩ : syracuseStep 441491 = 662237) B662237
theorem B441507 : Blo 439778 441507 := bstep (se 1 (by rfl) ⟨331130, by rfl⟩ : syracuseStep 441507 = 662261) B662261
theorem B441523 : Blo 439778 441523 := bstep (se 1 (by rfl) ⟨331142, by rfl⟩ : syracuseStep 441523 = 662285) B662285
theorem B441539 : Blo 439778 441539 := bstep (se 1 (by rfl) ⟨331154, by rfl⟩ : syracuseStep 441539 = 662309) B662309
theorem B1490129 : Blo 439778 1490129 := bstep (se 2 (by rfl) ⟨558798, by rfl⟩ : syracuseStep 1490129 = 1117597) B1117597
theorem B441555 : Blo 439778 441555 := bstep (se 1 (by rfl) ⟨331166, by rfl⟩ : syracuseStep 441555 = 662333) B662333
theorem B441571 : Blo 439778 441571 := bstep (se 1 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 441571 = 662357) B662357
theorem B441587 : Blo 439778 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B441603 : Blo 439778 441603 := bstep (se 1 (by rfl) ⟨331202, by rfl⟩ : syracuseStep 441603 = 662405) B662405
theorem B441619 : Blo 439778 441619 := bstep (se 1 (by rfl) ⟨331214, by rfl⟩ : syracuseStep 441619 = 662429) B662429
theorem B2145571 : Blo 439778 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B441635 : Blo 439778 441635 := bstep (se 1 (by rfl) ⟨331226, by rfl⟩ : syracuseStep 441635 = 662453) B662453
theorem B441651 : Blo 439778 441651 := bstep (se 1 (by rfl) ⟨331238, by rfl⟩ : syracuseStep 441651 = 662477) B662477
theorem B441667 : Blo 439778 441667 := bstep (se 1 (by rfl) ⟨331250, by rfl⟩ : syracuseStep 441667 = 662501) B662501
theorem B441683 : Blo 439778 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B441699 : Blo 439778 441699 := bstep (se 1 (by rfl) ⟨331274, by rfl⟩ : syracuseStep 441699 = 662549) B662549
theorem B441715 : Blo 439778 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B441731 : Blo 439778 441731 := bstep (se 1 (by rfl) ⟨331298, by rfl⟩ : syracuseStep 441731 = 662597) B662597
theorem B441747 : Blo 439778 441747 := bstep (se 1 (by rfl) ⟨331310, by rfl⟩ : syracuseStep 441747 = 662621) B662621
theorem B441763 : Blo 439778 441763 := bstep (se 1 (by rfl) ⟨331322, by rfl⟩ : syracuseStep 441763 = 662645) B662645
theorem B441779 : Blo 439778 441779 := bstep (se 1 (by rfl) ⟨331334, by rfl⟩ : syracuseStep 441779 = 662669) B662669
theorem B441795 : Blo 439778 441795 := bstep (se 1 (by rfl) ⟨331346, by rfl⟩ : syracuseStep 441795 = 662693) B662693
theorem B441811 : Blo 439778 441811 := bstep (se 1 (by rfl) ⟨331358, by rfl⟩ : syracuseStep 441811 = 662717) B662717
theorem B2506211 : Blo 439778 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B441827 : Blo 439778 441827 := bstep (se 1 (by rfl) ⟨331370, by rfl⟩ : syracuseStep 441827 = 662741) B662741
theorem B441843 : Blo 439778 441843 := bstep (se 1 (by rfl) ⟨331382, by rfl⟩ : syracuseStep 441843 = 662765) B662765
theorem B441859 : Blo 439778 441859 := bstep (se 1 (by rfl) ⟨331394, by rfl⟩ : syracuseStep 441859 = 662789) B662789
theorem B441875 : Blo 439778 441875 := bstep (se 1 (by rfl) ⟨331406, by rfl⟩ : syracuseStep 441875 = 662813) B662813
theorem B441891 : Blo 439778 441891 := bstep (se 1 (by rfl) ⟨331418, by rfl⟩ : syracuseStep 441891 = 662837) B662837
theorem B1064497 : Blo 439778 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B441907 : Blo 439778 441907 := bstep (se 1 (by rfl) ⟨331430, by rfl⟩ : syracuseStep 441907 = 662861) B662861
theorem B6372917 : Blo 439778 6372917 := bstep (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) B597461
theorem B441923 : Blo 439778 441923 := bstep (se 1 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 441923 = 662885) B662885
theorem B441939 : Blo 439778 441939 := bstep (se 1 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 441939 = 662909) B662909
theorem B441955 : Blo 439778 441955 := bstep (se 1 (by rfl) ⟨331466, by rfl⟩ : syracuseStep 441955 = 662933) B662933
theorem B441971 : Blo 439778 441971 := bstep (se 1 (by rfl) ⟨331478, by rfl⟩ : syracuseStep 441971 = 662957) B662957
theorem B441987 : Blo 439778 441987 := bstep (se 1 (by rfl) ⟨331490, by rfl⟩ : syracuseStep 441987 = 662981) B662981
theorem B442003 : Blo 439778 442003 := bstep (se 1 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 442003 = 663005) B663005
theorem B442019 : Blo 439778 442019 := bstep (se 1 (by rfl) ⟨331514, by rfl⟩ : syracuseStep 442019 = 663029) B663029
theorem B442035 : Blo 439778 442035 := bstep (se 1 (by rfl) ⟨331526, by rfl⟩ : syracuseStep 442035 = 663053) B663053
theorem B835267 : Blo 439778 835267 := bstep (se 1 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 835267 = 1252901) B1252901
theorem B442051 : Blo 439778 442051 := bstep (se 1 (by rfl) ⟨331538, by rfl⟩ : syracuseStep 442051 = 663077) B663077
theorem B1261261 : Blo 439778 1261261 := bstep (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) B472973
theorem B442067 : Blo 439778 442067 := bstep (se 1 (by rfl) ⟨331550, by rfl⟩ : syracuseStep 442067 = 663101) B663101
theorem B442083 : Blo 439778 442083 := bstep (se 1 (by rfl) ⟨331562, by rfl⟩ : syracuseStep 442083 = 663125) B663125
theorem B1490669 : Blo 439778 1490669 := bstep (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) B559001
theorem B442099 : Blo 439778 442099 := bstep (se 1 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 442099 = 663149) B663149
theorem B442115 : Blo 439778 442115 := bstep (se 1 (by rfl) ⟨331586, by rfl⟩ : syracuseStep 442115 = 663173) B663173
theorem B442131 : Blo 439778 442131 := bstep (se 1 (by rfl) ⟨331598, by rfl⟩ : syracuseStep 442131 = 663197) B663197
theorem B1490723 : Blo 439778 1490723 := bstep (se 1 (by rfl) ⟨1118042, by rfl⟩ : syracuseStep 1490723 = 2236085) B2236085
theorem B442147 : Blo 439778 442147 := bstep (se 1 (by rfl) ⟨331610, by rfl⟩ : syracuseStep 442147 = 663221) B663221
theorem B442163 : Blo 439778 442163 := bstep (se 1 (by rfl) ⟨331622, by rfl⟩ : syracuseStep 442163 = 663245) B663245
theorem B442179 : Blo 439778 442179 := bstep (se 1 (by rfl) ⟨331634, by rfl⟩ : syracuseStep 442179 = 663269) B663269
theorem B442195 : Blo 439778 442195 := bstep (se 1 (by rfl) ⟨331646, by rfl⟩ : syracuseStep 442195 = 663293) B663293
theorem B835427 : Blo 439778 835427 := bstep (se 1 (by rfl) ⟨626570, by rfl⟩ : syracuseStep 835427 = 1253141) B1253141
theorem B442211 : Blo 439778 442211 := bstep (se 1 (by rfl) ⟨331658, by rfl⟩ : syracuseStep 442211 = 663317) B663317
theorem B442227 : Blo 439778 442227 := bstep (se 1 (by rfl) ⟨331670, by rfl⟩ : syracuseStep 442227 = 663341) B663341
theorem B442243 : Blo 439778 442243 := bstep (se 1 (by rfl) ⟨331682, by rfl⟩ : syracuseStep 442243 = 663365) B663365
theorem B442259 : Blo 439778 442259 := bstep (se 1 (by rfl) ⟨331694, by rfl⟩ : syracuseStep 442259 = 663389) B663389
theorem B442275 : Blo 439778 442275 := bstep (se 1 (by rfl) ⟨331706, by rfl⟩ : syracuseStep 442275 = 663413) B663413
theorem B1261489 : Blo 439778 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B442291 : Blo 439778 442291 := bstep (se 1 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 442291 = 663437) B663437
theorem B442307 : Blo 439778 442307 := bstep (se 1 (by rfl) ⟨331730, by rfl⟩ : syracuseStep 442307 = 663461) B663461
theorem B6799301 : Blo 439778 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B442323 : Blo 439778 442323 := bstep (se 1 (by rfl) ⟨331742, by rfl⟩ : syracuseStep 442323 = 663485) B663485
theorem B442339 : Blo 439778 442339 := bstep (se 1 (by rfl) ⟨331754, by rfl⟩ : syracuseStep 442339 = 663509) B663509
theorem B442355 : Blo 439778 442355 := bstep (se 1 (by rfl) ⟨331766, by rfl⟩ : syracuseStep 442355 = 663533) B663533
theorem B442371 : Blo 439778 442371 := bstep (se 1 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 442371 = 663557) B663557
theorem B442387 : Blo 439778 442387 := bstep (se 1 (by rfl) ⟨331790, by rfl⟩ : syracuseStep 442387 = 663581) B663581
theorem B442403 : Blo 439778 442403 := bstep (se 1 (by rfl) ⟨331802, by rfl⟩ : syracuseStep 442403 = 663605) B663605
theorem B1490993 : Blo 439778 1490993 := bstep (se 2 (by rfl) ⟨559122, by rfl⟩ : syracuseStep 1490993 = 1118245) B1118245
theorem B442419 : Blo 439778 442419 := bstep (se 1 (by rfl) ⟨331814, by rfl⟩ : syracuseStep 442419 = 663629) B663629
theorem B442435 : Blo 439778 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B1261649 : Blo 439778 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B442451 : Blo 439778 442451 := bstep (se 1 (by rfl) ⟨331838, by rfl⟩ : syracuseStep 442451 = 663677) B663677
theorem B442467 : Blo 439778 442467 := bstep (se 1 (by rfl) ⟨331850, by rfl⟩ : syracuseStep 442467 = 663701) B663701
theorem B442483 : Blo 439778 442483 := bstep (se 1 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 442483 = 663725) B663725
theorem B442499 : Blo 439778 442499 := bstep (se 1 (by rfl) ⟨331874, by rfl⟩ : syracuseStep 442499 = 663749) B663749
theorem B442515 : Blo 439778 442515 := bstep (se 1 (by rfl) ⟨331886, by rfl⟩ : syracuseStep 442515 = 663773) B663773
theorem B442531 : Blo 439778 442531 := bstep (se 1 (by rfl) ⟨331898, by rfl⟩ : syracuseStep 442531 = 663797) B663797
theorem B442547 : Blo 439778 442547 := bstep (se 1 (by rfl) ⟨331910, by rfl⟩ : syracuseStep 442547 = 663821) B663821
theorem B442563 : Blo 439778 442563 := bstep (se 1 (by rfl) ⟨331922, by rfl⟩ : syracuseStep 442563 = 663845) B663845
theorem B1261763 : Blo 439778 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B442579 : Blo 439778 442579 := bstep (se 1 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 442579 = 663869) B663869
theorem B442595 : Blo 439778 442595 := bstep (se 1 (by rfl) ⟨331946, by rfl⟩ : syracuseStep 442595 = 663893) B663893
theorem B442611 : Blo 439778 442611 := bstep (se 1 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 442611 = 663917) B663917
theorem B442627 : Blo 439778 442627 := bstep (se 1 (by rfl) ⟨331970, by rfl⟩ : syracuseStep 442627 = 663941) B663941
theorem B442643 : Blo 439778 442643 := bstep (se 1 (by rfl) ⟨331982, by rfl⟩ : syracuseStep 442643 = 663965) B663965
theorem B1589539 : Blo 439778 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B442659 : Blo 439778 442659 := bstep (se 1 (by rfl) ⟨331994, by rfl⟩ : syracuseStep 442659 = 663989) B663989
theorem B442675 : Blo 439778 442675 := bstep (se 1 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 442675 = 664013) B664013
theorem B442691 : Blo 439778 442691 := bstep (se 1 (by rfl) ⟨332018, by rfl⟩ : syracuseStep 442691 = 664037) B664037
theorem B442707 : Blo 439778 442707 := bstep (se 1 (by rfl) ⟨332030, by rfl⟩ : syracuseStep 442707 = 664061) B664061
theorem B442723 : Blo 439778 442723 := bstep (se 1 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 442723 = 664085) B664085
theorem B442739 : Blo 439778 442739 := bstep (se 1 (by rfl) ⟨332054, by rfl⟩ : syracuseStep 442739 = 664109) B664109
theorem B442755 : Blo 439778 442755 := bstep (se 1 (by rfl) ⟨332066, by rfl⟩ : syracuseStep 442755 = 664133) B664133
theorem B442771 : Blo 439778 442771 := bstep (se 1 (by rfl) ⟨332078, by rfl⟩ : syracuseStep 442771 = 664157) B664157
theorem B442787 : Blo 439778 442787 := bstep (se 1 (by rfl) ⟨332090, by rfl⟩ : syracuseStep 442787 = 664181) B664181
theorem B442803 : Blo 439778 442803 := bstep (se 1 (by rfl) ⟨332102, by rfl⟩ : syracuseStep 442803 = 664205) B664205
theorem B442819 : Blo 439778 442819 := bstep (se 1 (by rfl) ⟨332114, by rfl⟩ : syracuseStep 442819 = 664229) B664229
theorem B14336453 : Blo 439778 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B2507213 : Blo 439778 2507213 := bstep (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) B940205
theorem B442835 : Blo 439778 442835 := bstep (se 1 (by rfl) ⟨332126, by rfl⟩ : syracuseStep 442835 = 664253) B664253
theorem B442851 : Blo 439778 442851 := bstep (se 1 (by rfl) ⟨332138, by rfl⟩ : syracuseStep 442851 = 664277) B664277
theorem B442867 : Blo 439778 442867 := bstep (se 1 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 442867 = 664301) B664301
theorem B442883 : Blo 439778 442883 := bstep (se 1 (by rfl) ⟨332162, by rfl⟩ : syracuseStep 442883 = 664325) B664325
theorem B442899 : Blo 439778 442899 := bstep (se 1 (by rfl) ⟨332174, by rfl⟩ : syracuseStep 442899 = 664349) B664349
theorem B442915 : Blo 439778 442915 := bstep (se 1 (by rfl) ⟨332186, by rfl⟩ : syracuseStep 442915 = 664373) B664373
theorem B442931 : Blo 439778 442931 := bstep (se 1 (by rfl) ⟨332198, by rfl⟩ : syracuseStep 442931 = 664397) B664397
theorem B442947 : Blo 439778 442947 := bstep (se 1 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 442947 = 664421) B664421
theorem B1491533 : Blo 439778 1491533 := bstep (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) B559325
theorem B442963 : Blo 439778 442963 := bstep (se 1 (by rfl) ⟨332222, by rfl⟩ : syracuseStep 442963 = 664445) B664445
theorem B442979 : Blo 439778 442979 := bstep (se 1 (by rfl) ⟨332234, by rfl⟩ : syracuseStep 442979 = 664469) B664469
theorem B442995 : Blo 439778 442995 := bstep (se 1 (by rfl) ⟨332246, by rfl⟩ : syracuseStep 442995 = 664493) B664493
theorem B1491587 : Blo 439778 1491587 := bstep (se 1 (by rfl) ⟨1118690, by rfl⟩ : syracuseStep 1491587 = 2237381) B2237381
theorem B443011 : Blo 439778 443011 := bstep (se 1 (by rfl) ⟨332258, by rfl⟩ : syracuseStep 443011 = 664517) B664517
theorem B443027 : Blo 439778 443027 := bstep (se 1 (by rfl) ⟨332270, by rfl⟩ : syracuseStep 443027 = 664541) B664541
theorem B443043 : Blo 439778 443043 := bstep (se 1 (by rfl) ⟨332282, by rfl⟩ : syracuseStep 443043 = 664565) B664565
theorem B443059 : Blo 439778 443059 := bstep (se 1 (by rfl) ⟨332294, by rfl⟩ : syracuseStep 443059 = 664589) B664589
theorem B443075 : Blo 439778 443075 := bstep (se 1 (by rfl) ⟨332306, by rfl⟩ : syracuseStep 443075 = 664613) B664613
theorem B443091 : Blo 439778 443091 := bstep (se 1 (by rfl) ⟨332318, by rfl⟩ : syracuseStep 443091 = 664637) B664637
theorem B443107 : Blo 439778 443107 := bstep (se 1 (by rfl) ⟨332330, by rfl⟩ : syracuseStep 443107 = 664661) B664661
theorem B443123 : Blo 439778 443123 := bstep (se 1 (by rfl) ⟨332342, by rfl⟩ : syracuseStep 443123 = 664685) B664685
theorem B443139 : Blo 439778 443139 := bstep (se 1 (by rfl) ⟨332354, by rfl⟩ : syracuseStep 443139 = 664709) B664709
theorem B443155 : Blo 439778 443155 := bstep (se 1 (by rfl) ⟨332366, by rfl⟩ : syracuseStep 443155 = 664733) B664733
theorem B443171 : Blo 439778 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B443187 : Blo 439778 443187 := bstep (se 1 (by rfl) ⟨332390, by rfl⟩ : syracuseStep 443187 = 664781) B664781
theorem B443203 : Blo 439778 443203 := bstep (se 1 (by rfl) ⟨332402, by rfl⟩ : syracuseStep 443203 = 664805) B664805
theorem B443219 : Blo 439778 443219 := bstep (se 1 (by rfl) ⟨332414, by rfl⟩ : syracuseStep 443219 = 664829) B664829
theorem B443235 : Blo 439778 443235 := bstep (se 1 (by rfl) ⟨332426, by rfl⟩ : syracuseStep 443235 = 664853) B664853
theorem B443251 : Blo 439778 443251 := bstep (se 1 (by rfl) ⟨332438, by rfl⟩ : syracuseStep 443251 = 664877) B664877
theorem B443267 : Blo 439778 443267 := bstep (se 1 (by rfl) ⟨332450, by rfl⟩ : syracuseStep 443267 = 664901) B664901
theorem B836497 : Blo 439778 836497 := bstep (se 2 (by rfl) ⟨313686, by rfl⟩ : syracuseStep 836497 = 627373) B627373
theorem B1491857 : Blo 439778 1491857 := bstep (se 2 (by rfl) ⟨559446, by rfl⟩ : syracuseStep 1491857 = 1118893) B1118893
theorem B443283 : Blo 439778 443283 := bstep (se 1 (by rfl) ⟨332462, by rfl⟩ : syracuseStep 443283 = 664925) B664925
theorem B443299 : Blo 439778 443299 := bstep (se 1 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 443299 = 664949) B664949
theorem B443315 : Blo 439778 443315 := bstep (se 1 (by rfl) ⟨332486, by rfl⟩ : syracuseStep 443315 = 664973) B664973
theorem B443331 : Blo 439778 443331 := bstep (se 1 (by rfl) ⟨332498, by rfl⟩ : syracuseStep 443331 = 664997) B664997
theorem B443347 : Blo 439778 443347 := bstep (se 1 (by rfl) ⟨332510, by rfl⟩ : syracuseStep 443347 = 665021) B665021
theorem B443363 : Blo 439778 443363 := bstep (se 1 (by rfl) ⟨332522, by rfl⟩ : syracuseStep 443363 = 665045) B665045
theorem B443379 : Blo 439778 443379 := bstep (se 1 (by rfl) ⟨332534, by rfl⟩ : syracuseStep 443379 = 665069) B665069
theorem B443395 : Blo 439778 443395 := bstep (se 1 (by rfl) ⟨332546, by rfl⟩ : syracuseStep 443395 = 665093) B665093
theorem B443411 : Blo 439778 443411 := bstep (se 1 (by rfl) ⟨332558, by rfl⟩ : syracuseStep 443411 = 665117) B665117
theorem B443427 : Blo 439778 443427 := bstep (se 1 (by rfl) ⟨332570, by rfl⟩ : syracuseStep 443427 = 665141) B665141
theorem B443443 : Blo 439778 443443 := bstep (se 1 (by rfl) ⟨332582, by rfl⟩ : syracuseStep 443443 = 665165) B665165
theorem B443459 : Blo 439778 443459 := bstep (se 1 (by rfl) ⟨332594, by rfl⟩ : syracuseStep 443459 = 665189) B665189
theorem B443475 : Blo 439778 443475 := bstep (se 1 (by rfl) ⟨332606, by rfl⟩ : syracuseStep 443475 = 665213) B665213
theorem B443491 : Blo 439778 443491 := bstep (se 1 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 443491 = 665237) B665237
theorem B443507 : Blo 439778 443507 := bstep (se 1 (by rfl) ⟨332630, by rfl⟩ : syracuseStep 443507 = 665261) B665261
theorem B705667 : Blo 439778 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B443523 : Blo 439778 443523 := bstep (se 1 (by rfl) ⟨332642, by rfl⟩ : syracuseStep 443523 = 665285) B665285
theorem B443539 : Blo 439778 443539 := bstep (se 1 (by rfl) ⟨332654, by rfl⟩ : syracuseStep 443539 = 665309) B665309
theorem B443555 : Blo 439778 443555 := bstep (se 1 (by rfl) ⟨332666, by rfl⟩ : syracuseStep 443555 = 665333) B665333
theorem B1262765 : Blo 439778 1262765 := bstep (se 3 (by rfl) ⟨236768, by rfl⟩ : syracuseStep 1262765 = 473537) B473537
theorem B443571 : Blo 439778 443571 := bstep (se 1 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 443571 = 665357) B665357
theorem B443587 : Blo 439778 443587 := bstep (se 1 (by rfl) ⟨332690, by rfl⟩ : syracuseStep 443587 = 665381) B665381
theorem B443603 : Blo 439778 443603 := bstep (se 1 (by rfl) ⟨332702, by rfl⟩ : syracuseStep 443603 = 665405) B665405
theorem B705763 : Blo 439778 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B443619 : Blo 439778 443619 := bstep (se 1 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 443619 = 665429) B665429
theorem B443635 : Blo 439778 443635 := bstep (se 1 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 443635 = 665453) B665453
theorem B443651 : Blo 439778 443651 := bstep (se 1 (by rfl) ⟨332738, by rfl⟩ : syracuseStep 443651 = 665477) B665477
theorem B443667 : Blo 439778 443667 := bstep (se 1 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 443667 = 665501) B665501
theorem B443683 : Blo 439778 443683 := bstep (se 1 (by rfl) ⟨332762, by rfl⟩ : syracuseStep 443683 = 665525) B665525
theorem B443699 : Blo 439778 443699 := bstep (se 1 (by rfl) ⟨332774, by rfl⟩ : syracuseStep 443699 = 665549) B665549
theorem B443715 : Blo 439778 443715 := bstep (se 1 (by rfl) ⟨332786, by rfl⟩ : syracuseStep 443715 = 665573) B665573
theorem B443731 : Blo 439778 443731 := bstep (se 1 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 443731 = 665597) B665597
theorem B1262947 : Blo 439778 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B443747 : Blo 439778 443747 := bstep (se 1 (by rfl) ⟨332810, by rfl⟩ : syracuseStep 443747 = 665621) B665621
theorem B443763 : Blo 439778 443763 := bstep (se 1 (by rfl) ⟨332822, by rfl⟩ : syracuseStep 443763 = 665645) B665645
theorem B705923 : Blo 439778 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B607651 : Blo 439778 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B1492397 : Blo 439778 1492397 := bstep (se 3 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 1492397 = 559649) B559649
theorem B1492451 : Blo 439778 1492451 := bstep (se 1 (by rfl) ⟨1119338, by rfl⟩ : syracuseStep 1492451 = 2238677) B2238677
theorem B2246129 : Blo 439778 2246129 := bstep (se 2 (by rfl) ⟨842298, by rfl⟩ : syracuseStep 2246129 = 1684597) B1684597
theorem B1263107 : Blo 439778 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B1492721 : Blo 439778 1492721 := bstep (se 2 (by rfl) ⟨559770, by rfl⟩ : syracuseStep 1492721 = 1119541) B1119541
theorem B837553 : Blo 439778 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B1198253 : Blo 439778 1198253 := bstep (se 3 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 1198253 = 449345) B449345
theorem B1493261 : Blo 439778 1493261 := bstep (se 3 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 1493261 = 559973) B559973
theorem B674065 : Blo 439778 674065 := bstep (se 2 (by rfl) ⟨252774, by rfl⟩ : syracuseStep 674065 = 505549) B505549
theorem B837955 : Blo 439778 837955 := bstep (se 1 (by rfl) ⟨628466, by rfl⟩ : syracuseStep 837955 = 1256933) B1256933
theorem B1493315 : Blo 439778 1493315 := bstep (se 1 (by rfl) ⟨1119986, by rfl⟩ : syracuseStep 1493315 = 2239973) B2239973
theorem B706897 : Blo 439778 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B838001 : Blo 439778 838001 := bstep (se 2 (by rfl) ⟨314250, by rfl⟩ : syracuseStep 838001 = 628501) B628501
theorem B1493585 : Blo 439778 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B674401 : Blo 439778 674401 := bstep (se 2 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 674401 = 505801) B505801
theorem B838289 : Blo 439778 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B1821361 : Blo 439778 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1887245 : Blo 439778 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B1494125 : Blo 439778 1494125 := bstep (se 3 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 1494125 = 560297) B560297
theorem B1494179 : Blo 439778 1494179 := bstep (se 1 (by rfl) ⟨1120634, by rfl⟩ : syracuseStep 1494179 = 2241269) B2241269
theorem B2510129 : Blo 439778 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B1887587 : Blo 439778 1887587 := bstep (se 1 (by rfl) ⟨1415690, by rfl⟩ : syracuseStep 1887587 = 2831381) B2831381
theorem B839011 : Blo 439778 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B3362147 : Blo 439778 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B6344077 : Blo 439778 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B1494449 : Blo 439778 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B839459 : Blo 439778 839459 := bstep (se 1 (by rfl) ⟨629594, by rfl⟩ : syracuseStep 839459 = 1259189) B1259189
theorem B1888049 : Blo 439778 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B1920881 : Blo 439778 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B3592133 : Blo 439778 3592133 := bstep (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) B673525
theorem B1494989 : Blo 439778 1494989 := bstep (se 3 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 1494989 = 560621) B560621
theorem B708563 : Blo 439778 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B1495043 : Blo 439778 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B839747 : Blo 439778 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B708691 : Blo 439778 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B708755 : Blo 439778 708755 := bstep (se 1 (by rfl) ⟨531566, by rfl⟩ : syracuseStep 708755 = 1063133) B1063133
theorem B1495313 : Blo 439778 1495313 := bstep (se 2 (by rfl) ⟨560742, by rfl⟩ : syracuseStep 1495313 = 1121485) B1121485
theorem B709249 : Blo 439778 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B2118307 : Blo 439778 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B447139 : Blo 439778 447139 := bstep (se 1 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 447139 = 670709) B670709
theorem B2511587 : Blo 439778 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B1495853 : Blo 439778 1495853 := bstep (se 3 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 1495853 = 560945) B560945
theorem B742243 : Blo 439778 742243 := bstep (se 1 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 742243 = 1113365) B1113365
theorem B1495907 : Blo 439778 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B742385 : Blo 439778 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B840689 : Blo 439778 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B742513 : Blo 439778 742513 := bstep (se 2 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 742513 = 556885) B556885
theorem B1430641 : Blo 439778 1430641 := bstep (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) B1072981
theorem B1496177 : Blo 439778 1496177 := bstep (se 2 (by rfl) ⟨561066, by rfl⟩ : syracuseStep 1496177 = 1122133) B1122133
theorem B742547 : Blo 439778 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B742675 : Blo 439778 742675 := bstep (se 1 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 742675 = 1114013) B1114013
theorem B709921 : Blo 439778 709921 := bstep (se 2 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 709921 = 532441) B532441
theorem B939377 : Blo 439778 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B742817 : Blo 439778 742817 := bstep (se 2 (by rfl) ⟨278556, by rfl⟩ : syracuseStep 742817 = 557113) B557113
theorem B742945 : Blo 439778 742945 := bstep (se 2 (by rfl) ⟨278604, by rfl⟩ : syracuseStep 742945 = 557209) B557209
theorem B742979 : Blo 439778 742979 := bstep (se 1 (by rfl) ⟨557234, by rfl⟩ : syracuseStep 742979 = 1114469) B1114469
theorem B1496717 : Blo 439778 1496717 := bstep (se 3 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 1496717 = 561269) B561269
theorem B743107 : Blo 439778 743107 := bstep (se 1 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 743107 = 1114661) B1114661
theorem B1496771 : Blo 439778 1496771 := bstep (se 1 (by rfl) ⟨1122578, by rfl⟩ : syracuseStep 1496771 = 2245157) B2245157
theorem B743249 : Blo 439778 743249 := bstep (se 2 (by rfl) ⟨278718, by rfl⟩ : syracuseStep 743249 = 557437) B557437
theorem B448339 : Blo 439778 448339 := bstep (se 1 (by rfl) ⟨336254, by rfl⟩ : syracuseStep 448339 = 672509) B672509
theorem B2119537 : Blo 439778 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B841585 : Blo 439778 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B743377 : Blo 439778 743377 := bstep (se 2 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 743377 = 557533) B557533
theorem B1497041 : Blo 439778 1497041 := bstep (se 2 (by rfl) ⟨561390, by rfl⟩ : syracuseStep 1497041 = 1122781) B1122781
theorem B743411 : Blo 439778 743411 := bstep (se 1 (by rfl) ⟨557558, by rfl⟩ : syracuseStep 743411 = 1115117) B1115117
theorem B841745 : Blo 439778 841745 := bstep (se 2 (by rfl) ⟨315654, by rfl⟩ : syracuseStep 841745 = 631309) B631309
theorem B3790961 : Blo 439778 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B743539 : Blo 439778 743539 := bstep (se 1 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 743539 = 1115309) B1115309
theorem B1366253 : Blo 439778 1366253 := bstep (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) B512345
theorem B743681 : Blo 439778 743681 := bstep (se 2 (by rfl) ⟨278880, by rfl⟩ : syracuseStep 743681 = 557761) B557761
theorem B743809 : Blo 439778 743809 := bstep (se 2 (by rfl) ⟨278928, by rfl⟩ : syracuseStep 743809 = 557857) B557857
theorem B743843 : Blo 439778 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B842147 : Blo 439778 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B1497581 : Blo 439778 1497581 := bstep (se 3 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 1497581 = 561593) B561593
theorem B940547 : Blo 439778 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B743971 : Blo 439778 743971 := bstep (se 1 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 743971 = 1115957) B1115957
theorem B1497635 : Blo 439778 1497635 := bstep (se 1 (by rfl) ⟨1123226, by rfl⟩ : syracuseStep 1497635 = 2246453) B2246453
theorem B4381253 : Blo 439778 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B1137233 : Blo 439778 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B744113 : Blo 439778 744113 := bstep (se 2 (by rfl) ⟨279042, by rfl⟩ : syracuseStep 744113 = 558085) B558085
theorem B744241 : Blo 439778 744241 := bstep (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) B558181
theorem B744275 : Blo 439778 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B744403 : Blo 439778 744403 := bstep (se 1 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 744403 = 1116605) B1116605
theorem B1137649 : Blo 439778 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B744545 : Blo 439778 744545 := bstep (se 2 (by rfl) ⟨279204, by rfl⟩ : syracuseStep 744545 = 558409) B558409
theorem B2841733 : Blo 439778 2841733 := bstep (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) B532825
theorem B744673 : Blo 439778 744673 := bstep (se 2 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 744673 = 558505) B558505
theorem B744707 : Blo 439778 744707 := bstep (se 1 (by rfl) ⟨558530, by rfl⟩ : syracuseStep 744707 = 1117061) B1117061
theorem B1891619 : Blo 439778 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B744835 : Blo 439778 744835 := bstep (se 1 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 744835 = 1117253) B1117253
theorem B1007011 : Blo 439778 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B744977 : Blo 439778 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B745105 : Blo 439778 745105 := bstep (se 2 (by rfl) ⟨279414, by rfl⟩ : syracuseStep 745105 = 558829) B558829
theorem B1597091 : Blo 439778 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B745139 : Blo 439778 745139 := bstep (se 1 (by rfl) ⟨558854, by rfl⟩ : syracuseStep 745139 = 1117709) B1117709
theorem B745267 : Blo 439778 745267 := bstep (se 1 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 745267 = 1117901) B1117901
theorem B8052533 : Blo 439778 8052533 := bstep (se 5 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 8052533 = 754925) B754925
theorem B745409 : Blo 439778 745409 := bstep (se 2 (by rfl) ⟨279528, by rfl⟩ : syracuseStep 745409 = 559057) B559057
theorem B745537 : Blo 439778 745537 := bstep (se 2 (by rfl) ⟨279576, by rfl⟩ : syracuseStep 745537 = 559153) B559153
theorem B745571 : Blo 439778 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B1597553 : Blo 439778 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B745699 : Blo 439778 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B745841 : Blo 439778 745841 := bstep (se 2 (by rfl) ⟨279690, by rfl⟩ : syracuseStep 745841 = 559381) B559381
theorem B942563 : Blo 439778 942563 := bstep (se 1 (by rfl) ⟨706922, by rfl⟩ : syracuseStep 942563 = 1413845) B1413845
theorem B1696241 : Blo 439778 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B745969 : Blo 439778 745969 := bstep (se 2 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 745969 = 559477) B559477
theorem B746003 : Blo 439778 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B3367493 : Blo 439778 3367493 := bstep (se 4 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 3367493 = 631405) B631405
theorem B746131 : Blo 439778 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B2548493 : Blo 439778 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B746273 : Blo 439778 746273 := bstep (se 2 (by rfl) ⟨279852, by rfl⟩ : syracuseStep 746273 = 559705) B559705
theorem B746401 : Blo 439778 746401 := bstep (se 2 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 746401 = 559801) B559801
theorem B746435 : Blo 439778 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B3761093 : Blo 439778 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B746563 : Blo 439778 746563 := bstep (se 1 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 746563 = 1119845) B1119845
theorem B746705 : Blo 439778 746705 := bstep (se 2 (by rfl) ⟨280014, by rfl⟩ : syracuseStep 746705 = 560029) B560029
theorem B746833 : Blo 439778 746833 := bstep (se 2 (by rfl) ⟨280062, by rfl⟩ : syracuseStep 746833 = 560125) B560125
theorem B746867 : Blo 439778 746867 := bstep (se 1 (by rfl) ⟨560150, by rfl⟩ : syracuseStep 746867 = 1120301) B1120301
theorem B746995 : Blo 439778 746995 := bstep (se 1 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 746995 = 1120493) B1120493
theorem B681587 : Blo 439778 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B747137 : Blo 439778 747137 := bstep (se 2 (by rfl) ⟨280176, by rfl⟩ : syracuseStep 747137 = 560353) B560353
theorem B2123441 : Blo 439778 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B747265 : Blo 439778 747265 := bstep (se 2 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 747265 = 560449) B560449
theorem B747299 : Blo 439778 747299 := bstep (se 1 (by rfl) ⟨560474, by rfl⟩ : syracuseStep 747299 = 1120949) B1120949
theorem B747427 : Blo 439778 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B747569 : Blo 439778 747569 := bstep (se 2 (by rfl) ⟨280338, by rfl⟩ : syracuseStep 747569 = 560677) B560677
theorem B452755 : Blo 439778 452755 := bstep (se 1 (by rfl) ⟨339566, by rfl⟩ : syracuseStep 452755 = 679133) B679133
theorem B747697 : Blo 439778 747697 := bstep (se 2 (by rfl) ⟨280386, by rfl⟩ : syracuseStep 747697 = 560773) B560773
theorem B747731 : Blo 439778 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B747859 : Blo 439778 747859 := bstep (se 1 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 747859 = 1121789) B1121789
theorem B944579 : Blo 439778 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B748001 : Blo 439778 748001 := bstep (se 2 (by rfl) ⟨280500, by rfl⟩ : syracuseStep 748001 = 561001) B561001
theorem B748129 : Blo 439778 748129 := bstep (se 2 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 748129 = 561097) B561097
theorem B748163 : Blo 439778 748163 := bstep (se 1 (by rfl) ⟨561122, by rfl⟩ : syracuseStep 748163 = 1122245) B1122245
theorem B748291 : Blo 439778 748291 := bstep (se 1 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 748291 = 1122437) B1122437
theorem B4254605 : Blo 439778 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B1895309 : Blo 439778 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B748433 : Blo 439778 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B1895345 : Blo 439778 1895345 := bstep (se 2 (by rfl) ⟨710754, by rfl⟩ : syracuseStep 1895345 = 1421509) B1421509
theorem B715763 : Blo 439778 715763 := bstep (se 1 (by rfl) ⟨536822, by rfl⟩ : syracuseStep 715763 = 1073645) B1073645
theorem B748561 : Blo 439778 748561 := bstep (se 2 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 748561 = 561421) B561421
theorem B2583587 : Blo 439778 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B748595 : Blo 439778 748595 := bstep (se 1 (by rfl) ⟨561446, by rfl⟩ : syracuseStep 748595 = 1122893) B1122893
theorem B5729393 : Blo 439778 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B748723 : Blo 439778 748723 := bstep (se 1 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 748723 = 1123085) B1123085
theorem B3566861 : Blo 439778 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B748865 : Blo 439778 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B2387333 : Blo 439778 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B5041763 : Blo 439778 5041763 := bstep (se 1 (by rfl) ⟨3781322, by rfl⟩ : syracuseStep 5041763 = 7562645) B7562645
theorem B945827 : Blo 439778 945827 := bstep (se 1 (by rfl) ⟨709370, by rfl⟩ : syracuseStep 945827 = 1418741) B1418741
theorem B749251 : Blo 439778 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B4419269 : Blo 439778 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B847651 : Blo 439778 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B2125901 : Blo 439778 2125901 := bstep (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) B797213
theorem B946417 : Blo 439778 946417 := bstep (se 2 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 946417 = 709813) B709813
theorem B2389283 : Blo 439778 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B2520517 : Blo 439778 2520517 := bstep (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) B472597
theorem B4553059 : Blo 439778 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B2259377 : Blo 439778 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B1505837 : Blo 439778 1505837 := bstep (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) B564689
theorem B2259533 : Blo 439778 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B2226851 : Blo 439778 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B752483 : Blo 439778 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B4258757 : Blo 439778 4258757 := bstep (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) B798517
theorem B719971 : Blo 439778 719971 := bstep (se 1 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 719971 = 1079957) B1079957
theorem B1670321 : Blo 439778 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B2522501 : Blo 439778 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B2686385 : Blo 439778 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B2227661 : Blo 439778 2227661 := bstep (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) B835373
theorem B556627 : Blo 439778 556627 := bstep (se 1 (by rfl) ⟨417470, by rfl⟩ : syracuseStep 556627 = 834941) B834941
theorem B1277549 : Blo 439778 1277549 := bstep (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) B479081
theorem B556723 : Blo 439778 556723 := bstep (se 1 (by rfl) ⟨417542, by rfl⟩ : syracuseStep 556723 = 835085) B835085
theorem B1343267 : Blo 439778 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B1670989 : Blo 439778 1670989 := bstep (se 3 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 1670989 = 626621) B626621
theorem B3342221 : Blo 439778 3342221 := bstep (se 3 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 3342221 = 1253333) B1253333
theorem B1114033 : Blo 439778 1114033 := bstep (se 2 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 1114033 = 835525) B835525
theorem B753617 : Blo 439778 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B1343459 : Blo 439778 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B1671475 : Blo 439778 1671475 := bstep (se 1 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 1671475 = 2507213) B2507213
theorem B1114519 : Blo 439778 1114519 := bstep (se 1 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 1114519 = 1671779) B1671779
theorem B4784791 : Blo 439778 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B1114955 : Blo 439778 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1115329 : Blo 439778 1115329 := bstep (se 2 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 1115329 = 836497) B836497
theorem B4523309 : Blo 439778 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B13731185 : Blo 439778 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B1672721 : Blo 439778 1672721 := bstep (se 2 (by rfl) ⟨627270, by rfl⟩ : syracuseStep 1672721 = 1254541) B1254541
theorem B558667 : Blo 439778 558667 := bstep (se 1 (by rfl) ⟨419000, by rfl⟩ : syracuseStep 558667 = 838001) B838001
theorem B1115927 : Blo 439778 1115927 := bstep (se 1 (by rfl) ⟨836945, by rfl⟩ : syracuseStep 1115927 = 1673891) B1673891
theorem B2230091 : Blo 439778 2230091 := bstep (se 1 (by rfl) ⟨1672568, by rfl⟩ : syracuseStep 2230091 = 3345137) B3345137
theorem B1673419 : Blo 439778 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B1673693 : Blo 439778 1673693 := bstep (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) B627635
theorem B559639 : Blo 439778 559639 := bstep (se 1 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 559639 = 839459) B839459
theorem B1116737 : Blo 439778 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B2394755 : Blo 439778 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B5671781 : Blo 439778 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B1117273 : Blo 439778 1117273 := bstep (se 2 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 1117273 = 837955) B837955
theorem B1674391 : Blo 439778 1674391 := bstep (se 1 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 1674391 = 2511587) B2511587
theorem B494923 : Blo 439778 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B560459 : Blo 439778 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B2690405 : Blo 439778 2690405 := bstep (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) B504451
theorem B495031 : Blo 439778 495031 := bstep (se 1 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 495031 = 742547) B742547
theorem B2231873 : Blo 439778 2231873 := bstep (se 2 (by rfl) ⟨836952, by rfl⟩ : syracuseStep 2231873 = 1673905) B1673905
theorem B2428481 : Blo 439778 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B495211 : Blo 439778 495211 := bstep (se 1 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 495211 = 742817) B742817
theorem B495319 : Blo 439778 495319 := bstep (se 1 (by rfl) ⟨371489, by rfl⟩ : syracuseStep 495319 = 742979) B742979
theorem B495499 : Blo 439778 495499 := bstep (se 1 (by rfl) ⟨371624, by rfl⟩ : syracuseStep 495499 = 743249) B743249
theorem B1675181 : Blo 439778 1675181 := bstep (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) B628193
theorem B495607 : Blo 439778 495607 := bstep (se 1 (by rfl) ⟨371705, by rfl⟩ : syracuseStep 495607 = 743411) B743411
theorem B561163 : Blo 439778 561163 := bstep (se 1 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 561163 = 841745) B841745
theorem B2527307 : Blo 439778 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B495787 : Blo 439778 495787 := bstep (se 1 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 495787 = 743681) B743681
theorem B1118387 : Blo 439778 1118387 := bstep (se 1 (by rfl) ⟨838790, by rfl⟩ : syracuseStep 1118387 = 1677581) B1677581
theorem B659723 : Blo 439778 659723 := bstep (se 1 (by rfl) ⟨494792, by rfl⟩ : syracuseStep 659723 = 989585) B989585
theorem B659735 : Blo 439778 659735 := bstep (se 1 (by rfl) ⟨494801, by rfl⟩ : syracuseStep 659735 = 989603) B989603
theorem B495895 : Blo 439778 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B561431 : Blo 439778 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B627031 : Blo 439778 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B659801 : Blo 439778 659801 := bstep (se 2 (by rfl) ⟨247425, by rfl⟩ : syracuseStep 659801 = 494851) B494851
theorem B2920835 : Blo 439778 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B758155 : Blo 439778 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B659915 : Blo 439778 659915 := bstep (se 1 (by rfl) ⟨494936, by rfl⟩ : syracuseStep 659915 = 989873) B989873
theorem B496075 : Blo 439778 496075 := bstep (se 1 (by rfl) ⟨372056, by rfl⟩ : syracuseStep 496075 = 744113) B744113
theorem B659927 : Blo 439778 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B1118681 : Blo 439778 1118681 := bstep (se 2 (by rfl) ⟨419505, by rfl⟩ : syracuseStep 1118681 = 839011) B839011
theorem B8458769 : Blo 439778 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B659993 : Blo 439778 659993 := bstep (se 2 (by rfl) ⟨247497, by rfl⟩ : syracuseStep 659993 = 494995) B494995
theorem B496183 : Blo 439778 496183 := bstep (se 1 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 496183 = 744275) B744275
theorem B660107 : Blo 439778 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B660119 : Blo 439778 660119 := bstep (se 1 (by rfl) ⟨495089, by rfl⟩ : syracuseStep 660119 = 990179) B990179
theorem B660185 : Blo 439778 660185 := bstep (se 2 (by rfl) ⟨247569, by rfl⟩ : syracuseStep 660185 = 495139) B495139
theorem B496363 : Blo 439778 496363 := bstep (se 1 (by rfl) ⟨372272, by rfl⟩ : syracuseStep 496363 = 744545) B744545
theorem B660299 : Blo 439778 660299 := bstep (se 1 (by rfl) ⟨495224, by rfl⟩ : syracuseStep 660299 = 990449) B990449
theorem B660311 : Blo 439778 660311 := bstep (se 1 (by rfl) ⟨495233, by rfl⟩ : syracuseStep 660311 = 990467) B990467
theorem B496471 : Blo 439778 496471 := bstep (se 1 (by rfl) ⟨372353, by rfl⟩ : syracuseStep 496471 = 744707) B744707
theorem B3183461 : Blo 439778 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B660377 : Blo 439778 660377 := bstep (se 2 (by rfl) ⟨247641, by rfl⟩ : syracuseStep 660377 = 495283) B495283
theorem B5378995 : Blo 439778 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B660491 : Blo 439778 660491 := bstep (se 1 (by rfl) ⟨495368, by rfl⟩ : syracuseStep 660491 = 990737) B990737
theorem B496651 : Blo 439778 496651 := bstep (se 1 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 496651 = 744977) B744977
theorem B660503 : Blo 439778 660503 := bstep (se 1 (by rfl) ⟨495377, by rfl⟩ : syracuseStep 660503 = 990755) B990755
theorem B660569 : Blo 439778 660569 := bstep (se 2 (by rfl) ⟨247713, by rfl⟩ : syracuseStep 660569 = 495427) B495427
theorem B496759 : Blo 439778 496759 := bstep (se 1 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 496759 = 745139) B745139
theorem B660683 : Blo 439778 660683 := bstep (se 1 (by rfl) ⟨495512, by rfl⟩ : syracuseStep 660683 = 991025) B991025
theorem B660695 : Blo 439778 660695 := bstep (se 1 (by rfl) ⟨495521, by rfl⟩ : syracuseStep 660695 = 991043) B991043
theorem B660761 : Blo 439778 660761 := bstep (se 2 (by rfl) ⟨247785, by rfl⟩ : syracuseStep 660761 = 495571) B495571
theorem B496939 : Blo 439778 496939 := bstep (se 1 (by rfl) ⟨372704, by rfl⟩ : syracuseStep 496939 = 745409) B745409
theorem B1676609 : Blo 439778 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B660875 : Blo 439778 660875 := bstep (se 1 (by rfl) ⟨495656, by rfl⟩ : syracuseStep 660875 = 991313) B991313
theorem B660887 : Blo 439778 660887 := bstep (se 1 (by rfl) ⟨495665, by rfl⟩ : syracuseStep 660887 = 991331) B991331
theorem B497047 : Blo 439778 497047 := bstep (se 1 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 497047 = 745571) B745571
theorem B660953 : Blo 439778 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B2233817 : Blo 439778 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B661067 : Blo 439778 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B497227 : Blo 439778 497227 := bstep (se 1 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 497227 = 745841) B745841
theorem B661079 : Blo 439778 661079 := bstep (se 1 (by rfl) ⟨495809, by rfl⟩ : syracuseStep 661079 = 991619) B991619
theorem B661145 : Blo 439778 661145 := bstep (se 2 (by rfl) ⟨247929, by rfl⟩ : syracuseStep 661145 = 495859) B495859
theorem B497335 : Blo 439778 497335 := bstep (se 1 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 497335 = 746003) B746003
theorem B661259 : Blo 439778 661259 := bstep (se 1 (by rfl) ⟨495944, by rfl⟩ : syracuseStep 661259 = 991889) B991889
theorem B661271 : Blo 439778 661271 := bstep (se 1 (by rfl) ⟨495953, by rfl⟩ : syracuseStep 661271 = 991907) B991907
theorem B661337 : Blo 439778 661337 := bstep (se 2 (by rfl) ⟨248001, by rfl⟩ : syracuseStep 661337 = 496003) B496003
theorem B3839845 : Blo 439778 3839845 := bstep (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) B719971
theorem B497515 : Blo 439778 497515 := bstep (se 1 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 497515 = 746273) B746273
theorem B661451 : Blo 439778 661451 := bstep (se 1 (by rfl) ⟨496088, by rfl⟩ : syracuseStep 661451 = 992177) B992177
theorem B661463 : Blo 439778 661463 := bstep (se 1 (by rfl) ⟨496097, by rfl⟩ : syracuseStep 661463 = 992195) B992195
theorem B497623 : Blo 439778 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B661529 : Blo 439778 661529 := bstep (se 2 (by rfl) ⟨248073, by rfl⟩ : syracuseStep 661529 = 496147) B496147
theorem B1120331 : Blo 439778 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B1022081 : Blo 439778 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B661643 : Blo 439778 661643 := bstep (se 1 (by rfl) ⟨496232, by rfl⟩ : syracuseStep 661643 = 992465) B992465
theorem B497803 : Blo 439778 497803 := bstep (se 1 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 497803 = 746705) B746705
theorem B661655 : Blo 439778 661655 := bstep (se 1 (by rfl) ⟨496241, by rfl⟩ : syracuseStep 661655 = 992483) B992483
theorem B792779 : Blo 439778 792779 := bstep (se 1 (by rfl) ⟨594584, by rfl⟩ : syracuseStep 792779 = 1189169) B1189169
theorem B2824409 : Blo 439778 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B661721 : Blo 439778 661721 := bstep (se 2 (by rfl) ⟨248145, by rfl⟩ : syracuseStep 661721 = 496291) B496291
theorem B497911 : Blo 439778 497911 := bstep (se 1 (by rfl) ⟨373433, by rfl⟩ : syracuseStep 497911 = 746867) B746867
theorem B661835 : Blo 439778 661835 := bstep (se 1 (by rfl) ⟨496376, by rfl⟩ : syracuseStep 661835 = 992753) B992753
theorem B661847 : Blo 439778 661847 := bstep (se 1 (by rfl) ⟨496385, by rfl⟩ : syracuseStep 661847 = 992771) B992771
theorem B661913 : Blo 439778 661913 := bstep (se 2 (by rfl) ⟨248217, by rfl⟩ : syracuseStep 661913 = 496435) B496435
theorem B498091 : Blo 439778 498091 := bstep (se 1 (by rfl) ⟨373568, by rfl⟩ : syracuseStep 498091 = 747137) B747137
theorem B1415627 : Blo 439778 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B989657 : Blo 439778 989657 := bstep (se 2 (by rfl) ⟨371121, by rfl⟩ : syracuseStep 989657 = 742243) B742243
theorem B662027 : Blo 439778 662027 := bstep (se 1 (by rfl) ⟨496520, by rfl⟩ : syracuseStep 662027 = 993041) B993041
theorem B662039 : Blo 439778 662039 := bstep (se 1 (by rfl) ⟨496529, by rfl⟩ : syracuseStep 662039 = 993059) B993059
theorem B498199 : Blo 439778 498199 := bstep (se 1 (by rfl) ⟨373649, by rfl⟩ : syracuseStep 498199 = 747299) B747299
theorem B989747 : Blo 439778 989747 := bstep (se 1 (by rfl) ⟨742310, by rfl⟩ : syracuseStep 989747 = 1484621) B1484621
theorem B989783 : Blo 439778 989783 := bstep (se 1 (by rfl) ⟨742337, by rfl⟩ : syracuseStep 989783 = 1484675) B1484675
theorem B662105 : Blo 439778 662105 := bstep (se 2 (by rfl) ⟨248289, by rfl⟩ : syracuseStep 662105 = 496579) B496579
theorem B793241 : Blo 439778 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B662219 : Blo 439778 662219 := bstep (se 1 (by rfl) ⟨496664, by rfl⟩ : syracuseStep 662219 = 993329) B993329
theorem B498379 : Blo 439778 498379 := bstep (se 1 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 498379 = 747569) B747569
theorem B662231 : Blo 439778 662231 := bstep (se 1 (by rfl) ⟨496673, by rfl⟩ : syracuseStep 662231 = 993347) B993347
theorem B989963 : Blo 439778 989963 := bstep (se 1 (by rfl) ⟨742472, by rfl⟩ : syracuseStep 989963 = 1484945) B1484945
theorem B531211 : Blo 439778 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B1678097 : Blo 439778 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B662297 : Blo 439778 662297 := bstep (se 2 (by rfl) ⟨248361, by rfl⟩ : syracuseStep 662297 = 496723) B496723
theorem B498487 : Blo 439778 498487 := bstep (se 1 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 498487 = 747731) B747731
theorem B990017 : Blo 439778 990017 := bstep (se 2 (by rfl) ⟨371256, by rfl⟩ : syracuseStep 990017 = 742513) B742513
theorem B11443045 : Blo 439778 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B662411 : Blo 439778 662411 := bstep (se 1 (by rfl) ⟨496808, by rfl⟩ : syracuseStep 662411 = 993617) B993617
theorem B662423 : Blo 439778 662423 := bstep (se 1 (by rfl) ⟨496817, by rfl⟩ : syracuseStep 662423 = 993635) B993635
theorem B793523 : Blo 439778 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B793559 : Blo 439778 793559 := bstep (se 1 (by rfl) ⟨595169, by rfl⟩ : syracuseStep 793559 = 1190339) B1190339
theorem B662489 : Blo 439778 662489 := bstep (se 2 (by rfl) ⟨248433, by rfl⟩ : syracuseStep 662489 = 496867) B496867
theorem B498667 : Blo 439778 498667 := bstep (se 1 (by rfl) ⟨374000, by rfl⟩ : syracuseStep 498667 = 748001) B748001
theorem B1121303 : Blo 439778 1121303 := bstep (se 1 (by rfl) ⟨840977, by rfl⟩ : syracuseStep 1121303 = 1681955) B1681955
theorem B990233 : Blo 439778 990233 := bstep (se 2 (by rfl) ⟨371337, by rfl⟩ : syracuseStep 990233 = 742675) B742675
theorem B2235437 : Blo 439778 2235437 := bstep (se 3 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 2235437 = 838289) B838289
theorem B662603 : Blo 439778 662603 := bstep (se 1 (by rfl) ⟨496952, by rfl⟩ : syracuseStep 662603 = 993905) B993905
theorem B662615 : Blo 439778 662615 := bstep (se 1 (by rfl) ⟨496961, by rfl⟩ : syracuseStep 662615 = 993923) B993923
theorem B498775 : Blo 439778 498775 := bstep (se 1 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 498775 = 748163) B748163
theorem B990323 : Blo 439778 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B531595 : Blo 439778 531595 := bstep (se 1 (by rfl) ⟨398696, by rfl⟩ : syracuseStep 531595 = 797393) B797393
theorem B990359 : Blo 439778 990359 := bstep (se 1 (by rfl) ⟨742769, by rfl⟩ : syracuseStep 990359 = 1485539) B1485539
theorem B662681 : Blo 439778 662681 := bstep (se 2 (by rfl) ⟨248505, by rfl⟩ : syracuseStep 662681 = 497011) B497011
theorem B1678553 : Blo 439778 1678553 := bstep (se 2 (by rfl) ⟨629457, by rfl⟩ : syracuseStep 1678553 = 1258915) B1258915
theorem B662795 : Blo 439778 662795 := bstep (se 1 (by rfl) ⟨497096, by rfl⟩ : syracuseStep 662795 = 994193) B994193
theorem B498955 : Blo 439778 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B662807 : Blo 439778 662807 := bstep (se 1 (by rfl) ⟨497105, by rfl⟩ : syracuseStep 662807 = 994211) B994211
theorem B990539 : Blo 439778 990539 := bstep (se 1 (by rfl) ⟨742904, by rfl⟩ : syracuseStep 990539 = 1485809) B1485809
theorem B662873 : Blo 439778 662873 := bstep (se 2 (by rfl) ⟨248577, by rfl⟩ : syracuseStep 662873 = 497155) B497155
theorem B499063 : Blo 439778 499063 := bstep (se 1 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 499063 = 748595) B748595
theorem B990593 : Blo 439778 990593 := bstep (se 2 (by rfl) ⟨371472, by rfl⟩ : syracuseStep 990593 = 742945) B742945
theorem B1678765 : Blo 439778 1678765 := bstep (se 3 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 1678765 = 629537) B629537
theorem B662987 : Blo 439778 662987 := bstep (se 1 (by rfl) ⟨497240, by rfl⟩ : syracuseStep 662987 = 994481) B994481
theorem B662999 : Blo 439778 662999 := bstep (se 1 (by rfl) ⟨497249, by rfl⟩ : syracuseStep 662999 = 994499) B994499
theorem B663065 : Blo 439778 663065 := bstep (se 2 (by rfl) ⟨248649, by rfl⟩ : syracuseStep 663065 = 497299) B497299
theorem B499243 : Blo 439778 499243 := bstep (se 1 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 499243 = 748865) B748865
theorem B990809 : Blo 439778 990809 := bstep (se 2 (by rfl) ⟨371553, by rfl⟩ : syracuseStep 990809 = 743107) B743107
theorem B663179 : Blo 439778 663179 := bstep (se 1 (by rfl) ⟨497384, by rfl⟩ : syracuseStep 663179 = 994769) B994769
theorem B1253015 : Blo 439778 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B663191 : Blo 439778 663191 := bstep (se 1 (by rfl) ⟨497393, by rfl⟩ : syracuseStep 663191 = 994787) B994787
theorem B990899 : Blo 439778 990899 := bstep (se 1 (by rfl) ⟨743174, by rfl⟩ : syracuseStep 990899 = 1486349) B1486349
theorem B1121971 : Blo 439778 1121971 := bstep (se 1 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 1121971 = 1682957) B1682957
theorem B990935 : Blo 439778 990935 := bstep (se 1 (by rfl) ⟨743201, by rfl⟩ : syracuseStep 990935 = 1486403) B1486403
theorem B663257 : Blo 439778 663257 := bstep (se 2 (by rfl) ⟨248721, by rfl⟩ : syracuseStep 663257 = 497443) B497443
theorem B1679069 : Blo 439778 1679069 := bstep (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) B629651
theorem B630551 : Blo 439778 630551 := bstep (se 1 (by rfl) ⟨472913, by rfl⟩ : syracuseStep 630551 = 945827) B945827
theorem B597785 : Blo 439778 597785 := bstep (se 2 (by rfl) ⟨224169, by rfl⟩ : syracuseStep 597785 = 448339) B448339
theorem B2826049 : Blo 439778 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1122113 : Blo 439778 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B663371 : Blo 439778 663371 := bstep (se 1 (by rfl) ⟨497528, by rfl⟩ : syracuseStep 663371 = 995057) B995057
theorem B663383 : Blo 439778 663383 := bstep (se 1 (by rfl) ⟨497537, by rfl⟩ : syracuseStep 663383 = 995075) B995075
theorem B991115 : Blo 439778 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B663449 : Blo 439778 663449 := bstep (se 2 (by rfl) ⟨248793, by rfl⟩ : syracuseStep 663449 = 497587) B497587
theorem B991169 : Blo 439778 991169 := bstep (se 2 (by rfl) ⟨371688, by rfl⟩ : syracuseStep 991169 = 743377) B743377
theorem B663563 : Blo 439778 663563 := bstep (se 1 (by rfl) ⟨497672, by rfl⟩ : syracuseStep 663563 = 995345) B995345
theorem B663575 : Blo 439778 663575 := bstep (se 1 (by rfl) ⟨497681, by rfl⟩ : syracuseStep 663575 = 995363) B995363
theorem B1417267 : Blo 439778 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B663641 : Blo 439778 663641 := bstep (se 2 (by rfl) ⟨248865, by rfl⟩ : syracuseStep 663641 = 497731) B497731
theorem B991385 : Blo 439778 991385 := bstep (se 2 (by rfl) ⟨371769, by rfl⟩ : syracuseStep 991385 = 743539) B743539
theorem B1024153 : Blo 439778 1024153 := bstep (se 2 (by rfl) ⟨384057, by rfl⟩ : syracuseStep 1024153 = 768115) B768115
theorem B1417409 : Blo 439778 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B663755 : Blo 439778 663755 := bstep (se 1 (by rfl) ⟨497816, by rfl⟩ : syracuseStep 663755 = 995633) B995633
theorem B663767 : Blo 439778 663767 := bstep (se 1 (by rfl) ⟨497825, by rfl⟩ : syracuseStep 663767 = 995651) B995651
theorem B991475 : Blo 439778 991475 := bstep (se 1 (by rfl) ⟨743606, by rfl⟩ : syracuseStep 991475 = 1487213) B1487213
theorem B991511 : Blo 439778 991511 := bstep (se 1 (by rfl) ⟨743633, by rfl⟩ : syracuseStep 991511 = 1487267) B1487267
theorem B532759 : Blo 439778 532759 := bstep (se 1 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 532759 = 799139) B799139
theorem B663833 : Blo 439778 663833 := bstep (se 2 (by rfl) ⟨248937, by rfl⟩ : syracuseStep 663833 = 497875) B497875
theorem B3776813 : Blo 439778 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B663947 : Blo 439778 663947 := bstep (se 1 (by rfl) ⟨497960, by rfl⟩ : syracuseStep 663947 = 995921) B995921
theorem B663959 : Blo 439778 663959 := bstep (se 1 (by rfl) ⟨497969, by rfl⟩ : syracuseStep 663959 = 995939) B995939
theorem B991691 : Blo 439778 991691 := bstep (se 1 (by rfl) ⟨743768, by rfl⟩ : syracuseStep 991691 = 1487537) B1487537
theorem B664025 : Blo 439778 664025 := bstep (se 2 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 664025 = 498019) B498019
theorem B6070745 : Blo 439778 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B991745 : Blo 439778 991745 := bstep (se 2 (by rfl) ⟨371904, by rfl⟩ : syracuseStep 991745 = 743809) B743809
theorem B664139 : Blo 439778 664139 := bstep (se 1 (by rfl) ⟨498104, by rfl⟩ : syracuseStep 664139 = 996209) B996209
theorem B664151 : Blo 439778 664151 := bstep (se 1 (by rfl) ⟨498113, by rfl⟩ : syracuseStep 664151 = 996227) B996227
theorem B664217 : Blo 439778 664217 := bstep (se 2 (by rfl) ⟨249081, by rfl⟩ : syracuseStep 664217 = 498163) B498163
theorem B991961 : Blo 439778 991961 := bstep (se 2 (by rfl) ⟨371985, by rfl⟩ : syracuseStep 991961 = 743971) B743971
theorem B664331 : Blo 439778 664331 := bstep (se 1 (by rfl) ⟨498248, by rfl⟩ : syracuseStep 664331 = 996497) B996497
theorem B664343 : Blo 439778 664343 := bstep (se 1 (by rfl) ⟨498257, by rfl⟩ : syracuseStep 664343 = 996515) B996515
theorem B992051 : Blo 439778 992051 := bstep (se 1 (by rfl) ⟨744038, by rfl⟩ : syracuseStep 992051 = 1488077) B1488077
theorem B992087 : Blo 439778 992087 := bstep (se 1 (by rfl) ⟨744065, by rfl⟩ : syracuseStep 992087 = 1488131) B1488131
theorem B664409 : Blo 439778 664409 := bstep (se 2 (by rfl) ⟨249153, by rfl⟩ : syracuseStep 664409 = 498307) B498307
theorem B3810199 : Blo 439778 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B664523 : Blo 439778 664523 := bstep (se 1 (by rfl) ⟨498392, by rfl⟩ : syracuseStep 664523 = 996785) B996785
theorem B664535 : Blo 439778 664535 := bstep (se 1 (by rfl) ⟨498401, by rfl⟩ : syracuseStep 664535 = 996803) B996803
theorem B893953 : Blo 439778 893953 := bstep (se 2 (by rfl) ⟨335232, by rfl⟩ : syracuseStep 893953 = 670465) B670465
theorem B992267 : Blo 439778 992267 := bstep (se 1 (by rfl) ⟨744200, by rfl⟩ : syracuseStep 992267 = 1488401) B1488401
theorem B6366221 : Blo 439778 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B664601 : Blo 439778 664601 := bstep (se 2 (by rfl) ⟨249225, by rfl⟩ : syracuseStep 664601 = 498451) B498451
theorem B992321 : Blo 439778 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B664715 : Blo 439778 664715 := bstep (se 1 (by rfl) ⟨498536, by rfl⟩ : syracuseStep 664715 = 997073) B997073
theorem B664727 : Blo 439778 664727 := bstep (se 1 (by rfl) ⟨498545, by rfl⟩ : syracuseStep 664727 = 997091) B997091
theorem B664793 : Blo 439778 664793 := bstep (se 2 (by rfl) ⟨249297, by rfl⟩ : syracuseStep 664793 = 498595) B498595
theorem B992537 : Blo 439778 992537 := bstep (se 2 (by rfl) ⟨372201, by rfl⟩ : syracuseStep 992537 = 744403) B744403
theorem B1516865 : Blo 439778 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B664907 : Blo 439778 664907 := bstep (se 1 (by rfl) ⟨498680, by rfl⟩ : syracuseStep 664907 = 997361) B997361
theorem B664919 : Blo 439778 664919 := bstep (se 1 (by rfl) ⟨498689, by rfl⟩ : syracuseStep 664919 = 997379) B997379
theorem B992627 : Blo 439778 992627 := bstep (se 1 (by rfl) ⟨744470, by rfl⟩ : syracuseStep 992627 = 1488941) B1488941
theorem B992663 : Blo 439778 992663 := bstep (se 1 (by rfl) ⟨744497, by rfl⟩ : syracuseStep 992663 = 1488995) B1488995
theorem B664985 : Blo 439778 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B665099 : Blo 439778 665099 := bstep (se 1 (by rfl) ⟨498824, by rfl⟩ : syracuseStep 665099 = 997649) B997649
theorem B665111 : Blo 439778 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B796211 : Blo 439778 796211 := bstep (se 1 (by rfl) ⟨597158, by rfl⟩ : syracuseStep 796211 = 1194317) B1194317
theorem B1189451 : Blo 439778 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B992843 : Blo 439778 992843 := bstep (se 1 (by rfl) ⟨744632, by rfl⟩ : syracuseStep 992843 = 1489265) B1489265
theorem B665177 : Blo 439778 665177 := bstep (se 2 (by rfl) ⟨249441, by rfl⟩ : syracuseStep 665177 = 498883) B498883
theorem B992897 : Blo 439778 992897 := bstep (se 2 (by rfl) ⟨372336, by rfl⟩ : syracuseStep 992897 = 744673) B744673
theorem B665291 : Blo 439778 665291 := bstep (se 1 (by rfl) ⟨498968, by rfl⟩ : syracuseStep 665291 = 997937) B997937
theorem B665303 : Blo 439778 665303 := bstep (se 1 (by rfl) ⟨498977, by rfl⟩ : syracuseStep 665303 = 997955) B997955
theorem B1484567 : Blo 439778 1484567 := bstep (se 1 (by rfl) ⟨1113425, by rfl⟩ : syracuseStep 1484567 = 2226851) B2226851
theorem B665369 : Blo 439778 665369 := bstep (se 2 (by rfl) ⟨249513, by rfl⟩ : syracuseStep 665369 = 499027) B499027
theorem B993113 : Blo 439778 993113 := bstep (se 2 (by rfl) ⟨372417, by rfl⟩ : syracuseStep 993113 = 744835) B744835
theorem B665483 : Blo 439778 665483 := bstep (se 1 (by rfl) ⟨499112, by rfl⟩ : syracuseStep 665483 = 998225) B998225
theorem B501655 : Blo 439778 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B665495 : Blo 439778 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B993203 : Blo 439778 993203 := bstep (se 1 (by rfl) ⟨744902, by rfl⟩ : syracuseStep 993203 = 1489805) B1489805
theorem B993239 : Blo 439778 993239 := bstep (se 1 (by rfl) ⟨744929, by rfl⟩ : syracuseStep 993239 = 1489859) B1489859
theorem B665561 : Blo 439778 665561 := bstep (se 2 (by rfl) ⟨249585, by rfl⟩ : syracuseStep 665561 = 499171) B499171
theorem B1255475 : Blo 439778 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1419329 : Blo 439778 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B993419 : Blo 439778 993419 := bstep (se 1 (by rfl) ⟨745064, by rfl⟩ : syracuseStep 993419 = 1490129) B1490129
theorem B993473 : Blo 439778 993473 := bstep (se 2 (by rfl) ⟨372552, by rfl⟩ : syracuseStep 993473 = 745105) B745105
theorem B1681667 : Blo 439778 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1681681 : Blo 439778 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B5122349 : Blo 439778 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B1485107 : Blo 439778 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B993689 : Blo 439778 993689 := bstep (se 2 (by rfl) ⟨372633, by rfl⟩ : syracuseStep 993689 = 745267) B745267
theorem B993779 : Blo 439778 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B993815 : Blo 439778 993815 := bstep (se 1 (by rfl) ⟨745361, by rfl⟩ : syracuseStep 993815 = 1490723) B1490723
theorem B895511 : Blo 439778 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B1485377 : Blo 439778 1485377 := bstep (se 2 (by rfl) ⟨557016, by rfl⟩ : syracuseStep 1485377 = 1114033) B1114033
theorem B797249 : Blo 439778 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B1681985 : Blo 439778 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B3582557 : Blo 439778 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B1419869 : Blo 439778 1419869 := bstep (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) B532451
theorem B4532867 : Blo 439778 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B502411 : Blo 439778 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B993995 : Blo 439778 993995 := bstep (se 1 (by rfl) ⟨745496, by rfl⟩ : syracuseStep 993995 = 1490993) B1490993
theorem B994049 : Blo 439778 994049 := bstep (se 2 (by rfl) ⟨372768, by rfl⟩ : syracuseStep 994049 = 745537) B745537
theorem B2239325 : Blo 439778 2239325 := bstep (se 3 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 2239325 = 839747) B839747
theorem B994265 : Blo 439778 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B994355 : Blo 439778 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B994391 : Blo 439778 994391 := bstep (se 1 (by rfl) ⟨745793, by rfl⟩ : syracuseStep 994391 = 1491587) B1491587
theorem B1485917 : Blo 439778 1485917 := bstep (se 3 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 1485917 = 557219) B557219
theorem B1060057 : Blo 439778 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B1682653 : Blo 439778 1682653 := bstep (se 3 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 1682653 = 630995) B630995
theorem B994571 : Blo 439778 994571 := bstep (se 1 (by rfl) ⟨745928, by rfl⟩ : syracuseStep 994571 = 1491857) B1491857
theorem B2829613 : Blo 439778 2829613 := bstep (se 3 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 2829613 = 1061105) B1061105
theorem B994625 : Blo 439778 994625 := bstep (se 2 (by rfl) ⟨372984, by rfl⟩ : syracuseStep 994625 = 745969) B745969
theorem B994841 : Blo 439778 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B470615 : Blo 439778 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B994931 : Blo 439778 994931 := bstep (se 1 (by rfl) ⟨746198, by rfl⟩ : syracuseStep 994931 = 1492397) B1492397
theorem B4238999 : Blo 439778 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B994967 : Blo 439778 994967 := bstep (se 1 (by rfl) ⟨746225, by rfl⟩ : syracuseStep 994967 = 1492451) B1492451
theorem B995147 : Blo 439778 995147 := bstep (se 1 (by rfl) ⟨746360, by rfl⟩ : syracuseStep 995147 = 1492721) B1492721
theorem B995201 : Blo 439778 995201 := bstep (se 2 (by rfl) ⟨373200, by rfl⟩ : syracuseStep 995201 = 746401) B746401
theorem B3780503 : Blo 439778 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B995417 : Blo 439778 995417 := bstep (se 2 (by rfl) ⟨373281, by rfl⟩ : syracuseStep 995417 = 746563) B746563
theorem B798835 : Blo 439778 798835 := bstep (se 1 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 798835 = 1198253) B1198253
theorem B995507 : Blo 439778 995507 := bstep (se 1 (by rfl) ⟨746630, by rfl⟩ : syracuseStep 995507 = 1493261) B1493261
theorem B1487051 : Blo 439778 1487051 := bstep (se 1 (by rfl) ⟨1115288, by rfl⟩ : syracuseStep 1487051 = 2230577) B2230577
theorem B995543 : Blo 439778 995543 := bstep (se 1 (by rfl) ⟨746657, by rfl⟩ : syracuseStep 995543 = 1493315) B1493315
theorem B995723 : Blo 439778 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B995777 : Blo 439778 995777 := bstep (se 2 (by rfl) ⟨373416, by rfl⟩ : syracuseStep 995777 = 746833) B746833
theorem B1487321 : Blo 439778 1487321 := bstep (se 2 (by rfl) ⟨557745, by rfl⟩ : syracuseStep 1487321 = 1115491) B1115491
theorem B1683929 : Blo 439778 1683929 := bstep (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) B1262947
theorem B995993 : Blo 439778 995993 := bstep (se 2 (by rfl) ⟨373497, by rfl⟩ : syracuseStep 995993 = 746995) B746995
theorem B1258163 : Blo 439778 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B996083 : Blo 439778 996083 := bstep (se 1 (by rfl) ⟨747062, by rfl⟩ : syracuseStep 996083 = 1494125) B1494125
theorem B996119 : Blo 439778 996119 := bstep (se 1 (by rfl) ⟨747089, by rfl⟩ : syracuseStep 996119 = 1494179) B1494179
theorem B2011979 : Blo 439778 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B1258391 : Blo 439778 1258391 := bstep (se 1 (by rfl) ⟨943793, by rfl⟩ : syracuseStep 1258391 = 1887587) B1887587
theorem B2241431 : Blo 439778 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B2012107 : Blo 439778 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B996299 : Blo 439778 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B996353 : Blo 439778 996353 := bstep (se 2 (by rfl) ⟨373632, by rfl⟩ : syracuseStep 996353 = 747265) B747265
theorem B1488023 : Blo 439778 1488023 := bstep (se 1 (by rfl) ⟨1116017, by rfl⟩ : syracuseStep 1488023 = 2232035) B2232035
theorem B1258699 : Blo 439778 1258699 := bstep (se 1 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 1258699 = 1888049) B1888049
theorem B996569 : Blo 439778 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B996659 : Blo 439778 996659 := bstep (se 1 (by rfl) ⟨747494, by rfl⟩ : syracuseStep 996659 = 1494989) B1494989
theorem B472375 : Blo 439778 472375 := bstep (se 1 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 472375 = 708563) B708563
theorem B996695 : Blo 439778 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B5354869 : Blo 439778 5354869 := bstep (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) B502019
theorem B1258973 : Blo 439778 1258973 := bstep (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) B472115
theorem B439787 : Blo 439778 439787 := bstep (se 1 (by rfl) ⟨329840, by rfl⟩ : syracuseStep 439787 = 659681) B659681
theorem B439799 : Blo 439778 439799 := bstep (se 1 (by rfl) ⟨329849, by rfl⟩ : syracuseStep 439799 = 659699) B659699
theorem B439819 : Blo 439778 439819 := bstep (se 1 (by rfl) ⟨329864, by rfl⟩ : syracuseStep 439819 = 659729) B659729
theorem B996875 : Blo 439778 996875 := bstep (se 1 (by rfl) ⟨747656, by rfl⟩ : syracuseStep 996875 = 1495313) B1495313
theorem B439831 : Blo 439778 439831 := bstep (se 1 (by rfl) ⟨329873, by rfl⟩ : syracuseStep 439831 = 659747) B659747
theorem B603673 : Blo 439778 603673 := bstep (se 2 (by rfl) ⟨226377, by rfl⟩ : syracuseStep 603673 = 452755) B452755
theorem B439851 : Blo 439778 439851 := bstep (se 1 (by rfl) ⟨329888, by rfl⟩ : syracuseStep 439851 = 659777) B659777
theorem B439863 : Blo 439778 439863 := bstep (se 1 (by rfl) ⟨329897, by rfl⟩ : syracuseStep 439863 = 659795) B659795
theorem B996929 : Blo 439778 996929 := bstep (se 2 (by rfl) ⟨373848, by rfl⟩ : syracuseStep 996929 = 747697) B747697
theorem B439883 : Blo 439778 439883 := bstep (se 1 (by rfl) ⟨329912, by rfl⟩ : syracuseStep 439883 = 659825) B659825
theorem B439895 : Blo 439778 439895 := bstep (se 1 (by rfl) ⟨329921, by rfl⟩ : syracuseStep 439895 = 659843) B659843
theorem B439915 : Blo 439778 439915 := bstep (se 1 (by rfl) ⟨329936, by rfl⟩ : syracuseStep 439915 = 659873) B659873
theorem B439927 : Blo 439778 439927 := bstep (se 1 (by rfl) ⟨329945, by rfl⟩ : syracuseStep 439927 = 659891) B659891
theorem B439947 : Blo 439778 439947 := bstep (se 1 (by rfl) ⟨329960, by rfl⟩ : syracuseStep 439947 = 659921) B659921
theorem B439959 : Blo 439778 439959 := bstep (se 1 (by rfl) ⟨329969, by rfl⟩ : syracuseStep 439959 = 659939) B659939
theorem B439979 : Blo 439778 439979 := bstep (se 1 (by rfl) ⟨329984, by rfl⟩ : syracuseStep 439979 = 659969) B659969
theorem B1488563 : Blo 439778 1488563 := bstep (se 1 (by rfl) ⟨1116422, by rfl⟩ : syracuseStep 1488563 = 2232845) B2232845
theorem B439991 : Blo 439778 439991 := bstep (se 1 (by rfl) ⟨329993, by rfl⟩ : syracuseStep 439991 = 659987) B659987
theorem B440011 : Blo 439778 440011 := bstep (se 1 (by rfl) ⟨330008, by rfl⟩ : syracuseStep 440011 = 660017) B660017
theorem B440023 : Blo 439778 440023 := bstep (se 1 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 440023 = 660035) B660035
theorem B440043 : Blo 439778 440043 := bstep (se 1 (by rfl) ⟨330032, by rfl⟩ : syracuseStep 440043 = 660065) B660065
theorem B440055 : Blo 439778 440055 := bstep (se 1 (by rfl) ⟨330041, by rfl⟩ : syracuseStep 440055 = 660083) B660083
theorem B440075 : Blo 439778 440075 := bstep (se 1 (by rfl) ⟨330056, by rfl⟩ : syracuseStep 440075 = 660113) B660113
theorem B440087 : Blo 439778 440087 := bstep (se 1 (by rfl) ⟨330065, by rfl⟩ : syracuseStep 440087 = 660131) B660131
theorem B997145 : Blo 439778 997145 := bstep (se 2 (by rfl) ⟨373929, by rfl⟩ : syracuseStep 997145 = 747859) B747859
theorem B440107 : Blo 439778 440107 := bstep (se 1 (by rfl) ⟨330080, by rfl⟩ : syracuseStep 440107 = 660161) B660161
theorem B440119 : Blo 439778 440119 := bstep (se 1 (by rfl) ⟨330089, by rfl⟩ : syracuseStep 440119 = 660179) B660179
theorem B440139 : Blo 439778 440139 := bstep (se 1 (by rfl) ⟨330104, by rfl⟩ : syracuseStep 440139 = 660209) B660209
theorem B440151 : Blo 439778 440151 := bstep (se 1 (by rfl) ⟨330113, by rfl⟩ : syracuseStep 440151 = 660227) B660227
theorem B440171 : Blo 439778 440171 := bstep (se 1 (by rfl) ⟨330128, by rfl⟩ : syracuseStep 440171 = 660257) B660257
theorem B997235 : Blo 439778 997235 := bstep (se 1 (by rfl) ⟨747926, by rfl⟩ : syracuseStep 997235 = 1495853) B1495853
theorem B440183 : Blo 439778 440183 := bstep (se 1 (by rfl) ⟨330137, by rfl⟩ : syracuseStep 440183 = 660275) B660275
theorem B440203 : Blo 439778 440203 := bstep (se 1 (by rfl) ⟨330152, by rfl⟩ : syracuseStep 440203 = 660305) B660305
theorem B440215 : Blo 439778 440215 := bstep (se 1 (by rfl) ⟨330161, by rfl⟩ : syracuseStep 440215 = 660323) B660323
theorem B997271 : Blo 439778 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B440235 : Blo 439778 440235 := bstep (se 1 (by rfl) ⟨330176, by rfl⟩ : syracuseStep 440235 = 660353) B660353
theorem B440247 : Blo 439778 440247 := bstep (se 1 (by rfl) ⟨330185, by rfl⟩ : syracuseStep 440247 = 660371) B660371
theorem B1488833 : Blo 439778 1488833 := bstep (se 2 (by rfl) ⟨558312, by rfl⟩ : syracuseStep 1488833 = 1116625) B1116625
theorem B440267 : Blo 439778 440267 := bstep (se 1 (by rfl) ⟨330200, by rfl⟩ : syracuseStep 440267 = 660401) B660401
theorem B440279 : Blo 439778 440279 := bstep (se 1 (by rfl) ⟨330209, by rfl⟩ : syracuseStep 440279 = 660419) B660419
theorem B440299 : Blo 439778 440299 := bstep (se 1 (by rfl) ⟨330224, by rfl⟩ : syracuseStep 440299 = 660449) B660449
theorem B440311 : Blo 439778 440311 := bstep (se 1 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 440311 = 660467) B660467
theorem B440331 : Blo 439778 440331 := bstep (se 1 (by rfl) ⟨330248, by rfl⟩ : syracuseStep 440331 = 660497) B660497
theorem B440343 : Blo 439778 440343 := bstep (se 1 (by rfl) ⟨330257, by rfl⟩ : syracuseStep 440343 = 660515) B660515
theorem B899095 : Blo 439778 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B440363 : Blo 439778 440363 := bstep (se 1 (by rfl) ⟨330272, by rfl⟩ : syracuseStep 440363 = 660545) B660545
theorem B440375 : Blo 439778 440375 := bstep (se 1 (by rfl) ⟨330281, by rfl⟩ : syracuseStep 440375 = 660563) B660563
theorem B440395 : Blo 439778 440395 := bstep (se 1 (by rfl) ⟨330296, by rfl⟩ : syracuseStep 440395 = 660593) B660593
theorem B1882187 : Blo 439778 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B997451 : Blo 439778 997451 := bstep (se 1 (by rfl) ⟨748088, by rfl⟩ : syracuseStep 997451 = 1496177) B1496177
theorem B440407 : Blo 439778 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B440427 : Blo 439778 440427 := bstep (se 1 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 440427 = 660641) B660641
theorem B440439 : Blo 439778 440439 := bstep (se 1 (by rfl) ⟨330329, by rfl⟩ : syracuseStep 440439 = 660659) B660659
theorem B997505 : Blo 439778 997505 := bstep (se 2 (by rfl) ⟨374064, by rfl⟩ : syracuseStep 997505 = 748129) B748129
theorem B899201 : Blo 439778 899201 := bstep (se 2 (by rfl) ⟨337200, by rfl⟩ : syracuseStep 899201 = 674401) B674401
theorem B440459 : Blo 439778 440459 := bstep (se 1 (by rfl) ⟨330344, by rfl⟩ : syracuseStep 440459 = 660689) B660689
theorem B440471 : Blo 439778 440471 := bstep (se 1 (by rfl) ⟨330353, by rfl⟩ : syracuseStep 440471 = 660707) B660707
theorem B440491 : Blo 439778 440491 := bstep (se 1 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 440491 = 660737) B660737
theorem B440503 : Blo 439778 440503 := bstep (se 1 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 440503 = 660755) B660755
theorem B440523 : Blo 439778 440523 := bstep (se 1 (by rfl) ⟨330392, by rfl⟩ : syracuseStep 440523 = 660785) B660785
theorem B440535 : Blo 439778 440535 := bstep (se 1 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 440535 = 660803) B660803
theorem B440555 : Blo 439778 440555 := bstep (se 1 (by rfl) ⟨330416, by rfl⟩ : syracuseStep 440555 = 660833) B660833
theorem B440567 : Blo 439778 440567 := bstep (se 1 (by rfl) ⟨330425, by rfl⟩ : syracuseStep 440567 = 660851) B660851
theorem B2013443 : Blo 439778 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B440587 : Blo 439778 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B440599 : Blo 439778 440599 := bstep (se 1 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 440599 = 660899) B660899
theorem B440619 : Blo 439778 440619 := bstep (se 1 (by rfl) ⟨330464, by rfl⟩ : syracuseStep 440619 = 660929) B660929
theorem B2505005 : Blo 439778 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B440631 : Blo 439778 440631 := bstep (se 1 (by rfl) ⟨330473, by rfl⟩ : syracuseStep 440631 = 660947) B660947
theorem B440651 : Blo 439778 440651 := bstep (se 1 (by rfl) ⟨330488, by rfl⟩ : syracuseStep 440651 = 660977) B660977
theorem B440663 : Blo 439778 440663 := bstep (se 1 (by rfl) ⟨330497, by rfl⟩ : syracuseStep 440663 = 660995) B660995
theorem B997721 : Blo 439778 997721 := bstep (se 2 (by rfl) ⟨374145, by rfl⟩ : syracuseStep 997721 = 748291) B748291
theorem B440683 : Blo 439778 440683 := bstep (se 1 (by rfl) ⟨330512, by rfl⟩ : syracuseStep 440683 = 661025) B661025
theorem B440695 : Blo 439778 440695 := bstep (se 1 (by rfl) ⟨330521, by rfl⟩ : syracuseStep 440695 = 661043) B661043
theorem B440715 : Blo 439778 440715 := bstep (se 1 (by rfl) ⟨330536, by rfl⟩ : syracuseStep 440715 = 661073) B661073
theorem B440727 : Blo 439778 440727 := bstep (se 1 (by rfl) ⟨330545, by rfl⟩ : syracuseStep 440727 = 661091) B661091
theorem B440747 : Blo 439778 440747 := bstep (se 1 (by rfl) ⟨330560, by rfl⟩ : syracuseStep 440747 = 661121) B661121
theorem B997811 : Blo 439778 997811 := bstep (se 1 (by rfl) ⟨748358, by rfl⟩ : syracuseStep 997811 = 1496717) B1496717
theorem B440759 : Blo 439778 440759 := bstep (se 1 (by rfl) ⟨330569, by rfl⟩ : syracuseStep 440759 = 661139) B661139
theorem B440779 : Blo 439778 440779 := bstep (se 1 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 440779 = 661169) B661169
theorem B440791 : Blo 439778 440791 := bstep (se 1 (by rfl) ⟨330593, by rfl⟩ : syracuseStep 440791 = 661187) B661187
theorem B997847 : Blo 439778 997847 := bstep (se 1 (by rfl) ⟨748385, by rfl⟩ : syracuseStep 997847 = 1496771) B1496771
theorem B1489373 : Blo 439778 1489373 := bstep (se 3 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 1489373 = 558515) B558515
theorem B440811 : Blo 439778 440811 := bstep (se 1 (by rfl) ⟨330608, by rfl⟩ : syracuseStep 440811 = 661217) B661217
theorem B440823 : Blo 439778 440823 := bstep (se 1 (by rfl) ⟨330617, by rfl⟩ : syracuseStep 440823 = 661235) B661235
theorem B440843 : Blo 439778 440843 := bstep (se 1 (by rfl) ⟨330632, by rfl⟩ : syracuseStep 440843 = 661265) B661265
theorem B440855 : Blo 439778 440855 := bstep (se 1 (by rfl) ⟨330641, by rfl⟩ : syracuseStep 440855 = 661283) B661283
theorem B440875 : Blo 439778 440875 := bstep (se 1 (by rfl) ⟨330656, by rfl⟩ : syracuseStep 440875 = 661313) B661313
theorem B440887 : Blo 439778 440887 := bstep (se 1 (by rfl) ⟨330665, by rfl⟩ : syracuseStep 440887 = 661331) B661331
theorem B440907 : Blo 439778 440907 := bstep (se 1 (by rfl) ⟨330680, by rfl⟩ : syracuseStep 440907 = 661361) B661361
theorem B440919 : Blo 439778 440919 := bstep (se 1 (by rfl) ⟨330689, by rfl⟩ : syracuseStep 440919 = 661379) B661379
theorem B440939 : Blo 439778 440939 := bstep (se 1 (by rfl) ⟨330704, by rfl⟩ : syracuseStep 440939 = 661409) B661409
theorem B440951 : Blo 439778 440951 := bstep (se 1 (by rfl) ⟨330713, by rfl⟩ : syracuseStep 440951 = 661427) B661427
theorem B440971 : Blo 439778 440971 := bstep (se 1 (by rfl) ⟨330728, by rfl⟩ : syracuseStep 440971 = 661457) B661457
theorem B998027 : Blo 439778 998027 := bstep (se 1 (by rfl) ⟨748520, by rfl⟩ : syracuseStep 998027 = 1497041) B1497041
theorem B440983 : Blo 439778 440983 := bstep (se 1 (by rfl) ⟨330737, by rfl⟩ : syracuseStep 440983 = 661475) B661475
theorem B441003 : Blo 439778 441003 := bstep (se 1 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 441003 = 661505) B661505
theorem B441015 : Blo 439778 441015 := bstep (se 1 (by rfl) ⟨330761, by rfl⟩ : syracuseStep 441015 = 661523) B661523
theorem B998081 : Blo 439778 998081 := bstep (se 2 (by rfl) ⟨374280, by rfl⟩ : syracuseStep 998081 = 748561) B748561
theorem B441035 : Blo 439778 441035 := bstep (se 1 (by rfl) ⟨330776, by rfl⟩ : syracuseStep 441035 = 661553) B661553
theorem B441047 : Blo 439778 441047 := bstep (se 1 (by rfl) ⟨330785, by rfl⟩ : syracuseStep 441047 = 661571) B661571
theorem B441067 : Blo 439778 441067 := bstep (se 1 (by rfl) ⟨330800, by rfl⟩ : syracuseStep 441067 = 661601) B661601
theorem B441079 : Blo 439778 441079 := bstep (se 1 (by rfl) ⟨330809, by rfl⟩ : syracuseStep 441079 = 661619) B661619
theorem B441099 : Blo 439778 441099 := bstep (se 1 (by rfl) ⟨330824, by rfl⟩ : syracuseStep 441099 = 661649) B661649
theorem B441111 : Blo 439778 441111 := bstep (se 1 (by rfl) ⟨330833, by rfl⟩ : syracuseStep 441111 = 661667) B661667
theorem B441131 : Blo 439778 441131 := bstep (se 1 (by rfl) ⟨330848, by rfl⟩ : syracuseStep 441131 = 661697) B661697
theorem B441143 : Blo 439778 441143 := bstep (se 1 (by rfl) ⟨330857, by rfl⟩ : syracuseStep 441143 = 661715) B661715
theorem B441163 : Blo 439778 441163 := bstep (se 1 (by rfl) ⟨330872, by rfl⟩ : syracuseStep 441163 = 661745) B661745
theorem B441175 : Blo 439778 441175 := bstep (se 1 (by rfl) ⟨330881, by rfl⟩ : syracuseStep 441175 = 661763) B661763
theorem B441195 : Blo 439778 441195 := bstep (se 1 (by rfl) ⟨330896, by rfl⟩ : syracuseStep 441195 = 661793) B661793
theorem B441207 : Blo 439778 441207 := bstep (se 1 (by rfl) ⟨330905, by rfl⟩ : syracuseStep 441207 = 661811) B661811
theorem B441227 : Blo 439778 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B441239 : Blo 439778 441239 := bstep (se 1 (by rfl) ⟨330929, by rfl⟩ : syracuseStep 441239 = 661859) B661859
theorem B998297 : Blo 439778 998297 := bstep (se 2 (by rfl) ⟨374361, by rfl⟩ : syracuseStep 998297 = 748723) B748723
theorem B441259 : Blo 439778 441259 := bstep (se 1 (by rfl) ⟨330944, by rfl⟩ : syracuseStep 441259 = 661889) B661889
theorem B441271 : Blo 439778 441271 := bstep (se 1 (by rfl) ⟨330953, by rfl⟩ : syracuseStep 441271 = 661907) B661907
theorem B441291 : Blo 439778 441291 := bstep (se 1 (by rfl) ⟨330968, by rfl⟩ : syracuseStep 441291 = 661937) B661937
theorem B441303 : Blo 439778 441303 := bstep (se 1 (by rfl) ⟨330977, by rfl⟩ : syracuseStep 441303 = 661955) B661955
theorem B441323 : Blo 439778 441323 := bstep (se 1 (by rfl) ⟨330992, by rfl⟩ : syracuseStep 441323 = 661985) B661985
theorem B998387 : Blo 439778 998387 := bstep (se 1 (by rfl) ⟨748790, by rfl⟩ : syracuseStep 998387 = 1497581) B1497581
theorem B441335 : Blo 439778 441335 := bstep (se 1 (by rfl) ⟨331001, by rfl⟩ : syracuseStep 441335 = 662003) B662003
theorem B441355 : Blo 439778 441355 := bstep (se 1 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 441355 = 662033) B662033
theorem B1588241 : Blo 439778 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B441367 : Blo 439778 441367 := bstep (se 1 (by rfl) ⟨331025, by rfl⟩ : syracuseStep 441367 = 662051) B662051
theorem B998423 : Blo 439778 998423 := bstep (se 1 (by rfl) ⟨748817, by rfl⟩ : syracuseStep 998423 = 1497635) B1497635
theorem B441387 : Blo 439778 441387 := bstep (se 1 (by rfl) ⟨331040, by rfl⟩ : syracuseStep 441387 = 662081) B662081
theorem B441399 : Blo 439778 441399 := bstep (se 1 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 441399 = 662099) B662099
theorem B441419 : Blo 439778 441419 := bstep (se 1 (by rfl) ⟨331064, by rfl⟩ : syracuseStep 441419 = 662129) B662129
theorem B441431 : Blo 439778 441431 := bstep (se 1 (by rfl) ⟨331073, by rfl⟩ : syracuseStep 441431 = 662147) B662147
theorem B441451 : Blo 439778 441451 := bstep (se 1 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 441451 = 662177) B662177
theorem B441463 : Blo 439778 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B441483 : Blo 439778 441483 := bstep (se 1 (by rfl) ⟨331112, by rfl⟩ : syracuseStep 441483 = 662225) B662225
theorem B441495 : Blo 439778 441495 := bstep (se 1 (by rfl) ⟨331121, by rfl⟩ : syracuseStep 441495 = 662243) B662243
theorem B441515 : Blo 439778 441515 := bstep (se 1 (by rfl) ⟨331136, by rfl⟩ : syracuseStep 441515 = 662273) B662273
theorem B441527 : Blo 439778 441527 := bstep (se 1 (by rfl) ⟨331145, by rfl⟩ : syracuseStep 441527 = 662291) B662291
theorem B441547 : Blo 439778 441547 := bstep (se 1 (by rfl) ⟨331160, by rfl⟩ : syracuseStep 441547 = 662321) B662321
theorem B441559 : Blo 439778 441559 := bstep (se 1 (by rfl) ⟨331169, by rfl⟩ : syracuseStep 441559 = 662339) B662339
theorem B441579 : Blo 439778 441579 := bstep (se 1 (by rfl) ⟨331184, by rfl⟩ : syracuseStep 441579 = 662369) B662369
theorem B441591 : Blo 439778 441591 := bstep (se 1 (by rfl) ⟨331193, by rfl⟩ : syracuseStep 441591 = 662387) B662387
theorem B441611 : Blo 439778 441611 := bstep (se 1 (by rfl) ⟨331208, by rfl⟩ : syracuseStep 441611 = 662417) B662417
theorem B441623 : Blo 439778 441623 := bstep (se 1 (by rfl) ⟨331217, by rfl⟩ : syracuseStep 441623 = 662435) B662435
theorem B441643 : Blo 439778 441643 := bstep (se 1 (by rfl) ⟨331232, by rfl⟩ : syracuseStep 441643 = 662465) B662465
theorem B441655 : Blo 439778 441655 := bstep (se 1 (by rfl) ⟨331241, by rfl⟩ : syracuseStep 441655 = 662483) B662483
theorem B441675 : Blo 439778 441675 := bstep (se 1 (by rfl) ⟨331256, by rfl⟩ : syracuseStep 441675 = 662513) B662513
theorem B441687 : Blo 439778 441687 := bstep (se 1 (by rfl) ⟨331265, by rfl⟩ : syracuseStep 441687 = 662531) B662531
theorem B441707 : Blo 439778 441707 := bstep (se 1 (by rfl) ⟨331280, by rfl⟩ : syracuseStep 441707 = 662561) B662561
theorem B441719 : Blo 439778 441719 := bstep (se 1 (by rfl) ⟨331289, by rfl⟩ : syracuseStep 441719 = 662579) B662579
theorem B441739 : Blo 439778 441739 := bstep (se 1 (by rfl) ⟨331304, by rfl⟩ : syracuseStep 441739 = 662609) B662609
theorem B441751 : Blo 439778 441751 := bstep (se 1 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 441751 = 662627) B662627
theorem B441771 : Blo 439778 441771 := bstep (se 1 (by rfl) ⟨331328, by rfl⟩ : syracuseStep 441771 = 662657) B662657
theorem B441783 : Blo 439778 441783 := bstep (se 1 (by rfl) ⟨331337, by rfl⟩ : syracuseStep 441783 = 662675) B662675
theorem B1588673 : Blo 439778 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B441803 : Blo 439778 441803 := bstep (se 1 (by rfl) ⟨331352, by rfl⟩ : syracuseStep 441803 = 662705) B662705
theorem B441815 : Blo 439778 441815 := bstep (se 1 (by rfl) ⟨331361, by rfl⟩ : syracuseStep 441815 = 662723) B662723
theorem B441835 : Blo 439778 441835 := bstep (se 1 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 441835 = 662753) B662753
theorem B441847 : Blo 439778 441847 := bstep (se 1 (by rfl) ⟨331385, by rfl⟩ : syracuseStep 441847 = 662771) B662771
theorem B441867 : Blo 439778 441867 := bstep (se 1 (by rfl) ⟨331400, by rfl⟩ : syracuseStep 441867 = 662801) B662801
theorem B2539025 : Blo 439778 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B441879 : Blo 439778 441879 := bstep (se 1 (by rfl) ⟨331409, by rfl⟩ : syracuseStep 441879 = 662819) B662819
theorem B1261079 : Blo 439778 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B441899 : Blo 439778 441899 := bstep (se 1 (by rfl) ⟨331424, by rfl⟩ : syracuseStep 441899 = 662849) B662849
theorem B835123 : Blo 439778 835123 := bstep (se 1 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 835123 = 1252685) B1252685
theorem B441911 : Blo 439778 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B1490507 : Blo 439778 1490507 := bstep (se 1 (by rfl) ⟨1117880, by rfl⟩ : syracuseStep 1490507 = 2235761) B2235761
theorem B441931 : Blo 439778 441931 := bstep (se 1 (by rfl) ⟨331448, by rfl⟩ : syracuseStep 441931 = 662897) B662897
theorem B441943 : Blo 439778 441943 := bstep (se 1 (by rfl) ⟨331457, by rfl⟩ : syracuseStep 441943 = 662915) B662915
theorem B999001 : Blo 439778 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B441963 : Blo 439778 441963 := bstep (se 1 (by rfl) ⟨331472, by rfl⟩ : syracuseStep 441963 = 662945) B662945
theorem B441975 : Blo 439778 441975 := bstep (se 1 (by rfl) ⟨331481, by rfl⟩ : syracuseStep 441975 = 662963) B662963
theorem B441995 : Blo 439778 441995 := bstep (se 1 (by rfl) ⟨331496, by rfl⟩ : syracuseStep 441995 = 662993) B662993
theorem B442007 : Blo 439778 442007 := bstep (se 1 (by rfl) ⟨331505, by rfl⟩ : syracuseStep 442007 = 663011) B663011
theorem B442027 : Blo 439778 442027 := bstep (se 1 (by rfl) ⟨331520, by rfl⟩ : syracuseStep 442027 = 663041) B663041
theorem B1883827 : Blo 439778 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B442039 : Blo 439778 442039 := bstep (se 1 (by rfl) ⟨331529, by rfl⟩ : syracuseStep 442039 = 663059) B663059
theorem B442059 : Blo 439778 442059 := bstep (se 1 (by rfl) ⟨331544, by rfl⟩ : syracuseStep 442059 = 663089) B663089
theorem B442071 : Blo 439778 442071 := bstep (se 1 (by rfl) ⟨331553, by rfl⟩ : syracuseStep 442071 = 663107) B663107
theorem B1130201 : Blo 439778 1130201 := bstep (se 2 (by rfl) ⟨423825, by rfl⟩ : syracuseStep 1130201 = 847651) B847651
theorem B442091 : Blo 439778 442091 := bstep (se 1 (by rfl) ⟨331568, by rfl⟩ : syracuseStep 442091 = 663137) B663137
theorem B442103 : Blo 439778 442103 := bstep (se 1 (by rfl) ⟨331577, by rfl⟩ : syracuseStep 442103 = 663155) B663155
theorem B442123 : Blo 439778 442123 := bstep (se 1 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 442123 = 663185) B663185
theorem B442135 : Blo 439778 442135 := bstep (se 1 (by rfl) ⟨331601, by rfl⟩ : syracuseStep 442135 = 663203) B663203
theorem B442155 : Blo 439778 442155 := bstep (se 1 (by rfl) ⟨331616, by rfl⟩ : syracuseStep 442155 = 663233) B663233
theorem B966451 : Blo 439778 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B442167 : Blo 439778 442167 := bstep (se 1 (by rfl) ⟨331625, by rfl⟩ : syracuseStep 442167 = 663251) B663251
theorem B442187 : Blo 439778 442187 := bstep (se 1 (by rfl) ⟨331640, by rfl⟩ : syracuseStep 442187 = 663281) B663281
theorem B442199 : Blo 439778 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B1490777 : Blo 439778 1490777 := bstep (se 2 (by rfl) ⟨559041, by rfl⟩ : syracuseStep 1490777 = 1118083) B1118083
theorem B442219 : Blo 439778 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B442231 : Blo 439778 442231 := bstep (se 1 (by rfl) ⟨331673, by rfl⟩ : syracuseStep 442231 = 663347) B663347
theorem B442251 : Blo 439778 442251 := bstep (se 1 (by rfl) ⟨331688, by rfl⟩ : syracuseStep 442251 = 663377) B663377
theorem B442263 : Blo 439778 442263 := bstep (se 1 (by rfl) ⟨331697, by rfl⟩ : syracuseStep 442263 = 663395) B663395
theorem B442283 : Blo 439778 442283 := bstep (se 1 (by rfl) ⟨331712, by rfl⟩ : syracuseStep 442283 = 663425) B663425
theorem B1589165 : Blo 439778 1589165 := bstep (se 3 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 1589165 = 595937) B595937
theorem B442295 : Blo 439778 442295 := bstep (se 1 (by rfl) ⟨331721, by rfl⟩ : syracuseStep 442295 = 663443) B663443
theorem B442315 : Blo 439778 442315 := bstep (se 1 (by rfl) ⟨331736, by rfl⟩ : syracuseStep 442315 = 663473) B663473
theorem B442327 : Blo 439778 442327 := bstep (se 1 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 442327 = 663491) B663491
theorem B1195993 : Blo 439778 1195993 := bstep (se 2 (by rfl) ⟨448497, by rfl⟩ : syracuseStep 1195993 = 896995) B896995
theorem B442347 : Blo 439778 442347 := bstep (se 1 (by rfl) ⟨331760, by rfl⟩ : syracuseStep 442347 = 663521) B663521
theorem B835571 : Blo 439778 835571 := bstep (se 1 (by rfl) ⟨626678, by rfl⟩ : syracuseStep 835571 = 1253357) B1253357
theorem B442359 : Blo 439778 442359 := bstep (se 1 (by rfl) ⟨331769, by rfl⟩ : syracuseStep 442359 = 663539) B663539
theorem B442379 : Blo 439778 442379 := bstep (se 1 (by rfl) ⟨331784, by rfl⟩ : syracuseStep 442379 = 663569) B663569
theorem B442391 : Blo 439778 442391 := bstep (se 1 (by rfl) ⟨331793, by rfl⟩ : syracuseStep 442391 = 663587) B663587
theorem B835609 : Blo 439778 835609 := bstep (se 2 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 835609 = 626707) B626707
theorem B442411 : Blo 439778 442411 := bstep (se 1 (by rfl) ⟨331808, by rfl⟩ : syracuseStep 442411 = 663617) B663617
theorem B442423 : Blo 439778 442423 := bstep (se 1 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 442423 = 663635) B663635
theorem B1720385 : Blo 439778 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B442443 : Blo 439778 442443 := bstep (se 1 (by rfl) ⟨331832, by rfl⟩ : syracuseStep 442443 = 663665) B663665
theorem B1065035 : Blo 439778 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B442455 : Blo 439778 442455 := bstep (se 1 (by rfl) ⟨331841, by rfl⟩ : syracuseStep 442455 = 663683) B663683
theorem B442475 : Blo 439778 442475 := bstep (se 1 (by rfl) ⟨331856, by rfl⟩ : syracuseStep 442475 = 663713) B663713
theorem B442487 : Blo 439778 442487 := bstep (se 1 (by rfl) ⟨331865, by rfl⟩ : syracuseStep 442487 = 663731) B663731
theorem B442507 : Blo 439778 442507 := bstep (se 1 (by rfl) ⟨331880, by rfl⟩ : syracuseStep 442507 = 663761) B663761
theorem B442519 : Blo 439778 442519 := bstep (se 1 (by rfl) ⟨331889, by rfl⟩ : syracuseStep 442519 = 663779) B663779
theorem B442539 : Blo 439778 442539 := bstep (se 1 (by rfl) ⟨331904, by rfl⟩ : syracuseStep 442539 = 663809) B663809
theorem B442551 : Blo 439778 442551 := bstep (se 1 (by rfl) ⟨331913, by rfl⟩ : syracuseStep 442551 = 663827) B663827
theorem B442571 : Blo 439778 442571 := bstep (se 1 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 442571 = 663857) B663857
theorem B442583 : Blo 439778 442583 := bstep (se 1 (by rfl) ⟨331937, by rfl⟩ : syracuseStep 442583 = 663875) B663875
theorem B442603 : Blo 439778 442603 := bstep (se 1 (by rfl) ⟨331952, by rfl⟩ : syracuseStep 442603 = 663905) B663905
theorem B442615 : Blo 439778 442615 := bstep (se 1 (by rfl) ⟨331961, by rfl⟩ : syracuseStep 442615 = 663923) B663923
theorem B442635 : Blo 439778 442635 := bstep (se 1 (by rfl) ⟨331976, by rfl⟩ : syracuseStep 442635 = 663953) B663953
theorem B442647 : Blo 439778 442647 := bstep (se 1 (by rfl) ⟨331985, by rfl⟩ : syracuseStep 442647 = 663971) B663971
theorem B442667 : Blo 439778 442667 := bstep (se 1 (by rfl) ⟨332000, by rfl⟩ : syracuseStep 442667 = 664001) B664001
theorem B1786157 : Blo 439778 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B442679 : Blo 439778 442679 := bstep (se 1 (by rfl) ⟨332009, by rfl⟩ : syracuseStep 442679 = 664019) B664019
theorem B1261889 : Blo 439778 1261889 := bstep (se 2 (by rfl) ⟨473208, by rfl⟩ : syracuseStep 1261889 = 946417) B946417
theorem B442699 : Blo 439778 442699 := bstep (se 1 (by rfl) ⟨332024, by rfl⟩ : syracuseStep 442699 = 664049) B664049
theorem B442711 : Blo 439778 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B1065305 : Blo 439778 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B442731 : Blo 439778 442731 := bstep (se 1 (by rfl) ⟨332048, by rfl⟩ : syracuseStep 442731 = 664097) B664097
theorem B442743 : Blo 439778 442743 := bstep (se 1 (by rfl) ⟨332057, by rfl⟩ : syracuseStep 442743 = 664115) B664115
theorem B2244995 : Blo 439778 2244995 := bstep (se 1 (by rfl) ⟨1683746, by rfl⟩ : syracuseStep 2244995 = 3367493) B3367493
theorem B442763 : Blo 439778 442763 := bstep (se 1 (by rfl) ⟨332072, by rfl⟩ : syracuseStep 442763 = 664145) B664145
theorem B442775 : Blo 439778 442775 := bstep (se 1 (by rfl) ⟨332081, by rfl⟩ : syracuseStep 442775 = 664163) B664163
theorem B442795 : Blo 439778 442795 := bstep (se 1 (by rfl) ⟨332096, by rfl⟩ : syracuseStep 442795 = 664193) B664193
theorem B442807 : Blo 439778 442807 := bstep (se 1 (by rfl) ⟨332105, by rfl⟩ : syracuseStep 442807 = 664211) B664211
theorem B442827 : Blo 439778 442827 := bstep (se 1 (by rfl) ⟨332120, by rfl⟩ : syracuseStep 442827 = 664241) B664241
theorem B442839 : Blo 439778 442839 := bstep (se 1 (by rfl) ⟨332129, by rfl⟩ : syracuseStep 442839 = 664259) B664259
theorem B836057 : Blo 439778 836057 := bstep (se 2 (by rfl) ⟨313521, by rfl⟩ : syracuseStep 836057 = 627043) B627043
theorem B442859 : Blo 439778 442859 := bstep (se 1 (by rfl) ⟨332144, by rfl⟩ : syracuseStep 442859 = 664289) B664289
theorem B442871 : Blo 439778 442871 := bstep (se 1 (by rfl) ⟨332153, by rfl⟩ : syracuseStep 442871 = 664307) B664307
theorem B442891 : Blo 439778 442891 := bstep (se 1 (by rfl) ⟨332168, by rfl⟩ : syracuseStep 442891 = 664337) B664337
theorem B1491479 : Blo 439778 1491479 := bstep (se 1 (by rfl) ⟨1118609, by rfl⟩ : syracuseStep 1491479 = 2237219) B2237219
theorem B442903 : Blo 439778 442903 := bstep (se 1 (by rfl) ⟨332177, by rfl⟩ : syracuseStep 442903 = 664355) B664355
theorem B442923 : Blo 439778 442923 := bstep (se 1 (by rfl) ⟨332192, by rfl⟩ : syracuseStep 442923 = 664385) B664385
theorem B442935 : Blo 439778 442935 := bstep (se 1 (by rfl) ⟨332201, by rfl⟩ : syracuseStep 442935 = 664403) B664403
theorem B442955 : Blo 439778 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B442967 : Blo 439778 442967 := bstep (se 1 (by rfl) ⟨332225, by rfl⟩ : syracuseStep 442967 = 664451) B664451
theorem B442987 : Blo 439778 442987 := bstep (se 1 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 442987 = 664481) B664481
theorem B442999 : Blo 439778 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B2507395 : Blo 439778 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B443019 : Blo 439778 443019 := bstep (se 1 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 443019 = 664529) B664529
theorem B443031 : Blo 439778 443031 := bstep (se 1 (by rfl) ⟨332273, by rfl⟩ : syracuseStep 443031 = 664547) B664547
theorem B443051 : Blo 439778 443051 := bstep (se 1 (by rfl) ⟨332288, by rfl⟩ : syracuseStep 443051 = 664577) B664577
theorem B443063 : Blo 439778 443063 := bstep (se 1 (by rfl) ⟨332297, by rfl⟩ : syracuseStep 443063 = 664595) B664595
theorem B443083 : Blo 439778 443083 := bstep (se 1 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 443083 = 664625) B664625
theorem B443095 : Blo 439778 443095 := bstep (se 1 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 443095 = 664643) B664643
theorem B443115 : Blo 439778 443115 := bstep (se 1 (by rfl) ⟨332336, by rfl⟩ : syracuseStep 443115 = 664673) B664673
theorem B443127 : Blo 439778 443127 := bstep (se 1 (by rfl) ⟨332345, by rfl⟩ : syracuseStep 443127 = 664691) B664691
theorem B443147 : Blo 439778 443147 := bstep (se 1 (by rfl) ⟨332360, by rfl⟩ : syracuseStep 443147 = 664721) B664721
theorem B443159 : Blo 439778 443159 := bstep (se 1 (by rfl) ⟨332369, by rfl⟩ : syracuseStep 443159 = 664739) B664739
theorem B443179 : Blo 439778 443179 := bstep (se 1 (by rfl) ⟨332384, by rfl⟩ : syracuseStep 443179 = 664769) B664769
theorem B443191 : Blo 439778 443191 := bstep (se 1 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 443191 = 664787) B664787
theorem B443211 : Blo 439778 443211 := bstep (se 1 (by rfl) ⟨332408, by rfl⟩ : syracuseStep 443211 = 664817) B664817
theorem B443223 : Blo 439778 443223 := bstep (se 1 (by rfl) ⟨332417, by rfl⟩ : syracuseStep 443223 = 664835) B664835
theorem B443243 : Blo 439778 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B443255 : Blo 439778 443255 := bstep (se 1 (by rfl) ⟨332441, by rfl⟩ : syracuseStep 443255 = 664883) B664883
theorem B443275 : Blo 439778 443275 := bstep (se 1 (by rfl) ⟨332456, by rfl⟩ : syracuseStep 443275 = 664913) B664913
theorem B443287 : Blo 439778 443287 := bstep (se 1 (by rfl) ⟨332465, by rfl⟩ : syracuseStep 443287 = 664931) B664931
theorem B443307 : Blo 439778 443307 := bstep (se 1 (by rfl) ⟨332480, by rfl⟩ : syracuseStep 443307 = 664961) B664961
theorem B443319 : Blo 439778 443319 := bstep (se 1 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 443319 = 664979) B664979
theorem B443339 : Blo 439778 443339 := bstep (se 1 (by rfl) ⟨332504, by rfl⟩ : syracuseStep 443339 = 665009) B665009
theorem B443351 : Blo 439778 443351 := bstep (se 1 (by rfl) ⟨332513, by rfl⟩ : syracuseStep 443351 = 665027) B665027
theorem B443371 : Blo 439778 443371 := bstep (se 1 (by rfl) ⟨332528, by rfl⟩ : syracuseStep 443371 = 665057) B665057
theorem B443383 : Blo 439778 443383 := bstep (se 1 (by rfl) ⟨332537, by rfl⟩ : syracuseStep 443383 = 665075) B665075
theorem B443403 : Blo 439778 443403 := bstep (se 1 (by rfl) ⟨332552, by rfl⟩ : syracuseStep 443403 = 665105) B665105
theorem B443415 : Blo 439778 443415 := bstep (se 1 (by rfl) ⟨332561, by rfl⟩ : syracuseStep 443415 = 665123) B665123
theorem B443435 : Blo 439778 443435 := bstep (se 1 (by rfl) ⟨332576, by rfl⟩ : syracuseStep 443435 = 665153) B665153
theorem B1492019 : Blo 439778 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B443447 : Blo 439778 443447 := bstep (se 1 (by rfl) ⟨332585, by rfl⟩ : syracuseStep 443447 = 665171) B665171
theorem B443467 : Blo 439778 443467 := bstep (se 1 (by rfl) ⟨332600, by rfl⟩ : syracuseStep 443467 = 665201) B665201
theorem B443479 : Blo 439778 443479 := bstep (se 1 (by rfl) ⟨332609, by rfl⟩ : syracuseStep 443479 = 665219) B665219
theorem B443499 : Blo 439778 443499 := bstep (se 1 (by rfl) ⟨332624, by rfl⟩ : syracuseStep 443499 = 665249) B665249
theorem B443511 : Blo 439778 443511 := bstep (se 1 (by rfl) ⟨332633, by rfl⟩ : syracuseStep 443511 = 665267) B665267
theorem B1885315 : Blo 439778 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B443531 : Blo 439778 443531 := bstep (se 1 (by rfl) ⟨332648, by rfl⟩ : syracuseStep 443531 = 665297) B665297
theorem B1229975 : Blo 439778 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B443543 : Blo 439778 443543 := bstep (se 1 (by rfl) ⟨332657, by rfl⟩ : syracuseStep 443543 = 665315) B665315
theorem B443563 : Blo 439778 443563 := bstep (se 1 (by rfl) ⟨332672, by rfl⟩ : syracuseStep 443563 = 665345) B665345
theorem B443575 : Blo 439778 443575 := bstep (se 1 (by rfl) ⟨332681, by rfl⟩ : syracuseStep 443575 = 665363) B665363
theorem B836801 : Blo 439778 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B443595 : Blo 439778 443595 := bstep (se 1 (by rfl) ⟨332696, by rfl⟩ : syracuseStep 443595 = 665393) B665393
theorem B443607 : Blo 439778 443607 := bstep (se 1 (by rfl) ⟨332705, by rfl⟩ : syracuseStep 443607 = 665411) B665411
theorem B443627 : Blo 439778 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B443639 : Blo 439778 443639 := bstep (se 1 (by rfl) ⟨332729, by rfl⟩ : syracuseStep 443639 = 665459) B665459
theorem B443659 : Blo 439778 443659 := bstep (se 1 (by rfl) ⟨332744, by rfl⟩ : syracuseStep 443659 = 665489) B665489
theorem B443671 : Blo 439778 443671 := bstep (se 1 (by rfl) ⟨332753, by rfl⟩ : syracuseStep 443671 = 665507) B665507
theorem B443691 : Blo 439778 443691 := bstep (se 1 (by rfl) ⟨332768, by rfl⟩ : syracuseStep 443691 = 665537) B665537
theorem B443703 : Blo 439778 443703 := bstep (se 1 (by rfl) ⟨332777, by rfl⟩ : syracuseStep 443703 = 665555) B665555
theorem B1492289 : Blo 439778 1492289 := bstep (se 2 (by rfl) ⟨559608, by rfl⟩ : syracuseStep 1492289 = 1119217) B1119217
theorem B443723 : Blo 439778 443723 := bstep (se 1 (by rfl) ⟨332792, by rfl⟩ : syracuseStep 443723 = 665585) B665585
theorem B443735 : Blo 439778 443735 := bstep (se 1 (by rfl) ⟨332801, by rfl⟩ : syracuseStep 443735 = 665603) B665603
theorem B443755 : Blo 439778 443755 := bstep (se 1 (by rfl) ⟨332816, by rfl⟩ : syracuseStep 443755 = 665633) B665633
theorem B443767 : Blo 439778 443767 := bstep (se 1 (by rfl) ⟨332825, by rfl⟩ : syracuseStep 443767 = 665651) B665651
theorem B837067 : Blo 439778 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B4015565 : Blo 439778 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B1590749 : Blo 439778 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B2508353 : Blo 439778 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B804505 : Blo 439778 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B1885913 : Blo 439778 1885913 := bstep (se 2 (by rfl) ⟨707217, by rfl⟩ : syracuseStep 1885913 = 1414435) B1414435
theorem B2148113 : Blo 439778 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1492829 : Blo 439778 1492829 := bstep (se 3 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 1492829 = 559811) B559811
theorem B837515 : Blo 439778 837515 := bstep (se 1 (by rfl) ⟨628136, by rfl⟩ : syracuseStep 837515 = 1256273) B1256273
theorem B3360689 : Blo 439778 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B2836403 : Blo 439778 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1263539 : Blo 439778 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1263563 : Blo 439778 1263563 := bstep (se 1 (by rfl) ⟨947672, by rfl⟩ : syracuseStep 1263563 = 1895345) B1895345
theorem B477175 : Blo 439778 477175 := bstep (se 1 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 477175 = 715763) B715763
theorem B1722391 : Blo 439778 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B837697 : Blo 439778 837697 := bstep (se 2 (by rfl) ⟨314136, by rfl⟩ : syracuseStep 837697 = 628273) B628273
theorem B1886273 : Blo 439778 1886273 := bstep (se 2 (by rfl) ⟨707352, by rfl⟩ : syracuseStep 1886273 = 1414705) B1414705
theorem B3819595 : Blo 439778 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B2377907 : Blo 439778 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B838039 : Blo 439778 838039 := bstep (se 1 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 838039 = 1257059) B1257059
theorem B3361175 : Blo 439778 3361175 := bstep (se 1 (by rfl) ⟨2520881, by rfl⟩ : syracuseStep 3361175 = 5041763) B5041763
theorem B838259 : Blo 439778 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B510635 : Blo 439778 510635 := bstep (se 1 (by rfl) ⟨382976, by rfl⟩ : syracuseStep 510635 = 765953) B765953
theorem B838487 : Blo 439778 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B3197873 : Blo 439778 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B9554867 : Blo 439778 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B1493963 : Blo 439778 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B707609 : Blo 439778 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B838745 : Blo 439778 838745 := bstep (se 2 (by rfl) ⟨314529, by rfl⟩ : syracuseStep 838745 = 629059) B629059
theorem B1494233 : Blo 439778 1494233 := bstep (se 2 (by rfl) ⟨560337, by rfl⟩ : syracuseStep 1494233 = 1120675) B1120675
theorem B839155 : Blo 439778 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B2117137 : Blo 439778 2117137 := bstep (se 2 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 2117137 = 1587853) B1587853
theorem B1592855 : Blo 439778 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B3591773 : Blo 439778 3591773 := bstep (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) B1346915
theorem B1494935 : Blo 439778 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B839641 : Blo 439778 839641 := bstep (se 2 (by rfl) ⟨314865, by rfl⟩ : syracuseStep 839641 = 629731) B629731
theorem B3788977 : Blo 439778 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B3887461 : Blo 439778 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B1495475 : Blo 439778 1495475 := bstep (se 1 (by rfl) ⟨1121606, by rfl⟩ : syracuseStep 1495475 = 2243213) B2243213
theorem B1364441 : Blo 439778 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B840203 : Blo 439778 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B2839171 : Blo 439778 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B840385 : Blo 439778 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B1495745 : Blo 439778 1495745 := bstep (se 2 (by rfl) ⟨560904, by rfl⟩ : syracuseStep 1495745 = 1121809) B1121809
theorem B742169 : Blo 439778 742169 := bstep (se 2 (by rfl) ⟨278313, by rfl⟩ : syracuseStep 742169 = 556627) B556627
theorem B2380589 : Blo 439778 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B742297 : Blo 439778 742297 := bstep (se 2 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 742297 = 556723) B556723
theorem B1790923 : Blo 439778 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B4248611 : Blo 439778 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B1496285 : Blo 439778 1496285 := bstep (se 3 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 1496285 = 561107) B561107
theorem B841099 : Blo 439778 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B742871 : Blo 439778 742871 := bstep (se 1 (by rfl) ⟨557153, by rfl⟩ : syracuseStep 742871 = 1114307) B1114307
theorem B841175 : Blo 439778 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B742999 : Blo 439778 742999 := bstep (se 1 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 742999 = 1114499) B1114499
theorem B9557635 : Blo 439778 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B1005259 : Blo 439778 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B2119385 : Blo 439778 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B1890013 : Blo 439778 1890013 := bstep (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) B708755
theorem B2021213 : Blo 439778 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B2676581 : Blo 439778 2676581 := bstep (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) B501859
theorem B5658659 : Blo 439778 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B841843 : Blo 439778 841843 := bstep (se 1 (by rfl) ⟨631382, by rfl⟩ : syracuseStep 841843 = 1262765) B1262765
theorem B743627 : Blo 439778 743627 := bstep (se 1 (by rfl) ⟨557720, by rfl⟩ : syracuseStep 743627 = 1115441) B1115441
theorem B743755 : Blo 439778 743755 := bstep (se 1 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 743755 = 1115633) B1115633
theorem B2513227 : Blo 439778 2513227 := bstep (se 1 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 2513227 = 3769841) B3769841
theorem B1497419 : Blo 439778 1497419 := bstep (se 1 (by rfl) ⟨1123064, by rfl⟩ : syracuseStep 1497419 = 2246129) B2246129
theorem B842071 : Blo 439778 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B940403 : Blo 439778 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B842177 : Blo 439778 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B743897 : Blo 439778 743897 := bstep (se 2 (by rfl) ⟨278961, by rfl⟩ : syracuseStep 743897 = 557923) B557923
theorem B744025 : Blo 439778 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B842329 : Blo 439778 842329 := bstep (se 2 (by rfl) ⟨315873, by rfl⟩ : syracuseStep 842329 = 631747) B631747
theorem B1497689 : Blo 439778 1497689 := bstep (se 2 (by rfl) ⟨561633, by rfl⟩ : syracuseStep 1497689 = 1123267) B1123267
theorem B2513501 : Blo 439778 2513501 := bstep (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) B942563
theorem B3595013 : Blo 439778 3595013 := bstep (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) B674065
theorem B940889 : Blo 439778 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B6904793 : Blo 439778 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B1891345 : Blo 439778 1891345 := bstep (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) B1418509
theorem B744599 : Blo 439778 744599 := bstep (se 1 (by rfl) ⟨558449, by rfl⟩ : syracuseStep 744599 = 1116899) B1116899
theorem B2022617 : Blo 439778 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B744727 : Blo 439778 744727 := bstep (se 1 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 744727 = 1117091) B1117091
theorem B745355 : Blo 439778 745355 := bstep (se 1 (by rfl) ⟨559016, by rfl⟩ : syracuseStep 745355 = 1118033) B1118033
theorem B12115889 : Blo 439778 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B745483 : Blo 439778 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B745625 : Blo 439778 745625 := bstep (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) B559219
theorem B1401025 : Blo 439778 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B1794251 : Blo 439778 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B745753 : Blo 439778 745753 := bstep (se 2 (by rfl) ⟨279657, by rfl⟩ : syracuseStep 745753 = 559315) B559315
theorem B942529 : Blo 439778 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B1532353 : Blo 439778 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B746327 : Blo 439778 746327 := bstep (se 1 (by rfl) ⟨559745, by rfl⟩ : syracuseStep 746327 = 1119491) B1119491
theorem B2384741 : Blo 439778 2384741 := bstep (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) B447139
theorem B746455 : Blo 439778 746455 := bstep (se 1 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 746455 = 1119683) B1119683
theorem B910835 : Blo 439778 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B3368465 : Blo 439778 3368465 := bstep (se 2 (by rfl) ⟨1263174, by rfl⟩ : syracuseStep 3368465 = 2526349) B2526349
theorem B747083 : Blo 439778 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B747211 : Blo 439778 747211 := bstep (se 1 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 747211 = 1120817) B1120817
theorem B747353 : Blo 439778 747353 := bstep (se 2 (by rfl) ⟨280257, by rfl⟩ : syracuseStep 747353 = 560515) B560515
theorem B1894337 : Blo 439778 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B747481 : Blo 439778 747481 := bstep (se 2 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 747481 = 560611) B560611
theorem B4253957 : Blo 439778 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B944435 : Blo 439778 944435 := bstep (se 1 (by rfl) ⟨708326, by rfl⟩ : syracuseStep 944435 = 1416653) B1416653
theorem B748055 : Blo 439778 748055 := bstep (se 1 (by rfl) ⟨561041, by rfl⟩ : syracuseStep 748055 = 1122083) B1122083
theorem B5368355 : Blo 439778 5368355 := bstep (se 1 (by rfl) ⟨4026266, by rfl⟩ : syracuseStep 5368355 = 8052533) B8052533
theorem B3762733 : Blo 439778 3762733 := bstep (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) B1411025
theorem B748183 : Blo 439778 748183 := bstep (se 1 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 748183 = 1122275) B1122275
theorem B944921 : Blo 439778 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B4025123 : Blo 439778 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B1272793 : Blo 439778 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B1338547 : Blo 439778 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B1698995 : Blo 439778 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B7630085 : Blo 439778 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B748811 : Blo 439778 748811 := bstep (se 1 (by rfl) ⟨561608, by rfl⟩ : syracuseStep 748811 = 1123217) B1123217
theorem B945665 : Blo 439778 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B454391 : Blo 439778 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B2518877 : Blo 439778 2518877 := bstep (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) B944579
theorem B3764069 : Blo 439778 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B4026289 : Blo 439778 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B2551769 : Blo 439778 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B2257075 : Blo 439778 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B6025421 : Blo 439778 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B946561 : Blo 439778 946561 := bstep (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) B709921
theorem B1012121 : Blo 439778 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B946903 : Blo 439778 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B5370725 : Blo 439778 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B3240805 : Blo 439778 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B4027315 : Blo 439778 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B1438685 : Blo 439778 1438685 := bstep (se 3 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 1438685 = 539507) B539507
theorem B2946179 : Blo 439778 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B3634307 : Blo 439778 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B947467 : Blo 439778 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B2127917 : Blo 439778 2127917 := bstep (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) B797969
theorem B1341515 : Blo 439778 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B2586775 : Blo 439778 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B2521475 : Blo 439778 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B1669805 : Blo 439778 1669805 := bstep (se 3 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 1669805 = 626177) B626177
theorem B1669835 : Blo 439778 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1506251 : Blo 439778 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B1342487 : Blo 439778 1342487 := bstep (se 1 (by rfl) ⟨1006865, by rfl⟩ : syracuseStep 1342487 = 2013731) B2013731
theorem B1276993 : Blo 439778 1276993 := bstep (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) B957745
theorem B4258909 : Blo 439778 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B1670489 : Blo 439778 1670489 := bstep (se 2 (by rfl) ⟨626433, by rfl⟩ : syracuseStep 1670489 = 1252867) B1252867
theorem B1113547 : Blo 439778 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B1113689 : Blo 439778 1113689 := bstep (se 2 (by rfl) ⟨417633, by rfl⟩ : syracuseStep 1113689 = 835267) B835267
theorem B1670807 : Blo 439778 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B851699 : Blo 439778 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B2227985 : Blo 439778 2227985 := bstep (se 2 (by rfl) ⟨835494, by rfl⟩ : syracuseStep 2227985 = 1670989) B1670989
theorem B556951 : Blo 439778 556951 := bstep (se 1 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 556951 = 835427) B835427
theorem B2228147 : Blo 439778 2228147 := bstep (se 1 (by rfl) ⟨1671110, by rfl⟩ : syracuseStep 2228147 = 3342221) B3342221
theorem B1114145 : Blo 439778 1114145 := bstep (se 2 (by rfl) ⟨417804, by rfl⟩ : syracuseStep 1114145 = 835609) B835609
theorem B1146923 : Blo 439778 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B1868033 : Blo 439778 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B557371 : Blo 439778 557371 := bstep (se 1 (by rfl) ⟨418028, by rfl⟩ : syracuseStep 557371 = 836057) B836057
theorem B2228633 : Blo 439778 2228633 := bstep (se 2 (by rfl) ⟨835737, by rfl⟩ : syracuseStep 2228633 = 1671475) B1671475
theorem B819983 : Blo 439778 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B557867 : Blo 439778 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B3343193 : Blo 439778 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B3015539 : Blo 439778 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B1115147 : Blo 439778 1115147 := bstep (se 1 (by rfl) ⟨836360, by rfl⟩ : syracuseStep 1115147 = 1672721) B1672721
theorem B1672235 : Blo 439778 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B5080265 : Blo 439778 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B16188653 : Blo 439778 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B558343 : Blo 439778 558343 := bstep (se 1 (by rfl) ⟨418757, by rfl⟩ : syracuseStep 558343 = 837515) B837515
theorem B1115795 : Blo 439778 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B558839 : Blo 439778 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B3344165 : Blo 439778 3344165 := bstep (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) B627031
theorem B558991 : Blo 439778 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B1116089 : Blo 439778 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B2131915 : Blo 439778 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B559163 : Blo 439778 559163 := bstep (se 1 (by rfl) ⟨419372, by rfl⟩ : syracuseStep 559163 = 838745) B838745
theorem B8456309 : Blo 439778 8456309 := bstep (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) B792779
theorem B2394515 : Blo 439778 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B1116787 : Blo 439778 1116787 := bstep (se 1 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 1116787 = 1675181) B1675181
theorem B1116929 : Blo 439778 1116929 := bstep (se 2 (by rfl) ⟨418848, by rfl⟩ : syracuseStep 1116929 = 837697) B837697
theorem B2231225 : Blo 439778 2231225 := bstep (se 2 (by rfl) ⟨836709, by rfl⟩ : syracuseStep 2231225 = 1673419) B1673419
theorem B560135 : Blo 439778 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B5639179 : Blo 439778 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B494779 : Blo 439778 494779 := bstep (se 1 (by rfl) ⟨371084, by rfl⟩ : syracuseStep 494779 = 742169) B742169
theorem B1117385 : Blo 439778 1117385 := bstep (se 2 (by rfl) ⟨419019, by rfl⟩ : syracuseStep 1117385 = 838039) B838039
theorem B5016977 : Blo 439778 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B1117739 : Blo 439778 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B495247 : Blo 439778 495247 := bstep (se 1 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 495247 = 742871) B742871
theorem B560783 : Blo 439778 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B1412923 : Blo 439778 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B1347475 : Blo 439778 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B3772439 : Blo 439778 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B495751 : Blo 439778 495751 := bstep (se 1 (by rfl) ⟨371813, by rfl⟩ : syracuseStep 495751 = 743627) B743627
theorem B2232521 : Blo 439778 2232521 := bstep (se 2 (by rfl) ⟨837195, by rfl⟩ : syracuseStep 2232521 = 1674391) B1674391
theorem B626935 : Blo 439778 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B659771 : Blo 439778 659771 := bstep (se 1 (by rfl) ⟨494828, by rfl⟩ : syracuseStep 659771 = 989657) B989657
theorem B495931 : Blo 439778 495931 := bstep (se 1 (by rfl) ⟨371948, by rfl⟩ : syracuseStep 495931 = 743897) B743897
theorem B659831 : Blo 439778 659831 := bstep (se 1 (by rfl) ⟨494873, by rfl⟩ : syracuseStep 659831 = 989747) B989747
theorem B659855 : Blo 439778 659855 := bstep (se 1 (by rfl) ⟨494891, by rfl⟩ : syracuseStep 659855 = 989783) B989783
theorem B3772817 : Blo 439778 3772817 := bstep (se 2 (by rfl) ⟨1414806, by rfl⟩ : syracuseStep 3772817 = 2829613) B2829613
theorem B1675667 : Blo 439778 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B659897 : Blo 439778 659897 := bstep (se 2 (by rfl) ⟨247461, by rfl⟩ : syracuseStep 659897 = 494923) B494923
theorem B528827 : Blo 439778 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B2396675 : Blo 439778 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B659975 : Blo 439778 659975 := bstep (se 1 (by rfl) ⟨494981, by rfl⟩ : syracuseStep 659975 = 989963) B989963
theorem B1118731 : Blo 439778 1118731 := bstep (se 1 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 1118731 = 1678097) B1678097
theorem B660011 : Blo 439778 660011 := bstep (se 1 (by rfl) ⟨495008, by rfl⟩ : syracuseStep 660011 = 990017) B990017
theorem B627259 : Blo 439778 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B660041 : Blo 439778 660041 := bstep (se 2 (by rfl) ⟨247515, by rfl⟩ : syracuseStep 660041 = 495031) B495031
theorem B529015 : Blo 439778 529015 := bstep (se 1 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 529015 = 793523) B793523
theorem B529039 : Blo 439778 529039 := bstep (se 1 (by rfl) ⟨396779, by rfl⟩ : syracuseStep 529039 = 793559) B793559
theorem B1118873 : Blo 439778 1118873 := bstep (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) B839155
theorem B660155 : Blo 439778 660155 := bstep (se 1 (by rfl) ⟨495116, by rfl⟩ : syracuseStep 660155 = 990233) B990233
theorem B2822849 : Blo 439778 2822849 := bstep (se 2 (by rfl) ⟨1058568, by rfl⟩ : syracuseStep 2822849 = 2117137) B2117137
theorem B660215 : Blo 439778 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B660239 : Blo 439778 660239 := bstep (se 1 (by rfl) ⟨495179, by rfl⟩ : syracuseStep 660239 = 990359) B990359
theorem B496399 : Blo 439778 496399 := bstep (se 1 (by rfl) ⟨372299, by rfl⟩ : syracuseStep 496399 = 744599) B744599
theorem B660281 : Blo 439778 660281 := bstep (se 2 (by rfl) ⟨247605, by rfl⟩ : syracuseStep 660281 = 495211) B495211
theorem B1119035 : Blo 439778 1119035 := bstep (se 1 (by rfl) ⟨839276, by rfl⟩ : syracuseStep 1119035 = 1678553) B1678553
theorem B1348411 : Blo 439778 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B660359 : Blo 439778 660359 := bstep (se 1 (by rfl) ⟨495269, by rfl⟩ : syracuseStep 660359 = 990539) B990539
theorem B660395 : Blo 439778 660395 := bstep (se 1 (by rfl) ⟨495296, by rfl⟩ : syracuseStep 660395 = 990593) B990593
theorem B14554037 : Blo 439778 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B660425 : Blo 439778 660425 := bstep (se 2 (by rfl) ⟨247659, by rfl⟩ : syracuseStep 660425 = 495319) B495319
theorem B660539 : Blo 439778 660539 := bstep (se 1 (by rfl) ⟨495404, by rfl⟩ : syracuseStep 660539 = 990809) B990809
theorem B660599 : Blo 439778 660599 := bstep (se 1 (by rfl) ⟨495449, by rfl⟩ : syracuseStep 660599 = 990899) B990899
theorem B660623 : Blo 439778 660623 := bstep (se 1 (by rfl) ⟨495467, by rfl⟩ : syracuseStep 660623 = 990935) B990935
theorem B1119379 : Blo 439778 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B660665 : Blo 439778 660665 := bstep (se 2 (by rfl) ⟨247749, by rfl⟩ : syracuseStep 660665 = 495499) B495499
theorem B660743 : Blo 439778 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B496903 : Blo 439778 496903 := bstep (se 1 (by rfl) ⟨372677, by rfl⟩ : syracuseStep 496903 = 745355) B745355
theorem B1119521 : Blo 439778 1119521 := bstep (se 2 (by rfl) ⟨419820, by rfl⟩ : syracuseStep 1119521 = 839641) B839641
theorem B660779 : Blo 439778 660779 := bstep (se 1 (by rfl) ⟨495584, by rfl⟩ : syracuseStep 660779 = 991169) B991169
theorem B660809 : Blo 439778 660809 := bstep (se 2 (by rfl) ⟨247803, by rfl⟩ : syracuseStep 660809 = 495607) B495607
theorem B660923 : Blo 439778 660923 := bstep (se 1 (by rfl) ⟨495692, by rfl⟩ : syracuseStep 660923 = 991385) B991385
theorem B497083 : Blo 439778 497083 := bstep (se 1 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 497083 = 745625) B745625
theorem B5674445 : Blo 439778 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B660983 : Blo 439778 660983 := bstep (se 1 (by rfl) ⟨495737, by rfl⟩ : syracuseStep 660983 = 991475) B991475
theorem B661007 : Blo 439778 661007 := bstep (se 1 (by rfl) ⟨495755, by rfl⟩ : syracuseStep 661007 = 991511) B991511
theorem B661049 : Blo 439778 661049 := bstep (se 2 (by rfl) ⟨247893, by rfl⟩ : syracuseStep 661049 = 495787) B495787
theorem B5051969 : Blo 439778 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B661127 : Blo 439778 661127 := bstep (se 1 (by rfl) ⟨495845, by rfl⟩ : syracuseStep 661127 = 991691) B991691
theorem B661163 : Blo 439778 661163 := bstep (se 1 (by rfl) ⟨495872, by rfl⟩ : syracuseStep 661163 = 991745) B991745
theorem B2397869 : Blo 439778 2397869 := bstep (se 3 (by rfl) ⟨449600, by rfl⟩ : syracuseStep 2397869 = 899201) B899201
theorem B661193 : Blo 439778 661193 := bstep (se 2 (by rfl) ⟨247947, by rfl⟩ : syracuseStep 661193 = 495895) B495895
theorem B5183281 : Blo 439778 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B661307 : Blo 439778 661307 := bstep (se 1 (by rfl) ⟨495980, by rfl⟩ : syracuseStep 661307 = 991961) B991961
theorem B661367 : Blo 439778 661367 := bstep (se 1 (by rfl) ⟨496025, by rfl⟩ : syracuseStep 661367 = 992051) B992051
theorem B661391 : Blo 439778 661391 := bstep (se 1 (by rfl) ⟨496043, by rfl⟩ : syracuseStep 661391 = 992087) B992087
theorem B497551 : Blo 439778 497551 := bstep (se 1 (by rfl) ⟨373163, by rfl⟩ : syracuseStep 497551 = 746327) B746327
theorem B661433 : Blo 439778 661433 := bstep (se 2 (by rfl) ⟨248037, by rfl⟩ : syracuseStep 661433 = 496075) B496075
theorem B661511 : Blo 439778 661511 := bstep (se 1 (by rfl) ⟨496133, by rfl⟩ : syracuseStep 661511 = 992267) B992267
theorem B661547 : Blo 439778 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B661577 : Blo 439778 661577 := bstep (se 2 (by rfl) ⟨248091, by rfl⟩ : syracuseStep 661577 = 496183) B496183
theorem B661691 : Blo 439778 661691 := bstep (se 1 (by rfl) ⟨496268, by rfl⟩ : syracuseStep 661691 = 992537) B992537
theorem B5019893 : Blo 439778 5019893 := bstep (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) B470615
theorem B661751 : Blo 439778 661751 := bstep (se 1 (by rfl) ⟨496313, by rfl⟩ : syracuseStep 661751 = 992627) B992627
theorem B1120513 : Blo 439778 1120513 := bstep (se 2 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 1120513 = 840385) B840385
theorem B661775 : Blo 439778 661775 := bstep (se 1 (by rfl) ⟨496331, by rfl⟩ : syracuseStep 661775 = 992663) B992663
theorem B661817 : Blo 439778 661817 := bstep (se 2 (by rfl) ⟨248181, by rfl⟩ : syracuseStep 661817 = 496363) B496363
theorem B530807 : Blo 439778 530807 := bstep (se 1 (by rfl) ⟨398105, by rfl⟩ : syracuseStep 530807 = 796211) B796211
theorem B661895 : Blo 439778 661895 := bstep (se 1 (by rfl) ⟨496421, by rfl⟩ : syracuseStep 661895 = 992843) B992843
theorem B498055 : Blo 439778 498055 := bstep (se 1 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 498055 = 747083) B747083
theorem B661931 : Blo 439778 661931 := bstep (se 1 (by rfl) ⟨496448, by rfl⟩ : syracuseStep 661931 = 992897) B992897
theorem B661961 : Blo 439778 661961 := bstep (se 2 (by rfl) ⟨248235, by rfl⟩ : syracuseStep 661961 = 496471) B496471
theorem B989711 : Blo 439778 989711 := bstep (se 1 (by rfl) ⟨742283, by rfl⟩ : syracuseStep 989711 = 1484567) B1484567
theorem B989729 : Blo 439778 989729 := bstep (se 2 (by rfl) ⟨371148, by rfl⟩ : syracuseStep 989729 = 742297) B742297
theorem B662075 : Blo 439778 662075 := bstep (se 1 (by rfl) ⟨496556, by rfl⟩ : syracuseStep 662075 = 993113) B993113
theorem B498235 : Blo 439778 498235 := bstep (se 1 (by rfl) ⟨373676, by rfl⟩ : syracuseStep 498235 = 747353) B747353
theorem B662135 : Blo 439778 662135 := bstep (se 1 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 662135 = 993203) B993203
theorem B662159 : Blo 439778 662159 := bstep (se 1 (by rfl) ⟨496619, by rfl⟩ : syracuseStep 662159 = 993239) B993239
theorem B662201 : Blo 439778 662201 := bstep (se 2 (by rfl) ⟨248325, by rfl⟩ : syracuseStep 662201 = 496651) B496651
theorem B662279 : Blo 439778 662279 := bstep (se 1 (by rfl) ⟨496709, by rfl⟩ : syracuseStep 662279 = 993419) B993419
theorem B662315 : Blo 439778 662315 := bstep (se 1 (by rfl) ⟨496736, by rfl⟩ : syracuseStep 662315 = 993473) B993473
theorem B662345 : Blo 439778 662345 := bstep (se 2 (by rfl) ⟨248379, by rfl⟩ : syracuseStep 662345 = 496759) B496759
theorem B1121111 : Blo 439778 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B3414899 : Blo 439778 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B990071 : Blo 439778 990071 := bstep (se 1 (by rfl) ⟨742553, by rfl⟩ : syracuseStep 990071 = 1485107) B1485107
theorem B629623 : Blo 439778 629623 := bstep (se 1 (by rfl) ⟨472217, by rfl⟩ : syracuseStep 629623 = 944435) B944435
theorem B1678265 : Blo 439778 1678265 := bstep (se 2 (by rfl) ⟨629349, by rfl⟩ : syracuseStep 1678265 = 1258699) B1258699
theorem B662459 : Blo 439778 662459 := bstep (se 1 (by rfl) ⟨496844, by rfl⟩ : syracuseStep 662459 = 993689) B993689
theorem B662519 : Blo 439778 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B662543 : Blo 439778 662543 := bstep (se 1 (by rfl) ⟨496907, by rfl⟩ : syracuseStep 662543 = 993815) B993815
theorem B597007 : Blo 439778 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B498703 : Blo 439778 498703 := bstep (se 1 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 498703 = 748055) B748055
theorem B3578903 : Blo 439778 3578903 := bstep (se 1 (by rfl) ⟨2684177, by rfl⟩ : syracuseStep 3578903 = 5368355) B5368355
theorem B1121323 : Blo 439778 1121323 := bstep (se 1 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 1121323 = 1681985) B1681985
theorem B990251 : Blo 439778 990251 := bstep (se 1 (by rfl) ⟨742688, by rfl⟩ : syracuseStep 990251 = 1485377) B1485377
theorem B662585 : Blo 439778 662585 := bstep (se 2 (by rfl) ⟨248469, by rfl⟩ : syracuseStep 662585 = 496939) B496939
theorem B3021911 : Blo 439778 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B662663 : Blo 439778 662663 := bstep (se 1 (by rfl) ⟨496997, by rfl⟩ : syracuseStep 662663 = 993995) B993995
theorem B662699 : Blo 439778 662699 := bstep (se 1 (by rfl) ⟨497024, by rfl⟩ : syracuseStep 662699 = 994049) B994049
theorem B1121465 : Blo 439778 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B629947 : Blo 439778 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B662729 : Blo 439778 662729 := bstep (se 2 (by rfl) ⟨248523, by rfl⟩ : syracuseStep 662729 = 497047) B497047
theorem B662843 : Blo 439778 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B662903 : Blo 439778 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B662927 : Blo 439778 662927 := bstep (se 1 (by rfl) ⟨497195, by rfl⟩ : syracuseStep 662927 = 994391) B994391
theorem B990611 : Blo 439778 990611 := bstep (se 1 (by rfl) ⟨742958, by rfl⟩ : syracuseStep 990611 = 1485917) B1485917
theorem B662969 : Blo 439778 662969 := bstep (se 2 (by rfl) ⟨248613, by rfl⟩ : syracuseStep 662969 = 497227) B497227
theorem B990665 : Blo 439778 990665 := bstep (se 2 (by rfl) ⟨371499, by rfl⟩ : syracuseStep 990665 = 742999) B742999
theorem B5086723 : Blo 439778 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B663047 : Blo 439778 663047 := bstep (se 1 (by rfl) ⟨497285, by rfl⟩ : syracuseStep 663047 = 994571) B994571
theorem B499207 : Blo 439778 499207 := bstep (se 1 (by rfl) ⟨374405, by rfl⟩ : syracuseStep 499207 = 748811) B748811
theorem B663083 : Blo 439778 663083 := bstep (se 1 (by rfl) ⟨497312, by rfl⟩ : syracuseStep 663083 = 994625) B994625
theorem B663113 : Blo 439778 663113 := bstep (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) B497335
theorem B630443 : Blo 439778 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B663227 : Blo 439778 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B663287 : Blo 439778 663287 := bstep (se 1 (by rfl) ⟨497465, by rfl⟩ : syracuseStep 663287 = 994931) B994931
theorem B2825999 : Blo 439778 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B663311 : Blo 439778 663311 := bstep (se 1 (by rfl) ⟨497483, by rfl⟩ : syracuseStep 663311 = 994967) B994967
theorem B5119793 : Blo 439778 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B663353 : Blo 439778 663353 := bstep (se 2 (by rfl) ⟨248757, by rfl⟩ : syracuseStep 663353 = 497515) B497515
theorem B663431 : Blo 439778 663431 := bstep (se 1 (by rfl) ⟨497573, by rfl⟩ : syracuseStep 663431 = 995147) B995147
theorem B1679251 : Blo 439778 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B663467 : Blo 439778 663467 := bstep (se 1 (by rfl) ⟨497600, by rfl⟩ : syracuseStep 663467 = 995201) B995201
theorem B663497 : Blo 439778 663497 := bstep (se 2 (by rfl) ⟨248811, by rfl⟩ : syracuseStep 663497 = 497623) B497623
theorem B663611 : Blo 439778 663611 := bstep (se 1 (by rfl) ⟨497708, by rfl⟩ : syracuseStep 663611 = 995417) B995417
theorem B663671 : Blo 439778 663671 := bstep (se 1 (by rfl) ⟨497753, by rfl⟩ : syracuseStep 663671 = 995507) B995507
theorem B3219589 : Blo 439778 3219589 := bstep (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) B603673
theorem B991367 : Blo 439778 991367 := bstep (se 1 (by rfl) ⟨743525, by rfl⟩ : syracuseStep 991367 = 1487051) B1487051
theorem B663695 : Blo 439778 663695 := bstep (se 1 (by rfl) ⟨497771, by rfl⟩ : syracuseStep 663695 = 995543) B995543
theorem B1122457 : Blo 439778 1122457 := bstep (se 2 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 1122457 = 841843) B841843
theorem B663737 : Blo 439778 663737 := bstep (se 2 (by rfl) ⟨248901, by rfl⟩ : syracuseStep 663737 = 497803) B497803
theorem B3449033 : Blo 439778 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B663815 : Blo 439778 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B663851 : Blo 439778 663851 := bstep (se 1 (by rfl) ⟨497888, by rfl⟩ : syracuseStep 663851 = 995777) B995777
theorem B991547 : Blo 439778 991547 := bstep (se 1 (by rfl) ⟨743660, by rfl⟩ : syracuseStep 991547 = 1487321) B1487321
theorem B1122619 : Blo 439778 1122619 := bstep (se 1 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 1122619 = 1683929) B1683929
theorem B663881 : Blo 439778 663881 := bstep (se 2 (by rfl) ⟨248955, by rfl⟩ : syracuseStep 663881 = 497911) B497911
theorem B991673 : Blo 439778 991673 := bstep (se 2 (by rfl) ⟨371877, by rfl⟩ : syracuseStep 991673 = 743755) B743755
theorem B3350969 : Blo 439778 3350969 := bstep (se 2 (by rfl) ⟨1256613, by rfl⟩ : syracuseStep 3350969 = 2513227) B2513227
theorem B663995 : Blo 439778 663995 := bstep (se 1 (by rfl) ⟨497996, by rfl⟩ : syracuseStep 663995 = 995993) B995993
theorem B1122761 : Blo 439778 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B664055 : Blo 439778 664055 := bstep (se 1 (by rfl) ⟨498041, by rfl⟩ : syracuseStep 664055 = 996083) B996083
theorem B664079 : Blo 439778 664079 := bstep (se 1 (by rfl) ⟨498059, by rfl⟩ : syracuseStep 664079 = 996119) B996119
theorem B664121 : Blo 439778 664121 := bstep (se 2 (by rfl) ⟨249045, by rfl⟩ : syracuseStep 664121 = 498091) B498091
theorem B3580483 : Blo 439778 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B664199 : Blo 439778 664199 := bstep (se 1 (by rfl) ⟨498149, by rfl⟩ : syracuseStep 664199 = 996299) B996299
theorem B959123 : Blo 439778 959123 := bstep (se 1 (by rfl) ⟨719342, by rfl⟩ : syracuseStep 959123 = 1438685) B1438685
theorem B664235 : Blo 439778 664235 := bstep (se 1 (by rfl) ⟨498176, by rfl⟩ : syracuseStep 664235 = 996353) B996353
theorem B664265 : Blo 439778 664265 := bstep (se 2 (by rfl) ⟨249099, by rfl⟩ : syracuseStep 664265 = 498199) B498199
theorem B992015 : Blo 439778 992015 := bstep (se 1 (by rfl) ⟨744011, by rfl⟩ : syracuseStep 992015 = 1488023) B1488023
theorem B992033 : Blo 439778 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B1123105 : Blo 439778 1123105 := bstep (se 2 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 1123105 = 842329) B842329
theorem B664379 : Blo 439778 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B664439 : Blo 439778 664439 := bstep (se 1 (by rfl) ⟨498329, by rfl⟩ : syracuseStep 664439 = 996659) B996659
theorem B664463 : Blo 439778 664463 := bstep (se 1 (by rfl) ⟨498347, by rfl⟩ : syracuseStep 664463 = 996695) B996695
theorem B664505 : Blo 439778 664505 := bstep (se 2 (by rfl) ⟨249189, by rfl⟩ : syracuseStep 664505 = 498379) B498379
theorem B664583 : Blo 439778 664583 := bstep (se 1 (by rfl) ⟨498437, by rfl⟩ : syracuseStep 664583 = 996875) B996875
theorem B664619 : Blo 439778 664619 := bstep (se 1 (by rfl) ⟨498464, by rfl⟩ : syracuseStep 664619 = 996929) B996929
theorem B664649 : Blo 439778 664649 := bstep (se 2 (by rfl) ⟨249243, by rfl⟩ : syracuseStep 664649 = 498487) B498487
theorem B992375 : Blo 439778 992375 := bstep (se 1 (by rfl) ⟨744281, by rfl⟩ : syracuseStep 992375 = 1488563) B1488563
theorem B4236461 : Blo 439778 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B664763 : Blo 439778 664763 := bstep (se 1 (by rfl) ⟨498572, by rfl⟩ : syracuseStep 664763 = 997145) B997145
theorem B664823 : Blo 439778 664823 := bstep (se 1 (by rfl) ⟨498617, by rfl⟩ : syracuseStep 664823 = 997235) B997235
theorem B664847 : Blo 439778 664847 := bstep (se 1 (by rfl) ⟨498635, by rfl⟩ : syracuseStep 664847 = 997271) B997271
theorem B992555 : Blo 439778 992555 := bstep (se 1 (by rfl) ⟨744416, by rfl⟩ : syracuseStep 992555 = 1488833) B1488833
theorem B664889 : Blo 439778 664889 := bstep (se 2 (by rfl) ⟨249333, by rfl⟩ : syracuseStep 664889 = 498667) B498667
theorem B1254791 : Blo 439778 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B894343 : Blo 439778 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B664967 : Blo 439778 664967 := bstep (se 1 (by rfl) ⟨498725, by rfl⟩ : syracuseStep 664967 = 997451) B997451
theorem B665003 : Blo 439778 665003 := bstep (se 1 (by rfl) ⟨498752, by rfl⟩ : syracuseStep 665003 = 997505) B997505
theorem B665033 : Blo 439778 665033 := bstep (se 2 (by rfl) ⟨249387, by rfl⟩ : syracuseStep 665033 = 498775) B498775
theorem B5678545 : Blo 439778 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B665147 : Blo 439778 665147 := bstep (se 1 (by rfl) ⟨498860, by rfl⟩ : syracuseStep 665147 = 997721) B997721
theorem B1680983 : Blo 439778 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B665207 : Blo 439778 665207 := bstep (se 1 (by rfl) ⟨498905, by rfl⟩ : syracuseStep 665207 = 997811) B997811
theorem B665231 : Blo 439778 665231 := bstep (se 1 (by rfl) ⟨498923, by rfl⟩ : syracuseStep 665231 = 997847) B997847
theorem B992915 : Blo 439778 992915 := bstep (se 1 (by rfl) ⟨744686, by rfl⟩ : syracuseStep 992915 = 1489373) B1489373
theorem B665273 : Blo 439778 665273 := bstep (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) B498955
theorem B992969 : Blo 439778 992969 := bstep (se 2 (by rfl) ⟨372363, by rfl⟩ : syracuseStep 992969 = 744727) B744727
theorem B665351 : Blo 439778 665351 := bstep (se 1 (by rfl) ⟨499013, by rfl⟩ : syracuseStep 665351 = 998027) B998027
theorem B665387 : Blo 439778 665387 := bstep (se 1 (by rfl) ⟨499040, by rfl⟩ : syracuseStep 665387 = 998081) B998081
theorem B665417 : Blo 439778 665417 := bstep (se 2 (by rfl) ⟨249531, by rfl⟩ : syracuseStep 665417 = 499063) B499063
theorem B2238353 : Blo 439778 2238353 := bstep (se 2 (by rfl) ⟨839382, by rfl⟩ : syracuseStep 2238353 = 1678765) B1678765
theorem B1484729 : Blo 439778 1484729 := bstep (se 2 (by rfl) ⟨556773, by rfl⟩ : syracuseStep 1484729 = 1113547) B1113547
theorem B665531 : Blo 439778 665531 := bstep (se 1 (by rfl) ⟨499148, by rfl⟩ : syracuseStep 665531 = 998297) B998297
theorem B665591 : Blo 439778 665591 := bstep (se 1 (by rfl) ⟨499193, by rfl⟩ : syracuseStep 665591 = 998387) B998387
theorem B1058827 : Blo 439778 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B894991 : Blo 439778 894991 := bstep (se 1 (by rfl) ⟨671243, by rfl⟩ : syracuseStep 894991 = 1342487) B1342487
theorem B665615 : Blo 439778 665615 := bstep (se 1 (by rfl) ⟨499211, by rfl⟩ : syracuseStep 665615 = 998423) B998423
theorem B665657 : Blo 439778 665657 := bstep (se 2 (by rfl) ⟨249621, by rfl⟩ : syracuseStep 665657 = 499243) B499243
theorem B1681469 : Blo 439778 1681469 := bstep (se 3 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 1681469 = 630551) B630551
theorem B993671 : Blo 439778 993671 := bstep (se 1 (by rfl) ⟨745253, by rfl⟩ : syracuseStep 993671 = 1490507) B1490507
theorem B1288601 : Blo 439778 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B567799 : Blo 439778 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B1485323 : Blo 439778 1485323 := bstep (se 1 (by rfl) ⟨1113992, by rfl⟩ : syracuseStep 1485323 = 2227985) B2227985
theorem B993851 : Blo 439778 993851 := bstep (se 1 (by rfl) ⟨745388, by rfl⟩ : syracuseStep 993851 = 1490777) B1490777
theorem B1059443 : Blo 439778 1059443 := bstep (se 1 (by rfl) ⟨794582, by rfl⟩ : syracuseStep 1059443 = 1589165) B1589165
theorem B1485431 : Blo 439778 1485431 := bstep (se 1 (by rfl) ⟨1114073, by rfl⟩ : syracuseStep 1485431 = 2228147) B2228147
theorem B993977 : Blo 439778 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B9186085 : Blo 439778 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1190771 : Blo 439778 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B994319 : Blo 439778 994319 := bstep (se 1 (by rfl) ⟨745739, by rfl⟩ : syracuseStep 994319 = 1491479) B1491479
theorem B994337 : Blo 439778 994337 := bstep (se 2 (by rfl) ⟨372876, by rfl⟩ : syracuseStep 994337 = 745753) B745753
theorem B1486025 : Blo 439778 1486025 := bstep (se 2 (by rfl) ⟨557259, by rfl⟩ : syracuseStep 1486025 = 1114519) B1114519
theorem B1256705 : Blo 439778 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B2043137 : Blo 439778 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B994679 : Blo 439778 994679 := bstep (se 1 (by rfl) ⟨746009, by rfl⟩ : syracuseStep 994679 = 1492019) B1492019
theorem B994859 : Blo 439778 994859 := bstep (se 1 (by rfl) ⟨746144, by rfl⟩ : syracuseStep 994859 = 1492289) B1492289
theorem B1060499 : Blo 439778 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1257275 : Blo 439778 1257275 := bstep (se 1 (by rfl) ⟨942956, by rfl⟩ : syracuseStep 1257275 = 1885913) B1885913
theorem B1486727 : Blo 439778 1486727 := bstep (se 1 (by rfl) ⟨1115045, by rfl⟩ : syracuseStep 1486727 = 2230091) B2230091
theorem B995219 : Blo 439778 995219 := bstep (se 1 (by rfl) ⟨746414, by rfl⟩ : syracuseStep 995219 = 1492829) B1492829
theorem B995273 : Blo 439778 995273 := bstep (se 2 (by rfl) ⟨373227, by rfl⟩ : syracuseStep 995273 = 746455) B746455
theorem B2240459 : Blo 439778 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B1191937 : Blo 439778 1191937 := bstep (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) B893953
theorem B1257515 : Blo 439778 1257515 := bstep (se 1 (by rfl) ⟨943136, by rfl⟩ : syracuseStep 1257515 = 1886273) B1886273
theorem B1585271 : Blo 439778 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B1487105 : Blo 439778 1487105 := bstep (se 2 (by rfl) ⟨557664, by rfl⟩ : syracuseStep 1487105 = 1115329) B1115329
theorem B2240783 : Blo 439778 2240783 := bstep (se 1 (by rfl) ⟨1680587, by rfl⟩ : syracuseStep 2240783 = 3361175) B3361175
theorem B3781187 : Blo 439778 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B6369911 : Blo 439778 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B995975 : Blo 439778 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B471739 : Blo 439778 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B996155 : Blo 439778 996155 := bstep (se 1 (by rfl) ⟨747116, by rfl⟩ : syracuseStep 996155 = 1494233) B1494233
theorem B996281 : Blo 439778 996281 := bstep (se 2 (by rfl) ⟨373605, by rfl⟩ : syracuseStep 996281 = 747211) B747211
theorem B1061903 : Blo 439778 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1487915 : Blo 439778 1487915 := bstep (se 1 (by rfl) ⟨1115936, by rfl⟩ : syracuseStep 1487915 = 2231873) B2231873
theorem B668873 : Blo 439778 668873 := bstep (se 2 (by rfl) ⟨250827, by rfl⟩ : syracuseStep 668873 = 501655) B501655
theorem B996623 : Blo 439778 996623 := bstep (se 1 (by rfl) ⟨747467, by rfl⟩ : syracuseStep 996623 = 1494935) B1494935
theorem B996641 : Blo 439778 996641 := bstep (se 2 (by rfl) ⟨373740, by rfl⟩ : syracuseStep 996641 = 747481) B747481
theorem B636233 : Blo 439778 636233 := bstep (se 2 (by rfl) ⟨238587, by rfl⟩ : syracuseStep 636233 = 477175) B477175
theorem B1684871 : Blo 439778 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B5092793 : Blo 439778 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B439815 : Blo 439778 439815 := bstep (se 1 (by rfl) ⟨329861, by rfl⟩ : syracuseStep 439815 = 659723) B659723
theorem B439823 : Blo 439778 439823 := bstep (se 1 (by rfl) ⟨329867, by rfl⟩ : syracuseStep 439823 = 659735) B659735
theorem B439867 : Blo 439778 439867 := bstep (se 1 (by rfl) ⟨329900, by rfl⟩ : syracuseStep 439867 = 659801) B659801
theorem B1947223 : Blo 439778 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B996983 : Blo 439778 996983 := bstep (se 1 (by rfl) ⟨747737, by rfl⟩ : syracuseStep 996983 = 1495475) B1495475
theorem B439943 : Blo 439778 439943 := bstep (se 1 (by rfl) ⟨329957, by rfl⟩ : syracuseStep 439943 = 659915) B659915
theorem B439951 : Blo 439778 439951 := bstep (se 1 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 439951 = 659927) B659927
theorem B439995 : Blo 439778 439995 := bstep (se 1 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 439995 = 659993) B659993
theorem B2242241 : Blo 439778 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B440071 : Blo 439778 440071 := bstep (se 1 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 440071 = 660107) B660107
theorem B440079 : Blo 439778 440079 := bstep (se 1 (by rfl) ⟨330059, by rfl⟩ : syracuseStep 440079 = 660119) B660119
theorem B997163 : Blo 439778 997163 := bstep (se 1 (by rfl) ⟨747872, by rfl⟩ : syracuseStep 997163 = 1495745) B1495745
theorem B440123 : Blo 439778 440123 := bstep (se 1 (by rfl) ⟨330092, by rfl⟩ : syracuseStep 440123 = 660185) B660185
theorem B1587059 : Blo 439778 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B440199 : Blo 439778 440199 := bstep (se 1 (by rfl) ⟨330149, by rfl⟩ : syracuseStep 440199 = 660299) B660299
theorem B440207 : Blo 439778 440207 := bstep (se 1 (by rfl) ⟨330155, by rfl⟩ : syracuseStep 440207 = 660311) B660311
theorem B440251 : Blo 439778 440251 := bstep (se 1 (by rfl) ⟨330188, by rfl⟩ : syracuseStep 440251 = 660377) B660377
theorem B440327 : Blo 439778 440327 := bstep (se 1 (by rfl) ⟨330245, by rfl⟩ : syracuseStep 440327 = 660491) B660491
theorem B440335 : Blo 439778 440335 := bstep (se 1 (by rfl) ⟨330251, by rfl⟩ : syracuseStep 440335 = 660503) B660503
theorem B2832407 : Blo 439778 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B440379 : Blo 439778 440379 := bstep (se 1 (by rfl) ⟨330284, by rfl⟩ : syracuseStep 440379 = 660569) B660569
theorem B440455 : Blo 439778 440455 := bstep (se 1 (by rfl) ⟨330341, by rfl⟩ : syracuseStep 440455 = 660683) B660683
theorem B440463 : Blo 439778 440463 := bstep (se 1 (by rfl) ⟨330347, by rfl⟩ : syracuseStep 440463 = 660695) B660695
theorem B997523 : Blo 439778 997523 := bstep (se 1 (by rfl) ⟨748142, by rfl⟩ : syracuseStep 997523 = 1496285) B1496285
theorem B4044973 : Blo 439778 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B669881 : Blo 439778 669881 := bstep (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) B502411
theorem B440507 : Blo 439778 440507 := bstep (se 1 (by rfl) ⟨330380, by rfl⟩ : syracuseStep 440507 = 660761) B660761
theorem B997577 : Blo 439778 997577 := bstep (se 2 (by rfl) ⟨374091, by rfl⟩ : syracuseStep 997577 = 748183) B748183
theorem B440583 : Blo 439778 440583 := bstep (se 1 (by rfl) ⟨330437, by rfl⟩ : syracuseStep 440583 = 660875) B660875
theorem B440591 : Blo 439778 440591 := bstep (se 1 (by rfl) ⟨330443, by rfl⟩ : syracuseStep 440591 = 660887) B660887
theorem B36616493 : Blo 439778 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B440635 : Blo 439778 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B1489211 : Blo 439778 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B440711 : Blo 439778 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B440719 : Blo 439778 440719 := bstep (se 1 (by rfl) ⟨330539, by rfl⟩ : syracuseStep 440719 = 661079) B661079
theorem B440763 : Blo 439778 440763 := bstep (se 1 (by rfl) ⟨330572, by rfl⟩ : syracuseStep 440763 = 661145) B661145
theorem B440839 : Blo 439778 440839 := bstep (se 1 (by rfl) ⟨330629, by rfl⟩ : syracuseStep 440839 = 661259) B661259
theorem B440847 : Blo 439778 440847 := bstep (se 1 (by rfl) ⟨330635, by rfl⟩ : syracuseStep 440847 = 661271) B661271
theorem B440891 : Blo 439778 440891 := bstep (se 1 (by rfl) ⟨330668, by rfl⟩ : syracuseStep 440891 = 661337) B661337
theorem B1784387 : Blo 439778 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B440967 : Blo 439778 440967 := bstep (se 1 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 440967 = 661451) B661451
theorem B440975 : Blo 439778 440975 := bstep (se 1 (by rfl) ⟨330731, by rfl⟩ : syracuseStep 440975 = 661463) B661463
theorem B441019 : Blo 439778 441019 := bstep (se 1 (by rfl) ⟨330764, by rfl⟩ : syracuseStep 441019 = 661529) B661529
theorem B441095 : Blo 439778 441095 := bstep (se 1 (by rfl) ⟨330821, by rfl⟩ : syracuseStep 441095 = 661643) B661643
theorem B441103 : Blo 439778 441103 := bstep (se 1 (by rfl) ⟨330827, by rfl⟩ : syracuseStep 441103 = 661655) B661655
theorem B1489697 : Blo 439778 1489697 := bstep (se 2 (by rfl) ⟨558636, by rfl⟩ : syracuseStep 1489697 = 1117273) B1117273
theorem B1882939 : Blo 439778 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B441147 : Blo 439778 441147 := bstep (se 1 (by rfl) ⟨330860, by rfl⟩ : syracuseStep 441147 = 661721) B661721
theorem B441223 : Blo 439778 441223 := bstep (se 1 (by rfl) ⟨330917, by rfl⟩ : syracuseStep 441223 = 661835) B661835
theorem B998279 : Blo 439778 998279 := bstep (se 1 (by rfl) ⟨748709, by rfl⟩ : syracuseStep 998279 = 1497419) B1497419
theorem B441231 : Blo 439778 441231 := bstep (se 1 (by rfl) ⟨330923, by rfl⟩ : syracuseStep 441231 = 661847) B661847
theorem B1784729 : Blo 439778 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B441275 : Blo 439778 441275 := bstep (se 1 (by rfl) ⟨330956, by rfl⟩ : syracuseStep 441275 = 661913) B661913
theorem B2243537 : Blo 439778 2243537 := bstep (se 2 (by rfl) ⟨841326, by rfl⟩ : syracuseStep 2243537 = 1682653) B1682653
theorem B441351 : Blo 439778 441351 := bstep (se 1 (by rfl) ⟨331013, by rfl⟩ : syracuseStep 441351 = 662027) B662027
theorem B441359 : Blo 439778 441359 := bstep (se 1 (by rfl) ⟨331019, by rfl⟩ : syracuseStep 441359 = 662039) B662039
theorem B441403 : Blo 439778 441403 := bstep (se 1 (by rfl) ⟨331052, by rfl⟩ : syracuseStep 441403 = 662105) B662105
theorem B998459 : Blo 439778 998459 := bstep (se 1 (by rfl) ⟨748844, by rfl⟩ : syracuseStep 998459 = 1497689) B1497689
theorem B441479 : Blo 439778 441479 := bstep (se 1 (by rfl) ⟨331109, by rfl⟩ : syracuseStep 441479 = 662219) B662219
theorem B441487 : Blo 439778 441487 := bstep (se 1 (by rfl) ⟨331115, by rfl⟩ : syracuseStep 441487 = 662231) B662231
theorem B441531 : Blo 439778 441531 := bstep (se 1 (by rfl) ⟨331148, by rfl⟩ : syracuseStep 441531 = 662297) B662297
theorem B441607 : Blo 439778 441607 := bstep (se 1 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 441607 = 662411) B662411
theorem B441615 : Blo 439778 441615 := bstep (se 1 (by rfl) ⟨331211, by rfl⟩ : syracuseStep 441615 = 662423) B662423
theorem B441659 : Blo 439778 441659 := bstep (se 1 (by rfl) ⟨331244, by rfl⟩ : syracuseStep 441659 = 662489) B662489
theorem B4603195 : Blo 439778 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B1490291 : Blo 439778 1490291 := bstep (se 1 (by rfl) ⟨1117718, by rfl⟩ : syracuseStep 1490291 = 2235437) B2235437
theorem B441735 : Blo 439778 441735 := bstep (se 1 (by rfl) ⟨331301, by rfl⟩ : syracuseStep 441735 = 662603) B662603
theorem B441743 : Blo 439778 441743 := bstep (se 1 (by rfl) ⟨331307, by rfl⟩ : syracuseStep 441743 = 662615) B662615
theorem B441787 : Blo 439778 441787 := bstep (se 1 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 441787 = 662681) B662681
theorem B441863 : Blo 439778 441863 := bstep (se 1 (by rfl) ⟨331397, by rfl⟩ : syracuseStep 441863 = 662795) B662795
theorem B441871 : Blo 439778 441871 := bstep (se 1 (by rfl) ⟨331403, by rfl⟩ : syracuseStep 441871 = 662807) B662807
theorem B441915 : Blo 439778 441915 := bstep (se 1 (by rfl) ⟨331436, by rfl⟩ : syracuseStep 441915 = 662873) B662873
theorem B441991 : Blo 439778 441991 := bstep (se 1 (by rfl) ⟨331493, by rfl⟩ : syracuseStep 441991 = 662987) B662987
theorem B441999 : Blo 439778 441999 := bstep (se 1 (by rfl) ⟨331499, by rfl⟩ : syracuseStep 441999 = 662999) B662999
theorem B442043 : Blo 439778 442043 := bstep (se 1 (by rfl) ⟨331532, by rfl⟩ : syracuseStep 442043 = 663065) B663065
theorem B442119 : Blo 439778 442119 := bstep (se 1 (by rfl) ⟨331589, by rfl⟩ : syracuseStep 442119 = 663179) B663179
theorem B835343 : Blo 439778 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B442127 : Blo 439778 442127 := bstep (se 1 (by rfl) ⟨331595, by rfl⟩ : syracuseStep 442127 = 663191) B663191
theorem B442171 : Blo 439778 442171 := bstep (se 1 (by rfl) ⟨331628, by rfl⟩ : syracuseStep 442171 = 663257) B663257
theorem B9715573 : Blo 439778 9715573 := bstep (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) B910835
theorem B442247 : Blo 439778 442247 := bstep (se 1 (by rfl) ⟨331685, by rfl⟩ : syracuseStep 442247 = 663371) B663371
theorem B442255 : Blo 439778 442255 := bstep (se 1 (by rfl) ⟨331691, by rfl⟩ : syracuseStep 442255 = 663383) B663383
theorem B442299 : Blo 439778 442299 := bstep (se 1 (by rfl) ⟨331724, by rfl⟩ : syracuseStep 442299 = 663449) B663449
theorem B8077259 : Blo 439778 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B442375 : Blo 439778 442375 := bstep (se 1 (by rfl) ⟨331781, by rfl⟩ : syracuseStep 442375 = 663563) B663563
theorem B442383 : Blo 439778 442383 := bstep (se 1 (by rfl) ⟨331787, by rfl⟩ : syracuseStep 442383 = 663575) B663575
theorem B442427 : Blo 439778 442427 := bstep (se 1 (by rfl) ⟨331820, by rfl⟩ : syracuseStep 442427 = 663641) B663641
theorem B442503 : Blo 439778 442503 := bstep (se 1 (by rfl) ⟨331877, by rfl⟩ : syracuseStep 442503 = 663755) B663755
theorem B1196167 : Blo 439778 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B442511 : Blo 439778 442511 := bstep (se 1 (by rfl) ⟨331883, by rfl⟩ : syracuseStep 442511 = 663767) B663767
theorem B1065113 : Blo 439778 1065113 := bstep (se 2 (by rfl) ⟨399417, by rfl⟩ : syracuseStep 1065113 = 798835) B798835
theorem B3784877 : Blo 439778 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B442555 : Blo 439778 442555 := bstep (se 1 (by rfl) ⟨331916, by rfl⟩ : syracuseStep 442555 = 663833) B663833
theorem B442631 : Blo 439778 442631 := bstep (se 1 (by rfl) ⟨331973, by rfl⟩ : syracuseStep 442631 = 663947) B663947
theorem B442639 : Blo 439778 442639 := bstep (se 1 (by rfl) ⟨331979, by rfl⟩ : syracuseStep 442639 = 663959) B663959
theorem B442683 : Blo 439778 442683 := bstep (se 1 (by rfl) ⟨332012, by rfl⟩ : syracuseStep 442683 = 664025) B664025
theorem B442759 : Blo 439778 442759 := bstep (se 1 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 442759 = 664139) B664139
theorem B442767 : Blo 439778 442767 := bstep (se 1 (by rfl) ⟨332075, by rfl⟩ : syracuseStep 442767 = 664151) B664151
theorem B442811 : Blo 439778 442811 := bstep (se 1 (by rfl) ⟨332108, by rfl⟩ : syracuseStep 442811 = 664217) B664217
theorem B1262081 : Blo 439778 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B442887 : Blo 439778 442887 := bstep (se 1 (by rfl) ⟨332165, by rfl⟩ : syracuseStep 442887 = 664331) B664331
theorem B442895 : Blo 439778 442895 := bstep (se 1 (by rfl) ⟨332171, by rfl⟩ : syracuseStep 442895 = 664343) B664343
theorem B442939 : Blo 439778 442939 := bstep (se 1 (by rfl) ⟨332204, by rfl⟩ : syracuseStep 442939 = 664409) B664409
theorem B1589827 : Blo 439778 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B443015 : Blo 439778 443015 := bstep (se 1 (by rfl) ⟨332261, by rfl⟩ : syracuseStep 443015 = 664523) B664523
theorem B443023 : Blo 439778 443023 := bstep (se 1 (by rfl) ⟨332267, by rfl⟩ : syracuseStep 443023 = 664535) B664535
theorem B4244147 : Blo 439778 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B443067 : Blo 439778 443067 := bstep (se 1 (by rfl) ⟨332300, by rfl⟩ : syracuseStep 443067 = 664601) B664601
theorem B443143 : Blo 439778 443143 := bstep (se 1 (by rfl) ⟨332357, by rfl⟩ : syracuseStep 443143 = 664715) B664715
theorem B443151 : Blo 439778 443151 := bstep (se 1 (by rfl) ⟨332363, by rfl⟩ : syracuseStep 443151 = 664727) B664727
theorem B443195 : Blo 439778 443195 := bstep (se 1 (by rfl) ⟨332396, by rfl⟩ : syracuseStep 443195 = 664793) B664793
theorem B3785561 : Blo 439778 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B443271 : Blo 439778 443271 := bstep (se 1 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 443271 = 664907) B664907
theorem B443279 : Blo 439778 443279 := bstep (se 1 (by rfl) ⟨332459, by rfl⟩ : syracuseStep 443279 = 664919) B664919
theorem B443323 : Blo 439778 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B1262537 : Blo 439778 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B443399 : Blo 439778 443399 := bstep (se 1 (by rfl) ⟨332549, by rfl⟩ : syracuseStep 443399 = 665099) B665099
theorem B2245643 : Blo 439778 2245643 := bstep (se 1 (by rfl) ⟨1684232, by rfl⟩ : syracuseStep 2245643 = 3368465) B3368465
theorem B443407 : Blo 439778 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B443451 : Blo 439778 443451 := bstep (se 1 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 443451 = 665177) B665177
theorem B5653637 : Blo 439778 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B443527 : Blo 439778 443527 := bstep (se 1 (by rfl) ⟨332645, by rfl⟩ : syracuseStep 443527 = 665291) B665291
theorem B443535 : Blo 439778 443535 := bstep (se 1 (by rfl) ⟨332651, by rfl⟩ : syracuseStep 443535 = 665303) B665303
theorem B2245805 : Blo 439778 2245805 := bstep (se 3 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 2245805 = 842177) B842177
theorem B443579 : Blo 439778 443579 := bstep (se 1 (by rfl) ⟨332684, by rfl⟩ : syracuseStep 443579 = 665369) B665369
theorem B443655 : Blo 439778 443655 := bstep (se 1 (by rfl) ⟨332741, by rfl⟩ : syracuseStep 443655 = 665483) B665483
theorem B443663 : Blo 439778 443663 := bstep (se 1 (by rfl) ⟨332747, by rfl⟩ : syracuseStep 443663 = 665495) B665495
theorem B1262891 : Blo 439778 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B443707 : Blo 439778 443707 := bstep (se 1 (by rfl) ⟨332780, by rfl⟩ : syracuseStep 443707 = 665561) B665561
theorem B836983 : Blo 439778 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B2835971 : Blo 439778 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B1263289 : Blo 439778 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B1361693 : Blo 439778 1361693 := bstep (se 3 (by rfl) ⟨255317, by rfl⟩ : syracuseStep 1361693 = 510635) B510635
theorem B1492883 : Blo 439778 1492883 := bstep (se 1 (by rfl) ⟨1119662, by rfl⟩ : syracuseStep 1492883 = 2239325) B2239325
theorem B1132663 : Blo 439778 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B2509379 : Blo 439778 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B1198793 : Blo 439778 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B4016947 : Blo 439778 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B674747 : Blo 439778 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B838775 : Blo 439778 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B838927 : Blo 439778 838927 := bstep (se 1 (by rfl) ⟨629195, by rfl⟩ : syracuseStep 838927 = 1258391) B1258391
theorem B1494287 : Blo 439778 1494287 := bstep (se 1 (by rfl) ⟨1120715, by rfl⟩ : syracuseStep 1494287 = 2241431) B2241431
theorem B1494557 : Blo 439778 1494557 := bstep (se 3 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 1494557 = 560459) B560459
theorem B839315 : Blo 439778 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B708281 : Blo 439778 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B15257393 : Blo 439778 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B6475949 : Blo 439778 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B708793 : Blo 439778 708793 := bstep (se 2 (by rfl) ⟨265797, by rfl⟩ : syracuseStep 708793 = 531595) B531595
theorem B1004167 : Blo 439778 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B1594093 : Blo 439778 1594093 := bstep (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) B597785
theorem B1332001 : Blo 439778 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B2511769 : Blo 439778 2511769 := bstep (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) B1883827
theorem B1495961 : Blo 439778 1495961 := bstep (se 2 (by rfl) ⟨560985, by rfl⟩ : syracuseStep 1495961 = 1121971) B1121971
theorem B1692683 : Blo 439778 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B840719 : Blo 439778 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B742459 : Blo 439778 742459 := bstep (se 1 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 742459 = 1113689) B1113689
theorem B742601 : Blo 439778 742601 := bstep (se 2 (by rfl) ⟨278475, by rfl⟩ : syracuseStep 742601 = 556951) B556951
theorem B1594657 : Blo 439778 1594657 := bstep (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) B1195993
theorem B1889689 : Blo 439778 1889689 := bstep (se 2 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 1889689 = 1417267) B1417267
theorem B2840093 : Blo 439778 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B841259 : Blo 439778 841259 := bstep (se 1 (by rfl) ⟨630944, by rfl⟩ : syracuseStep 841259 = 1261889) B1261889
theorem B710203 : Blo 439778 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B1496663 : Blo 439778 1496663 := bstep (se 1 (by rfl) ⟨1122497, by rfl⟩ : syracuseStep 1496663 = 2244995) B2244995
theorem B710345 : Blo 439778 710345 := bstep (se 2 (by rfl) ⟨266379, by rfl⟩ : syracuseStep 710345 = 532759) B532759
theorem B743303 : Blo 439778 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B1497149 : Blo 439778 1497149 := bstep (se 3 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 1497149 = 561431) B561431
theorem B5462149 : Blo 439778 5462149 := bstep (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) B1024153
theorem B6379721 : Blo 439778 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B2677043 : Blo 439778 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1432075 : Blo 439778 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B743951 : Blo 439778 743951 := bstep (se 1 (by rfl) ⟨557963, by rfl⟩ : syracuseStep 743951 = 1115927) B1115927
theorem B1890935 : Blo 439778 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B842375 : Blo 439778 842375 := bstep (se 1 (by rfl) ⟨631781, by rfl⟩ : syracuseStep 842375 = 1263563) B1263563
theorem B10902197 : Blo 439778 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B2513753 : Blo 439778 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B744491 : Blo 439778 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B1596503 : Blo 439778 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B744889 : Blo 439778 744889 := bstep (se 2 (by rfl) ⟨279333, by rfl⟩ : syracuseStep 744889 = 558667) B558667
theorem B1072673 : Blo 439778 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1793603 : Blo 439778 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B745591 : Blo 439778 745591 := bstep (se 1 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 745591 = 1118387) B1118387
theorem B745787 : Blo 439778 745787 := bstep (se 1 (by rfl) ⟨559340, by rfl⟩ : syracuseStep 745787 = 1118681) B1118681
theorem B2122307 : Blo 439778 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B746185 : Blo 439778 746185 := bstep (se 2 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 746185 = 559639) B559639
theorem B1697057 : Blo 439778 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B746887 : Blo 439778 746887 := bstep (se 1 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 746887 = 1120331) B1120331
theorem B3171869 : Blo 439778 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B943751 : Blo 439778 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B747535 : Blo 439778 747535 := bstep (se 1 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 747535 = 1121303) B1121303
theorem B3369437 : Blo 439778 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B748075 : Blo 439778 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B5368385 : Blo 439778 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B748217 : Blo 439778 748217 := bstep (se 2 (by rfl) ⟨280581, by rfl⟩ : syracuseStep 748217 = 561163) B561163
theorem B944939 : Blo 439778 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B2517875 : Blo 439778 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B3009433 : Blo 439778 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B1010873 : Blo 439778 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B4321073 : Blo 439778 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B5369753 : Blo 439778 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B7171993 : Blo 439778 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2682809 : Blo 439778 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B2387897 : Blo 439778 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B2125997 : Blo 439778 2125997 := bstep (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) B797249
theorem B2519333 : Blo 439778 2519333 := bstep (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) B472375
theorem B2388371 : Blo 439778 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B946579 : Blo 439778 946579 := bstep (se 1 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 946579 = 1419869) B1419869
theorem B7139825 : Blo 439778 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B2683415 : Blo 439778 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B12743513 : Blo 439778 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B1340345 : Blo 439778 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B2520017 : Blo 439778 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B4846837 : Blo 439778 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B2520335 : Blo 439778 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B1701179 : Blo 439778 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B1341319 : Blo 439778 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B1964119 : Blo 439778 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2422871 : Blo 439778 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B2521793 : Blo 439778 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B1702657 : Blo 439778 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B1342295 : Blo 439778 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B1670003 : Blo 439778 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B1113203 : Blo 439778 1113203 := bstep (se 1 (by rfl) ⟨834902, by rfl⟩ : syracuseStep 1113203 = 1669805) B1669805
theorem B1113223 : Blo 439778 1113223 := bstep (se 1 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 1113223 = 1669835) B1669835
theorem B1113497 : Blo 439778 1113497 := bstep (se 2 (by rfl) ⟨417561, by rfl⟩ : syracuseStep 1113497 = 835123) B835123
theorem B1113659 : Blo 439778 1113659 := bstep (se 1 (by rfl) ⟨835244, by rfl⟩ : syracuseStep 1113659 = 1670489) B1670489
theorem B3768065 : Blo 439778 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B1113871 : Blo 439778 1113871 := bstep (se 1 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 1113871 = 1670807) B1670807
theorem B753467 : Blo 439778 753467 := bstep (se 1 (by rfl) ⟨565100, by rfl⟩ : syracuseStep 753467 = 1130201) B1130201
theorem B557047 : Blo 439778 557047 := bstep (se 1 (by rfl) ⟨417785, by rfl⟩ : syracuseStep 557047 = 835571) B835571
theorem B2523251 : Blo 439778 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B4292785 : Blo 439778 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B4227389 : Blo 439778 4227389 := bstep (se 3 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 4227389 = 1585271) B1585271
theorem B2228795 : Blo 439778 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B2523707 : Blo 439778 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B4981421 : Blo 439778 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1114823 : Blo 439778 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B3769091 : Blo 439778 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B1410205 : Blo 439778 1410205 := bstep (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) B528827
theorem B2229443 : Blo 439778 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B6391133 : Blo 439778 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B5637539 : Blo 439778 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B1672919 : Blo 439778 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B1115977 : Blo 439778 1115977 := bstep (se 2 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 1115977 = 836983) B836983
theorem B7571393 : Blo 439778 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B3344651 : Blo 439778 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B559543 : Blo 439778 559543 := bstep (se 1 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 559543 = 839315) B839315
theorem B3574253 : Blo 439778 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B1411769 : Blo 439778 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B1510217 : Blo 439778 1510217 := bstep (se 2 (by rfl) ⟨566331, by rfl⟩ : syracuseStep 1510217 = 1132663) B1132663
theorem B1117111 : Blo 439778 1117111 := bstep (se 1 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 1117111 = 1675667) B1675667
theorem B495067 : Blo 439778 495067 := bstep (se 1 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 495067 = 742601) B742601
theorem B3346109 : Blo 439778 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B560839 : Blo 439778 560839 := bstep (se 1 (by rfl) ⟨420629, by rfl⟩ : syracuseStep 560839 = 841259) B841259
theorem B495535 : Blo 439778 495535 := bstep (se 1 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 495535 = 743303) B743303
theorem B3346595 : Blo 439778 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B659705 : Blo 439778 659705 := bstep (se 2 (by rfl) ⟨247389, by rfl⟩ : syracuseStep 659705 = 494779) B494779
theorem B659807 : Blo 439778 659807 := bstep (se 1 (by rfl) ⟨494855, by rfl⟩ : syracuseStep 659807 = 989711) B989711
theorem B495967 : Blo 439778 495967 := bstep (se 1 (by rfl) ⟨371975, by rfl⟩ : syracuseStep 495967 = 743951) B743951
theorem B1118569 : Blo 439778 1118569 := bstep (se 2 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 1118569 = 838927) B838927
theorem B659819 : Blo 439778 659819 := bstep (se 1 (by rfl) ⟨494864, by rfl⟩ : syracuseStep 659819 = 989729) B989729
theorem B561583 : Blo 439778 561583 := bstep (se 1 (by rfl) ⟨421187, by rfl⟩ : syracuseStep 561583 = 842375) B842375
theorem B1675835 : Blo 439778 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B660047 : Blo 439778 660047 := bstep (se 1 (by rfl) ⟨495035, by rfl⟩ : syracuseStep 660047 = 990071) B990071
theorem B1118843 : Blo 439778 1118843 := bstep (se 1 (by rfl) ⟨839132, by rfl⟩ : syracuseStep 1118843 = 1678265) B1678265
theorem B660167 : Blo 439778 660167 := bstep (se 1 (by rfl) ⟨495125, by rfl⟩ : syracuseStep 660167 = 990251) B990251
theorem B496327 : Blo 439778 496327 := bstep (se 1 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 496327 = 744491) B744491
theorem B660329 : Blo 439778 660329 := bstep (se 2 (by rfl) ⟨247623, by rfl⟩ : syracuseStep 660329 = 495247) B495247
theorem B660407 : Blo 439778 660407 := bstep (se 1 (by rfl) ⟨495305, by rfl⟩ : syracuseStep 660407 = 990611) B990611
theorem B660443 : Blo 439778 660443 := bstep (se 1 (by rfl) ⟨495332, by rfl⟩ : syracuseStep 660443 = 990665) B990665
theorem B3413195 : Blo 439778 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B660911 : Blo 439778 660911 := bstep (se 1 (by rfl) ⟨495683, by rfl⟩ : syracuseStep 660911 = 991367) B991367
theorem B2299355 : Blo 439778 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B661001 : Blo 439778 661001 := bstep (se 2 (by rfl) ⟨247875, by rfl⟩ : syracuseStep 661001 = 495751) B495751
theorem B661031 : Blo 439778 661031 := bstep (se 1 (by rfl) ⟨495773, by rfl⟩ : syracuseStep 661031 = 991547) B991547
theorem B497191 : Blo 439778 497191 := bstep (se 1 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 497191 = 745787) B745787
theorem B661115 : Blo 439778 661115 := bstep (se 1 (by rfl) ⟨495836, by rfl⟩ : syracuseStep 661115 = 991673) B991673
theorem B2233979 : Blo 439778 2233979 := bstep (se 1 (by rfl) ⟨1675484, by rfl⟩ : syracuseStep 2233979 = 3350969) B3350969
theorem B1414871 : Blo 439778 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B661241 : Blo 439778 661241 := bstep (se 2 (by rfl) ⟨247965, by rfl⟩ : syracuseStep 661241 = 495931) B495931
theorem B661343 : Blo 439778 661343 := bstep (se 1 (by rfl) ⟨496007, by rfl⟩ : syracuseStep 661343 = 992015) B992015
theorem B661355 : Blo 439778 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B661583 : Blo 439778 661583 := bstep (se 1 (by rfl) ⟨496187, by rfl⟩ : syracuseStep 661583 = 992375) B992375
theorem B2824307 : Blo 439778 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B661703 : Blo 439778 661703 := bstep (se 1 (by rfl) ⟨496277, by rfl⟩ : syracuseStep 661703 = 992555) B992555
theorem B628985 : Blo 439778 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B1415485 : Blo 439778 1415485 := bstep (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) B530807
theorem B661865 : Blo 439778 661865 := bstep (se 2 (by rfl) ⟨248199, by rfl⟩ : syracuseStep 661865 = 496399) B496399
theorem B1776001 : Blo 439778 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B1120655 : Blo 439778 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B661943 : Blo 439778 661943 := bstep (se 1 (by rfl) ⟨496457, by rfl⟩ : syracuseStep 661943 = 992915) B992915
theorem B661979 : Blo 439778 661979 := bstep (se 1 (by rfl) ⟨496484, by rfl⟩ : syracuseStep 661979 = 992969) B992969
theorem B3349025 : Blo 439778 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B989819 : Blo 439778 989819 := bstep (se 1 (by rfl) ⟨742364, by rfl⟩ : syracuseStep 989819 = 1484729) B1484729
theorem B1120979 : Blo 439778 1120979 := bstep (se 1 (by rfl) ⟨840734, by rfl⟩ : syracuseStep 1120979 = 1681469) B1681469
theorem B989945 : Blo 439778 989945 := bstep (se 2 (by rfl) ⟨371229, by rfl⟩ : syracuseStep 989945 = 742459) B742459
theorem B4758365 : Blo 439778 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B662447 : Blo 439778 662447 := bstep (se 1 (by rfl) ⟨496835, by rfl⟩ : syracuseStep 662447 = 993671) B993671
theorem B859067 : Blo 439778 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B6462449 : Blo 439778 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B990215 : Blo 439778 990215 := bstep (se 1 (by rfl) ⟨742661, by rfl⟩ : syracuseStep 990215 = 1485323) B1485323
theorem B662537 : Blo 439778 662537 := bstep (se 2 (by rfl) ⟨248451, by rfl⟩ : syracuseStep 662537 = 496903) B496903
theorem B662567 : Blo 439778 662567 := bstep (se 1 (by rfl) ⟨496925, by rfl⟩ : syracuseStep 662567 = 993851) B993851
theorem B3578923 : Blo 439778 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B990287 : Blo 439778 990287 := bstep (se 1 (by rfl) ⟨742715, by rfl⟩ : syracuseStep 990287 = 1485431) B1485431
theorem B662651 : Blo 439778 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B498811 : Blo 439778 498811 := bstep (se 1 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 498811 = 748217) B748217
theorem B629959 : Blo 439778 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B793847 : Blo 439778 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B1678583 : Blo 439778 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B662777 : Blo 439778 662777 := bstep (se 2 (by rfl) ⟨248541, by rfl⟩ : syracuseStep 662777 = 497083) B497083
theorem B662879 : Blo 439778 662879 := bstep (se 1 (by rfl) ⟨497159, by rfl⟩ : syracuseStep 662879 = 994319) B994319
theorem B662891 : Blo 439778 662891 := bstep (se 1 (by rfl) ⟨497168, by rfl⟩ : syracuseStep 662891 = 994337) B994337
theorem B990683 : Blo 439778 990683 := bstep (se 1 (by rfl) ⟨743012, by rfl⟩ : syracuseStep 990683 = 1486025) B1486025
theorem B663119 : Blo 439778 663119 := bstep (se 1 (by rfl) ⟨497339, by rfl⟩ : syracuseStep 663119 = 994679) B994679
theorem B663239 : Blo 439778 663239 := bstep (se 1 (by rfl) ⟨497429, by rfl⟩ : syracuseStep 663239 = 994859) B994859
theorem B663401 : Blo 439778 663401 := bstep (se 2 (by rfl) ⟨248775, by rfl⟩ : syracuseStep 663401 = 497551) B497551
theorem B991151 : Blo 439778 991151 := bstep (se 1 (by rfl) ⟨743363, by rfl⟩ : syracuseStep 991151 = 1486727) B1486727
theorem B663479 : Blo 439778 663479 := bstep (se 1 (by rfl) ⟨497609, by rfl⟩ : syracuseStep 663479 = 995219) B995219
theorem B3579835 : Blo 439778 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B663515 : Blo 439778 663515 := bstep (se 1 (by rfl) ⟨497636, by rfl⟩ : syracuseStep 663515 = 995273) B995273
theorem B1417331 : Blo 439778 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B991403 : Blo 439778 991403 := bstep (se 1 (by rfl) ⟨743552, by rfl⟩ : syracuseStep 991403 = 1487105) B1487105
theorem B7282865 : Blo 439778 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B1679555 : Blo 439778 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B2236733 : Blo 439778 2236733 := bstep (se 3 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 2236733 = 838775) B838775
theorem B4759883 : Blo 439778 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B663983 : Blo 439778 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B664073 : Blo 439778 664073 := bstep (se 2 (by rfl) ⟨249027, by rfl⟩ : syracuseStep 664073 = 498055) B498055
theorem B664103 : Blo 439778 664103 := bstep (se 1 (by rfl) ⟨498077, by rfl⟩ : syracuseStep 664103 = 996155) B996155
theorem B8495675 : Blo 439778 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B664187 : Blo 439778 664187 := bstep (se 1 (by rfl) ⟨498140, by rfl⟩ : syracuseStep 664187 = 996281) B996281
theorem B1680011 : Blo 439778 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B1909433 : Blo 439778 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B991943 : Blo 439778 991943 := bstep (se 1 (by rfl) ⟨743957, by rfl⟩ : syracuseStep 991943 = 1487915) B1487915
theorem B664313 : Blo 439778 664313 := bstep (se 2 (by rfl) ⟨249117, by rfl⟩ : syracuseStep 664313 = 498235) B498235
theorem B1680223 : Blo 439778 1680223 := bstep (se 1 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 1680223 = 2520335) B2520335
theorem B664415 : Blo 439778 664415 := bstep (se 1 (by rfl) ⟨498311, by rfl⟩ : syracuseStep 664415 = 996623) B996623
theorem B664427 : Blo 439778 664427 := bstep (se 1 (by rfl) ⟨498320, by rfl⟩ : syracuseStep 664427 = 996641) B996641
theorem B1123247 : Blo 439778 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B2270209 : Blo 439778 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B664655 : Blo 439778 664655 := bstep (se 1 (by rfl) ⟨498491, by rfl⟩ : syracuseStep 664655 = 996983) B996983
theorem B664775 : Blo 439778 664775 := bstep (se 1 (by rfl) ⟨498581, by rfl⟩ : syracuseStep 664775 = 997163) B997163
theorem B1058039 : Blo 439778 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B796009 : Blo 439778 796009 := bstep (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) B597007
theorem B664937 : Blo 439778 664937 := bstep (se 2 (by rfl) ⟨249351, by rfl⟩ : syracuseStep 664937 = 498703) B498703
theorem B1615247 : Blo 439778 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B665015 : Blo 439778 665015 := bstep (se 1 (by rfl) ⟨498761, by rfl⟩ : syracuseStep 665015 = 997523) B997523
theorem B665051 : Blo 439778 665051 := bstep (se 1 (by rfl) ⟨498788, by rfl⟩ : syracuseStep 665051 = 997577) B997577
theorem B1484297 : Blo 439778 1484297 := bstep (se 2 (by rfl) ⟨556611, by rfl⟩ : syracuseStep 1484297 = 1113223) B1113223
theorem B992807 : Blo 439778 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B2827997 : Blo 439778 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B6137593 : Blo 439778 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B1681181 : Blo 439778 1681181 := bstep (se 3 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 1681181 = 630443) B630443
theorem B1681195 : Blo 439778 1681195 := bstep (se 1 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 1681195 = 2521793) B2521793
theorem B993131 : Blo 439778 993131 := bstep (se 1 (by rfl) ⟨744848, by rfl⟩ : syracuseStep 993131 = 1489697) B1489697
theorem B894863 : Blo 439778 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B993185 : Blo 439778 993185 := bstep (se 2 (by rfl) ⟨372444, by rfl⟩ : syracuseStep 993185 = 744889) B744889
theorem B665519 : Blo 439778 665519 := bstep (se 1 (by rfl) ⟨499139, by rfl⟩ : syracuseStep 665519 = 998279) B998279
theorem B1189819 : Blo 439778 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B665609 : Blo 439778 665609 := bstep (se 2 (by rfl) ⟨249603, by rfl⟩ : syracuseStep 665609 = 499207) B499207
theorem B665639 : Blo 439778 665639 := bstep (se 1 (by rfl) ⟨499229, by rfl⟩ : syracuseStep 665639 = 998459) B998459
theorem B2009245 : Blo 439778 2009245 := bstep (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) B753467
theorem B993527 : Blo 439778 993527 := bstep (se 1 (by rfl) ⟨745145, by rfl⟩ : syracuseStep 993527 = 1490291) B1490291
theorem B1485161 : Blo 439778 1485161 := bstep (se 2 (by rfl) ⟨556935, by rfl⟩ : syracuseStep 1485161 = 1113871) B1113871
theorem B12954097 : Blo 439778 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B2239001 : Blo 439778 2239001 := bstep (se 2 (by rfl) ⟨839625, by rfl⟩ : syracuseStep 2239001 = 1679251) B1679251
theorem B5384839 : Blo 439778 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B764615 : Blo 439778 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B994121 : Blo 439778 994121 := bstep (se 2 (by rfl) ⟨372795, by rfl⟩ : syracuseStep 994121 = 745591) B745591
theorem B1485755 : Blo 439778 1485755 := bstep (se 1 (by rfl) ⟨1114316, by rfl⟩ : syracuseStep 1485755 = 2228633) B2228633
theorem B2829431 : Blo 439778 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B2010359 : Blo 439778 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B3386843 : Blo 439778 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B10792435 : Blo 439778 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B994913 : Blo 439778 994913 := bstep (se 2 (by rfl) ⟨373092, by rfl⟩ : syracuseStep 994913 = 746185) B746185
theorem B3780229 : Blo 439778 3780229 := bstep (se 4 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 3780229 = 708793) B708793
theorem B6368989 : Blo 439778 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B995255 : Blo 439778 995255 := bstep (se 1 (by rfl) ⟨746441, by rfl⟩ : syracuseStep 995255 = 1492883) B1492883
theorem B7155773 : Blo 439778 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B799195 : Blo 439778 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B1192457 : Blo 439778 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B995849 : Blo 439778 995849 := bstep (se 2 (by rfl) ⟨373443, by rfl⟩ : syracuseStep 995849 = 746887) B746887
theorem B1487483 : Blo 439778 1487483 := bstep (se 1 (by rfl) ⟨1115612, by rfl⟩ : syracuseStep 1487483 = 2231225) B2231225
theorem B1487645 : Blo 439778 1487645 := bstep (se 3 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 1487645 = 557867) B557867
theorem B996191 : Blo 439778 996191 := bstep (se 1 (by rfl) ⟨747143, by rfl⟩ : syracuseStep 996191 = 1494287) B1494287
theorem B1684385 : Blo 439778 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B996371 : Blo 439778 996371 := bstep (se 1 (by rfl) ⟨747278, by rfl⟩ : syracuseStep 996371 = 1494557) B1494557
theorem B472187 : Blo 439778 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B38810765 : Blo 439778 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B10171595 : Blo 439778 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B3028261 : Blo 439778 3028261 := bstep (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) B567799
theorem B1193321 : Blo 439778 1193321 := bstep (se 2 (by rfl) ⟨447495, by rfl⟩ : syracuseStep 1193321 = 894991) B894991
theorem B996713 : Blo 439778 996713 := bstep (se 2 (by rfl) ⟨373767, by rfl⟩ : syracuseStep 996713 = 747535) B747535
theorem B2241917 : Blo 439778 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B1488347 : Blo 439778 1488347 := bstep (se 1 (by rfl) ⟨1116260, by rfl⟩ : syracuseStep 1488347 = 2232521) B2232521
theorem B439847 : Blo 439778 439847 := bstep (se 1 (by rfl) ⟨329885, by rfl⟩ : syracuseStep 439847 = 659771) B659771
theorem B439887 : Blo 439778 439887 := bstep (se 1 (by rfl) ⟨329915, by rfl⟩ : syracuseStep 439887 = 659831) B659831
theorem B439903 : Blo 439778 439903 := bstep (se 1 (by rfl) ⟨329927, by rfl⟩ : syracuseStep 439903 = 659855) B659855
theorem B439931 : Blo 439778 439931 := bstep (se 1 (by rfl) ⟨329948, by rfl⟩ : syracuseStep 439931 = 659897) B659897
theorem B439983 : Blo 439778 439983 := bstep (se 1 (by rfl) ⟨329987, by rfl⟩ : syracuseStep 439983 = 659975) B659975
theorem B440007 : Blo 439778 440007 := bstep (se 1 (by rfl) ⟨330005, by rfl⟩ : syracuseStep 440007 = 660011) B660011
theorem B440027 : Blo 439778 440027 := bstep (se 1 (by rfl) ⟨330020, by rfl⟩ : syracuseStep 440027 = 660041) B660041
theorem B440103 : Blo 439778 440103 := bstep (se 1 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 440103 = 660155) B660155
theorem B1881899 : Blo 439778 1881899 := bstep (se 1 (by rfl) ⟨1411424, by rfl⟩ : syracuseStep 1881899 = 2822849) B2822849
theorem B440143 : Blo 439778 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B440159 : Blo 439778 440159 := bstep (se 1 (by rfl) ⟨330119, by rfl⟩ : syracuseStep 440159 = 660239) B660239
theorem B440187 : Blo 439778 440187 := bstep (se 1 (by rfl) ⟨330140, by rfl⟩ : syracuseStep 440187 = 660281) B660281
theorem B440239 : Blo 439778 440239 := bstep (se 1 (by rfl) ⟨330179, by rfl⟩ : syracuseStep 440239 = 660359) B660359
theorem B997307 : Blo 439778 997307 := bstep (se 1 (by rfl) ⟨747980, by rfl⟩ : syracuseStep 997307 = 1495961) B1495961
theorem B440263 : Blo 439778 440263 := bstep (se 1 (by rfl) ⟨330197, by rfl⟩ : syracuseStep 440263 = 660395) B660395
theorem B440283 : Blo 439778 440283 := bstep (se 1 (by rfl) ⟨330212, by rfl⟩ : syracuseStep 440283 = 660425) B660425
theorem B1128455 : Blo 439778 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B440359 : Blo 439778 440359 := bstep (se 1 (by rfl) ⟨330269, by rfl⟩ : syracuseStep 440359 = 660539) B660539
theorem B997433 : Blo 439778 997433 := bstep (se 2 (by rfl) ⟨374037, by rfl⟩ : syracuseStep 997433 = 748075) B748075
theorem B440399 : Blo 439778 440399 := bstep (se 1 (by rfl) ⟨330299, by rfl⟩ : syracuseStep 440399 = 660599) B660599
theorem B440415 : Blo 439778 440415 := bstep (se 1 (by rfl) ⟨330311, by rfl⟩ : syracuseStep 440415 = 660623) B660623
theorem B440443 : Blo 439778 440443 := bstep (se 1 (by rfl) ⟨330332, by rfl⟩ : syracuseStep 440443 = 660665) B660665
theorem B1489049 : Blo 439778 1489049 := bstep (se 2 (by rfl) ⟨558393, by rfl⟩ : syracuseStep 1489049 = 1116787) B1116787
theorem B440495 : Blo 439778 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B440519 : Blo 439778 440519 := bstep (se 1 (by rfl) ⟨330389, by rfl⟩ : syracuseStep 440519 = 660779) B660779
theorem B440539 : Blo 439778 440539 := bstep (se 1 (by rfl) ⟨330404, by rfl⟩ : syracuseStep 440539 = 660809) B660809
theorem B440615 : Blo 439778 440615 := bstep (se 1 (by rfl) ⟨330461, by rfl⟩ : syracuseStep 440615 = 660923) B660923
theorem B3782963 : Blo 439778 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B440655 : Blo 439778 440655 := bstep (se 1 (by rfl) ⟨330491, by rfl⟩ : syracuseStep 440655 = 660983) B660983
theorem B440671 : Blo 439778 440671 := bstep (se 1 (by rfl) ⟨330503, by rfl⟩ : syracuseStep 440671 = 661007) B661007
theorem B440699 : Blo 439778 440699 := bstep (se 1 (by rfl) ⟨330524, by rfl⟩ : syracuseStep 440699 = 661049) B661049
theorem B997775 : Blo 439778 997775 := bstep (se 1 (by rfl) ⟨748331, by rfl⟩ : syracuseStep 997775 = 1496663) B1496663
theorem B5355929 : Blo 439778 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B440751 : Blo 439778 440751 := bstep (se 1 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 440751 = 661127) B661127
theorem B440775 : Blo 439778 440775 := bstep (se 1 (by rfl) ⟨330581, by rfl⟩ : syracuseStep 440775 = 661163) B661163
theorem B440795 : Blo 439778 440795 := bstep (se 1 (by rfl) ⟨330596, by rfl⟩ : syracuseStep 440795 = 661193) B661193
theorem B473563 : Blo 439778 473563 := bstep (se 1 (by rfl) ⟨355172, by rfl⟩ : syracuseStep 473563 = 710345) B710345
theorem B4012577 : Blo 439778 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B440871 : Blo 439778 440871 := bstep (se 1 (by rfl) ⟨330653, by rfl⟩ : syracuseStep 440871 = 661307) B661307
theorem B440911 : Blo 439778 440911 := bstep (se 1 (by rfl) ⟨330683, by rfl⟩ : syracuseStep 440911 = 661367) B661367
theorem B440927 : Blo 439778 440927 := bstep (se 1 (by rfl) ⟨330695, by rfl⟩ : syracuseStep 440927 = 661391) B661391
theorem B440955 : Blo 439778 440955 := bstep (se 1 (by rfl) ⟨330716, by rfl⟩ : syracuseStep 440955 = 661433) B661433
theorem B441007 : Blo 439778 441007 := bstep (se 1 (by rfl) ⟨330755, by rfl⟩ : syracuseStep 441007 = 661511) B661511
theorem B7518905 : Blo 439778 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B441031 : Blo 439778 441031 := bstep (se 1 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 441031 = 661547) B661547
theorem B998099 : Blo 439778 998099 := bstep (se 1 (by rfl) ⟨748574, by rfl⟩ : syracuseStep 998099 = 1497149) B1497149
theorem B441051 : Blo 439778 441051 := bstep (se 1 (by rfl) ⟨330788, by rfl⟩ : syracuseStep 441051 = 661577) B661577
theorem B441127 : Blo 439778 441127 := bstep (se 1 (by rfl) ⟨330845, by rfl⟩ : syracuseStep 441127 = 661691) B661691
theorem B441167 : Blo 439778 441167 := bstep (se 1 (by rfl) ⟨330875, by rfl⟩ : syracuseStep 441167 = 661751) B661751
theorem B441183 : Blo 439778 441183 := bstep (se 1 (by rfl) ⟨330887, by rfl⟩ : syracuseStep 441183 = 661775) B661775
theorem B1784695 : Blo 439778 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B441211 : Blo 439778 441211 := bstep (se 1 (by rfl) ⟨330908, by rfl⟩ : syracuseStep 441211 = 661817) B661817
theorem B441263 : Blo 439778 441263 := bstep (se 1 (by rfl) ⟨330947, by rfl⟩ : syracuseStep 441263 = 661895) B661895
theorem B441287 : Blo 439778 441287 := bstep (se 1 (by rfl) ⟨330965, by rfl⟩ : syracuseStep 441287 = 661931) B661931
theorem B441307 : Blo 439778 441307 := bstep (se 1 (by rfl) ⟨330980, by rfl⟩ : syracuseStep 441307 = 661961) B661961
theorem B441383 : Blo 439778 441383 := bstep (se 1 (by rfl) ⟨331037, by rfl⟩ : syracuseStep 441383 = 662075) B662075
theorem B441423 : Blo 439778 441423 := bstep (se 1 (by rfl) ⟨331067, by rfl⟩ : syracuseStep 441423 = 662135) B662135
theorem B1260623 : Blo 439778 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B441439 : Blo 439778 441439 := bstep (se 1 (by rfl) ⟨331079, by rfl⟩ : syracuseStep 441439 = 662159) B662159
theorem B441467 : Blo 439778 441467 := bstep (se 1 (by rfl) ⟨331100, by rfl⟩ : syracuseStep 441467 = 662201) B662201
theorem B441519 : Blo 439778 441519 := bstep (se 1 (by rfl) ⟨331139, by rfl⟩ : syracuseStep 441519 = 662279) B662279
theorem B441543 : Blo 439778 441543 := bstep (se 1 (by rfl) ⟨331157, by rfl⟩ : syracuseStep 441543 = 662315) B662315
theorem B441563 : Blo 439778 441563 := bstep (se 1 (by rfl) ⟨331172, by rfl⟩ : syracuseStep 441563 = 662345) B662345
theorem B2276599 : Blo 439778 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B441639 : Blo 439778 441639 := bstep (se 1 (by rfl) ⟨331229, by rfl⟩ : syracuseStep 441639 = 662459) B662459
theorem B1490237 : Blo 439778 1490237 := bstep (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) B558839
theorem B441679 : Blo 439778 441679 := bstep (se 1 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 441679 = 662519) B662519
theorem B441695 : Blo 439778 441695 := bstep (se 1 (by rfl) ⟨331271, by rfl⟩ : syracuseStep 441695 = 662543) B662543
theorem B441723 : Blo 439778 441723 := bstep (se 1 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 441723 = 662585) B662585
theorem B2014607 : Blo 439778 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B1064335 : Blo 439778 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B441775 : Blo 439778 441775 := bstep (se 1 (by rfl) ⟨331331, by rfl⟩ : syracuseStep 441775 = 662663) B662663
theorem B441799 : Blo 439778 441799 := bstep (se 1 (by rfl) ⟨331349, by rfl⟩ : syracuseStep 441799 = 662699) B662699
theorem B441819 : Blo 439778 441819 := bstep (se 1 (by rfl) ⟨331364, by rfl⟩ : syracuseStep 441819 = 662729) B662729
theorem B441895 : Blo 439778 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B441935 : Blo 439778 441935 := bstep (se 1 (by rfl) ⟨331451, by rfl⟩ : syracuseStep 441935 = 662903) B662903
theorem B441951 : Blo 439778 441951 := bstep (se 1 (by rfl) ⟨331463, by rfl⟩ : syracuseStep 441951 = 662927) B662927
theorem B441979 : Blo 439778 441979 := bstep (se 1 (by rfl) ⟨331484, by rfl⟩ : syracuseStep 441979 = 662969) B662969
theorem B442031 : Blo 439778 442031 := bstep (se 1 (by rfl) ⟨331523, by rfl⟩ : syracuseStep 442031 = 663047) B663047
theorem B442055 : Blo 439778 442055 := bstep (se 1 (by rfl) ⟨331541, by rfl⟩ : syracuseStep 442055 = 663083) B663083
theorem B1195735 : Blo 439778 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B442075 : Blo 439778 442075 := bstep (se 1 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 442075 = 663113) B663113
theorem B1883897 : Blo 439778 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B442151 : Blo 439778 442151 := bstep (se 1 (by rfl) ⟨331613, by rfl⟩ : syracuseStep 442151 = 663227) B663227
theorem B442191 : Blo 439778 442191 := bstep (se 1 (by rfl) ⟨331643, by rfl⟩ : syracuseStep 442191 = 663287) B663287
theorem B1883999 : Blo 439778 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B442207 : Blo 439778 442207 := bstep (se 1 (by rfl) ⟨331655, by rfl⟩ : syracuseStep 442207 = 663311) B663311
theorem B442235 : Blo 439778 442235 := bstep (se 1 (by rfl) ⟨331676, by rfl⟩ : syracuseStep 442235 = 663353) B663353
theorem B442287 : Blo 439778 442287 := bstep (se 1 (by rfl) ⟨331715, by rfl⟩ : syracuseStep 442287 = 663431) B663431
theorem B442311 : Blo 439778 442311 := bstep (se 1 (by rfl) ⟨331733, by rfl⟩ : syracuseStep 442311 = 663467) B663467
theorem B442331 : Blo 439778 442331 := bstep (se 1 (by rfl) ⟨331748, by rfl⟩ : syracuseStep 442331 = 663497) B663497
theorem B1589249 : Blo 439778 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B442407 : Blo 439778 442407 := bstep (se 1 (by rfl) ⟨331805, by rfl⟩ : syracuseStep 442407 = 663611) B663611
theorem B442447 : Blo 439778 442447 := bstep (se 1 (by rfl) ⟨331835, by rfl⟩ : syracuseStep 442447 = 663671) B663671
theorem B442463 : Blo 439778 442463 := bstep (se 1 (by rfl) ⟨331847, by rfl⟩ : syracuseStep 442463 = 663695) B663695
theorem B442491 : Blo 439778 442491 := bstep (se 1 (by rfl) ⟨331868, by rfl⟩ : syracuseStep 442491 = 663737) B663737
theorem B1491101 : Blo 439778 1491101 := bstep (se 3 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 1491101 = 559163) B559163
theorem B442543 : Blo 439778 442543 := bstep (se 1 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 442543 = 663815) B663815
theorem B442567 : Blo 439778 442567 := bstep (se 1 (by rfl) ⟨331925, by rfl⟩ : syracuseStep 442567 = 663851) B663851
theorem B442587 : Blo 439778 442587 := bstep (se 1 (by rfl) ⟨331940, by rfl⟩ : syracuseStep 442587 = 663881) B663881
theorem B442663 : Blo 439778 442663 := bstep (se 1 (by rfl) ⟨331997, by rfl⟩ : syracuseStep 442663 = 663995) B663995
theorem B835913 : Blo 439778 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B442703 : Blo 439778 442703 := bstep (se 1 (by rfl) ⟨332027, by rfl⟩ : syracuseStep 442703 = 664055) B664055
theorem B442719 : Blo 439778 442719 := bstep (se 1 (by rfl) ⟨332039, by rfl⟩ : syracuseStep 442719 = 664079) B664079
theorem B442747 : Blo 439778 442747 := bstep (se 1 (by rfl) ⟨332060, by rfl⟩ : syracuseStep 442747 = 664121) B664121
theorem B442799 : Blo 439778 442799 := bstep (se 1 (by rfl) ⟨332099, by rfl⟩ : syracuseStep 442799 = 664199) B664199
theorem B639415 : Blo 439778 639415 := bstep (se 1 (by rfl) ⟨479561, by rfl⟩ : syracuseStep 639415 = 959123) B959123
theorem B442823 : Blo 439778 442823 := bstep (se 1 (by rfl) ⟨332117, by rfl⟩ : syracuseStep 442823 = 664235) B664235
theorem B442843 : Blo 439778 442843 := bstep (se 1 (by rfl) ⟨332132, by rfl⟩ : syracuseStep 442843 = 664265) B664265
theorem B1786349 : Blo 439778 1786349 := bstep (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) B669881
theorem B1262105 : Blo 439778 1262105 := bstep (se 2 (by rfl) ⟨473289, by rfl⟩ : syracuseStep 1262105 = 946579) B946579
theorem B442919 : Blo 439778 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B442959 : Blo 439778 442959 := bstep (se 1 (by rfl) ⟨332219, by rfl⟩ : syracuseStep 442959 = 664439) B664439
theorem B442975 : Blo 439778 442975 := bstep (se 1 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 442975 = 664463) B664463
theorem B443003 : Blo 439778 443003 := bstep (se 1 (by rfl) ⟨332252, by rfl⟩ : syracuseStep 443003 = 664505) B664505
theorem B443055 : Blo 439778 443055 := bstep (se 1 (by rfl) ⟨332291, by rfl⟩ : syracuseStep 443055 = 664583) B664583
theorem B1491641 : Blo 439778 1491641 := bstep (se 2 (by rfl) ⟨559365, by rfl⟩ : syracuseStep 1491641 = 1118731) B1118731
theorem B443079 : Blo 439778 443079 := bstep (se 1 (by rfl) ⟨332309, by rfl⟩ : syracuseStep 443079 = 664619) B664619
theorem B443099 : Blo 439778 443099 := bstep (se 1 (by rfl) ⟨332324, by rfl⟩ : syracuseStep 443099 = 664649) B664649
theorem B836345 : Blo 439778 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B443175 : Blo 439778 443175 := bstep (se 1 (by rfl) ⟨332381, by rfl⟩ : syracuseStep 443175 = 664763) B664763
theorem B705353 : Blo 439778 705353 := bstep (se 2 (by rfl) ⟨264507, by rfl⟩ : syracuseStep 705353 = 529015) B529015
theorem B443215 : Blo 439778 443215 := bstep (se 1 (by rfl) ⟨332411, by rfl⟩ : syracuseStep 443215 = 664823) B664823
theorem B443231 : Blo 439778 443231 := bstep (se 1 (by rfl) ⟨332423, by rfl⟩ : syracuseStep 443231 = 664847) B664847
theorem B705385 : Blo 439778 705385 := bstep (se 2 (by rfl) ⟨264519, by rfl⟩ : syracuseStep 705385 = 529039) B529039
theorem B1131371 : Blo 439778 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B443259 : Blo 439778 443259 := bstep (se 1 (by rfl) ⟨332444, by rfl⟩ : syracuseStep 443259 = 664889) B664889
theorem B443311 : Blo 439778 443311 := bstep (se 1 (by rfl) ⟨332483, by rfl⟩ : syracuseStep 443311 = 664967) B664967
theorem B443335 : Blo 439778 443335 := bstep (se 1 (by rfl) ⟨332501, by rfl⟩ : syracuseStep 443335 = 665003) B665003
theorem B443355 : Blo 439778 443355 := bstep (se 1 (by rfl) ⟨332516, by rfl⟩ : syracuseStep 443355 = 665033) B665033
theorem B3359717 : Blo 439778 3359717 := bstep (se 4 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 3359717 = 629947) B629947
theorem B2114579 : Blo 439778 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B443431 : Blo 439778 443431 := bstep (se 1 (by rfl) ⟨332573, by rfl⟩ : syracuseStep 443431 = 665147) B665147
theorem B443471 : Blo 439778 443471 := bstep (se 1 (by rfl) ⟨332603, by rfl⟩ : syracuseStep 443471 = 665207) B665207
theorem B443487 : Blo 439778 443487 := bstep (se 1 (by rfl) ⟨332615, by rfl⟩ : syracuseStep 443487 = 665231) B665231
theorem B443515 : Blo 439778 443515 := bstep (se 1 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 443515 = 665273) B665273
theorem B443567 : Blo 439778 443567 := bstep (se 1 (by rfl) ⟨332675, by rfl⟩ : syracuseStep 443567 = 665351) B665351
theorem B443591 : Blo 439778 443591 := bstep (se 1 (by rfl) ⟨332693, by rfl⟩ : syracuseStep 443591 = 665387) B665387
theorem B443611 : Blo 439778 443611 := bstep (se 1 (by rfl) ⟨332708, by rfl⟩ : syracuseStep 443611 = 665417) B665417
theorem B1492235 : Blo 439778 1492235 := bstep (se 1 (by rfl) ⟨1119176, by rfl⟩ : syracuseStep 1492235 = 2238353) B2238353
theorem B443687 : Blo 439778 443687 := bstep (se 1 (by rfl) ⟨332765, by rfl⟩ : syracuseStep 443687 = 665531) B665531
theorem B443727 : Blo 439778 443727 := bstep (se 1 (by rfl) ⟨332795, by rfl⟩ : syracuseStep 443727 = 665591) B665591
theorem B443743 : Blo 439778 443743 := bstep (se 1 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 443743 = 665615) B665615
theorem B443771 : Blo 439778 443771 := bstep (se 1 (by rfl) ⟨332828, by rfl⟩ : syracuseStep 443771 = 665657) B665657
theorem B1492505 : Blo 439778 1492505 := bstep (se 2 (by rfl) ⟨559689, by rfl⟩ : syracuseStep 1492505 = 1119379) B1119379
theorem B2246291 : Blo 439778 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B706295 : Blo 439778 706295 := bstep (se 1 (by rfl) ⟨529721, by rfl⟩ : syracuseStep 706295 = 1059443) B1059443
theorem B673915 : Blo 439778 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B837803 : Blo 439778 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B1362091 : Blo 439778 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B1788425 : Blo 439778 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B838183 : Blo 439778 838183 := bstep (se 1 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 838183 = 1257275) B1257275
theorem B1788539 : Blo 439778 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B1591931 : Blo 439778 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B1493639 : Blo 439778 1493639 := bstep (se 1 (by rfl) ⟨1120229, by rfl⟩ : syracuseStep 1493639 = 2240459) B2240459
theorem B1493693 : Blo 439778 1493693 := bstep (se 3 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 1493693 = 560135) B560135
theorem B838343 : Blo 439778 838343 := bstep (se 1 (by rfl) ⟨628757, by rfl⟩ : syracuseStep 838343 = 1257515) B1257515
theorem B1493855 : Blo 439778 1493855 := bstep (se 1 (by rfl) ⟨1120391, by rfl⟩ : syracuseStep 1493855 = 2240783) B2240783
theorem B5393297 : Blo 439778 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B1494017 : Blo 439778 1494017 := bstep (se 2 (by rfl) ⟨560256, by rfl⟩ : syracuseStep 1494017 = 1120513) B1120513
theorem B4246607 : Blo 439778 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B707935 : Blo 439778 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B445915 : Blo 439778 445915 := bstep (se 1 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 445915 = 668873) B668873
theorem B1134119 : Blo 439778 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B3395195 : Blo 439778 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B2510585 : Blo 439778 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B1494827 : Blo 439778 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B839497 : Blo 439778 839497 := bstep (se 2 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 839497 = 629623) B629623
theorem B1888271 : Blo 439778 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B1495097 : Blo 439778 1495097 := bstep (se 2 (by rfl) ⟨560661, by rfl⟩ : syracuseStep 1495097 = 1121323) B1121323
theorem B1495421 : Blo 439778 1495421 := bstep (se 3 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 1495421 = 560783) B560783
theorem B1495691 : Blo 439778 1495691 := bstep (se 1 (by rfl) ⟨1121768, by rfl⟩ : syracuseStep 1495691 = 2243537) B2243537
theorem B742135 : Blo 439778 742135 := bstep (se 1 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 742135 = 1113203) B1113203
theorem B742331 : Blo 439778 742331 := bstep (se 1 (by rfl) ⟨556748, by rfl⟩ : syracuseStep 742331 = 1113497) B1113497
theorem B742439 : Blo 439778 742439 := bstep (se 1 (by rfl) ⟨556829, by rfl⟩ : syracuseStep 742439 = 1113659) B1113659
theorem B2512043 : Blo 439778 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B742729 : Blo 439778 742729 := bstep (se 2 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 742729 = 557047) B557047
theorem B742763 : Blo 439778 742763 := bstep (se 1 (by rfl) ⟨557072, by rfl⟩ : syracuseStep 742763 = 1114145) B1114145
theorem B710075 : Blo 439778 710075 := bstep (se 1 (by rfl) ⟨532556, by rfl⟩ : syracuseStep 710075 = 1065113) B1065113
theorem B1594889 : Blo 439778 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B1496609 : Blo 439778 1496609 := bstep (se 2 (by rfl) ⟨561228, by rfl⟩ : syracuseStep 1496609 = 1122457) B1122457
theorem B743161 : Blo 439778 743161 := bstep (se 2 (by rfl) ⟨278685, by rfl⟩ : syracuseStep 743161 = 557371) B557371
theorem B1496825 : Blo 439778 1496825 := bstep (se 2 (by rfl) ⟨561309, by rfl⟩ : syracuseStep 1496825 = 1122619) B1122619
theorem B841691 : Blo 439778 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B743431 : Blo 439778 743431 := bstep (se 1 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 743431 = 1115147) B1115147
theorem B1497095 : Blo 439778 1497095 := bstep (se 1 (by rfl) ⟨1122821, by rfl⟩ : syracuseStep 1497095 = 2245643) B2245643
theorem B2119769 : Blo 439778 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B4773977 : Blo 439778 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B1497203 : Blo 439778 1497203 := bstep (se 1 (by rfl) ⟨1122902, by rfl⟩ : syracuseStep 1497203 = 2245805) B2245805
theorem B841927 : Blo 439778 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1890647 : Blo 439778 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B1497473 : Blo 439778 1497473 := bstep (se 2 (by rfl) ⟨561552, by rfl⟩ : syracuseStep 1497473 = 1123105) B1123105
theorem B743863 : Blo 439778 743863 := bstep (se 1 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 743863 = 1115795) B1115795
theorem B907795 : Blo 439778 907795 := bstep (se 1 (by rfl) ⟨680846, by rfl⟩ : syracuseStep 907795 = 1361693) B1361693
theorem B744059 : Blo 439778 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B3365549 : Blo 439778 3365549 := bstep (se 3 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 3365549 = 1262081) B1262081
theorem B1596343 : Blo 439778 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B744457 : Blo 439778 744457 := bstep (se 2 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 744457 = 558343) B558343
theorem B744619 : Blo 439778 744619 := bstep (se 1 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 744619 = 1116929) B1116929
theorem B449831 : Blo 439778 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B2186621 : Blo 439778 2186621 := bstep (se 3 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 2186621 = 819983) B819983
theorem B744923 : Blo 439778 744923 := bstep (se 1 (by rfl) ⟨558692, by rfl⟩ : syracuseStep 744923 = 1117385) B1117385
theorem B745159 : Blo 439778 745159 := bstep (se 1 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 745159 = 1117739) B1117739
theorem B745321 : Blo 439778 745321 := bstep (se 2 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 745321 = 558991) B558991
theorem B2842553 : Blo 439778 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B2514959 : Blo 439778 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B4317299 : Blo 439778 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B2515211 : Blo 439778 2515211 := bstep (se 1 (by rfl) ⟨1886408, by rfl⟩ : syracuseStep 2515211 = 3772817) B3772817
theorem B745915 : Blo 439778 745915 := bstep (se 1 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 745915 = 1118873) B1118873
theorem B746023 : Blo 439778 746023 := bstep (se 1 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 746023 = 1119035) B1119035
theorem B746347 : Blo 439778 746347 := bstep (se 1 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 746347 = 1119521) B1119521
theorem B1696621 : Blo 439778 1696621 := bstep (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) B636233
theorem B1893395 : Blo 439778 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B3367979 : Blo 439778 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B12248113 : Blo 439778 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B1598579 : Blo 439778 1598579 := bstep (se 1 (by rfl) ⟨1198934, by rfl⟩ : syracuseStep 1598579 = 2397869) B2397869
theorem B4253147 : Blo 439778 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B2516669 : Blo 439778 2516669 := bstep (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) B943751
theorem B7268131 : Blo 439778 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B747407 : Blo 439778 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B2385935 : Blo 439778 2385935 := bstep (se 1 (by rfl) ⟨1789451, by rfl⟩ : syracuseStep 2385935 = 3578903) B3578903
theorem B747643 : Blo 439778 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B715115 : Blo 439778 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B1796633 : Blo 439778 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B9562657 : Blo 439778 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B748507 : Blo 439778 748507 := bstep (se 1 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 748507 = 1122761) B1122761
theorem B97643981 : Blo 439778 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B1338889 : Blo 439778 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B2125457 : Blo 439778 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1797881 : Blo 439778 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B2126209 : Blo 439778 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B2519585 : Blo 439778 2519585 := bstep (se 2 (by rfl) ⟨944844, by rfl⟩ : syracuseStep 2519585 = 1889689) B1889689
theorem B946937 : Blo 439778 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B6911041 : Blo 439778 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B2880715 : Blo 439778 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B2618825 : Blo 439778 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2520791 : Blo 439778 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B10385189 : Blo 439778 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B1113335 : Blo 439778 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B6782297 : Blo 439778 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B556895 : Blo 439778 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B2818259 : Blo 439778 2818259 := bstep (se 1 (by rfl) ⟨2113694, by rfl⟩ : syracuseStep 2818259 = 4227389) B4227389
theorem B557275 : Blo 439778 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B754247 : Blo 439778 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B852553 : Blo 439778 852553 := bstep (se 2 (by rfl) ⟨319707, by rfl⟩ : syracuseStep 852553 = 639415) B639415
theorem B1409719 : Blo 439778 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B4260755 : Blo 439778 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B1115279 : Blo 439778 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B2262161 : Blo 439778 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B5047595 : Blo 439778 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B2229767 : Blo 439778 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B558895 : Blo 439778 558895 := bstep (se 1 (by rfl) ⟨419171, by rfl⟩ : syracuseStep 558895 = 838343) B838343
theorem B2230253 : Blo 439778 2230253 := bstep (se 3 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 2230253 = 836345) B836345
theorem B2525165 : Blo 439778 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B2263463 : Blo 439778 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B2230739 : Blo 439778 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B1673723 : Blo 439778 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B5049053 : Blo 439778 5049053 := bstep (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) B1893395
theorem B2231063 : Blo 439778 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B1117223 : Blo 439778 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B494887 : Blo 439778 494887 := bstep (se 1 (by rfl) ⟨371165, by rfl⟩ : syracuseStep 494887 = 742331) B742331
theorem B17272129 : Blo 439778 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B494959 : Blo 439778 494959 := bstep (se 1 (by rfl) ⟨371219, by rfl⟩ : syracuseStep 494959 = 742439) B742439
theorem B12750209 : Blo 439778 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B1117577 : Blo 439778 1117577 := bstep (se 2 (by rfl) ⟨419091, by rfl⟩ : syracuseStep 1117577 = 838183) B838183
theorem B1674695 : Blo 439778 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B7179785 : Blo 439778 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B495175 : Blo 439778 495175 := bstep (se 1 (by rfl) ⟨371381, by rfl⟩ : syracuseStep 495175 = 742763) B742763
theorem B6983533 : Blo 439778 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B1413179 : Blo 439778 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B3182651 : Blo 439778 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B2232683 : Blo 439778 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B659879 : Blo 439778 659879 := bstep (se 1 (by rfl) ⟨494909, by rfl⟩ : syracuseStep 659879 = 989819) B989819
theorem B496039 : Blo 439778 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B659963 : Blo 439778 659963 := bstep (se 1 (by rfl) ⟨494972, by rfl⟩ : syracuseStep 659963 = 989945) B989945
theorem B594553 : Blo 439778 594553 := bstep (se 2 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 594553 = 445915) B445915
theorem B660089 : Blo 439778 660089 := bstep (se 2 (by rfl) ⟨247533, by rfl⟩ : syracuseStep 660089 = 495067) B495067
theorem B14389913 : Blo 439778 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B660143 : Blo 439778 660143 := bstep (se 1 (by rfl) ⟨495107, by rfl⟩ : syracuseStep 660143 = 990215) B990215
theorem B660191 : Blo 439778 660191 := bstep (se 1 (by rfl) ⟨495143, by rfl⟩ : syracuseStep 660191 = 990287) B990287
theorem B1119055 : Blo 439778 1119055 := bstep (se 1 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 1119055 = 1678583) B1678583
theorem B8491985 : Blo 439778 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B660455 : Blo 439778 660455 := bstep (se 1 (by rfl) ⟨495341, by rfl⟩ : syracuseStep 660455 = 990683) B990683
theorem B496615 : Blo 439778 496615 := bstep (se 1 (by rfl) ⟨372461, by rfl⟩ : syracuseStep 496615 = 744923) B744923
theorem B1119329 : Blo 439778 1119329 := bstep (se 2 (by rfl) ⟨419748, by rfl⟩ : syracuseStep 1119329 = 839497) B839497
theorem B660713 : Blo 439778 660713 := bstep (se 2 (by rfl) ⟨247767, by rfl⟩ : syracuseStep 660713 = 495535) B495535
theorem B660767 : Blo 439778 660767 := bstep (se 1 (by rfl) ⟨495575, by rfl⟩ : syracuseStep 660767 = 991151) B991151
theorem B1676639 : Blo 439778 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B660935 : Blo 439778 660935 := bstep (se 1 (by rfl) ⟨495701, by rfl⟩ : syracuseStep 660935 = 991403) B991403
theorem B4855243 : Blo 439778 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B1119703 : Blo 439778 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B1676807 : Blo 439778 1676807 := bstep (se 1 (by rfl) ⟨1257605, by rfl⟩ : syracuseStep 1676807 = 2515211) B2515211
theorem B1120007 : Blo 439778 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B2234141 : Blo 439778 2234141 := bstep (se 3 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 2234141 = 837803) B837803
theorem B661289 : Blo 439778 661289 := bstep (se 2 (by rfl) ⟨247983, by rfl⟩ : syracuseStep 661289 = 495967) B495967
theorem B661295 : Blo 439778 661295 := bstep (se 1 (by rfl) ⟨495971, by rfl⟩ : syracuseStep 661295 = 991943) B991943
theorem B1677293 : Blo 439778 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B661769 : Blo 439778 661769 := bstep (se 2 (by rfl) ⟨248163, by rfl⟩ : syracuseStep 661769 = 496327) B496327
theorem B1906973 : Blo 439778 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B989513 : Blo 439778 989513 := bstep (se 2 (by rfl) ⟨371067, by rfl⟩ : syracuseStep 989513 = 742135) B742135
theorem B989531 : Blo 439778 989531 := bstep (se 1 (by rfl) ⟨742148, by rfl⟩ : syracuseStep 989531 = 1484297) B1484297
theorem B661871 : Blo 439778 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B1677779 : Blo 439778 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B1120787 : Blo 439778 1120787 := bstep (se 1 (by rfl) ⟨840590, by rfl⟩ : syracuseStep 1120787 = 1681181) B1681181
theorem B662087 : Blo 439778 662087 := bstep (se 1 (by rfl) ⟨496565, by rfl⟩ : syracuseStep 662087 = 993131) B993131
theorem B596575 : Blo 439778 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B498271 : Blo 439778 498271 := bstep (se 1 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 498271 = 747407) B747407
theorem B662123 : Blo 439778 662123 := bstep (se 1 (by rfl) ⟨496592, by rfl⟩ : syracuseStep 662123 = 993185) B993185
theorem B9214721 : Blo 439778 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B662351 : Blo 439778 662351 := bstep (se 1 (by rfl) ⟨496763, by rfl⟩ : syracuseStep 662351 = 993527) B993527
theorem B990107 : Blo 439778 990107 := bstep (se 1 (by rfl) ⟨742580, by rfl⟩ : syracuseStep 990107 = 1485161) B1485161
theorem B3840953 : Blo 439778 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B4037681 : Blo 439778 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B990305 : Blo 439778 990305 := bstep (se 2 (by rfl) ⟨371364, by rfl⟩ : syracuseStep 990305 = 742729) B742729
theorem B662747 : Blo 439778 662747 := bstep (se 1 (by rfl) ⟨497060, by rfl⟩ : syracuseStep 662747 = 994121) B994121
theorem B990503 : Blo 439778 990503 := bstep (se 1 (by rfl) ⟨742877, by rfl⟩ : syracuseStep 990503 = 1485755) B1485755
theorem B662921 : Blo 439778 662921 := bstep (se 2 (by rfl) ⟨248595, by rfl⟩ : syracuseStep 662921 = 497191) B497191
theorem B12688973 : Blo 439778 12688973 := bstep (se 3 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 12688973 = 4758365) B4758365
theorem B990881 : Blo 439778 990881 := bstep (se 2 (by rfl) ⟨371580, by rfl⟩ : syracuseStep 990881 = 743161) B743161
theorem B663275 : Blo 439778 663275 := bstep (se 1 (by rfl) ⟨497456, by rfl⟩ : syracuseStep 663275 = 994913) B994913
theorem B1416971 : Blo 439778 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B663503 : Blo 439778 663503 := bstep (se 1 (by rfl) ⟨497627, by rfl⟩ : syracuseStep 663503 = 995255) B995255
theorem B991241 : Blo 439778 991241 := bstep (se 2 (by rfl) ⟨371715, by rfl⟩ : syracuseStep 991241 = 743431) B743431
theorem B1122569 : Blo 439778 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B7545149 : Blo 439778 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B794971 : Blo 439778 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B663899 : Blo 439778 663899 := bstep (se 1 (by rfl) ⟨497924, by rfl⟩ : syracuseStep 663899 = 995849) B995849
theorem B1679723 : Blo 439778 1679723 := bstep (se 1 (by rfl) ⟨1259792, by rfl⟩ : syracuseStep 1679723 = 2519585) B2519585
theorem B991655 : Blo 439778 991655 := bstep (se 1 (by rfl) ⟨743741, by rfl⟩ : syracuseStep 991655 = 1487483) B1487483
theorem B2368001 : Blo 439778 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B991763 : Blo 439778 991763 := bstep (se 1 (by rfl) ⟨743822, by rfl⟩ : syracuseStep 991763 = 1487645) B1487645
theorem B664127 : Blo 439778 664127 := bstep (se 1 (by rfl) ⟨498095, by rfl⟩ : syracuseStep 664127 = 996191) B996191
theorem B991817 : Blo 439778 991817 := bstep (se 2 (by rfl) ⟨371931, by rfl⟩ : syracuseStep 991817 = 743863) B743863
theorem B1122923 : Blo 439778 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B631417 : Blo 439778 631417 := bstep (se 2 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 631417 = 473563) B473563
theorem B664247 : Blo 439778 664247 := bstep (se 1 (by rfl) ⟨498185, by rfl⟩ : syracuseStep 664247 = 996371) B996371
theorem B795547 : Blo 439778 795547 := bstep (se 1 (by rfl) ⟨596660, by rfl⟩ : syracuseStep 795547 = 1193321) B1193321
theorem B664475 : Blo 439778 664475 := bstep (se 1 (by rfl) ⟨498356, by rfl⟩ : syracuseStep 664475 = 996713) B996713
theorem B992231 : Blo 439778 992231 := bstep (se 1 (by rfl) ⟨744173, by rfl⟩ : syracuseStep 992231 = 1488347) B1488347
theorem B1680527 : Blo 439778 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B6923459 : Blo 439778 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B1254599 : Blo 439778 1254599 := bstep (se 1 (by rfl) ⟨940949, by rfl⟩ : syracuseStep 1254599 = 1881899) B1881899
theorem B664871 : Blo 439778 664871 := bstep (se 1 (by rfl) ⟨498653, by rfl⟩ : syracuseStep 664871 = 997307) B997307
theorem B992609 : Blo 439778 992609 := bstep (se 2 (by rfl) ⟨372228, by rfl⟩ : syracuseStep 992609 = 744457) B744457
theorem B664955 : Blo 439778 664955 := bstep (se 1 (by rfl) ⟨498716, by rfl⟩ : syracuseStep 664955 = 997433) B997433
theorem B992699 : Blo 439778 992699 := bstep (se 1 (by rfl) ⟨744524, by rfl⟩ : syracuseStep 992699 = 1489049) B1489049
theorem B3024317 : Blo 439778 3024317 := bstep (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) B1134119
theorem B665081 : Blo 439778 665081 := bstep (se 2 (by rfl) ⟨249405, by rfl⟩ : syracuseStep 665081 = 498811) B498811
theorem B992825 : Blo 439778 992825 := bstep (se 2 (by rfl) ⟨372309, by rfl⟩ : syracuseStep 992825 = 744619) B744619
theorem B665183 : Blo 439778 665183 := bstep (se 1 (by rfl) ⟨498887, by rfl⟩ : syracuseStep 665183 = 997775) B997775
theorem B665399 : Blo 439778 665399 := bstep (se 1 (by rfl) ⟨499049, by rfl⟩ : syracuseStep 665399 = 998099) B998099
theorem B1419113 : Blo 439778 1419113 := bstep (se 2 (by rfl) ⟨532167, by rfl⟩ : syracuseStep 1419113 = 1064335) B1064335
theorem B4794349 : Blo 439778 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B993491 : Blo 439778 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B1485053 : Blo 439778 1485053 := bstep (se 3 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 1485053 = 556895) B556895
theorem B993545 : Blo 439778 993545 := bstep (se 2 (by rfl) ⟨372579, by rfl⟩ : syracuseStep 993545 = 745159) B745159
theorem B993761 : Blo 439778 993761 := bstep (se 2 (by rfl) ⟨372660, by rfl⟩ : syracuseStep 993761 = 745321) B745321
theorem B7580141 : Blo 439778 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B1255931 : Blo 439778 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B1255999 : Blo 439778 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B1059499 : Blo 439778 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B1682167 : Blo 439778 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B994067 : Blo 439778 994067 := bstep (se 1 (by rfl) ⟨745550, by rfl⟩ : syracuseStep 994067 = 1491101) B1491101
theorem B1190899 : Blo 439778 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B1485863 : Blo 439778 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B1682471 : Blo 439778 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B3320947 : Blo 439778 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B994427 : Blo 439778 994427 := bstep (se 1 (by rfl) ⟨745820, by rfl⟩ : syracuseStep 994427 = 1491641) B1491641
theorem B994553 : Blo 439778 994553 := bstep (se 2 (by rfl) ⟨372957, by rfl⟩ : syracuseStep 994553 = 745915) B745915
theorem B2239811 : Blo 439778 2239811 := bstep (se 1 (by rfl) ⟨1679858, by rfl⟩ : syracuseStep 2239811 = 3359717) B3359717
theorem B994697 : Blo 439778 994697 := bstep (se 2 (by rfl) ⟨373011, by rfl⟩ : syracuseStep 994697 = 746023) B746023
theorem B1486295 : Blo 439778 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B994823 : Blo 439778 994823 := bstep (se 1 (by rfl) ⟨746117, by rfl⟩ : syracuseStep 994823 = 1492235) B1492235
theorem B995003 : Blo 439778 995003 := bstep (se 1 (by rfl) ⟨746252, by rfl⟩ : syracuseStep 995003 = 1492505) B1492505
theorem B2240297 : Blo 439778 2240297 := bstep (se 2 (by rfl) ⟨840111, by rfl⟩ : syracuseStep 2240297 = 1680223) B1680223
theorem B995129 : Blo 439778 995129 := bstep (se 2 (by rfl) ⟨373173, by rfl⟩ : syracuseStep 995129 = 746347) B746347
theorem B470863 : Blo 439778 470863 := bstep (se 1 (by rfl) ⟨353147, by rfl⟩ : syracuseStep 470863 = 706295) B706295
theorem B3026945 : Blo 439778 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B16330817 : Blo 439778 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1880273 : Blo 439778 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1192283 : Blo 439778 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B995759 : Blo 439778 995759 := bstep (se 1 (by rfl) ⟨746819, by rfl⟩ : syracuseStep 995759 = 1493639) B1493639
theorem B995795 : Blo 439778 995795 := bstep (se 1 (by rfl) ⟨746846, by rfl⟩ : syracuseStep 995795 = 1493693) B1493693
theorem B1061345 : Blo 439778 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B995903 : Blo 439778 995903 := bstep (se 1 (by rfl) ⟨746927, by rfl⟩ : syracuseStep 995903 = 1493855) B1493855
theorem B996011 : Blo 439778 996011 := bstep (se 1 (by rfl) ⟨747008, by rfl⟩ : syracuseStep 996011 = 1494017) B1494017
theorem B1880941 : Blo 439778 1880941 := bstep (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) B705353
theorem B2241593 : Blo 439778 2241593 := bstep (se 2 (by rfl) ⟨840597, by rfl⟩ : syracuseStep 2241593 = 1681195) B1681195
theorem B1487969 : Blo 439778 1487969 := bstep (se 2 (by rfl) ⟨557988, by rfl⟩ : syracuseStep 1487969 = 1115977) B1115977
theorem B996551 : Blo 439778 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B1586425 : Blo 439778 1586425 := bstep (se 2 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 1586425 = 1189819) B1189819
theorem B1258847 : Blo 439778 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B996731 : Blo 439778 996731 := bstep (se 1 (by rfl) ⟨747548, by rfl⟩ : syracuseStep 996731 = 1495097) B1495097
theorem B996857 : Blo 439778 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B898553 : Blo 439778 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B439803 : Blo 439778 439803 := bstep (se 1 (by rfl) ⟨329852, by rfl⟩ : syracuseStep 439803 = 659705) B659705
theorem B1816121 : Blo 439778 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B439871 : Blo 439778 439871 := bstep (se 1 (by rfl) ⟨329903, by rfl⟩ : syracuseStep 439871 = 659807) B659807
theorem B439879 : Blo 439778 439879 := bstep (se 1 (by rfl) ⟨329909, by rfl⟩ : syracuseStep 439879 = 659819) B659819
theorem B996947 : Blo 439778 996947 := bstep (se 1 (by rfl) ⟨747710, by rfl⟩ : syracuseStep 996947 = 1495421) B1495421
theorem B1259165 : Blo 439778 1259165 := bstep (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) B472187
theorem B440031 : Blo 439778 440031 := bstep (se 1 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 440031 = 660047) B660047
theorem B997127 : Blo 439778 997127 := bstep (se 1 (by rfl) ⟨747845, by rfl⟩ : syracuseStep 997127 = 1495691) B1495691
theorem B440111 : Blo 439778 440111 := bstep (se 1 (by rfl) ⟨330083, by rfl⟩ : syracuseStep 440111 = 660167) B660167
theorem B440219 : Blo 439778 440219 := bstep (se 1 (by rfl) ⟨330164, by rfl⟩ : syracuseStep 440219 = 660329) B660329
theorem B440271 : Blo 439778 440271 := bstep (se 1 (by rfl) ⟨330203, by rfl⟩ : syracuseStep 440271 = 660407) B660407
theorem B440295 : Blo 439778 440295 := bstep (se 1 (by rfl) ⟨330221, by rfl⟩ : syracuseStep 440295 = 660443) B660443
theorem B2275463 : Blo 439778 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B440607 : Blo 439778 440607 := bstep (se 1 (by rfl) ⟨330455, by rfl⟩ : syracuseStep 440607 = 660911) B660911
theorem B473383 : Blo 439778 473383 := bstep (se 1 (by rfl) ⟨355037, by rfl⟩ : syracuseStep 473383 = 710075) B710075
theorem B440667 : Blo 439778 440667 := bstep (se 1 (by rfl) ⟨330500, by rfl⟩ : syracuseStep 440667 = 661001) B661001
theorem B1063259 : Blo 439778 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B997739 : Blo 439778 997739 := bstep (se 1 (by rfl) ⟨748304, by rfl⟩ : syracuseStep 997739 = 1496609) B1496609
theorem B440687 : Blo 439778 440687 := bstep (se 1 (by rfl) ⟨330515, by rfl⟩ : syracuseStep 440687 = 661031) B661031
theorem B440743 : Blo 439778 440743 := bstep (se 1 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 440743 = 661115) B661115
theorem B1489319 : Blo 439778 1489319 := bstep (se 1 (by rfl) ⟨1116989, by rfl⟩ : syracuseStep 1489319 = 2233979) B2233979
theorem B440827 : Blo 439778 440827 := bstep (se 1 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 440827 = 661241) B661241
theorem B997883 : Blo 439778 997883 := bstep (se 1 (by rfl) ⟨748412, by rfl⟩ : syracuseStep 997883 = 1496825) B1496825
theorem B440895 : Blo 439778 440895 := bstep (se 1 (by rfl) ⟨330671, by rfl⟩ : syracuseStep 440895 = 661343) B661343
theorem B440903 : Blo 439778 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B1489481 : Blo 439778 1489481 := bstep (se 2 (by rfl) ⟨558555, by rfl⟩ : syracuseStep 1489481 = 1117111) B1117111
theorem B998009 : Blo 439778 998009 := bstep (se 2 (by rfl) ⟨374253, by rfl⟩ : syracuseStep 998009 = 748507) B748507
theorem B998063 : Blo 439778 998063 := bstep (se 1 (by rfl) ⟨748547, by rfl⟩ : syracuseStep 998063 = 1497095) B1497095
theorem B441055 : Blo 439778 441055 := bstep (se 1 (by rfl) ⟨330791, by rfl⟩ : syracuseStep 441055 = 661583) B661583
theorem B1882871 : Blo 439778 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B998135 : Blo 439778 998135 := bstep (se 1 (by rfl) ⟨748601, by rfl⟩ : syracuseStep 998135 = 1497203) B1497203
theorem B441135 : Blo 439778 441135 := bstep (se 1 (by rfl) ⟨330851, by rfl⟩ : syracuseStep 441135 = 661703) B661703
theorem B1260431 : Blo 439778 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B441243 : Blo 439778 441243 := bstep (se 1 (by rfl) ⟨330932, by rfl⟩ : syracuseStep 441243 = 661865) B661865
theorem B998315 : Blo 439778 998315 := bstep (se 1 (by rfl) ⟨748736, by rfl⟩ : syracuseStep 998315 = 1497473) B1497473
theorem B441295 : Blo 439778 441295 := bstep (se 1 (by rfl) ⟨330971, by rfl⟩ : syracuseStep 441295 = 661943) B661943
theorem B441319 : Blo 439778 441319 := bstep (se 1 (by rfl) ⟨330989, by rfl⟩ : syracuseStep 441319 = 661979) B661979
theorem B2243699 : Blo 439778 2243699 := bstep (se 1 (by rfl) ⟨1682774, by rfl⟩ : syracuseStep 2243699 = 3365549) B3365549
theorem B441631 : Blo 439778 441631 := bstep (se 1 (by rfl) ⟨331223, by rfl⟩ : syracuseStep 441631 = 662447) B662447
theorem B572711 : Blo 439778 572711 := bstep (se 1 (by rfl) ⟨429533, by rfl⟩ : syracuseStep 572711 = 859067) B859067
theorem B4308299 : Blo 439778 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B441691 : Blo 439778 441691 := bstep (se 1 (by rfl) ⟨331268, by rfl⟩ : syracuseStep 441691 = 662537) B662537
theorem B1785185 : Blo 439778 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B441711 : Blo 439778 441711 := bstep (se 1 (by rfl) ⟨331283, by rfl⟩ : syracuseStep 441711 = 662567) B662567
theorem B441767 : Blo 439778 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B441851 : Blo 439778 441851 := bstep (se 1 (by rfl) ⟨331388, by rfl⟩ : syracuseStep 441851 = 662777) B662777
theorem B441919 : Blo 439778 441919 := bstep (se 1 (by rfl) ⟨331439, by rfl⟩ : syracuseStep 441919 = 662879) B662879
theorem B441927 : Blo 439778 441927 := bstep (se 1 (by rfl) ⟨331445, by rfl⟩ : syracuseStep 441927 = 662891) B662891
theorem B1457747 : Blo 439778 1457747 := bstep (se 1 (by rfl) ⟨1093310, by rfl⟩ : syracuseStep 1457747 = 2186621) B2186621
theorem B442079 : Blo 439778 442079 := bstep (se 1 (by rfl) ⟨331559, by rfl⟩ : syracuseStep 442079 = 663119) B663119
theorem B442159 : Blo 439778 442159 := bstep (se 1 (by rfl) ⟨331619, by rfl⟩ : syracuseStep 442159 = 663239) B663239
theorem B442267 : Blo 439778 442267 := bstep (se 1 (by rfl) ⟨331700, by rfl⟩ : syracuseStep 442267 = 663401) B663401
theorem B2244509 : Blo 439778 2244509 := bstep (se 3 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 2244509 = 841691) B841691
theorem B442319 : Blo 439778 442319 := bstep (se 1 (by rfl) ⟨331739, by rfl⟩ : syracuseStep 442319 = 663479) B663479
theorem B442343 : Blo 439778 442343 := bstep (se 1 (by rfl) ⟨331757, by rfl⟩ : syracuseStep 442343 = 663515) B663515
theorem B1491155 : Blo 439778 1491155 := bstep (se 1 (by rfl) ⟨1118366, by rfl⟩ : syracuseStep 1491155 = 2236733) B2236733
theorem B19087589 : Blo 439778 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B442655 : Blo 439778 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B442715 : Blo 439778 442715 := bstep (se 1 (by rfl) ⟨332036, by rfl⟩ : syracuseStep 442715 = 664073) B664073
theorem B442735 : Blo 439778 442735 := bstep (se 1 (by rfl) ⟨332051, by rfl⟩ : syracuseStep 442735 = 664103) B664103
theorem B442791 : Blo 439778 442791 := bstep (se 1 (by rfl) ⟨332093, by rfl⟩ : syracuseStep 442791 = 664187) B664187
theorem B1491425 : Blo 439778 1491425 := bstep (se 2 (by rfl) ⟨559284, by rfl⟩ : syracuseStep 1491425 = 1118569) B1118569
theorem B442875 : Blo 439778 442875 := bstep (se 1 (by rfl) ⟨332156, by rfl⟩ : syracuseStep 442875 = 664313) B664313
theorem B2834945 : Blo 439778 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B442943 : Blo 439778 442943 := bstep (se 1 (by rfl) ⟨332207, by rfl⟩ : syracuseStep 442943 = 664415) B664415
theorem B442951 : Blo 439778 442951 := bstep (se 1 (by rfl) ⟨332213, by rfl⟩ : syracuseStep 442951 = 664427) B664427
theorem B1065593 : Blo 439778 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B2245319 : Blo 439778 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B443103 : Blo 439778 443103 := bstep (se 1 (by rfl) ⟨332327, by rfl⟩ : syracuseStep 443103 = 664655) B664655
theorem B1065719 : Blo 439778 1065719 := bstep (se 1 (by rfl) ⟨799289, by rfl⟩ : syracuseStep 1065719 = 1598579) B1598579
theorem B443183 : Blo 439778 443183 := bstep (se 1 (by rfl) ⟨332387, by rfl⟩ : syracuseStep 443183 = 664775) B664775
theorem B705359 : Blo 439778 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B443291 : Blo 439778 443291 := bstep (se 1 (by rfl) ⟨332468, by rfl⟩ : syracuseStep 443291 = 664937) B664937
theorem B443343 : Blo 439778 443343 := bstep (se 1 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 443343 = 665015) B665015
theorem B2835431 : Blo 439778 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B443367 : Blo 439778 443367 := bstep (se 1 (by rfl) ⟨332525, by rfl⟩ : syracuseStep 443367 = 665051) B665051
theorem B1885331 : Blo 439778 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B443679 : Blo 439778 443679 := bstep (se 1 (by rfl) ⟨332759, by rfl⟩ : syracuseStep 443679 = 665519) B665519
theorem B443739 : Blo 439778 443739 := bstep (se 1 (by rfl) ⟨332804, by rfl⟩ : syracuseStep 443739 = 665609) B665609
theorem B1590623 : Blo 439778 1590623 := bstep (se 1 (by rfl) ⟨1192967, by rfl⟩ : syracuseStep 1590623 = 2385935) B2385935
theorem B443759 : Blo 439778 443759 := bstep (se 1 (by rfl) ⟨332819, by rfl⟩ : syracuseStep 443759 = 665639) B665639
theorem B4769437 : Blo 439778 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B4245149 : Blo 439778 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B1492667 : Blo 439778 1492667 := bstep (se 1 (by rfl) ⟨1119500, by rfl⟩ : syracuseStep 1492667 = 2239001) B2239001
theorem B1197755 : Blo 439778 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B509743 : Blo 439778 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B65095987 : Blo 439778 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B4770515 : Blo 439778 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B11324285 : Blo 439778 11324285 := bstep (se 3 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 11324285 = 4246607) B4246607
theorem B3361661 : Blo 439778 3361661 := bstep (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) B1260623
theorem B1887313 : Blo 439778 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B2116925 : Blo 439778 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B25873843 : Blo 439778 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B1199549 : Blo 439778 1199549 := bstep (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) B449831
theorem B1494611 : Blo 439778 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B2379593 : Blo 439778 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B839945 : Blo 439778 839945 := bstep (se 2 (by rfl) ⟨314979, by rfl⟩ : syracuseStep 839945 = 629959) B629959
theorem B3035465 : Blo 439778 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B2675051 : Blo 439778 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B742223 : Blo 439778 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B1594313 : Blo 439778 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B4773113 : Blo 439778 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B5723713 : Blo 439778 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B841403 : Blo 439778 841403 := bstep (se 1 (by rfl) ⟨631052, by rfl⟩ : syracuseStep 841403 = 1262105) B1262105
theorem B743215 : Blo 439778 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B2512727 : Blo 439778 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B3758359 : Blo 439778 3758359 := bstep (se 1 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 3758359 = 5637539) B5637539
theorem B1497527 : Blo 439778 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B940513 : Blo 439778 940513 := bstep (se 2 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 940513 = 705385) B705385
theorem B1006811 : Blo 439778 1006811 := bstep (se 1 (by rfl) ⟨755108, by rfl⟩ : syracuseStep 1006811 = 1510217) B1510217
theorem B3595531 : Blo 439778 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B9690841 : Blo 439778 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B2678993 : Blo 439778 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B745895 : Blo 439778 745895 := bstep (se 1 (by rfl) ⟨559421, by rfl⟩ : syracuseStep 745895 = 1118843) B1118843
theorem B27124253 : Blo 439778 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B746057 : Blo 439778 746057 := bstep (se 2 (by rfl) ⟨279771, by rfl⟩ : syracuseStep 746057 = 559543) B559543
theorem B1532903 : Blo 439778 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B943247 : Blo 439778 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B747103 : Blo 439778 747103 := bstep (se 1 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 747103 = 1120655) B1120655
theorem B943913 : Blo 439778 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B747319 : Blo 439778 747319 := bstep (se 1 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 747319 = 1120979) B1120979
theorem B5040305 : Blo 439778 5040305 := bstep (se 2 (by rfl) ⟨1890114, by rfl⟩ : syracuseStep 5040305 = 3780229) B3780229
theorem B747785 : Blo 439778 747785 := bstep (se 2 (by rfl) ⟨280419, by rfl⟩ : syracuseStep 747785 = 560839) B560839
theorem B944887 : Blo 439778 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B2878199 : Blo 439778 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B3173255 : Blo 439778 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B5663783 : Blo 439778 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B1272955 : Blo 439778 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B748777 : Blo 439778 748777 := bstep (se 2 (by rfl) ⟨280791, by rfl⟩ : syracuseStep 748777 = 561583) B561583
theorem B748831 : Blo 439778 748831 := bstep (se 1 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 748831 = 1123247) B1123247
theorem B1076831 : Blo 439778 1076831 := bstep (se 1 (by rfl) ⟨807623, by rfl⟩ : syracuseStep 1076831 = 1615247) B1615247
theorem B14282477 : Blo 439778 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B9531341 : Blo 439778 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B3764717 : Blo 439778 3764717 := bstep (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) B1411769
theorem B1340239 : Blo 439778 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B2257895 : Blo 439778 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B1210393 : Blo 439778 1210393 := bstep (se 2 (by rfl) ⟨453897, by rfl⟩ : syracuseStep 1210393 = 907795) B907795
theorem B18086125 : Blo 439778 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B2128457 : Blo 439778 2128457 := bstep (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) B1596343
theorem B32733829 : Blo 439778 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B752303 : Blo 439778 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B2521975 : Blo 439778 2521975 := bstep (se 1 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 2521975 = 3782963) B3782963
theorem B5012603 : Blo 439778 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B1343071 : Blo 439778 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B5014061 : Blo 439778 5014061 := bstep (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) B1880273
theorem B1508107 : Blo 439778 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B2524709 : Blo 439778 2524709 := bstep (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) B473383
theorem B1508975 : Blo 439778 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B1115815 : Blo 439778 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B3180343 : Blo 439778 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B6359249 : Blo 439778 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B1411283 : Blo 439778 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B1116463 : Blo 439778 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B4786523 : Blo 439778 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B6392465 : Blo 439778 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B559963 : Blo 439778 559963 := bstep (se 1 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 559963 = 839945) B839945
theorem B494815 : Blo 439778 494815 := bstep (se 1 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 494815 = 742223) B742223
theorem B1674665 : Blo 439778 1674665 := bstep (se 2 (by rfl) ⟨627999, by rfl⟩ : syracuseStep 1674665 = 1255999) B1255999
theorem B3182075 : Blo 439778 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B1117759 : Blo 439778 1117759 := bstep (se 1 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 1117759 = 1676639) B1676639
theorem B1117871 : Blo 439778 1117871 := bstep (se 1 (by rfl) ⟨838403, by rfl⟩ : syracuseStep 1117871 = 1676807) B1676807
theorem B560935 : Blo 439778 560935 := bstep (se 1 (by rfl) ⟨420701, by rfl⟩ : syracuseStep 560935 = 841403) B841403
theorem B8064845 : Blo 439778 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B1675151 : Blo 439778 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B2396141 : Blo 439778 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B1118195 : Blo 439778 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B4427929 : Blo 439778 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B659675 : Blo 439778 659675 := bstep (se 1 (by rfl) ⟨494756, by rfl⟩ : syracuseStep 659675 = 989513) B989513
theorem B659687 : Blo 439778 659687 := bstep (se 1 (by rfl) ⟨494765, by rfl⟩ : syracuseStep 659687 = 989531) B989531
theorem B1118519 : Blo 439778 1118519 := bstep (se 1 (by rfl) ⟨838889, by rfl⟩ : syracuseStep 1118519 = 1677779) B1677779
theorem B659849 : Blo 439778 659849 := bstep (se 2 (by rfl) ⟨247443, by rfl⟩ : syracuseStep 659849 = 494887) B494887
theorem B659945 : Blo 439778 659945 := bstep (se 2 (by rfl) ⟨247479, by rfl⟩ : syracuseStep 659945 = 494959) B494959
theorem B660071 : Blo 439778 660071 := bstep (se 1 (by rfl) ⟨495053, by rfl⟩ : syracuseStep 660071 = 990107) B990107
theorem B2691787 : Blo 439778 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B660203 : Blo 439778 660203 := bstep (se 1 (by rfl) ⟨495152, by rfl⟩ : syracuseStep 660203 = 990305) B990305
theorem B660233 : Blo 439778 660233 := bstep (se 2 (by rfl) ⟨247587, by rfl⟩ : syracuseStep 660233 = 495175) B495175
theorem B660335 : Blo 439778 660335 := bstep (se 1 (by rfl) ⟨495251, by rfl⟩ : syracuseStep 660335 = 990503) B990503
theorem B8459315 : Blo 439778 8459315 := bstep (se 1 (by rfl) ⟨6344486, by rfl⟩ : syracuseStep 8459315 = 12688973) B12688973
theorem B660587 : Blo 439778 660587 := bstep (se 1 (by rfl) ⟨495440, by rfl⟩ : syracuseStep 660587 = 990881) B990881
theorem B9311377 : Blo 439778 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B660827 : Blo 439778 660827 := bstep (se 1 (by rfl) ⟨495620, by rfl⟩ : syracuseStep 660827 = 991241) B991241
theorem B1119815 : Blo 439778 1119815 := bstep (se 1 (by rfl) ⟨839861, by rfl⟩ : syracuseStep 1119815 = 1679723) B1679723
theorem B661103 : Blo 439778 661103 := bstep (se 1 (by rfl) ⟨495827, by rfl⟩ : syracuseStep 661103 = 991655) B991655
theorem B497263 : Blo 439778 497263 := bstep (se 1 (by rfl) ⟨372947, by rfl⟩ : syracuseStep 497263 = 745895) B745895
theorem B661175 : Blo 439778 661175 := bstep (se 1 (by rfl) ⟨495881, by rfl⟩ : syracuseStep 661175 = 991763) B991763
theorem B661211 : Blo 439778 661211 := bstep (se 1 (by rfl) ⟨495908, by rfl⟩ : syracuseStep 661211 = 991817) B991817
theorem B497371 : Blo 439778 497371 := bstep (se 1 (by rfl) ⟨373028, by rfl⟩ : syracuseStep 497371 = 746057) B746057
theorem B661385 : Blo 439778 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B661487 : Blo 439778 661487 := bstep (se 1 (by rfl) ⟨496115, by rfl⟩ : syracuseStep 661487 = 992231) B992231
theorem B1120351 : Blo 439778 1120351 := bstep (se 1 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 1120351 = 1680527) B1680527
theorem B628831 : Blo 439778 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B792737 : Blo 439778 792737 := bstep (se 2 (by rfl) ⟨297276, by rfl⟩ : syracuseStep 792737 = 594553) B594553
theorem B661739 : Blo 439778 661739 := bstep (se 1 (by rfl) ⟨496304, by rfl⟩ : syracuseStep 661739 = 992609) B992609
theorem B661799 : Blo 439778 661799 := bstep (se 1 (by rfl) ⟨496349, by rfl⟩ : syracuseStep 661799 = 992699) B992699
theorem B661883 : Blo 439778 661883 := bstep (se 1 (by rfl) ⟨496412, by rfl⟩ : syracuseStep 661883 = 992825) B992825
theorem B662153 : Blo 439778 662153 := bstep (se 2 (by rfl) ⟨248307, by rfl⟩ : syracuseStep 662153 = 496615) B496615
theorem B662327 : Blo 439778 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B990035 : Blo 439778 990035 := bstep (se 1 (by rfl) ⟨742526, by rfl⟩ : syracuseStep 990035 = 1485053) B1485053
theorem B662363 : Blo 439778 662363 := bstep (se 1 (by rfl) ⟨496772, by rfl⟩ : syracuseStep 662363 = 993545) B993545
theorem B498523 : Blo 439778 498523 := bstep (se 1 (by rfl) ⟨373892, by rfl⟩ : syracuseStep 498523 = 747785) B747785
theorem B662507 : Blo 439778 662507 := bstep (se 1 (by rfl) ⟨496880, by rfl⟩ : syracuseStep 662507 = 993761) B993761
theorem B5053427 : Blo 439778 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B662711 : Blo 439778 662711 := bstep (se 1 (by rfl) ⟨497033, by rfl⟩ : syracuseStep 662711 = 994067) B994067
theorem B990575 : Blo 439778 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B3775855 : Blo 439778 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B1121647 : Blo 439778 1121647 := bstep (se 1 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 1121647 = 1682471) B1682471
theorem B662951 : Blo 439778 662951 := bstep (se 1 (by rfl) ⟨497213, by rfl⟩ : syracuseStep 662951 = 994427) B994427
theorem B663035 : Blo 439778 663035 := bstep (se 1 (by rfl) ⟨497276, by rfl⟩ : syracuseStep 663035 = 994553) B994553
theorem B663131 : Blo 439778 663131 := bstep (se 1 (by rfl) ⟨497348, by rfl⟩ : syracuseStep 663131 = 994697) B994697
theorem B990863 : Blo 439778 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B663215 : Blo 439778 663215 := bstep (se 1 (by rfl) ⟨497411, by rfl⟩ : syracuseStep 663215 = 994823) B994823
theorem B990953 : Blo 439778 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B663335 : Blo 439778 663335 := bstep (se 1 (by rfl) ⟨497501, by rfl⟩ : syracuseStep 663335 = 995003) B995003
theorem B663419 : Blo 439778 663419 := bstep (se 1 (by rfl) ⟨497564, by rfl⟩ : syracuseStep 663419 = 995129) B995129
theorem B1613857 : Blo 439778 1613857 := bstep (se 2 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 1613857 = 1210393) B1210393
theorem B10887211 : Blo 439778 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B794855 : Blo 439778 794855 := bstep (se 1 (by rfl) ⟨596141, by rfl⟩ : syracuseStep 794855 = 1192283) B1192283
theorem B663839 : Blo 439778 663839 := bstep (se 1 (by rfl) ⟨497879, by rfl⟩ : syracuseStep 663839 = 995759) B995759
theorem B663863 : Blo 439778 663863 := bstep (se 1 (by rfl) ⟨497897, by rfl⟩ : syracuseStep 663863 = 995795) B995795
theorem B663935 : Blo 439778 663935 := bstep (se 1 (by rfl) ⟨497951, by rfl⟩ : syracuseStep 663935 = 995903) B995903
theorem B664007 : Blo 439778 664007 := bstep (se 1 (by rfl) ⟨498005, by rfl⟩ : syracuseStep 664007 = 996011) B996011
theorem B1254017 : Blo 439778 1254017 := bstep (se 2 (by rfl) ⟨470256, by rfl⟩ : syracuseStep 1254017 = 940513) B940513
theorem B991979 : Blo 439778 991979 := bstep (se 1 (by rfl) ⟨743984, by rfl⟩ : syracuseStep 991979 = 1487969) B1487969
theorem B795433 : Blo 439778 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B664361 : Blo 439778 664361 := bstep (se 2 (by rfl) ⟨249135, by rfl⟩ : syracuseStep 664361 = 498271) B498271
theorem B664367 : Blo 439778 664367 := bstep (se 1 (by rfl) ⟨498275, by rfl⟩ : syracuseStep 664367 = 996551) B996551
theorem B664487 : Blo 439778 664487 := bstep (se 1 (by rfl) ⟨498365, by rfl⟩ : syracuseStep 664487 = 996731) B996731
theorem B664571 : Blo 439778 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B664631 : Blo 439778 664631 := bstep (se 1 (by rfl) ⟨498473, by rfl⟩ : syracuseStep 664631 = 996947) B996947
theorem B664751 : Blo 439778 664751 := bstep (se 1 (by rfl) ⟨498563, by rfl⟩ : syracuseStep 664751 = 997127) B997127
theorem B1516975 : Blo 439778 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B665159 : Blo 439778 665159 := bstep (se 1 (by rfl) ⟨498869, by rfl⟩ : syracuseStep 665159 = 997739) B997739
theorem B992879 : Blo 439778 992879 := bstep (se 1 (by rfl) ⟨744659, by rfl⟩ : syracuseStep 992879 = 1489319) B1489319
theorem B665255 : Blo 439778 665255 := bstep (se 1 (by rfl) ⟨498941, by rfl⟩ : syracuseStep 665255 = 997883) B997883
theorem B4794041 : Blo 439778 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B992987 : Blo 439778 992987 := bstep (se 1 (by rfl) ⟨744740, by rfl⟩ : syracuseStep 992987 = 1489481) B1489481
theorem B1418971 : Blo 439778 1418971 := bstep (se 1 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 1418971 = 2128457) B2128457
theorem B665339 : Blo 439778 665339 := bstep (se 1 (by rfl) ⟨499004, by rfl⟩ : syracuseStep 665339 = 998009) B998009
theorem B501535 : Blo 439778 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B665375 : Blo 439778 665375 := bstep (se 1 (by rfl) ⟨499031, by rfl⟩ : syracuseStep 665375 = 998063) B998063
theorem B1255247 : Blo 439778 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B665423 : Blo 439778 665423 := bstep (se 1 (by rfl) ⟨499067, by rfl⟩ : syracuseStep 665423 = 998135) B998135
theorem B665543 : Blo 439778 665543 := bstep (se 1 (by rfl) ⟨499157, by rfl⟩ : syracuseStep 665543 = 998315) B998315
theorem B3778589 : Blo 439778 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B1190123 : Blo 439778 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B12921121 : Blo 439778 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B1878839 : Blo 439778 1878839 := bstep (se 1 (by rfl) ⟨1409129, by rfl⟩ : syracuseStep 1878839 = 2818259) B2818259
theorem B994103 : Blo 439778 994103 := bstep (se 1 (by rfl) ⟨745577, by rfl⟩ : syracuseStep 994103 = 1491155) B1491155
theorem B12725059 : Blo 439778 12725059 := bstep (se 1 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 12725059 = 19087589) B19087589
theorem B994283 : Blo 439778 994283 := bstep (se 1 (by rfl) ⟨745712, by rfl⟩ : syracuseStep 994283 = 1491425) B1491425
theorem B502831 : Blo 439778 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B1059961 : Blo 439778 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B1256887 : Blo 439778 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B1060415 : Blo 439778 1060415 := bstep (se 1 (by rfl) ⟨795311, by rfl⟩ : syracuseStep 1060415 = 1590623) B1590623
theorem B1879625 : Blo 439778 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B1486511 : Blo 439778 1486511 := bstep (se 1 (by rfl) ⟨1114883, by rfl⟩ : syracuseStep 1486511 = 2229767) B2229767
theorem B2830099 : Blo 439778 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B995111 : Blo 439778 995111 := bstep (se 1 (by rfl) ⟨746333, by rfl⟩ : syracuseStep 995111 = 1492667) B1492667
theorem B798503 : Blo 439778 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B1486835 : Blo 439778 1486835 := bstep (se 1 (by rfl) ⟨1115126, by rfl⟩ : syracuseStep 1486835 = 2230253) B2230253
theorem B1683443 : Blo 439778 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B1487159 : Blo 439778 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B1487375 : Blo 439778 1487375 := bstep (se 1 (by rfl) ⟨1115531, by rfl⟩ : syracuseStep 1487375 = 2231063) B2231063
theorem B7549523 : Blo 439778 7549523 := bstep (se 1 (by rfl) ⟨5662142, by rfl⟩ : syracuseStep 7549523 = 11324285) B11324285
theorem B2241107 : Blo 439778 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B996137 : Blo 439778 996137 := bstep (se 2 (by rfl) ⟨373551, by rfl⟩ : syracuseStep 996137 = 747103) B747103
theorem B1880957 : Blo 439778 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B8500139 : Blo 439778 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B996407 : Blo 439778 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B996425 : Blo 439778 996425 := bstep (se 2 (by rfl) ⟨373659, by rfl⟩ : syracuseStep 996425 = 747319) B747319
theorem B1586395 : Blo 439778 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B1783367 : Blo 439778 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B1488455 : Blo 439778 1488455 := bstep (se 1 (by rfl) ⟨1116341, by rfl⟩ : syracuseStep 1488455 = 2232683) B2232683
theorem B439919 : Blo 439778 439919 := bstep (se 1 (by rfl) ⟨329939, by rfl⟩ : syracuseStep 439919 = 659879) B659879
theorem B439975 : Blo 439778 439975 := bstep (se 1 (by rfl) ⟨329981, by rfl⟩ : syracuseStep 439975 = 659963) B659963
theorem B440059 : Blo 439778 440059 := bstep (se 1 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 440059 = 660089) B660089
theorem B440095 : Blo 439778 440095 := bstep (se 1 (by rfl) ⟨330071, by rfl⟩ : syracuseStep 440095 = 660143) B660143
theorem B440127 : Blo 439778 440127 := bstep (se 1 (by rfl) ⟨330095, by rfl⟩ : syracuseStep 440127 = 660191) B660191
theorem B1062875 : Blo 439778 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B440303 : Blo 439778 440303 := bstep (se 1 (by rfl) ⟨330227, by rfl⟩ : syracuseStep 440303 = 660455) B660455
theorem B440475 : Blo 439778 440475 := bstep (se 1 (by rfl) ⟨330356, by rfl⟩ : syracuseStep 440475 = 660713) B660713
theorem B440511 : Blo 439778 440511 := bstep (se 1 (by rfl) ⟨330383, by rfl⟩ : syracuseStep 440511 = 660767) B660767
theorem B5650661 : Blo 439778 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B440623 : Blo 439778 440623 := bstep (se 1 (by rfl) ⟨330467, by rfl⟩ : syracuseStep 440623 = 660935) B660935
theorem B2242889 : Blo 439778 2242889 := bstep (se 2 (by rfl) ⟨841083, by rfl⟩ : syracuseStep 2242889 = 1682167) B1682167
theorem B1259849 : Blo 439778 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B1489427 : Blo 439778 1489427 := bstep (se 1 (by rfl) ⟨1117070, by rfl⟩ : syracuseStep 1489427 = 2234141) B2234141
theorem B440859 : Blo 439778 440859 := bstep (se 1 (by rfl) ⟨330644, by rfl⟩ : syracuseStep 440859 = 661289) B661289
theorem B440863 : Blo 439778 440863 := bstep (se 1 (by rfl) ⟨330647, by rfl⟩ : syracuseStep 440863 = 661295) B661295
theorem B1587865 : Blo 439778 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B441179 : Blo 439778 441179 := bstep (se 1 (by rfl) ⟨330884, by rfl⟩ : syracuseStep 441179 = 661769) B661769
theorem B441247 : Blo 439778 441247 := bstep (se 1 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 441247 = 661871) B661871
theorem B998351 : Blo 439778 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B998369 : Blo 439778 998369 := bstep (se 2 (by rfl) ⟨374388, by rfl⟩ : syracuseStep 998369 = 748777) B748777
theorem B998441 : Blo 439778 998441 := bstep (se 2 (by rfl) ⟨374415, by rfl⟩ : syracuseStep 998441 = 748831) B748831
theorem B441391 : Blo 439778 441391 := bstep (se 1 (by rfl) ⟨331043, by rfl⟩ : syracuseStep 441391 = 662087) B662087
theorem B441415 : Blo 439778 441415 := bstep (se 1 (by rfl) ⟨331061, by rfl⟩ : syracuseStep 441415 = 662123) B662123
theorem B3357773 : Blo 439778 3357773 := bstep (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) B1259165
theorem B6143147 : Blo 439778 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B441567 : Blo 439778 441567 := bstep (se 1 (by rfl) ⟨331175, by rfl⟩ : syracuseStep 441567 = 662351) B662351
theorem B4242917 : Blo 439778 4242917 := bstep (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) B795547
theorem B671207 : Blo 439778 671207 := bstep (se 1 (by rfl) ⟨503405, by rfl⟩ : syracuseStep 671207 = 1006811) B1006811
theorem B441831 : Blo 439778 441831 := bstep (se 1 (by rfl) ⟨331373, by rfl⟩ : syracuseStep 441831 = 662747) B662747
theorem B441947 : Blo 439778 441947 := bstep (se 1 (by rfl) ⟨331460, by rfl⟩ : syracuseStep 441947 = 662921) B662921
theorem B442183 : Blo 439778 442183 := bstep (se 1 (by rfl) ⟨331637, by rfl⟩ : syracuseStep 442183 = 663275) B663275
theorem B442335 : Blo 439778 442335 := bstep (se 1 (by rfl) ⟨331751, by rfl⟩ : syracuseStep 442335 = 663503) B663503
theorem B1785995 : Blo 439778 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B5030099 : Blo 439778 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B442599 : Blo 439778 442599 := bstep (se 1 (by rfl) ⟨331949, by rfl⟩ : syracuseStep 442599 = 663899) B663899
theorem B442751 : Blo 439778 442751 := bstep (se 1 (by rfl) ⟨332063, by rfl⟩ : syracuseStep 442751 = 664127) B664127
theorem B442831 : Blo 439778 442831 := bstep (se 1 (by rfl) ⟨332123, by rfl⟩ : syracuseStep 442831 = 664247) B664247
theorem B442983 : Blo 439778 442983 := bstep (se 1 (by rfl) ⟨332237, by rfl⟩ : syracuseStep 442983 = 664475) B664475
theorem B836399 : Blo 439778 836399 := bstep (se 1 (by rfl) ⟨627299, by rfl⟩ : syracuseStep 836399 = 1254599) B1254599
theorem B443247 : Blo 439778 443247 := bstep (se 1 (by rfl) ⟨332435, by rfl⟩ : syracuseStep 443247 = 664871) B664871
theorem B443303 : Blo 439778 443303 := bstep (se 1 (by rfl) ⟨332477, by rfl⟩ : syracuseStep 443303 = 664955) B664955
theorem B443387 : Blo 439778 443387 := bstep (se 1 (by rfl) ⟨332540, by rfl⟩ : syracuseStep 443387 = 665081) B665081
theorem B443455 : Blo 439778 443455 := bstep (se 1 (by rfl) ⟨332591, by rfl⟩ : syracuseStep 443455 = 665183) B665183
theorem B1786985 : Blo 439778 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B1492073 : Blo 439778 1492073 := bstep (se 2 (by rfl) ⟨559527, by rfl⟩ : syracuseStep 1492073 = 1119055) B1119055
theorem B2507921 : Blo 439778 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B443599 : Blo 439778 443599 := bstep (se 1 (by rfl) ⟨332699, by rfl⟩ : syracuseStep 443599 = 665399) B665399
theorem B3360203 : Blo 439778 3360203 := bstep (se 1 (by rfl) ⟨2520152, by rfl⟩ : syracuseStep 3360203 = 5040305) B5040305
theorem B2115233 : Blo 439778 2115233 := bstep (se 2 (by rfl) ⟨793212, by rfl⟩ : syracuseStep 2115233 = 1586425) B1586425
theorem B837287 : Blo 439778 837287 := bstep (se 1 (by rfl) ⟨627965, by rfl⟩ : syracuseStep 837287 = 1255931) B1255931
theorem B1918799 : Blo 439778 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B2115503 : Blo 439778 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B6473657 : Blo 439778 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B1492937 : Blo 439778 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B1493207 : Blo 439778 1493207 := bstep (se 1 (by rfl) ⟨1119905, by rfl⟩ : syracuseStep 1493207 = 2239811) B2239811
theorem B10242541 : Blo 439778 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B9521651 : Blo 439778 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B1493531 : Blo 439778 1493531 := bstep (se 1 (by rfl) ⟨1120148, by rfl⟩ : syracuseStep 1493531 = 2240297) B2240297
theorem B2017963 : Blo 439778 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B707563 : Blo 439778 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B2509811 : Blo 439778 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B1494395 : Blo 439778 1494395 := bstep (se 1 (by rfl) ⟨1120796, by rfl⟩ : syracuseStep 1494395 = 2241593) B2241593
theorem B1527229 : Blo 439778 1527229 := bstep (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) B572711
theorem B839231 : Blo 439778 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B3362633 : Blo 439778 3362633 := bstep (se 2 (by rfl) ⟨1260987, by rfl⟩ : syracuseStep 3362633 = 2521975) B2521975
theorem B3198797 : Blo 439778 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B708839 : Blo 439778 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B2511269 : Blo 439778 2511269 := bstep (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) B470863
theorem B840287 : Blo 439778 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B1495799 : Blo 439778 1495799 := bstep (se 1 (by rfl) ⟨1121849, by rfl⟩ : syracuseStep 1495799 = 2243699) B2243699
theorem B1790761 : Blo 439778 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B2872199 : Blo 439778 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B971831 : Blo 439778 971831 := bstep (se 1 (by rfl) ⟨728873, by rfl⟩ : syracuseStep 971831 = 1457747) B1457747
theorem B1496339 : Blo 439778 1496339 := bstep (se 1 (by rfl) ⟨1122254, by rfl⟩ : syracuseStep 1496339 = 2244509) B2244509
theorem B743033 : Blo 439778 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B1889963 : Blo 439778 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B1496879 : Blo 439778 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B710479 : Blo 439778 710479 := bstep (se 1 (by rfl) ⟨532859, by rfl⟩ : syracuseStep 710479 = 1065719) B1065719
theorem B2840503 : Blo 439778 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B1890287 : Blo 439778 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B743519 : Blo 439778 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B1136737 : Blo 439778 1136737 := bstep (se 2 (by rfl) ⟨426276, by rfl⟩ : syracuseStep 1136737 = 852553) B852553
theorem B841889 : Blo 439778 841889 := bstep (se 2 (by rfl) ⟨315708, by rfl⟩ : syracuseStep 841889 = 631417) B631417
theorem B3365063 : Blo 439778 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B6314669 : Blo 439778 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B2841581 : Blo 439778 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B3366035 : Blo 439778 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B744815 : Blo 439778 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B745051 : Blo 439778 745051 := bstep (se 1 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 745051 = 1117577) B1117577
theorem B679657 : Blo 439778 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B745193 : Blo 439778 745193 := bstep (se 2 (by rfl) ⟨279447, by rfl⟩ : syracuseStep 745193 = 558895) B558895
theorem B6021053 : Blo 439778 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B4087741 : Blo 439778 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B942119 : Blo 439778 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B2121767 : Blo 439778 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B2023643 : Blo 439778 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B86794649 : Blo 439778 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B9593275 : Blo 439778 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B5661323 : Blo 439778 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B746219 : Blo 439778 746219 := bstep (se 1 (by rfl) ⟨559664, by rfl⟩ : syracuseStep 746219 = 1119329) B1119329
theorem B746671 : Blo 439778 746671 := bstep (se 1 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 746671 = 1120007) B1120007
theorem B2516417 : Blo 439778 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B1697273 : Blo 439778 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1271315 : Blo 439778 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B747191 : Blo 439778 747191 := bstep (se 1 (by rfl) ⟨560393, by rfl⟩ : syracuseStep 747191 = 1120787) B1120787
theorem B23029505 : Blo 439778 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B34498457 : Blo 439778 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B2517101 : Blo 439778 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B748379 : Blo 439778 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B18082835 : Blo 439778 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B748615 : Blo 439778 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B4615639 : Blo 439778 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B946075 : Blo 439778 946075 := bstep (se 1 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 946075 = 1419113) B1419113
theorem B7631617 : Blo 439778 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B717887 : Blo 439778 717887 := bstep (se 1 (by rfl) ⟨538415, by rfl⟩ : syracuseStep 717887 = 1076831) B1076831
theorem B6354227 : Blo 439778 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B24114833 : Blo 439778 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B5011145 : Blo 439778 5011145 := bstep (se 2 (by rfl) ⟨1879179, by rfl⟩ : syracuseStep 5011145 = 3758359) B3758359
theorem B43645105 : Blo 439778 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B1210747 : Blo 439778 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B3341735 : Blo 439778 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B14516281 : Blo 439778 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B3342707 : Blo 439778 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B6062597 : Blo 439778 6062597 := bstep (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) B1136737
theorem B557599 : Blo 439778 557599 := bstep (se 1 (by rfl) ⟨418199, by rfl⟩ : syracuseStep 557599 = 836399) B836399
theorem B1671947 : Blo 439778 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B1410155 : Blo 439778 1410155 := bstep (se 1 (by rfl) ⟨1057616, by rfl⟩ : syracuseStep 1410155 = 2115233) B2115233
theorem B558191 : Blo 439778 558191 := bstep (se 1 (by rfl) ⟨418643, by rfl⟩ : syracuseStep 558191 = 837287) B837287
theorem B1279199 : Blo 439778 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B1410335 : Blo 439778 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B4261643 : Blo 439778 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B1673207 : Blo 439778 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B1116443 : Blo 439778 1116443 := bstep (se 1 (by rfl) ⟨837332, by rfl⟩ : syracuseStep 1116443 = 1674665) B1674665
theorem B559487 : Blo 439778 559487 := bstep (se 1 (by rfl) ⟨419615, by rfl⟩ : syracuseStep 559487 = 839231) B839231
theorem B5376563 : Blo 439778 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B2132531 : Blo 439778 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B1116767 : Blo 439778 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B1674179 : Blo 439778 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B560191 : Blo 439778 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B5639543 : Blo 439778 5639543 := bstep (se 1 (by rfl) ⟨4229657, by rfl⟩ : syracuseStep 5639543 = 8459315) B8459315
theorem B495355 : Blo 439778 495355 := bstep (se 1 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 495355 = 743033) B743033
theorem B495679 : Blo 439778 495679 := bstep (se 1 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 495679 = 743519) B743519
theorem B528491 : Blo 439778 528491 := bstep (se 1 (by rfl) ⟨396368, by rfl⟩ : syracuseStep 528491 = 792737) B792737
theorem B561259 : Blo 439778 561259 := bstep (se 1 (by rfl) ⟨420944, by rfl⟩ : syracuseStep 561259 = 841889) B841889
theorem B1413281 : Blo 439778 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B659753 : Blo 439778 659753 := bstep (se 2 (by rfl) ⟨247407, by rfl⟩ : syracuseStep 659753 = 494815) B494815
theorem B660023 : Blo 439778 660023 := bstep (se 1 (by rfl) ⟨495017, by rfl⟩ : syracuseStep 660023 = 990035) B990035
theorem B1675849 : Blo 439778 1675849 := bstep (se 2 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 1675849 = 1256887) B1256887
theorem B2036305 : Blo 439778 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B660383 : Blo 439778 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B496543 : Blo 439778 496543 := bstep (se 1 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 496543 = 744815) B744815
theorem B3773465 : Blo 439778 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B660575 : Blo 439778 660575 := bstep (se 1 (by rfl) ⟨495431, by rfl⟩ : syracuseStep 660575 = 990863) B990863
theorem B660635 : Blo 439778 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B496795 : Blo 439778 496795 := bstep (se 1 (by rfl) ⟨372596, by rfl⟩ : syracuseStep 496795 = 745193) B745193
theorem B628079 : Blo 439778 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B1414511 : Blo 439778 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B1349095 : Blo 439778 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B3774215 : Blo 439778 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B661319 : Blo 439778 661319 := bstep (se 1 (by rfl) ⟨495989, by rfl⟩ : syracuseStep 661319 = 991979) B991979
theorem B497479 : Blo 439778 497479 := bstep (se 1 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 497479 = 746219) B746219
theorem B1677611 : Blo 439778 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B661919 : Blo 439778 661919 := bstep (se 1 (by rfl) ⟨496439, by rfl⟩ : syracuseStep 661919 = 992879) B992879
theorem B498127 : Blo 439778 498127 := bstep (se 1 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 498127 = 747191) B747191
theorem B8460773 : Blo 439778 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B661991 : Blo 439778 661991 := bstep (se 1 (by rfl) ⟨496493, by rfl⟩ : syracuseStep 661991 = 992987) B992987
theorem B1678067 : Blo 439778 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B793415 : Blo 439778 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B1252559 : Blo 439778 1252559 := bstep (se 1 (by rfl) ⟨939419, by rfl⟩ : syracuseStep 1252559 = 1878839) B1878839
theorem B662735 : Blo 439778 662735 := bstep (se 1 (by rfl) ⟨497051, by rfl⟩ : syracuseStep 662735 = 994103) B994103
theorem B498919 : Blo 439778 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B662855 : Blo 439778 662855 := bstep (se 1 (by rfl) ⟨497141, by rfl⟩ : syracuseStep 662855 = 994283) B994283
theorem B663017 : Blo 439778 663017 := bstep (se 2 (by rfl) ⟨248631, by rfl⟩ : syracuseStep 663017 = 497263) B497263
theorem B663161 : Blo 439778 663161 := bstep (se 2 (by rfl) ⟨248685, by rfl⟩ : syracuseStep 663161 = 497371) B497371
theorem B1253083 : Blo 439778 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B991007 : Blo 439778 991007 := bstep (se 1 (by rfl) ⟨743255, by rfl⟩ : syracuseStep 991007 = 1486511) B1486511
theorem B663407 : Blo 439778 663407 := bstep (se 1 (by rfl) ⟨497555, by rfl⟩ : syracuseStep 663407 = 995111) B995111
theorem B991223 : Blo 439778 991223 := bstep (se 1 (by rfl) ⟨743417, by rfl⟩ : syracuseStep 991223 = 1486835) B1486835
theorem B1122295 : Blo 439778 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B991439 : Blo 439778 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B991583 : Blo 439778 991583 := bstep (se 1 (by rfl) ⟨743687, by rfl⟩ : syracuseStep 991583 = 1487375) B1487375
theorem B1614329 : Blo 439778 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B664091 : Blo 439778 664091 := bstep (se 1 (by rfl) ⟨498068, by rfl⟩ : syracuseStep 664091 = 996137) B996137
theorem B1253971 : Blo 439778 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B664271 : Blo 439778 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B664283 : Blo 439778 664283 := bstep (se 1 (by rfl) ⟨498212, by rfl⟩ : syracuseStep 664283 = 996425) B996425
theorem B4236151 : Blo 439778 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1188911 : Blo 439778 1188911 := bstep (se 1 (by rfl) ⟨891683, by rfl⟩ : syracuseStep 1188911 = 1783367) B1783367
theorem B992303 : Blo 439778 992303 := bstep (se 1 (by rfl) ⟨744227, by rfl⟩ : syracuseStep 992303 = 1488455) B1488455
theorem B664697 : Blo 439778 664697 := bstep (se 2 (by rfl) ⟨249261, by rfl⟩ : syracuseStep 664697 = 498523) B498523
theorem B992951 : Blo 439778 992951 := bstep (se 1 (by rfl) ⟨744713, by rfl⟩ : syracuseStep 992951 = 1489427) B1489427
theorem B665567 : Blo 439778 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B665579 : Blo 439778 665579 := bstep (se 1 (by rfl) ⟨499184, by rfl⟩ : syracuseStep 665579 = 998369) B998369
theorem B665627 : Blo 439778 665627 := bstep (se 1 (by rfl) ⟨499220, by rfl⟩ : syracuseStep 665627 = 998441) B998441
theorem B2238515 : Blo 439778 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B993401 : Blo 439778 993401 := bstep (se 2 (by rfl) ⟨372525, by rfl⟩ : syracuseStep 993401 = 745051) B745051
theorem B2828611 : Blo 439778 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B5450321 : Blo 439778 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B1190663 : Blo 439778 1190663 := bstep (se 1 (by rfl) ⟨892997, by rfl⟩ : syracuseStep 1190663 = 1785995) B1785995
theorem B3353399 : Blo 439778 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B12791033 : Blo 439778 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B1191323 : Blo 439778 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B994715 : Blo 439778 994715 := bstep (se 1 (by rfl) ⟨746036, by rfl⟩ : syracuseStep 994715 = 1492073) B1492073
theorem B2240135 : Blo 439778 2240135 := bstep (se 1 (by rfl) ⟨1680101, by rfl⟩ : syracuseStep 2240135 = 3360203) B3360203
theorem B2010809 : Blo 439778 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1683139 : Blo 439778 1683139 := bstep (se 1 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 1683139 = 2524709) B2524709
theorem B1060577 : Blo 439778 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B995291 : Blo 439778 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B4239499 : Blo 439778 4239499 := bstep (se 1 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 4239499 = 6359249) B6359249
theorem B995471 : Blo 439778 995471 := bstep (se 1 (by rfl) ⟨746603, by rfl⟩ : syracuseStep 995471 = 1493207) B1493207
theorem B3191015 : Blo 439778 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B995561 : Blo 439778 995561 := bstep (se 2 (by rfl) ⟨373335, by rfl⟩ : syracuseStep 995561 = 746671) B746671
theorem B995687 : Blo 439778 995687 := bstep (se 1 (by rfl) ⟨746765, by rfl⟩ : syracuseStep 995687 = 1493531) B1493531
theorem B1487753 : Blo 439778 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B996263 : Blo 439778 996263 := bstep (se 1 (by rfl) ⟨747197, by rfl⟩ : syracuseStep 996263 = 1494395) B1494395
theorem B4240457 : Blo 439778 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2241755 : Blo 439778 2241755 := bstep (se 1 (by rfl) ⟨1681316, by rfl⟩ : syracuseStep 2241755 = 3362633) B3362633
theorem B439783 : Blo 439778 439783 := bstep (se 1 (by rfl) ⟨329837, by rfl⟩ : syracuseStep 439783 = 659675) B659675
theorem B439791 : Blo 439778 439791 := bstep (se 1 (by rfl) ⟨329843, by rfl⟩ : syracuseStep 439791 = 659687) B659687
theorem B472559 : Blo 439778 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B439899 : Blo 439778 439899 := bstep (se 1 (by rfl) ⟨329924, by rfl⟩ : syracuseStep 439899 = 659849) B659849
theorem B439963 : Blo 439778 439963 := bstep (se 1 (by rfl) ⟨329972, by rfl⟩ : syracuseStep 439963 = 659945) B659945
theorem B1488617 : Blo 439778 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B440047 : Blo 439778 440047 := bstep (se 1 (by rfl) ⟨330035, by rfl⟩ : syracuseStep 440047 = 660071) B660071
theorem B440135 : Blo 439778 440135 := bstep (se 1 (by rfl) ⟨330101, by rfl⟩ : syracuseStep 440135 = 660203) B660203
theorem B997199 : Blo 439778 997199 := bstep (se 1 (by rfl) ⟨747899, by rfl⟩ : syracuseStep 997199 = 1495799) B1495799
theorem B440155 : Blo 439778 440155 := bstep (se 1 (by rfl) ⟨330116, by rfl⟩ : syracuseStep 440155 = 660233) B660233
theorem B440223 : Blo 439778 440223 := bstep (se 1 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 440223 = 660335) B660335
theorem B1914799 : Blo 439778 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B440391 : Blo 439778 440391 := bstep (se 1 (by rfl) ⟨330293, by rfl⟩ : syracuseStep 440391 = 660587) B660587
theorem B997559 : Blo 439778 997559 := bstep (se 1 (by rfl) ⟨748169, by rfl⟩ : syracuseStep 997559 = 1496339) B1496339
theorem B10762469 : Blo 439778 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B440551 : Blo 439778 440551 := bstep (se 1 (by rfl) ⟨330413, by rfl⟩ : syracuseStep 440551 = 660827) B660827
theorem B440735 : Blo 439778 440735 := bstep (se 1 (by rfl) ⟨330551, by rfl⟩ : syracuseStep 440735 = 661103) B661103
theorem B1259975 : Blo 439778 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B440783 : Blo 439778 440783 := bstep (se 1 (by rfl) ⟨330587, by rfl⟩ : syracuseStep 440783 = 661175) B661175
theorem B440807 : Blo 439778 440807 := bstep (se 1 (by rfl) ⟨330605, by rfl⟩ : syracuseStep 440807 = 661211) B661211
theorem B997919 : Blo 439778 997919 := bstep (se 1 (by rfl) ⟨748439, by rfl⟩ : syracuseStep 997919 = 1496879) B1496879
theorem B440923 : Blo 439778 440923 := bstep (se 1 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 440923 = 661385) B661385
theorem B440991 : Blo 439778 440991 := bstep (se 1 (by rfl) ⟨330743, by rfl⟩ : syracuseStep 440991 = 661487) B661487
theorem B1260191 : Blo 439778 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B670441 : Blo 439778 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B998153 : Blo 439778 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B2243375 : Blo 439778 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B441159 : Blo 439778 441159 := bstep (se 1 (by rfl) ⟨330869, by rfl⟩ : syracuseStep 441159 = 661739) B661739
theorem B441199 : Blo 439778 441199 := bstep (se 1 (by rfl) ⟨330899, by rfl⟩ : syracuseStep 441199 = 661799) B661799
theorem B441255 : Blo 439778 441255 := bstep (se 1 (by rfl) ⟨330941, by rfl⟩ : syracuseStep 441255 = 661883) B661883
theorem B441435 : Blo 439778 441435 := bstep (se 1 (by rfl) ⟨331076, by rfl⟩ : syracuseStep 441435 = 662153) B662153
theorem B4209779 : Blo 439778 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B441551 : Blo 439778 441551 := bstep (se 1 (by rfl) ⟨331163, by rfl⟩ : syracuseStep 441551 = 662327) B662327
theorem B441575 : Blo 439778 441575 := bstep (se 1 (by rfl) ⟨331181, by rfl⟩ : syracuseStep 441575 = 662363) B662363
theorem B441671 : Blo 439778 441671 := bstep (se 1 (by rfl) ⟨331253, by rfl⟩ : syracuseStep 441671 = 662507) B662507
theorem B1490345 : Blo 439778 1490345 := bstep (se 2 (by rfl) ⟨558879, by rfl⟩ : syracuseStep 1490345 = 1117759) B1117759
theorem B2244023 : Blo 439778 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B441807 : Blo 439778 441807 := bstep (se 1 (by rfl) ⟨331355, by rfl⟩ : syracuseStep 441807 = 662711) B662711
theorem B441967 : Blo 439778 441967 := bstep (se 1 (by rfl) ⟨331475, by rfl⟩ : syracuseStep 441967 = 662951) B662951
theorem B442023 : Blo 439778 442023 := bstep (se 1 (by rfl) ⟨331517, by rfl⟩ : syracuseStep 442023 = 663035) B663035
theorem B442087 : Blo 439778 442087 := bstep (se 1 (by rfl) ⟨331565, by rfl⟩ : syracuseStep 442087 = 663131) B663131
theorem B442143 : Blo 439778 442143 := bstep (se 1 (by rfl) ⟨331607, by rfl⟩ : syracuseStep 442143 = 663215) B663215
theorem B442223 : Blo 439778 442223 := bstep (se 1 (by rfl) ⟨331667, by rfl⟩ : syracuseStep 442223 = 663335) B663335
theorem B1261433 : Blo 439778 1261433 := bstep (se 2 (by rfl) ⟨473037, by rfl⟩ : syracuseStep 1261433 = 946075) B946075
theorem B442279 : Blo 439778 442279 := bstep (se 1 (by rfl) ⟨331709, by rfl⟩ : syracuseStep 442279 = 663419) B663419
theorem B4014035 : Blo 439778 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B442559 : Blo 439778 442559 := bstep (se 1 (by rfl) ⟨331919, by rfl⟩ : syracuseStep 442559 = 663839) B663839
theorem B442575 : Blo 439778 442575 := bstep (se 1 (by rfl) ⟨331931, by rfl⟩ : syracuseStep 442575 = 663863) B663863
theorem B442623 : Blo 439778 442623 := bstep (se 1 (by rfl) ⟨331967, by rfl⟩ : syracuseStep 442623 = 663935) B663935
theorem B442671 : Blo 439778 442671 := bstep (se 1 (by rfl) ⟨332003, by rfl⟩ : syracuseStep 442671 = 664007) B664007
theorem B836011 : Blo 439778 836011 := bstep (se 1 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 836011 = 1254017) B1254017
theorem B442907 : Blo 439778 442907 := bstep (se 1 (by rfl) ⟨332180, by rfl⟩ : syracuseStep 442907 = 664361) B664361
theorem B442911 : Blo 439778 442911 := bstep (se 1 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 442911 = 664367) B664367
theorem B442991 : Blo 439778 442991 := bstep (se 1 (by rfl) ⟨332243, by rfl⟩ : syracuseStep 442991 = 664487) B664487
theorem B443047 : Blo 439778 443047 := bstep (se 1 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 443047 = 664571) B664571
theorem B443087 : Blo 439778 443087 := bstep (se 1 (by rfl) ⟨332315, by rfl⟩ : syracuseStep 443087 = 664631) B664631
theorem B443167 : Blo 439778 443167 := bstep (se 1 (by rfl) ⟨332375, by rfl⟩ : syracuseStep 443167 = 664751) B664751
theorem B3589049 : Blo 439778 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1131515 : Blo 439778 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B10175489 : Blo 439778 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B443439 : Blo 439778 443439 := bstep (se 1 (by rfl) ⟨332579, by rfl⟩ : syracuseStep 443439 = 665159) B665159
theorem B443503 : Blo 439778 443503 := bstep (se 1 (by rfl) ⟨332627, by rfl⟩ : syracuseStep 443503 = 665255) B665255
theorem B3196027 : Blo 439778 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B443559 : Blo 439778 443559 := bstep (se 1 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 443559 = 665339) B665339
theorem B15353003 : Blo 439778 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B443583 : Blo 439778 443583 := bstep (se 1 (by rfl) ⟨332687, by rfl⟩ : syracuseStep 443583 = 665375) B665375
theorem B836831 : Blo 439778 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B443615 : Blo 439778 443615 := bstep (se 1 (by rfl) ⟨332711, by rfl⟩ : syracuseStep 443615 = 665423) B665423
theorem B443695 : Blo 439778 443695 := bstep (se 1 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 443695 = 665543) B665543
theorem B706943 : Blo 439778 706943 := bstep (se 1 (by rfl) ⟨530207, by rfl⟩ : syracuseStep 706943 = 1060415) B1060415
theorem B3787337 : Blo 439778 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B838441 : Blo 439778 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B1493801 : Blo 439778 1493801 := bstep (se 2 (by rfl) ⟨560175, by rfl⟩ : syracuseStep 1493801 = 1120351) B1120351
theorem B5033015 : Blo 439778 5033015 := bstep (se 1 (by rfl) ⟨3774761, by rfl⟩ : syracuseStep 5033015 = 7549523) B7549523
theorem B1494071 : Blo 439778 1494071 := bstep (se 1 (by rfl) ⟨1120553, by rfl⟩ : syracuseStep 1494071 = 2241107) B2241107
theorem B478591 : Blo 439778 478591 := bstep (se 1 (by rfl) ⟨358943, by rfl⟩ : syracuseStep 478591 = 717887) B717887
theorem B2117153 : Blo 439778 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B16076555 : Blo 439778 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B1789885 : Blo 439778 1789885 := bstep (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) B671207
theorem B708583 : Blo 439778 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B2674853 : Blo 439778 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B839899 : Blo 439778 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B1495259 : Blo 439778 1495259 := bstep (se 1 (by rfl) ⟨1121444, by rfl⟩ : syracuseStep 1495259 = 2242889) B2242889
theorem B5034473 : Blo 439778 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B1495529 : Blo 439778 1495529 := bstep (se 2 (by rfl) ⟨560823, by rfl⟩ : syracuseStep 1495529 = 1121647) B1121647
theorem B906209 : Blo 439778 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B2151809 : Blo 439778 2151809 := bstep (se 2 (by rfl) ⟨806928, by rfl⟩ : syracuseStep 2151809 = 1613857) B1613857
theorem B2119613 : Blo 439778 2119613 := bstep (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) B794855
theorem B23615621 : Blo 439778 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B1005983 : Blo 439778 1005983 := bstep (se 1 (by rfl) ⟨754487, by rfl⟩ : syracuseStep 1005983 = 1508975) B1508975
theorem B4315771 : Blo 439778 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B940855 : Blo 439778 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B1891961 : Blo 439778 1891961 := bstep (se 2 (by rfl) ⟨709485, by rfl⟩ : syracuseStep 1891961 = 1418971) B1418971
theorem B2121383 : Blo 439778 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B745247 : Blo 439778 745247 := bstep (se 1 (by rfl) ⟨558935, by rfl⟩ : syracuseStep 745247 = 1117871) B1117871
theorem B1597427 : Blo 439778 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B745463 : Blo 439778 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B745679 : Blo 439778 745679 := bstep (se 1 (by rfl) ⟨559259, by rfl⟩ : syracuseStep 745679 = 1118519) B1118519
theorem B17228161 : Blo 439778 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B13656721 : Blo 439778 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B647887 : Blo 439778 647887 := bstep (se 1 (by rfl) ⟨485915, by rfl⟩ : syracuseStep 647887 = 971831) B971831
theorem B746543 : Blo 439778 746543 := bstep (se 1 (by rfl) ⟨559907, by rfl⟩ : syracuseStep 746543 = 1119815) B1119815
theorem B16966745 : Blo 439778 16966745 := bstep (se 2 (by rfl) ⟨6362529, by rfl⟩ : syracuseStep 16966745 = 12725059) B12725059
theorem B746617 : Blo 439778 746617 := bstep (se 2 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 746617 = 559963) B559963
theorem B943417 : Blo 439778 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B1894387 : Blo 439778 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B3368951 : Blo 439778 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B747913 : Blo 439778 747913 := bstep (se 2 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 747913 = 560935) B560935
theorem B57863099 : Blo 439778 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B847543 : Blo 439778 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B2387681 : Blo 439778 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B22998971 : Blo 439778 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B25391069 : Blo 439778 25391069 := bstep (se 3 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 25391069 = 9521651) B9521651
theorem B2519059 : Blo 439778 2519059 := bstep (se 1 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 2519059 = 3778589) B3778589
theorem B12415169 : Blo 439778 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B12055223 : Blo 439778 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B8090533 : Blo 439778 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B947305 : Blo 439778 947305 := bstep (se 2 (by rfl) ⟨355239, by rfl⟩ : syracuseStep 947305 = 710479) B710479
theorem B58193473 : Blo 439778 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B5666759 : Blo 439778 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B3340763 : Blo 439778 3340763 := bstep (se 1 (by rfl) ⟨2505572, by rfl⟩ : syracuseStep 3340763 = 5011145) B5011145
theorem B3767107 : Blo 439778 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B98466965 : Blo 439778 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B2129341 : Blo 439778 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B4095431 : Blo 439778 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2227823 : Blo 439778 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B2228471 : Blo 439778 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B1409309 : Blo 439778 1409309 := bstep (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) B528491
theorem B22970881 : Blo 439778 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B1114631 : Blo 439778 1114631 := bstep (se 1 (by rfl) ⟨835973, by rfl⟩ : syracuseStep 1114631 = 1671947) B1671947
theorem B1114681 : Blo 439778 1114681 := bstep (se 2 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 1114681 = 836011) B836011
theorem B2392699 : Blo 439778 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B754343 : Blo 439778 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B6783659 : Blo 439778 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B1671961 : Blo 439778 1671961 := bstep (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) B1253971
theorem B1115471 : Blo 439778 1115471 := bstep (se 1 (by rfl) ⟨836603, by rfl⟩ : syracuseStep 1115471 = 1673207) B1673207
theorem B2524891 : Blo 439778 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B1116119 : Blo 439778 1116119 := bstep (se 1 (by rfl) ⟨837089, by rfl⟩ : syracuseStep 1116119 = 1674179) B1674179
theorem B1411435 : Blo 439778 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B10717703 : Blo 439778 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B2525849 : Blo 439778 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B3771481 : Blo 439778 3771481 := bstep (se 2 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 3771481 = 2828611) B2828611
theorem B2231549 : Blo 439778 2231549 := bstep (se 3 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 2231549 = 836831) B836831
theorem B3411197 : Blo 439778 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B1674877 : Blo 439778 1674877 := bstep (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) B628079
theorem B1117921 : Blo 439778 1117921 := bstep (se 2 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 1117921 = 838441) B838441
theorem B1118407 : Blo 439778 1118407 := bstep (se 1 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 1118407 = 1677611) B1677611
theorem B5640515 : Blo 439778 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B1118711 : Blo 439778 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B528943 : Blo 439778 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B660473 : Blo 439778 660473 := bstep (se 2 (by rfl) ⟨247677, by rfl⟩ : syracuseStep 660473 = 495355) B495355
theorem B1414255 : Blo 439778 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B660671 : Blo 439778 660671 := bstep (se 1 (by rfl) ⟨495503, by rfl⟩ : syracuseStep 660671 = 991007) B991007
theorem B496831 : Blo 439778 496831 := bstep (se 1 (by rfl) ⟨372623, by rfl⟩ : syracuseStep 496831 = 745247) B745247
theorem B660815 : Blo 439778 660815 := bstep (se 1 (by rfl) ⟨495611, by rfl⟩ : syracuseStep 660815 = 991223) B991223
theorem B496975 : Blo 439778 496975 := bstep (se 1 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 496975 = 745463) B745463
theorem B660905 : Blo 439778 660905 := bstep (se 2 (by rfl) ⟨247839, by rfl⟩ : syracuseStep 660905 = 495679) B495679
theorem B660959 : Blo 439778 660959 := bstep (se 1 (by rfl) ⟨495719, by rfl⟩ : syracuseStep 660959 = 991439) B991439
theorem B497119 : Blo 439778 497119 := bstep (se 1 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 497119 = 745679) B745679
theorem B661055 : Blo 439778 661055 := bstep (se 1 (by rfl) ⟨495791, by rfl⟩ : syracuseStep 661055 = 991583) B991583
theorem B1119865 : Blo 439778 1119865 := bstep (se 2 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 1119865 = 839899) B839899
theorem B17045477 : Blo 439778 17045477 := bstep (se 4 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 17045477 = 3196027) B3196027
theorem B792607 : Blo 439778 792607 := bstep (se 1 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 792607 = 1188911) B1188911
theorem B661535 : Blo 439778 661535 := bstep (se 1 (by rfl) ⟨496151, by rfl⟩ : syracuseStep 661535 = 992303) B992303
theorem B497695 : Blo 439778 497695 := bstep (se 1 (by rfl) ⟨373271, by rfl⟩ : syracuseStep 497695 = 746543) B746543
theorem B11311163 : Blo 439778 11311163 := bstep (se 1 (by rfl) ⟨8483372, by rfl⟩ : syracuseStep 11311163 = 16966745) B16966745
theorem B2234465 : Blo 439778 2234465 := bstep (se 2 (by rfl) ⟨837924, by rfl⟩ : syracuseStep 2234465 = 1675849) B1675849
theorem B661967 : Blo 439778 661967 := bstep (se 1 (by rfl) ⟨496475, by rfl⟩ : syracuseStep 661967 = 992951) B992951
theorem B662057 : Blo 439778 662057 := bstep (se 2 (by rfl) ⟨248271, by rfl⟩ : syracuseStep 662057 = 496543) B496543
theorem B10787377 : Blo 439778 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B662267 : Blo 439778 662267 := bstep (se 1 (by rfl) ⟨496700, by rfl⟩ : syracuseStep 662267 = 993401) B993401
theorem B662393 : Blo 439778 662393 := bstep (se 2 (by rfl) ⟨248397, by rfl⟩ : syracuseStep 662393 = 496795) B496795
theorem B793775 : Blo 439778 793775 := bstep (se 1 (by rfl) ⟨595331, by rfl⟩ : syracuseStep 793775 = 1190663) B1190663
theorem B2235599 : Blo 439778 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B38575399 : Blo 439778 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B8527355 : Blo 439778 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B794215 : Blo 439778 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B663143 : Blo 439778 663143 := bstep (se 1 (by rfl) ⟨497357, by rfl⟩ : syracuseStep 663143 = 994715) B994715
theorem B663305 : Blo 439778 663305 := bstep (se 2 (by rfl) ⟨248739, by rfl⟩ : syracuseStep 663305 = 497479) B497479
theorem B663527 : Blo 439778 663527 := bstep (se 1 (by rfl) ⟨497645, by rfl⟩ : syracuseStep 663527 = 995291) B995291
theorem B663647 : Blo 439778 663647 := bstep (se 1 (by rfl) ⟨497735, by rfl⟩ : syracuseStep 663647 = 995471) B995471
theorem B663707 : Blo 439778 663707 := bstep (se 1 (by rfl) ⟨497780, by rfl⟩ : syracuseStep 663707 = 995561) B995561
theorem B663791 : Blo 439778 663791 := bstep (se 1 (by rfl) ⟨497843, by rfl⟩ : syracuseStep 663791 = 995687) B995687
theorem B8036815 : Blo 439778 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B991835 : Blo 439778 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B664169 : Blo 439778 664169 := bstep (se 2 (by rfl) ⟨249063, by rfl⟩ : syracuseStep 664169 = 498127) B498127
theorem B664175 : Blo 439778 664175 := bstep (se 1 (by rfl) ⟨498131, by rfl⟩ : syracuseStep 664175 = 996263) B996263
theorem B2826971 : Blo 439778 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B893921 : Blo 439778 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B1254473 : Blo 439778 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B5022809 : Blo 439778 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B992411 : Blo 439778 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B664799 : Blo 439778 664799 := bstep (se 1 (by rfl) ⟨498599, by rfl⟩ : syracuseStep 664799 = 997199) B997199
theorem B3777839 : Blo 439778 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B665039 : Blo 439778 665039 := bstep (se 1 (by rfl) ⟨498779, by rfl⟩ : syracuseStep 665039 = 997559) B997559
theorem B665225 : Blo 439778 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B665279 : Blo 439778 665279 := bstep (se 1 (by rfl) ⟨498959, by rfl⟩ : syracuseStep 665279 = 997919) B997919
theorem B665435 : Blo 439778 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B65644643 : Blo 439778 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B993563 : Blo 439778 993563 := bstep (se 1 (by rfl) ⟨745172, by rfl⟩ : syracuseStep 993563 = 1490345) B1490345
theorem B2730287 : Blo 439778 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B1485215 : Blo 439778 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B4041731 : Blo 439778 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B10235335 : Blo 439778 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B863849 : Blo 439778 863849 := bstep (se 2 (by rfl) ⟨323943, by rfl⟩ : syracuseStep 863849 = 647887) B647887
theorem B5648201 : Blo 439778 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B995489 : Blo 439778 995489 := bstep (se 2 (by rfl) ⟨373308, by rfl⟩ : syracuseStep 995489 = 746617) B746617
theorem B471295 : Blo 439778 471295 := bstep (se 1 (by rfl) ⟨353471, by rfl⟩ : syracuseStep 471295 = 706943) B706943
theorem B3584375 : Blo 439778 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B1421687 : Blo 439778 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B995867 : Blo 439778 995867 := bstep (se 1 (by rfl) ⟨746900, by rfl⟩ : syracuseStep 995867 = 1493801) B1493801
theorem B3355343 : Blo 439778 3355343 := bstep (se 1 (by rfl) ⟨2516507, by rfl⟩ : syracuseStep 3355343 = 5033015) B5033015
theorem B996047 : Blo 439778 996047 := bstep (se 1 (by rfl) ⟨747035, by rfl⟩ : syracuseStep 996047 = 1494071) B1494071
theorem B1783235 : Blo 439778 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B996839 : Blo 439778 996839 := bstep (se 1 (by rfl) ⟨747629, by rfl⟩ : syracuseStep 996839 = 1495259) B1495259
theorem B439835 : Blo 439778 439835 := bstep (se 1 (by rfl) ⟨329876, by rfl⟩ : syracuseStep 439835 = 659753) B659753
theorem B1488509 : Blo 439778 1488509 := bstep (se 3 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 1488509 = 558191) B558191
theorem B3356315 : Blo 439778 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B997019 : Blo 439778 997019 := bstep (se 1 (by rfl) ⟨747764, by rfl⟩ : syracuseStep 997019 = 1495529) B1495529
theorem B440015 : Blo 439778 440015 := bstep (se 1 (by rfl) ⟨330011, by rfl⟩ : syracuseStep 440015 = 660023) B660023
theorem B10860293 : Blo 439778 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B997217 : Blo 439778 997217 := bstep (se 2 (by rfl) ⟨373956, by rfl⟩ : syracuseStep 997217 = 747913) B747913
theorem B440255 : Blo 439778 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B23017445 : Blo 439778 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B604139 : Blo 439778 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B440383 : Blo 439778 440383 := bstep (se 1 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 440383 = 660575) B660575
theorem B440423 : Blo 439778 440423 := bstep (se 1 (by rfl) ⟨330317, by rfl⟩ : syracuseStep 440423 = 660635) B660635
theorem B440879 : Blo 439778 440879 := bstep (se 1 (by rfl) ⟨330659, by rfl⟩ : syracuseStep 440879 = 661319) B661319
theorem B1260157 : Blo 439778 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B15743747 : Blo 439778 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B670655 : Blo 439778 670655 := bstep (se 1 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 670655 = 1005983) B1005983
theorem B441279 : Blo 439778 441279 := bstep (se 1 (by rfl) ⟨330959, by rfl⟩ : syracuseStep 441279 = 661919) B661919
theorem B441327 : Blo 439778 441327 := bstep (se 1 (by rfl) ⟨330995, by rfl⟩ : syracuseStep 441327 = 661991) B661991
theorem B835039 : Blo 439778 835039 := bstep (se 1 (by rfl) ⟨626279, by rfl⟩ : syracuseStep 835039 = 1252559) B1252559
theorem B441823 : Blo 439778 441823 := bstep (se 1 (by rfl) ⟨331367, by rfl⟩ : syracuseStep 441823 = 662735) B662735
theorem B441903 : Blo 439778 441903 := bstep (se 1 (by rfl) ⟨331427, by rfl⟩ : syracuseStep 441903 = 662855) B662855
theorem B1130057 : Blo 439778 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B2244185 : Blo 439778 2244185 := bstep (se 2 (by rfl) ⟨841569, by rfl⟩ : syracuseStep 2244185 = 1683139) B1683139
theorem B442011 : Blo 439778 442011 := bstep (se 1 (by rfl) ⟨331508, by rfl⟩ : syracuseStep 442011 = 663017) B663017
theorem B1261307 : Blo 439778 1261307 := bstep (se 1 (by rfl) ⟨945980, by rfl⟩ : syracuseStep 1261307 = 1891961) B1891961
theorem B442107 : Blo 439778 442107 := bstep (se 1 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 442107 = 663161) B663161
theorem B5652301 : Blo 439778 5652301 := bstep (se 3 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 5652301 = 2119613) B2119613
theorem B442271 : Blo 439778 442271 := bstep (se 1 (by rfl) ⟨331703, by rfl⟩ : syracuseStep 442271 = 663407) B663407
theorem B1064951 : Blo 439778 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B3358745 : Blo 439778 3358745 := bstep (se 2 (by rfl) ⟨1259529, by rfl⟩ : syracuseStep 3358745 = 2519059) B2519059
theorem B5652665 : Blo 439778 5652665 := bstep (se 2 (by rfl) ⟨2119749, by rfl⟩ : syracuseStep 5652665 = 4239499) B4239499
theorem B442727 : Blo 439778 442727 := bstep (se 1 (by rfl) ⟨332045, by rfl⟩ : syracuseStep 442727 = 664091) B664091
theorem B442847 : Blo 439778 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B442855 : Blo 439778 442855 := bstep (se 1 (by rfl) ⟨332141, by rfl⟩ : syracuseStep 442855 = 664283) B664283
theorem B443131 : Blo 439778 443131 := bstep (se 1 (by rfl) ⟨332348, by rfl⟩ : syracuseStep 443131 = 664697) B664697
theorem B1491965 : Blo 439778 1491965 := bstep (se 3 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 1491965 = 559487) B559487
theorem B443711 : Blo 439778 443711 := bstep (se 1 (by rfl) ⟨332783, by rfl⟩ : syracuseStep 443711 = 665567) B665567
theorem B443719 : Blo 439778 443719 := bstep (se 1 (by rfl) ⟨332789, by rfl⟩ : syracuseStep 443719 = 665579) B665579
theorem B2245967 : Blo 439778 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B443751 : Blo 439778 443751 := bstep (se 1 (by rfl) ⟨332813, by rfl⟩ : syracuseStep 443751 = 665627) B665627
theorem B1492343 : Blo 439778 1492343 := bstep (se 1 (by rfl) ⟨1119257, by rfl⟩ : syracuseStep 1492343 = 2238515) B2238515
theorem B1263073 : Blo 439778 1263073 := bstep (se 2 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 1263073 = 947305) B947305
theorem B5031557 : Blo 439778 5031557 := bstep (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) B943417
theorem B1493423 : Blo 439778 1493423 := bstep (se 1 (by rfl) ⟨1120067, by rfl⟩ : syracuseStep 1493423 = 2240135) B2240135
theorem B707051 : Blo 439778 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B1591787 : Blo 439778 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B16927379 : Blo 439778 16927379 := bstep (se 1 (by rfl) ⟨12695534, by rfl⟩ : syracuseStep 16927379 = 25391069) B25391069
theorem B8276779 : Blo 439778 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B11226077 : Blo 439778 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B1494503 : Blo 439778 1494503 := bstep (se 1 (by rfl) ⟨1120877, by rfl⟩ : syracuseStep 1494503 = 2241755) B2241755
theorem B839983 : Blo 439778 839983 := bstep (se 1 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 839983 = 1259975) B1259975
theorem B840127 : Blo 439778 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B5362157 : Blo 439778 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B1495583 : Blo 439778 1495583 := bstep (se 1 (by rfl) ⟨1121687, by rfl⟩ : syracuseStep 1495583 = 2243375) B2243375
theorem B2839121 : Blo 439778 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B1496015 : Blo 439778 1496015 := bstep (se 1 (by rfl) ⟨1122011, by rfl⟩ : syracuseStep 1496015 = 2244023) B2244023
theorem B840955 : Blo 439778 840955 := bstep (se 1 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 840955 = 1261433) B1261433
theorem B2676023 : Blo 439778 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B1496393 : Blo 439778 1496393 := bstep (se 2 (by rfl) ⟨561147, by rfl⟩ : syracuseStep 1496393 = 1122295) B1122295
theorem B19355041 : Blo 439778 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B743465 : Blo 439778 743465 := bstep (se 2 (by rfl) ⟨278799, by rfl⟩ : syracuseStep 743465 = 557599) B557599
theorem B940103 : Blo 439778 940103 := bstep (se 1 (by rfl) ⟨705077, by rfl⟩ : syracuseStep 940103 = 1410155) B1410155
theorem B940223 : Blo 439778 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B18208961 : Blo 439778 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B2841095 : Blo 439778 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B744295 : Blo 439778 744295 := bstep (se 1 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 744295 = 1116443) B1116443
theorem B744511 : Blo 439778 744511 := bstep (se 1 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 744511 = 1116767) B1116767
theorem B3759695 : Blo 439778 3759695 := bstep (se 1 (by rfl) ⟨2819771, by rfl⟩ : syracuseStep 3759695 = 5639543) B5639543
theorem B942187 : Blo 439778 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B2515643 : Blo 439778 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B943007 : Blo 439778 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B1434539 : Blo 439778 1434539 := bstep (se 1 (by rfl) ⟨1075904, by rfl⟩ : syracuseStep 1434539 = 2151809) B2151809
theorem B2516143 : Blo 439778 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B746921 : Blo 439778 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B2386513 : Blo 439778 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B944777 : Blo 439778 944777 := bstep (se 2 (by rfl) ⟨354291, by rfl⟩ : syracuseStep 944777 = 708583) B708583
theorem B748345 : Blo 439778 748345 := bstep (se 2 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 748345 = 561259) B561259
theorem B1076219 : Blo 439778 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B3633547 : Blo 439778 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B1798793 : Blo 439778 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B2552485 : Blo 439778 2552485 := bstep (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) B478591
theorem B77591297 : Blo 439778 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B2553065 : Blo 439778 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B15332647 : Blo 439778 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2127343 : Blo 439778 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B7174979 : Blo 439778 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B2227175 : Blo 439778 2227175 := bstep (se 1 (by rfl) ⟨1670381, by rfl⟩ : syracuseStep 2227175 = 3340763) B3340763
theorem B1670777 : Blo 439778 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B3768443 : Blo 439778 3768443 := bstep (se 1 (by rfl) ⟨2826332, by rfl⟩ : syracuseStep 3768443 = 5652665) B5652665
theorem B4522439 : Blo 439778 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B10715753 : Blo 439778 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B2229281 : Blo 439778 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B7145135 : Blo 439778 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B3182017 : Blo 439778 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B495643 : Blo 439778 495643 := bstep (se 1 (by rfl) ⟨371732, by rfl⟩ : syracuseStep 495643 = 743465) B743465
theorem B7540775 : Blo 439778 7540775 := bstep (se 1 (by rfl) ⟨5655581, by rfl⟩ : syracuseStep 7540775 = 11311163) B11311163
theorem B626735 : Blo 439778 626735 := bstep (se 1 (by rfl) ⟨470051, by rfl⟩ : syracuseStep 626735 = 940103) B940103
theorem B626815 : Blo 439778 626815 := bstep (se 1 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 626815 = 940223) B940223
theorem B529183 : Blo 439778 529183 := bstep (se 1 (by rfl) ⟨396887, by rfl⟩ : syracuseStep 529183 = 793775) B793775
theorem B2233169 : Blo 439778 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B1611037 : Blo 439778 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B628393 : Blo 439778 628393 := bstep (se 2 (by rfl) ⟨235647, by rfl⟩ : syracuseStep 628393 = 471295) B471295
theorem B661223 : Blo 439778 661223 := bstep (se 1 (by rfl) ⟨495917, by rfl⟩ : syracuseStep 661223 = 991835) B991835
theorem B1119977 : Blo 439778 1119977 := bstep (se 2 (by rfl) ⟨419991, by rfl⟩ : syracuseStep 1119977 = 839983) B839983
theorem B1677095 : Blo 439778 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B1120169 : Blo 439778 1120169 := bstep (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) B840127
theorem B956359 : Blo 439778 956359 := bstep (se 1 (by rfl) ⟨717269, by rfl⟩ : syracuseStep 956359 = 1434539) B1434539
theorem B3348539 : Blo 439778 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B661607 : Blo 439778 661607 := bstep (se 1 (by rfl) ⟨496205, by rfl⟩ : syracuseStep 661607 = 992411) B992411
theorem B7280765 : Blo 439778 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B497947 : Blo 439778 497947 := bstep (se 1 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 497947 = 746921) B746921
theorem B662375 : Blo 439778 662375 := bstep (se 1 (by rfl) ⟨496781, by rfl⟩ : syracuseStep 662375 = 993563) B993563
theorem B662441 : Blo 439778 662441 := bstep (se 2 (by rfl) ⟨248415, by rfl⟩ : syracuseStep 662441 = 496831) B496831
theorem B990143 : Blo 439778 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B1121273 : Blo 439778 1121273 := bstep (se 2 (by rfl) ⟨420477, by rfl⟩ : syracuseStep 1121273 = 840955) B840955
theorem B629851 : Blo 439778 629851 := bstep (se 1 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 629851 = 944777) B944777
theorem B662633 : Blo 439778 662633 := bstep (se 2 (by rfl) ⟨248487, by rfl⟩ : syracuseStep 662633 = 496975) B496975
theorem B662825 : Blo 439778 662825 := bstep (se 2 (by rfl) ⟨248559, by rfl⟩ : syracuseStep 662825 = 497119) B497119
theorem B2694487 : Blo 439778 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B1056809 : Blo 439778 1056809 := bstep (se 2 (by rfl) ⟨396303, by rfl⟩ : syracuseStep 1056809 = 792607) B792607
theorem B663593 : Blo 439778 663593 := bstep (se 2 (by rfl) ⟨248847, by rfl⟩ : syracuseStep 663593 = 497695) B497695
theorem B663659 : Blo 439778 663659 := bstep (se 1 (by rfl) ⟨497744, by rfl⟩ : syracuseStep 663659 = 995489) B995489
theorem B663911 : Blo 439778 663911 := bstep (se 1 (by rfl) ⟨497933, by rfl⟩ : syracuseStep 663911 = 995867) B995867
theorem B2236895 : Blo 439778 2236895 := bstep (se 1 (by rfl) ⟨1677671, by rfl⟩ : syracuseStep 2236895 = 3355343) B3355343
theorem B664031 : Blo 439778 664031 := bstep (se 1 (by rfl) ⟨498023, by rfl⟩ : syracuseStep 664031 = 996047) B996047
theorem B1680209 : Blo 439778 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B1188823 : Blo 439778 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B664559 : Blo 439778 664559 := bstep (se 1 (by rfl) ⟨498419, by rfl⟩ : syracuseStep 664559 = 996839) B996839
theorem B992339 : Blo 439778 992339 := bstep (se 1 (by rfl) ⟨744254, by rfl⟩ : syracuseStep 992339 = 1488509) B1488509
theorem B2237543 : Blo 439778 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B664679 : Blo 439778 664679 := bstep (se 1 (by rfl) ⟨498509, by rfl⟩ : syracuseStep 664679 = 997019) B997019
theorem B992393 : Blo 439778 992393 := bstep (se 2 (by rfl) ⟨372147, by rfl⟩ : syracuseStep 992393 = 744295) B744295
theorem B664811 : Blo 439778 664811 := bstep (se 1 (by rfl) ⟨498608, by rfl⟩ : syracuseStep 664811 = 997217) B997217
theorem B15344963 : Blo 439778 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B992681 : Blo 439778 992681 := bstep (se 2 (by rfl) ⟨372255, by rfl⟩ : syracuseStep 992681 = 744511) B744511
theorem B10495831 : Blo 439778 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B1484783 : Blo 439778 1484783 := bstep (se 1 (by rfl) ⟨1113587, by rfl⟩ : syracuseStep 1484783 = 2227175) B2227175
theorem B1058953 : Blo 439778 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B2239163 : Blo 439778 2239163 := bstep (se 1 (by rfl) ⟨1679372, by rfl⟩ : syracuseStep 2239163 = 3358745) B3358745
theorem B1256249 : Blo 439778 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B1485647 : Blo 439778 1485647 := bstep (se 1 (by rfl) ⟨1114235, by rfl⟩ : syracuseStep 1485647 = 2228471) B2228471
theorem B502895 : Blo 439778 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B994643 : Blo 439778 994643 := bstep (se 1 (by rfl) ⟨745982, by rfl⟩ : syracuseStep 994643 = 1491965) B1491965
theorem B1486241 : Blo 439778 1486241 := bstep (se 2 (by rfl) ⟨557340, by rfl⟩ : syracuseStep 1486241 = 1114681) B1114681
theorem B3190265 : Blo 439778 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B994895 : Blo 439778 994895 := bstep (se 1 (by rfl) ⟨746171, by rfl⟩ : syracuseStep 994895 = 1492343) B1492343
theorem B3354371 : Blo 439778 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B14299085 : Blo 439778 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B3354857 : Blo 439778 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B995615 : Blo 439778 995615 := bstep (se 1 (by rfl) ⟨746711, by rfl⟩ : syracuseStep 995615 = 1493423) B1493423
theorem B471367 : Blo 439778 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B1061191 : Blo 439778 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B11284919 : Blo 439778 11284919 := bstep (se 1 (by rfl) ⟨8463689, by rfl⟩ : syracuseStep 11284919 = 16927379) B16927379
theorem B1683899 : Blo 439778 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B1684097 : Blo 439778 1684097 := bstep (se 2 (by rfl) ⟨631536, by rfl⟩ : syracuseStep 1684097 = 1263073) B1263073
theorem B7484051 : Blo 439778 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B206910125 : Blo 439778 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B1487699 : Blo 439778 1487699 := bstep (se 1 (by rfl) ⟨1115774, by rfl⟩ : syracuseStep 1487699 = 2231549) B2231549
theorem B2274131 : Blo 439778 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B996335 : Blo 439778 996335 := bstep (se 1 (by rfl) ⟨747251, by rfl⟩ : syracuseStep 996335 = 1494503) B1494503
theorem B997055 : Blo 439778 997055 := bstep (se 1 (by rfl) ⟨747791, by rfl⟩ : syracuseStep 997055 = 1495583) B1495583
theorem B997343 : Blo 439778 997343 := bstep (se 1 (by rfl) ⟨748007, by rfl⟩ : syracuseStep 997343 = 1496015) B1496015
theorem B440315 : Blo 439778 440315 := bstep (se 1 (by rfl) ⟨330236, by rfl⟩ : syracuseStep 440315 = 660473) B660473
theorem B440447 : Blo 439778 440447 := bstep (se 1 (by rfl) ⟨330335, by rfl⟩ : syracuseStep 440447 = 660671) B660671
theorem B1784015 : Blo 439778 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B997595 : Blo 439778 997595 := bstep (se 1 (by rfl) ⟨748196, by rfl⟩ : syracuseStep 997595 = 1496393) B1496393
theorem B440543 : Blo 439778 440543 := bstep (se 1 (by rfl) ⟨330407, by rfl⟩ : syracuseStep 440543 = 660815) B660815
theorem B440603 : Blo 439778 440603 := bstep (se 1 (by rfl) ⟨330452, by rfl⟩ : syracuseStep 440603 = 660905) B660905
theorem B440639 : Blo 439778 440639 := bstep (se 1 (by rfl) ⟨330479, by rfl⟩ : syracuseStep 440639 = 660959) B660959
theorem B440703 : Blo 439778 440703 := bstep (se 1 (by rfl) ⟨330527, by rfl⟩ : syracuseStep 440703 = 661055) B661055
theorem B997793 : Blo 439778 997793 := bstep (se 2 (by rfl) ⟨374172, by rfl⟩ : syracuseStep 997793 = 748345) B748345
theorem B441023 : Blo 439778 441023 := bstep (se 1 (by rfl) ⟨330767, by rfl⟩ : syracuseStep 441023 = 661535) B661535
theorem B1489643 : Blo 439778 1489643 := bstep (se 1 (by rfl) ⟨1117232, by rfl⟩ : syracuseStep 1489643 = 2234465) B2234465
theorem B5028641 : Blo 439778 5028641 := bstep (se 2 (by rfl) ⟨1885740, by rfl⟩ : syracuseStep 5028641 = 3771481) B3771481
theorem B12139307 : Blo 439778 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B441311 : Blo 439778 441311 := bstep (se 1 (by rfl) ⟨330983, by rfl⟩ : syracuseStep 441311 = 661967) B661967
theorem B441371 : Blo 439778 441371 := bstep (se 1 (by rfl) ⟨331028, by rfl⟩ : syracuseStep 441371 = 662057) B662057
theorem B441511 : Blo 439778 441511 := bstep (se 1 (by rfl) ⟨331133, by rfl⟩ : syracuseStep 441511 = 662267) B662267
theorem B441595 : Blo 439778 441595 := bstep (se 1 (by rfl) ⟨331196, by rfl⟩ : syracuseStep 441595 = 662393) B662393
theorem B13647113 : Blo 439778 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B1490399 : Blo 439778 1490399 := bstep (se 1 (by rfl) ⟨1117799, by rfl⟩ : syracuseStep 1490399 = 2235599) B2235599
theorem B1490561 : Blo 439778 1490561 := bstep (se 2 (by rfl) ⟨558960, by rfl⟩ : syracuseStep 1490561 = 1117921) B1117921
theorem B5684903 : Blo 439778 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B2506463 : Blo 439778 2506463 := bstep (se 1 (by rfl) ⟨1879847, by rfl⟩ : syracuseStep 2506463 = 3759695) B3759695
theorem B442095 : Blo 439778 442095 := bstep (se 1 (by rfl) ⟨331571, by rfl⟩ : syracuseStep 442095 = 663143) B663143
theorem B442203 : Blo 439778 442203 := bstep (se 1 (by rfl) ⟨331652, by rfl⟩ : syracuseStep 442203 = 663305) B663305
theorem B442351 : Blo 439778 442351 := bstep (se 1 (by rfl) ⟨331763, by rfl⟩ : syracuseStep 442351 = 663527) B663527
theorem B442431 : Blo 439778 442431 := bstep (se 1 (by rfl) ⟨331823, by rfl⟩ : syracuseStep 442431 = 663647) B663647
theorem B442471 : Blo 439778 442471 := bstep (se 1 (by rfl) ⟨331853, by rfl⟩ : syracuseStep 442471 = 663707) B663707
theorem B442527 : Blo 439778 442527 := bstep (se 1 (by rfl) ⟨331895, by rfl⟩ : syracuseStep 442527 = 663791) B663791
theorem B1491209 : Blo 439778 1491209 := bstep (se 2 (by rfl) ⟨559203, by rfl⟩ : syracuseStep 1491209 = 1118407) B1118407
theorem B442779 : Blo 439778 442779 := bstep (se 1 (by rfl) ⟨332084, by rfl⟩ : syracuseStep 442779 = 664169) B664169
theorem B442783 : Blo 439778 442783 := bstep (se 1 (by rfl) ⟨332087, by rfl⟩ : syracuseStep 442783 = 664175) B664175
theorem B1884647 : Blo 439778 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B836315 : Blo 439778 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B705257 : Blo 439778 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B443199 : Blo 439778 443199 := bstep (se 1 (by rfl) ⟨332399, by rfl⟩ : syracuseStep 443199 = 664799) B664799
theorem B443359 : Blo 439778 443359 := bstep (se 1 (by rfl) ⟨332519, by rfl⟩ : syracuseStep 443359 = 665039) B665039
theorem B443483 : Blo 439778 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B443519 : Blo 439778 443519 := bstep (se 1 (by rfl) ⟨332639, by rfl⟩ : syracuseStep 443519 = 665279) B665279
theorem B443623 : Blo 439778 443623 := bstep (se 1 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 443623 = 665435) B665435
theorem B43763095 : Blo 439778 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B1885673 : Blo 439778 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B25806721 : Blo 439778 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B2836457 : Blo 439778 2836457 := bstep (se 2 (by rfl) ⟨1063671, by rfl⟩ : syracuseStep 2836457 = 2127343) B2127343
theorem B1493153 : Blo 439778 1493153 := bstep (se 2 (by rfl) ⟨559932, by rfl⟩ : syracuseStep 1493153 = 1119865) B1119865
theorem B575899 : Blo 439778 575899 := bstep (se 1 (by rfl) ⟨431924, by rfl⟩ : syracuseStep 575899 = 863849) B863849
theorem B1199195 : Blo 439778 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B51433865 : Blo 439778 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B447103 : Blo 439778 447103 := bstep (se 1 (by rfl) ⟨335327, by rfl⟩ : syracuseStep 447103 = 670655) B670655
theorem B1496123 : Blo 439778 1496123 := bstep (se 1 (by rfl) ⟨1122092, by rfl⟩ : syracuseStep 1496123 = 2244185) B2244185
theorem B840871 : Blo 439778 840871 := bstep (se 1 (by rfl) ⟨630653, by rfl⟩ : syracuseStep 840871 = 1261307) B1261307
theorem B709967 : Blo 439778 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B939539 : Blo 439778 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B743087 : Blo 439778 743087 := bstep (se 1 (by rfl) ⟨557315, by rfl⟩ : syracuseStep 743087 = 1114631) B1114631
theorem B30627841 : Blo 439778 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B743647 : Blo 439778 743647 := bstep (se 1 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 743647 = 1115471) B1115471
theorem B1497311 : Blo 439778 1497311 := bstep (se 1 (by rfl) ⟨1122983, by rfl⟩ : syracuseStep 1497311 = 2245967) B2245967
theorem B744079 : Blo 439778 744079 := bstep (se 1 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 744079 = 1116119) B1116119
theorem B7527653 : Blo 439778 7527653 := bstep (se 4 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 7527653 = 1411435) B1411435
theorem B3366521 : Blo 439778 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B2514685 : Blo 439778 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B2383789 : Blo 439778 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B3760343 : Blo 439778 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B745807 : Blo 439778 745807 := bstep (se 1 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 745807 = 1118711) B1118711
theorem B1892747 : Blo 439778 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B11035705 : Blo 439778 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B11363651 : Blo 439778 11363651 := bstep (se 1 (by rfl) ⟨8522738, by rfl⟩ : syracuseStep 11363651 = 17045477) B17045477
theorem B1894063 : Blo 439778 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B4844729 : Blo 439778 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B2518559 : Blo 439778 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B3403313 : Blo 439778 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B20443529 : Blo 439778 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B717479 : Blo 439778 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B3765467 : Blo 439778 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B2389583 : Blo 439778 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B947791 : Blo 439778 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B14383169 : Blo 439778 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B1702043 : Blo 439778 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B7240195 : Blo 439778 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B4783319 : Blo 439778 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B1113385 : Blo 439778 1113385 := bstep (se 2 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 1113385 = 835039) B835039
theorem B753371 : Blo 439778 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B1113851 : Blo 439778 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B7536401 : Blo 439778 7536401 := bstep (se 2 (by rfl) ⟨2826150, by rfl⟩ : syracuseStep 7536401 = 5652301) B5652301
theorem B1671293 : Blo 439778 1671293 := bstep (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) B626735
theorem B557543 : Blo 439778 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B12059837 : Blo 439778 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B14714273 : Blo 439778 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B28575341 : Blo 439778 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B2525417 : Blo 439778 2525417 := bstep (se 2 (by rfl) ⟨947031, by rfl⟩ : syracuseStep 2525417 = 1894063) B1894063
theorem B13994441 : Blo 439778 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B34408961 : Blo 439778 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B1411937 : Blo 439778 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B495391 : Blo 439778 495391 := bstep (se 1 (by rfl) ⟨371543, by rfl⟩ : syracuseStep 495391 = 743087) B743087
theorem B1118063 : Blo 439778 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B2232359 : Blo 439778 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B4853843 : Blo 439778 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B2822309 : Blo 439778 2822309 := bstep (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) B529183
theorem B660095 : Blo 439778 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B5018435 : Blo 439778 5018435 := bstep (se 1 (by rfl) ⟨3763826, by rfl⟩ : syracuseStep 5018435 = 7527653) B7527653
theorem B660857 : Blo 439778 660857 := bstep (se 2 (by rfl) ⟨247821, by rfl⟩ : syracuseStep 660857 = 495643) B495643
theorem B628489 : Blo 439778 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B1414921 : Blo 439778 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B1120139 : Blo 439778 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B661559 : Blo 439778 661559 := bstep (se 1 (by rfl) ⟨496169, by rfl⟩ : syracuseStep 661559 = 992339) B992339
theorem B661595 : Blo 439778 661595 := bstep (se 1 (by rfl) ⟨496196, by rfl⟩ : syracuseStep 661595 = 992393) B992393
theorem B10229975 : Blo 439778 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B7575767 : Blo 439778 7575767 := bstep (se 1 (by rfl) ⟨5681825, by rfl⟩ : syracuseStep 7575767 = 11363651) B11363651
theorem B661787 : Blo 439778 661787 := bstep (se 1 (by rfl) ⟨496340, by rfl⟩ : syracuseStep 661787 = 992681) B992681
theorem B989855 : Blo 439778 989855 := bstep (se 1 (by rfl) ⟨742391, by rfl⟩ : syracuseStep 989855 = 1484783) B1484783
theorem B1121161 : Blo 439778 1121161 := bstep (se 2 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 1121161 = 840871) B840871
theorem B990431 : Blo 439778 990431 := bstep (se 1 (by rfl) ⟨742823, by rfl⟩ : syracuseStep 990431 = 1485647) B1485647
theorem B3349997 : Blo 439778 3349997 := bstep (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) B1256249
theorem B663095 : Blo 439778 663095 := bstep (se 1 (by rfl) ⟨497321, by rfl⟩ : syracuseStep 663095 = 994643) B994643
theorem B990827 : Blo 439778 990827 := bstep (se 1 (by rfl) ⟨743120, by rfl⟩ : syracuseStep 990827 = 1486241) B1486241
theorem B1679039 : Blo 439778 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B2268875 : Blo 439778 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B663263 : Blo 439778 663263 := bstep (se 1 (by rfl) ⟨497447, by rfl⟩ : syracuseStep 663263 = 994895) B994895
theorem B2236247 : Blo 439778 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B40837121 : Blo 439778 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B2236571 : Blo 439778 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B663743 : Blo 439778 663743 := bstep (se 1 (by rfl) ⟨497807, by rfl⟩ : syracuseStep 663743 = 995615) B995615
theorem B1122599 : Blo 439778 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B991529 : Blo 439778 991529 := bstep (se 2 (by rfl) ⟨371823, by rfl⟩ : syracuseStep 991529 = 743647) B743647
theorem B663929 : Blo 439778 663929 := bstep (se 2 (by rfl) ⟨248973, by rfl⟩ : syracuseStep 663929 = 497947) B497947
theorem B5054885 : Blo 439778 5054885 := bstep (se 4 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 5054885 = 947791) B947791
theorem B1122731 : Blo 439778 1122731 := bstep (se 1 (by rfl) ⟨842048, by rfl⟩ : syracuseStep 1122731 = 1684097) B1684097
theorem B4989367 : Blo 439778 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B12919277 : Blo 439778 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B991799 : Blo 439778 991799 := bstep (se 1 (by rfl) ⟨743849, by rfl⟩ : syracuseStep 991799 = 1487699) B1487699
theorem B1516087 : Blo 439778 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B664223 : Blo 439778 664223 := bstep (se 1 (by rfl) ⟨498167, by rfl⟩ : syracuseStep 664223 = 996335) B996335
theorem B992105 : Blo 439778 992105 := bstep (se 2 (by rfl) ⟨372039, by rfl⟩ : syracuseStep 992105 = 744079) B744079
theorem B664703 : Blo 439778 664703 := bstep (se 1 (by rfl) ⟨498527, by rfl⟩ : syracuseStep 664703 = 997055) B997055
theorem B664895 : Blo 439778 664895 := bstep (se 1 (by rfl) ⟨498671, by rfl⟩ : syracuseStep 664895 = 997343) B997343
theorem B1189343 : Blo 439778 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B665063 : Blo 439778 665063 := bstep (se 1 (by rfl) ⟨498797, by rfl⟩ : syracuseStep 665063 = 997595) B997595
theorem B665195 : Blo 439778 665195 := bstep (se 1 (by rfl) ⟨498896, by rfl⟩ : syracuseStep 665195 = 997793) B997793
theorem B1484513 : Blo 439778 1484513 := bstep (se 2 (by rfl) ⟨556692, by rfl⟩ : syracuseStep 1484513 = 1113385) B1113385
theorem B993095 : Blo 439778 993095 := bstep (se 1 (by rfl) ⟨744821, by rfl⟩ : syracuseStep 993095 = 1489643) B1489643
theorem B3352427 : Blo 439778 3352427 := bstep (se 1 (by rfl) ⟨2514320, by rfl⟩ : syracuseStep 3352427 = 5028641) B5028641
theorem B3188879 : Blo 439778 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B993599 : Blo 439778 993599 := bstep (se 1 (by rfl) ⟨745199, by rfl⟩ : syracuseStep 993599 = 1490399) B1490399
theorem B3352913 : Blo 439778 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B993707 : Blo 439778 993707 := bstep (se 1 (by rfl) ⟨745280, by rfl⟩ : syracuseStep 993707 = 1490561) B1490561
theorem B502247 : Blo 439778 502247 := bstep (se 1 (by rfl) ⟨376685, by rfl⟩ : syracuseStep 502247 = 753371) B753371
theorem B5024267 : Blo 439778 5024267 := bstep (se 1 (by rfl) ⟨3768200, by rfl⟩ : syracuseStep 5024267 = 7536401) B7536401
theorem B994139 : Blo 439778 994139 := bstep (se 1 (by rfl) ⟨745604, by rfl⟩ : syracuseStep 994139 = 1491209) B1491209
theorem B994409 : Blo 439778 994409 := bstep (se 2 (by rfl) ⟨372903, by rfl⟩ : syracuseStep 994409 = 745807) B745807
theorem B470171 : Blo 439778 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B1486187 : Blo 439778 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B1257115 : Blo 439778 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B4763423 : Blo 439778 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B5025725 : Blo 439778 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B1585097 : Blo 439778 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B995435 : Blo 439778 995435 := bstep (se 1 (by rfl) ⟨746576, by rfl⟩ : syracuseStep 995435 = 1493153) B1493153
theorem B799463 : Blo 439778 799463 := bstep (se 1 (by rfl) ⟨599597, by rfl⟩ : syracuseStep 799463 = 1199195) B1199195
theorem B5027183 : Blo 439778 5027183 := bstep (se 1 (by rfl) ⟨3770387, by rfl⟩ : syracuseStep 5027183 = 7540775) B7540775
theorem B34289243 : Blo 439778 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B1488779 : Blo 439778 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B997415 : Blo 439778 997415 := bstep (se 1 (by rfl) ⟨748061, by rfl⟩ : syracuseStep 997415 = 1496123) B1496123
theorem B473311 : Blo 439778 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B440815 : Blo 439778 440815 := bstep (se 1 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 440815 = 661223) B661223
theorem B2505437 : Blo 439778 2505437 := bstep (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) B939539
theorem B441071 : Blo 439778 441071 := bstep (se 1 (by rfl) ⟨330803, by rfl⟩ : syracuseStep 441071 = 661607) B661607
theorem B998207 : Blo 439778 998207 := bstep (se 1 (by rfl) ⟨748655, by rfl⟩ : syracuseStep 998207 = 1497311) B1497311
theorem B441583 : Blo 439778 441583 := bstep (se 1 (by rfl) ⟨331187, by rfl⟩ : syracuseStep 441583 = 662375) B662375
theorem B4242689 : Blo 439778 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B441627 : Blo 439778 441627 := bstep (se 1 (by rfl) ⟨331220, by rfl⟩ : syracuseStep 441627 = 662441) B662441
theorem B441755 : Blo 439778 441755 := bstep (se 1 (by rfl) ⟨331316, by rfl⟩ : syracuseStep 441755 = 662633) B662633
theorem B441883 : Blo 439778 441883 := bstep (se 1 (by rfl) ⟨331412, by rfl⟩ : syracuseStep 441883 = 662825) B662825
theorem B2244347 : Blo 439778 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B704539 : Blo 439778 704539 := bstep (se 1 (by rfl) ⟨528404, by rfl⟩ : syracuseStep 704539 = 1056809) B1056809
theorem B442395 : Blo 439778 442395 := bstep (se 1 (by rfl) ⟨331796, by rfl⟩ : syracuseStep 442395 = 663593) B663593
theorem B442439 : Blo 439778 442439 := bstep (se 1 (by rfl) ⟨331829, by rfl⟩ : syracuseStep 442439 = 663659) B663659
theorem B2506895 : Blo 439778 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B835753 : Blo 439778 835753 := bstep (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) B626815
theorem B442607 : Blo 439778 442607 := bstep (se 1 (by rfl) ⟨331955, by rfl⟩ : syracuseStep 442607 = 663911) B663911
theorem B1261831 : Blo 439778 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B1491263 : Blo 439778 1491263 := bstep (se 1 (by rfl) ⟨1118447, by rfl⟩ : syracuseStep 1491263 = 2236895) B2236895
theorem B442687 : Blo 439778 442687 := bstep (se 1 (by rfl) ⟨332015, by rfl⟩ : syracuseStep 442687 = 664031) B664031
theorem B443039 : Blo 439778 443039 := bstep (se 1 (by rfl) ⟨332279, by rfl⟩ : syracuseStep 443039 = 664559) B664559
theorem B1491695 : Blo 439778 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B443119 : Blo 439778 443119 := bstep (se 1 (by rfl) ⟨332339, by rfl⟩ : syracuseStep 443119 = 664679) B664679
theorem B443207 : Blo 439778 443207 := bstep (se 1 (by rfl) ⟨332405, by rfl⟩ : syracuseStep 443207 = 664811) B664811
theorem B2148049 : Blo 439778 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1492775 : Blo 439778 1492775 := bstep (se 1 (by rfl) ⟨1119581, by rfl⟩ : syracuseStep 1492775 = 2239163) B2239163
theorem B837857 : Blo 439778 837857 := bstep (se 2 (by rfl) ⟨314196, by rfl⟩ : syracuseStep 837857 = 628393) B628393
theorem B7523279 : Blo 439778 7523279 := bstep (se 1 (by rfl) ⟨5642459, by rfl⟩ : syracuseStep 7523279 = 11284919) B11284919
theorem B478319 : Blo 439778 478319 := bstep (se 1 (by rfl) ⟨358739, by rfl⟩ : syracuseStep 478319 = 717479) B717479
theorem B137940083 : Blo 439778 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B9653593 : Blo 439778 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B2510311 : Blo 439778 2510311 := bstep (se 1 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 2510311 = 3765467) B3765467
theorem B1593055 : Blo 439778 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B9588779 : Blo 439778 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B1134695 : Blo 439778 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B839801 : Blo 439778 839801 := bstep (se 2 (by rfl) ⟨314925, by rfl⟩ : syracuseStep 839801 = 629851) B629851
theorem B3592649 : Blo 439778 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B9098075 : Blo 439778 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B3789935 : Blo 439778 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B742567 : Blo 439778 742567 := bstep (se 1 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 742567 = 1113851) B1113851
theorem B2512295 : Blo 439778 2512295 := bstep (se 1 (by rfl) ⟨1884221, by rfl⟩ : syracuseStep 2512295 = 3768443) B3768443
theorem B1890971 : Blo 439778 1890971 := bstep (se 1 (by rfl) ⟨1418228, by rfl⟩ : syracuseStep 1890971 = 2836457) B2836457
theorem B58350793 : Blo 439778 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B3071461 : Blo 439778 3071461 := bstep (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) B575899
theorem B2384549 : Blo 439778 2384549 := bstep (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) B447103
theorem B746651 : Blo 439778 746651 := bstep (se 1 (by rfl) ⟨559988, by rfl⟩ : syracuseStep 746651 = 1119977) B1119977
theorem B746779 : Blo 439778 746779 := bstep (se 1 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 746779 = 1120169) B1120169
theorem B747515 : Blo 439778 747515 := bstep (se 1 (by rfl) ⟨560636, by rfl⟩ : syracuseStep 747515 = 1121273) B1121273
theorem B2126843 : Blo 439778 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B1275145 : Blo 439778 1275145 := bstep (se 2 (by rfl) ⟨478179, by rfl⟩ : syracuseStep 1275145 = 956359) B956359
theorem B9532723 : Blo 439778 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B13629019 : Blo 439778 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B1341053 : Blo 439778 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B8092871 : Blo 439778 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B1670975 : Blo 439778 1670975 := bstep (se 1 (by rfl) ⟨1253231, by rfl⟩ : syracuseStep 1670975 = 2506463) B2506463
theorem B3178385 : Blo 439778 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B1114195 : Blo 439778 1114195 := bstep (se 1 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 1114195 = 1671293) B1671293
theorem B1671263 : Blo 439778 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B1114337 : Blo 439778 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B6652489 : Blo 439778 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B558571 : Blo 439778 558571 := bstep (se 1 (by rfl) ⟨418928, by rfl⟩ : syracuseStep 558571 = 837857) B837857
theorem B22939307 : Blo 439778 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B5015519 : Blo 439778 5015519 := bstep (se 1 (by rfl) ⟨3761639, by rfl⟩ : syracuseStep 5015519 = 7523279) B7523279
theorem B6392519 : Blo 439778 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B756463 : Blo 439778 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B559867 : Blo 439778 559867 := bstep (se 1 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 559867 = 839801) B839801
theorem B2395099 : Blo 439778 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B3345623 : Blo 439778 3345623 := bstep (se 1 (by rfl) ⟨2509217, by rfl⟩ : syracuseStep 3345623 = 5018435) B5018435
theorem B6065383 : Blo 439778 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B2526623 : Blo 439778 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B1674863 : Blo 439778 1674863 := bstep (se 1 (by rfl) ⟨1256147, by rfl⟩ : syracuseStep 1674863 = 2512295) B2512295
theorem B6819983 : Blo 439778 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B5050511 : Blo 439778 5050511 := bstep (se 1 (by rfl) ⟨3787883, by rfl⟩ : syracuseStep 5050511 = 7575767) B7575767
theorem B659903 : Blo 439778 659903 := bstep (se 1 (by rfl) ⟨494927, by rfl⟩ : syracuseStep 659903 = 989855) B989855
theorem B3347081 : Blo 439778 3347081 := bstep (se 2 (by rfl) ⟨1255155, by rfl⟩ : syracuseStep 3347081 = 2510311) B2510311
theorem B660287 : Blo 439778 660287 := bstep (se 1 (by rfl) ⟨495215, by rfl⟩ : syracuseStep 660287 = 990431) B990431
theorem B1676153 : Blo 439778 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B2233331 : Blo 439778 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B660521 : Blo 439778 660521 := bstep (se 2 (by rfl) ⟨247695, by rfl⟩ : syracuseStep 660521 = 495391) B495391
theorem B660551 : Blo 439778 660551 := bstep (se 1 (by rfl) ⟨495413, by rfl⟩ : syracuseStep 660551 = 990827) B990827
theorem B1119359 : Blo 439778 1119359 := bstep (se 1 (by rfl) ⟨839519, by rfl⟩ : syracuseStep 1119359 = 1679039) B1679039
theorem B1512583 : Blo 439778 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B661019 : Blo 439778 661019 := bstep (se 1 (by rfl) ⟨495764, by rfl⟩ : syracuseStep 661019 = 991529) B991529
theorem B661199 : Blo 439778 661199 := bstep (se 1 (by rfl) ⟨495899, by rfl⟩ : syracuseStep 661199 = 991799) B991799
theorem B661403 : Blo 439778 661403 := bstep (se 1 (by rfl) ⟨496052, by rfl⟩ : syracuseStep 661403 = 992105) B992105
theorem B497767 : Blo 439778 497767 := bstep (se 1 (by rfl) ⟨373325, by rfl⟩ : syracuseStep 497767 = 746651) B746651
theorem B792895 : Blo 439778 792895 := bstep (se 1 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 792895 = 1189343) B1189343
theorem B989675 : Blo 439778 989675 := bstep (se 1 (by rfl) ⟨742256, by rfl⟩ : syracuseStep 989675 = 1484513) B1484513
theorem B662063 : Blo 439778 662063 := bstep (se 1 (by rfl) ⟨496547, by rfl⟩ : syracuseStep 662063 = 993095) B993095
theorem B2234951 : Blo 439778 2234951 := bstep (se 1 (by rfl) ⟨1676213, by rfl⟩ : syracuseStep 2234951 = 3352427) B3352427
theorem B498343 : Blo 439778 498343 := bstep (se 1 (by rfl) ⟨373757, by rfl⟩ : syracuseStep 498343 = 747515) B747515
theorem B662399 : Blo 439778 662399 := bstep (se 1 (by rfl) ⟨496799, by rfl⟩ : syracuseStep 662399 = 993599) B993599
theorem B990089 : Blo 439778 990089 := bstep (se 2 (by rfl) ⟨371283, by rfl⟩ : syracuseStep 990089 = 742567) B742567
theorem B2235275 : Blo 439778 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B662471 : Blo 439778 662471 := bstep (se 1 (by rfl) ⟨496853, by rfl⟩ : syracuseStep 662471 = 993707) B993707
theorem B3349511 : Blo 439778 3349511 := bstep (se 1 (by rfl) ⟨2512133, by rfl⟩ : syracuseStep 3349511 = 5024267) B5024267
theorem B662759 : Blo 439778 662759 := bstep (se 1 (by rfl) ⟨497069, by rfl⟩ : syracuseStep 662759 = 994139) B994139
theorem B662939 : Blo 439778 662939 := bstep (se 1 (by rfl) ⟨497204, by rfl⟩ : syracuseStep 662939 = 994409) B994409
theorem B990791 : Blo 439778 990791 := bstep (se 1 (by rfl) ⟨743093, by rfl⟩ : syracuseStep 990791 = 1486187) B1486187
theorem B3350483 : Blo 439778 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B1056731 : Blo 439778 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B663623 : Blo 439778 663623 := bstep (se 1 (by rfl) ⟨497717, by rfl⟩ : syracuseStep 663623 = 995435) B995435
theorem B631081 : Blo 439778 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B1253789 : Blo 439778 1253789 := bstep (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) B470171
theorem B532975 : Blo 439778 532975 := bstep (se 1 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 532975 = 799463) B799463
theorem B1417895 : Blo 439778 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B3351455 : Blo 439778 3351455 := bstep (se 1 (by rfl) ⟨2513591, by rfl⟩ : syracuseStep 3351455 = 5027183) B5027183
theorem B894035 : Blo 439778 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B992519 : Blo 439778 992519 := bstep (se 1 (by rfl) ⟨744389, by rfl⟩ : syracuseStep 992519 = 1488779) B1488779
theorem B664943 : Blo 439778 664943 := bstep (se 1 (by rfl) ⟨498707, by rfl⟩ : syracuseStep 664943 = 997415) B997415
theorem B3351941 : Blo 439778 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B77801057 : Blo 439778 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B665471 : Blo 439778 665471 := bstep (se 1 (by rfl) ⟨499103, by rfl⟩ : syracuseStep 665471 = 998207) B998207
theorem B2828459 : Blo 439778 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B994175 : Blo 439778 994175 := bstep (se 1 (by rfl) ⟨745631, by rfl⟩ : syracuseStep 994175 = 1491263) B1491263
theorem B1682441 : Blo 439778 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B994463 : Blo 439778 994463 := bstep (se 1 (by rfl) ⟨745847, by rfl⟩ : syracuseStep 994463 = 1491695) B1491695
theorem B8039891 : Blo 439778 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B9809515 : Blo 439778 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B19050227 : Blo 439778 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B995183 : Blo 439778 995183 := bstep (se 1 (by rfl) ⟨746387, by rfl⟩ : syracuseStep 995183 = 1492775) B1492775
theorem B1486781 : Blo 439778 1486781 := bstep (se 3 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 1486781 = 557543) B557543
theorem B1683611 : Blo 439778 1683611 := bstep (se 1 (by rfl) ⟨1262708, by rfl⟩ : syracuseStep 1683611 = 2525417) B2525417
theorem B995705 : Blo 439778 995705 := bstep (se 2 (by rfl) ⟨373389, by rfl⟩ : syracuseStep 995705 = 746779) B746779
theorem B91960055 : Blo 439778 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B2864065 : Blo 439778 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1488239 : Blo 439778 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B1881539 : Blo 439778 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B440063 : Blo 439778 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B440571 : Blo 439778 440571 := bstep (se 1 (by rfl) ⟨330428, by rfl⟩ : syracuseStep 440571 = 660857) B660857
theorem B441039 : Blo 439778 441039 := bstep (se 1 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 441039 = 661559) B661559
theorem B441063 : Blo 439778 441063 := bstep (se 1 (by rfl) ⟨330797, by rfl⟩ : syracuseStep 441063 = 661595) B661595
theorem B441191 : Blo 439778 441191 := bstep (se 1 (by rfl) ⟨330893, by rfl⟩ : syracuseStep 441191 = 661787) B661787
theorem B1260647 : Blo 439778 1260647 := bstep (se 1 (by rfl) ⟨945485, by rfl⟩ : syracuseStep 1260647 = 1890971) B1890971
theorem B442063 : Blo 439778 442063 := bstep (se 1 (by rfl) ⟨331547, by rfl⟩ : syracuseStep 442063 = 663095) B663095
theorem B442175 : Blo 439778 442175 := bstep (se 1 (by rfl) ⟨331631, by rfl⟩ : syracuseStep 442175 = 663263) B663263
theorem B1490831 : Blo 439778 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B1491047 : Blo 439778 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B442495 : Blo 439778 442495 := bstep (se 1 (by rfl) ⟨331871, by rfl⟩ : syracuseStep 442495 = 663743) B663743
theorem B442619 : Blo 439778 442619 := bstep (se 1 (by rfl) ⟨331964, by rfl⟩ : syracuseStep 442619 = 663929) B663929
theorem B442815 : Blo 439778 442815 := bstep (se 1 (by rfl) ⟨332111, by rfl⟩ : syracuseStep 442815 = 664223) B664223
theorem B1589699 : Blo 439778 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B443135 : Blo 439778 443135 := bstep (se 1 (by rfl) ⟨332351, by rfl⟩ : syracuseStep 443135 = 664703) B664703
theorem B443263 : Blo 439778 443263 := bstep (se 1 (by rfl) ⟨332447, by rfl⟩ : syracuseStep 443263 = 664895) B664895
theorem B443375 : Blo 439778 443375 := bstep (se 1 (by rfl) ⟨332531, by rfl⟩ : syracuseStep 443375 = 665063) B665063
theorem B443463 : Blo 439778 443463 := bstep (se 1 (by rfl) ⟨332597, by rfl⟩ : syracuseStep 443463 = 665195) B665195
theorem B6800773 : Blo 439778 6800773 := bstep (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) B1275145
theorem B18172025 : Blo 439778 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1886561 : Blo 439778 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B22859495 : Blo 439778 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B1494881 : Blo 439778 1494881 := bstep (se 2 (by rfl) ⟨560580, by rfl⟩ : syracuseStep 1494881 = 1121161) B1121161
theorem B5395247 : Blo 439778 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B1496231 : Blo 439778 1496231 := bstep (se 1 (by rfl) ⟨1122173, by rfl⟩ : syracuseStep 1496231 = 2244347) B2244347
theorem B2118923 : Blo 439778 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B939385 : Blo 439778 939385 := bstep (se 2 (by rfl) ⟨352269, by rfl⟩ : syracuseStep 939385 = 704539) B704539
theorem B2021449 : Blo 439778 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B9329627 : Blo 439778 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B941291 : Blo 439778 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B745375 : Blo 439778 745375 := bstep (se 1 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 745375 = 1118063) B1118063
theorem B3235895 : Blo 439778 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B746759 : Blo 439778 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B12871457 : Blo 439778 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B2124073 : Blo 439778 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B27224747 : Blo 439778 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B748399 : Blo 439778 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B3369923 : Blo 439778 3369923 := bstep (se 1 (by rfl) ⟨2527442, by rfl⟩ : syracuseStep 3369923 = 5054885) B5054885
theorem B748487 : Blo 439778 748487 := bstep (se 1 (by rfl) ⟨561365, by rfl⟩ : syracuseStep 748487 = 1122731) B1122731
theorem B8612851 : Blo 439778 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B1339325 : Blo 439778 1339325 := bstep (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) B502247
theorem B2125919 : Blo 439778 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B12710297 : Blo 439778 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B3175615 : Blo 439778 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B1275517 : Blo 439778 1275517 := bstep (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) B478319
theorem B1670291 : Blo 439778 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B4095281 : Blo 439778 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B1113983 : Blo 439778 1113983 := bstep (se 1 (by rfl) ⟨835487, by rfl⟩ : syracuseStep 1113983 = 1670975) B1670975
theorem B1114175 : Blo 439778 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B3343679 : Blo 439778 3343679 := bstep (se 1 (by rfl) ⟨2507759, by rfl⟩ : syracuseStep 3343679 = 5015519) B5015519
theorem B4261679 : Blo 439778 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B2230415 : Blo 439778 2230415 := bstep (se 1 (by rfl) ⟨1672811, by rfl⟩ : syracuseStep 2230415 = 3345623) B3345623
theorem B1116575 : Blo 439778 1116575 := bstep (se 1 (by rfl) ⟨837431, by rfl⟩ : syracuseStep 1116575 = 1674863) B1674863
theorem B15239663 : Blo 439778 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B2231387 : Blo 439778 2231387 := bstep (se 1 (by rfl) ⟨1673540, by rfl⟩ : syracuseStep 2231387 = 3347081) B3347081
theorem B1117435 : Blo 439778 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B1412615 : Blo 439778 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B659783 : Blo 439778 659783 := bstep (se 1 (by rfl) ⟨494837, by rfl⟩ : syracuseStep 659783 = 989675) B989675
theorem B660059 : Blo 439778 660059 := bstep (se 1 (by rfl) ⟨495044, by rfl⟩ : syracuseStep 660059 = 990089) B990089
theorem B2233007 : Blo 439778 2233007 := bstep (se 1 (by rfl) ⟨1674755, by rfl⟩ : syracuseStep 2233007 = 3349511) B3349511
theorem B627527 : Blo 439778 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B660527 : Blo 439778 660527 := bstep (se 1 (by rfl) ⟨495395, by rfl⟩ : syracuseStep 660527 = 990791) B990791
theorem B2233655 : Blo 439778 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B2234303 : Blo 439778 2234303 := bstep (se 1 (by rfl) ⟨1675727, by rfl⟩ : syracuseStep 2234303 = 3351455) B3351455
theorem B8067109 : Blo 439778 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B661679 : Blo 439778 661679 := bstep (se 1 (by rfl) ⟨496259, by rfl⟩ : syracuseStep 661679 = 992519) B992519
theorem B497839 : Blo 439778 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B2234627 : Blo 439778 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B4234153 : Blo 439778 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B1252513 : Blo 439778 1252513 := bstep (se 2 (by rfl) ⟨469692, by rfl⟩ : syracuseStep 1252513 = 939385) B939385
theorem B662783 : Blo 439778 662783 := bstep (se 1 (by rfl) ⟨497087, by rfl⟩ : syracuseStep 662783 = 994175) B994175
theorem B498991 : Blo 439778 498991 := bstep (se 1 (by rfl) ⟨374243, by rfl⟩ : syracuseStep 498991 = 748487) B748487
theorem B1121627 : Blo 439778 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B662975 : Blo 439778 662975 := bstep (se 1 (by rfl) ⟨497231, by rfl⟩ : syracuseStep 662975 = 994463) B994463
theorem B24879005 : Blo 439778 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B663455 : Blo 439778 663455 := bstep (se 1 (by rfl) ⟨497591, by rfl⟩ : syracuseStep 663455 = 995183) B995183
theorem B892883 : Blo 439778 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B991187 : Blo 439778 991187 := bstep (se 1 (by rfl) ⟨743390, by rfl⟩ : syracuseStep 991187 = 1486781) B1486781
theorem B1417279 : Blo 439778 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B2695265 : Blo 439778 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1122407 : Blo 439778 1122407 := bstep (se 1 (by rfl) ⟨841805, by rfl⟩ : syracuseStep 1122407 = 1683611) B1683611
theorem B663689 : Blo 439778 663689 := bstep (se 2 (by rfl) ⟨248883, by rfl⟩ : syracuseStep 663689 = 497767) B497767
theorem B663803 : Blo 439778 663803 := bstep (se 1 (by rfl) ⟨497852, by rfl⟩ : syracuseStep 663803 = 995705) B995705
theorem B1057193 : Blo 439778 1057193 := bstep (se 2 (by rfl) ⟨396447, by rfl⟩ : syracuseStep 1057193 = 792895) B792895
theorem B664457 : Blo 439778 664457 := bstep (se 2 (by rfl) ⟨249171, by rfl⟩ : syracuseStep 664457 = 498343) B498343
theorem B992159 : Blo 439778 992159 := bstep (se 1 (by rfl) ⟨744119, by rfl⟩ : syracuseStep 992159 = 1488239) B1488239
theorem B1254359 : Blo 439778 1254359 := bstep (se 1 (by rfl) ⟨940769, by rfl⟩ : syracuseStep 1254359 = 1881539) B1881539
theorem B2730187 : Blo 439778 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B993833 : Blo 439778 993833 := bstep (se 2 (by rfl) ⟨372687, by rfl⟩ : syracuseStep 993833 = 745375) B745375
theorem B993887 : Blo 439778 993887 := bstep (se 1 (by rfl) ⟨745415, by rfl⟩ : syracuseStep 993887 = 1490831) B1490831
theorem B994031 : Blo 439778 994031 := bstep (se 1 (by rfl) ⟨745523, by rfl⟩ : syracuseStep 994031 = 1491047) B1491047
theorem B1485593 : Blo 439778 1485593 := bstep (se 2 (by rfl) ⟨557097, by rfl⟩ : syracuseStep 1485593 = 1114195) B1114195
theorem B1059799 : Blo 439778 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B1257707 : Blo 439778 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B1684415 : Blo 439778 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B996587 : Blo 439778 996587 := bstep (se 1 (by rfl) ⟨747440, by rfl⟩ : syracuseStep 996587 = 1494881) B1494881
theorem B439935 : Blo 439778 439935 := bstep (se 1 (by rfl) ⟨329951, by rfl⟩ : syracuseStep 439935 = 659903) B659903
theorem B2832097 : Blo 439778 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B440191 : Blo 439778 440191 := bstep (se 1 (by rfl) ⟨330143, by rfl⟩ : syracuseStep 440191 = 660287) B660287
theorem B1488887 : Blo 439778 1488887 := bstep (se 1 (by rfl) ⟨1116665, by rfl⟩ : syracuseStep 1488887 = 2233331) B2233331
theorem B440347 : Blo 439778 440347 := bstep (se 1 (by rfl) ⟨330260, by rfl⟩ : syracuseStep 440347 = 660521) B660521
theorem B440367 : Blo 439778 440367 := bstep (se 1 (by rfl) ⟨330275, by rfl⟩ : syracuseStep 440367 = 660551) B660551
theorem B997487 : Blo 439778 997487 := bstep (se 1 (by rfl) ⟨748115, by rfl⟩ : syracuseStep 997487 = 1496231) B1496231
theorem B440679 : Blo 439778 440679 := bstep (se 1 (by rfl) ⟨330509, by rfl⟩ : syracuseStep 440679 = 661019) B661019
theorem B440799 : Blo 439778 440799 := bstep (se 1 (by rfl) ⟨330599, by rfl⟩ : syracuseStep 440799 = 661199) B661199
theorem B997865 : Blo 439778 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B440935 : Blo 439778 440935 := bstep (se 1 (by rfl) ⟨330701, by rfl⟩ : syracuseStep 440935 = 661403) B661403
theorem B3193465 : Blo 439778 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B11483801 : Blo 439778 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B441375 : Blo 439778 441375 := bstep (se 1 (by rfl) ⟨331031, by rfl⟩ : syracuseStep 441375 = 662063) B662063
theorem B1489967 : Blo 439778 1489967 := bstep (se 1 (by rfl) ⟨1117475, by rfl⟩ : syracuseStep 1489967 = 2234951) B2234951
theorem B441599 : Blo 439778 441599 := bstep (se 1 (by rfl) ⟨331199, by rfl⟩ : syracuseStep 441599 = 662399) B662399
theorem B1490183 : Blo 439778 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B441647 : Blo 439778 441647 := bstep (se 1 (by rfl) ⟨331235, by rfl⟩ : syracuseStep 441647 = 662471) B662471
theorem B441839 : Blo 439778 441839 := bstep (se 1 (by rfl) ⟨331379, by rfl⟩ : syracuseStep 441839 = 662759) B662759
theorem B441959 : Blo 439778 441959 := bstep (se 1 (by rfl) ⟨331469, by rfl⟩ : syracuseStep 441959 = 662939) B662939
theorem B442415 : Blo 439778 442415 := bstep (se 1 (by rfl) ⟨331811, by rfl⟩ : syracuseStep 442415 = 663623) B663623
theorem B835859 : Blo 439778 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B443295 : Blo 439778 443295 := bstep (se 1 (by rfl) ⟨332471, by rfl⟩ : syracuseStep 443295 = 664943) B664943
theorem B443647 : Blo 439778 443647 := bstep (se 1 (by rfl) ⟨332735, by rfl⟩ : syracuseStep 443647 = 665471) B665471
theorem B3818753 : Blo 439778 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1885639 : Blo 439778 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B2246615 : Blo 439778 2246615 := bstep (se 1 (by rfl) ⟨1684961, by rfl⟩ : syracuseStep 2246615 = 3369923) B3369923
theorem B5359927 : Blo 439778 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B12700151 : Blo 439778 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B8473531 : Blo 439778 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B52317413 : Blo 439778 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B840431 : Blo 439778 840431 := bstep (se 1 (by rfl) ⟨630323, by rfl⟩ : syracuseStep 840431 = 1260647) B1260647
theorem B742655 : Blo 439778 742655 := bstep (se 1 (by rfl) ⟨556991, by rfl⟩ : syracuseStep 742655 = 1113983) B1113983
theorem B742891 : Blo 439778 742891 := bstep (se 1 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 742891 = 1114337) B1114337
theorem B841441 : Blo 439778 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B710633 : Blo 439778 710633 := bstep (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) B532975
theorem B8869985 : Blo 439778 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B15292871 : Blo 439778 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B12114683 : Blo 439778 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B9067697 : Blo 439778 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B744761 : Blo 439778 744761 := bstep (se 2 (by rfl) ⟨279285, by rfl⟩ : syracuseStep 744761 = 558571) B558571
theorem B4546655 : Blo 439778 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B3367007 : Blo 439778 3367007 := bstep (se 1 (by rfl) ⟨2525255, by rfl⟩ : syracuseStep 3367007 = 5050511) B5050511
theorem B2384093 : Blo 439778 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B3596831 : Blo 439778 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B746239 : Blo 439778 746239 := bstep (se 1 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 746239 = 1119359) B1119359
theorem B1008617 : Blo 439778 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B746489 : Blo 439778 746489 := bstep (se 2 (by rfl) ⟨279933, by rfl⟩ : syracuseStep 746489 = 559867) B559867
theorem B8087177 : Blo 439778 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B2157263 : Blo 439778 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B945263 : Blo 439778 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B51867371 : Blo 439778 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B8580971 : Blo 439778 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B18149831 : Blo 439778 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B1700689 : Blo 439778 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B61306703 : Blo 439778 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B1113527 : Blo 439778 1113527 := bstep (se 1 (by rfl) ⟨835145, by rfl⟩ : syracuseStep 1113527 = 1670291) B1670291
theorem B11271797 : Blo 439778 11271797 := bstep (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) B1056731
theorem B2228957 : Blo 439778 2228957 := bstep (se 3 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 2228957 = 835859) B835859
theorem B2229119 : Blo 439778 2229119 := bstep (se 1 (by rfl) ⟨1671839, by rfl⟩ : syracuseStep 2229119 = 3343679) B3343679
theorem B10159775 : Blo 439778 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1673405 : Blo 439778 1673405 := bstep (se 3 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 1673405 = 627527) B627527
theorem B2689645 : Blo 439778 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B3640249 : Blo 439778 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B7146569 : Blo 439778 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B560287 : Blo 439778 560287 := bstep (se 1 (by rfl) ⟨420215, by rfl⟩ : syracuseStep 560287 = 840431) B840431
theorem B495103 : Blo 439778 495103 := bstep (se 1 (by rfl) ⟨371327, by rfl⟩ : syracuseStep 495103 = 742655) B742655
theorem B1413065 : Blo 439778 1413065 := bstep (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) B1059799
theorem B10195247 : Blo 439778 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B496507 : Blo 439778 496507 := bstep (se 1 (by rfl) ⟨372380, by rfl⟩ : syracuseStep 496507 = 744761) B744761
theorem B16586003 : Blo 439778 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B660791 : Blo 439778 660791 := bstep (se 1 (by rfl) ⟨495593, by rfl⟩ : syracuseStep 660791 = 991187) B991187
theorem B2397887 : Blo 439778 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B661439 : Blo 439778 661439 := bstep (se 1 (by rfl) ⟨496079, by rfl⟩ : syracuseStep 661439 = 992159) B992159
theorem B497659 : Blo 439778 497659 := bstep (se 1 (by rfl) ⟨373244, by rfl⟩ : syracuseStep 497659 = 746489) B746489
theorem B2267585 : Blo 439778 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B662555 : Blo 439778 662555 := bstep (se 1 (by rfl) ⟨496916, by rfl⟩ : syracuseStep 662555 = 993833) B993833
theorem B662591 : Blo 439778 662591 := bstep (se 1 (by rfl) ⟨496943, by rfl⟩ : syracuseStep 662591 = 993887) B993887
theorem B662687 : Blo 439778 662687 := bstep (se 1 (by rfl) ⟨497015, by rfl⟩ : syracuseStep 662687 = 994031) B994031
theorem B990395 : Blo 439778 990395 := bstep (se 1 (by rfl) ⟨742796, by rfl⟩ : syracuseStep 990395 = 1485593) B1485593
theorem B990521 : Blo 439778 990521 := bstep (se 2 (by rfl) ⟨371445, by rfl⟩ : syracuseStep 990521 = 742891) B742891
theorem B630175 : Blo 439778 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B3776129 : Blo 439778 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B1121921 : Blo 439778 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B34578247 : Blo 439778 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B10756145 : Blo 439778 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B663785 : Blo 439778 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B12099887 : Blo 439778 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B1122943 : Blo 439778 1122943 := bstep (se 1 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 1122943 = 1684415) B1684415
theorem B664391 : Blo 439778 664391 := bstep (se 1 (by rfl) ⟨498293, by rfl⟩ : syracuseStep 664391 = 996587) B996587
theorem B40871135 : Blo 439778 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B5645537 : Blo 439778 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B992591 : Blo 439778 992591 := bstep (se 1 (by rfl) ⟨744443, by rfl⟩ : syracuseStep 992591 = 1488887) B1488887
theorem B664991 : Blo 439778 664991 := bstep (se 1 (by rfl) ⟨498743, by rfl⟩ : syracuseStep 664991 = 997487) B997487
theorem B665243 : Blo 439778 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B665321 : Blo 439778 665321 := bstep (se 2 (by rfl) ⟨249495, by rfl⟩ : syracuseStep 665321 = 498991) B498991
theorem B993311 : Blo 439778 993311 := bstep (se 1 (by rfl) ⟨744983, by rfl⟩ : syracuseStep 993311 = 1489967) B1489967
theorem B993455 : Blo 439778 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B7514531 : Blo 439778 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B3353885 : Blo 439778 3353885 := bstep (se 3 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 3353885 = 1257707) B1257707
theorem B994985 : Blo 439778 994985 := bstep (se 2 (by rfl) ⟨373119, by rfl⟩ : syracuseStep 994985 = 746239) B746239
theorem B1486943 : Blo 439778 1486943 := bstep (se 1 (by rfl) ⟨1115207, by rfl⟩ : syracuseStep 1486943 = 2230415) B2230415
theorem B8466767 : Blo 439778 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B1487591 : Blo 439778 1487591 := bstep (se 1 (by rfl) ⟨1115693, by rfl⟩ : syracuseStep 1487591 = 2231387) B2231387
theorem B34878275 : Blo 439778 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B439855 : Blo 439778 439855 := bstep (se 1 (by rfl) ⟨329891, by rfl⟩ : syracuseStep 439855 = 659783) B659783
theorem B440039 : Blo 439778 440039 := bstep (se 1 (by rfl) ⟨330029, by rfl⟩ : syracuseStep 440039 = 660059) B660059
theorem B1488671 : Blo 439778 1488671 := bstep (se 1 (by rfl) ⟨1116503, by rfl⟩ : syracuseStep 1488671 = 2233007) B2233007
theorem B440351 : Blo 439778 440351 := bstep (se 1 (by rfl) ⟨330263, by rfl⟩ : syracuseStep 440351 = 660527) B660527
theorem B1489103 : Blo 439778 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B1489535 : Blo 439778 1489535 := bstep (se 1 (by rfl) ⟨1117151, by rfl⟩ : syracuseStep 1489535 = 2234303) B2234303
theorem B5913323 : Blo 439778 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B441119 : Blo 439778 441119 := bstep (se 1 (by rfl) ⟨330839, by rfl⟩ : syracuseStep 441119 = 661679) B661679
theorem B1489751 : Blo 439778 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B1489913 : Blo 439778 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B8076455 : Blo 439778 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B6045131 : Blo 439778 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B441855 : Blo 439778 441855 := bstep (se 1 (by rfl) ⟨331391, by rfl⟩ : syracuseStep 441855 = 662783) B662783
theorem B441983 : Blo 439778 441983 := bstep (se 1 (by rfl) ⟨331487, by rfl⟩ : syracuseStep 441983 = 662975) B662975
theorem B442303 : Blo 439778 442303 := bstep (se 1 (by rfl) ⟨331727, by rfl⟩ : syracuseStep 442303 = 663455) B663455
theorem B3031103 : Blo 439778 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B2244671 : Blo 439778 2244671 := bstep (se 1 (by rfl) ⟨1683503, by rfl⟩ : syracuseStep 2244671 = 3367007) B3367007
theorem B442459 : Blo 439778 442459 := bstep (se 1 (by rfl) ⟨331844, by rfl⟩ : syracuseStep 442459 = 663689) B663689
theorem B1589395 : Blo 439778 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B442535 : Blo 439778 442535 := bstep (se 1 (by rfl) ⟨331901, by rfl⟩ : syracuseStep 442535 = 663803) B663803
theorem B704795 : Blo 439778 704795 := bstep (se 1 (by rfl) ⟨528596, by rfl⟩ : syracuseStep 704795 = 1057193) B1057193
theorem B442971 : Blo 439778 442971 := bstep (se 1 (by rfl) ⟨332228, by rfl⟩ : syracuseStep 442971 = 664457) B664457
theorem B836239 : Blo 439778 836239 := bstep (se 1 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 836239 = 1254359) B1254359
theorem B5391451 : Blo 439778 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B5720647 : Blo 439778 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B7655867 : Blo 439778 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B742351 : Blo 439778 742351 := bstep (se 1 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 742351 = 1113527) B1113527
theorem B2381021 : Blo 439778 2381021 := bstep (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) B892883
theorem B742783 : Blo 439778 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B1889705 : Blo 439778 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B2545835 : Blo 439778 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B2841119 : Blo 439778 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B1497743 : Blo 439778 1497743 := bstep (se 1 (by rfl) ⟨1123307, by rfl⟩ : syracuseStep 1497743 = 2246615) B2246615
theorem B744383 : Blo 439778 744383 := bstep (se 1 (by rfl) ⟨558287, by rfl⟩ : syracuseStep 744383 = 1116575) B1116575
theorem B2514185 : Blo 439778 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B941743 : Blo 439778 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B11298041 : Blo 439778 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B747751 : Blo 439778 747751 := bstep (se 1 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 747751 = 1121627) B1121627
theorem B1895021 : Blo 439778 1895021 := bstep (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) B710633
theorem B1796843 : Blo 439778 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B748271 : Blo 439778 748271 := bstep (se 1 (by rfl) ⟨561203, by rfl⟩ : syracuseStep 748271 = 1122407) B1122407
theorem B1438175 : Blo 439778 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B4257953 : Blo 439778 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B1670017 : Blo 439778 1670017 := bstep (se 2 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 1670017 = 1252513) B1252513
theorem B1114985 : Blo 439778 1114985 := bstep (se 2 (by rfl) ⟨418119, by rfl⟩ : syracuseStep 1114985 = 836239) B836239
theorem B3835133 : Blo 439778 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B1115603 : Blo 439778 1115603 := bstep (se 1 (by rfl) ⟨836702, by rfl⟩ : syracuseStep 1115603 = 1673405) B1673405
theorem B4853665 : Blo 439778 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B1511723 : Blo 439778 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B496255 : Blo 439778 496255 := bstep (se 1 (by rfl) ⟨372191, by rfl⟩ : syracuseStep 496255 = 744383) B744383
theorem B660137 : Blo 439778 660137 := bstep (se 2 (by rfl) ⟨247551, by rfl⟩ : syracuseStep 660137 = 495103) B495103
theorem B660263 : Blo 439778 660263 := bstep (se 1 (by rfl) ⟨495197, by rfl⟩ : syracuseStep 660263 = 990395) B990395
theorem B1676123 : Blo 439778 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B660347 : Blo 439778 660347 := bstep (se 1 (by rfl) ⟨495260, by rfl⟩ : syracuseStep 660347 = 990521) B990521
theorem B8066591 : Blo 439778 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B6788893 : Blo 439778 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B661727 : Blo 439778 661727 := bstep (se 1 (by rfl) ⟨496295, by rfl⟩ : syracuseStep 661727 = 992591) B992591
theorem B662009 : Blo 439778 662009 := bstep (se 2 (by rfl) ⟨248253, by rfl⟩ : syracuseStep 662009 = 496507) B496507
theorem B989801 : Blo 439778 989801 := bstep (se 2 (by rfl) ⟨371175, by rfl⟩ : syracuseStep 989801 = 742351) B742351
theorem B662207 : Blo 439778 662207 := bstep (se 1 (by rfl) ⟨496655, by rfl⟩ : syracuseStep 662207 = 993311) B993311
theorem B662303 : Blo 439778 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B498847 : Blo 439778 498847 := bstep (se 1 (by rfl) ⟨374135, by rfl⟩ : syracuseStep 498847 = 748271) B748271
theorem B990377 : Blo 439778 990377 := bstep (se 2 (by rfl) ⟨371391, by rfl⟩ : syracuseStep 990377 = 742783) B742783
theorem B4791581 : Blo 439778 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B2235923 : Blo 439778 2235923 := bstep (se 1 (by rfl) ⟨1676942, by rfl⟩ : syracuseStep 2235923 = 3353885) B3353885
theorem B663323 : Blo 439778 663323 := bstep (se 1 (by rfl) ⟨497492, by rfl⟩ : syracuseStep 663323 = 994985) B994985
theorem B663545 : Blo 439778 663545 := bstep (se 2 (by rfl) ⟨248829, by rfl⟩ : syracuseStep 663545 = 497659) B497659
theorem B991295 : Blo 439778 991295 := bstep (se 1 (by rfl) ⟨743471, by rfl⟩ : syracuseStep 991295 = 1486943) B1486943
theorem B5644511 : Blo 439778 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B991727 : Blo 439778 991727 := bstep (se 1 (by rfl) ⟨743795, by rfl⟩ : syracuseStep 991727 = 1487591) B1487591
theorem B992447 : Blo 439778 992447 := bstep (se 1 (by rfl) ⟨744335, by rfl⟩ : syracuseStep 992447 = 1488671) B1488671
theorem B992735 : Blo 439778 992735 := bstep (se 1 (by rfl) ⟨744551, by rfl⟩ : syracuseStep 992735 = 1489103) B1489103
theorem B993023 : Blo 439778 993023 := bstep (se 1 (by rfl) ⟨744767, by rfl⟩ : syracuseStep 993023 = 1489535) B1489535
theorem B3942215 : Blo 439778 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B993167 : Blo 439778 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B993275 : Blo 439778 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B5384303 : Blo 439778 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B1255657 : Blo 439778 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B1485971 : Blo 439778 1485971 := bstep (se 1 (by rfl) ⟨1114478, by rfl⟩ : syracuseStep 1485971 = 2228957) B2228957
theorem B1486079 : Blo 439778 1486079 := bstep (se 1 (by rfl) ⟨1114559, by rfl⟩ : syracuseStep 1486079 = 2229119) B2229119
theorem B1879453 : Blo 439778 1879453 := bstep (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) B704795
theorem B7188601 : Blo 439778 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B4764379 : Blo 439778 4764379 := bstep (se 1 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 4764379 = 7146569) B7146569
theorem B6796831 : Blo 439778 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B997001 : Blo 439778 997001 := bstep (se 2 (by rfl) ⟨373875, by rfl⟩ : syracuseStep 997001 = 747751) B747751
theorem B3586193 : Blo 439778 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1587347 : Blo 439778 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B440527 : Blo 439778 440527 := bstep (se 1 (by rfl) ⟨330395, by rfl⟩ : syracuseStep 440527 = 660791) B660791
theorem B1259803 : Blo 439778 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B440959 : Blo 439778 440959 := bstep (se 1 (by rfl) ⟨330719, by rfl⟩ : syracuseStep 440959 = 661439) B661439
theorem B998495 : Blo 439778 998495 := bstep (se 1 (by rfl) ⟨748871, by rfl⟩ : syracuseStep 998495 = 1497743) B1497743
theorem B441703 : Blo 439778 441703 := bstep (se 1 (by rfl) ⟨331277, by rfl⟩ : syracuseStep 441703 = 662555) B662555
theorem B441727 : Blo 439778 441727 := bstep (se 1 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 441727 = 662591) B662591
theorem B441791 : Blo 439778 441791 := bstep (se 1 (by rfl) ⟨331343, by rfl⟩ : syracuseStep 441791 = 662687) B662687
theorem B442523 : Blo 439778 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B442927 : Blo 439778 442927 := bstep (se 1 (by rfl) ⟨332195, by rfl⟩ : syracuseStep 442927 = 664391) B664391
theorem B27247423 : Blo 439778 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B443327 : Blo 439778 443327 := bstep (se 1 (by rfl) ⟨332495, by rfl⟩ : syracuseStep 443327 = 664991) B664991
theorem B443495 : Blo 439778 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B443547 : Blo 439778 443547 := bstep (se 1 (by rfl) ⟨332660, by rfl⟩ : syracuseStep 443547 = 665321) B665321
theorem B1263347 : Blo 439778 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B23252183 : Blo 439778 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B2838635 : Blo 439778 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B840233 : Blo 439778 840233 := bstep (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) B630175
theorem B2020735 : Blo 439778 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B1496447 : Blo 439778 1496447 := bstep (se 1 (by rfl) ⟨1122335, by rfl⟩ : syracuseStep 1496447 = 2244671) B2244671
theorem B2119193 : Blo 439778 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B1497257 : Blo 439778 1497257 := bstep (se 2 (by rfl) ⟨561471, by rfl⟩ : syracuseStep 1497257 = 1122943) B1122943
theorem B6773183 : Blo 439778 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B942043 : Blo 439778 942043 := bstep (se 1 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 942043 = 1413065) B1413065
theorem B5103911 : Blo 439778 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B44229341 : Blo 439778 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B7627529 : Blo 439778 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B1598591 : Blo 439778 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B747049 : Blo 439778 747049 := bstep (se 2 (by rfl) ⟨280143, by rfl⟩ : syracuseStep 747049 = 560287) B560287
theorem B1894079 : Blo 439778 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B2517419 : Blo 439778 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B747947 : Blo 439778 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B7170763 : Blo 439778 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B3763691 : Blo 439778 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B7532027 : Blo 439778 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B5009687 : Blo 439778 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B2226689 : Blo 439778 2226689 := bstep (se 2 (by rfl) ⟨835008, by rfl⟩ : syracuseStep 2226689 = 1670017) B1670017
theorem B4030087 : Blo 439778 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B46104329 : Blo 439778 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B2556755 : Blo 439778 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B15501455 : Blo 439778 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B1674209 : Blo 439778 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B1117415 : Blo 439778 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B1412795 : Blo 439778 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B5377727 : Blo 439778 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B659867 : Blo 439778 659867 := bstep (se 1 (by rfl) ⟨494900, by rfl⟩ : syracuseStep 659867 = 989801) B989801
theorem B660251 : Blo 439778 660251 := bstep (se 1 (by rfl) ⟨495188, by rfl⟩ : syracuseStep 660251 = 990377) B990377
theorem B660863 : Blo 439778 660863 := bstep (se 1 (by rfl) ⟨495647, by rfl⟩ : syracuseStep 660863 = 991295) B991295
theorem B661151 : Blo 439778 661151 := bstep (se 1 (by rfl) ⟨495863, by rfl⟩ : syracuseStep 661151 = 991727) B991727
theorem B5085019 : Blo 439778 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B661631 : Blo 439778 661631 := bstep (se 1 (by rfl) ⟨496223, by rfl⟩ : syracuseStep 661631 = 992447) B992447
theorem B661673 : Blo 439778 661673 := bstep (se 2 (by rfl) ⟨248127, by rfl⟩ : syracuseStep 661673 = 496255) B496255
theorem B661823 : Blo 439778 661823 := bstep (se 1 (by rfl) ⟨496367, by rfl⟩ : syracuseStep 661823 = 992735) B992735
theorem B662015 : Blo 439778 662015 := bstep (se 1 (by rfl) ⟨496511, by rfl⟩ : syracuseStep 662015 = 993023) B993023
theorem B2628143 : Blo 439778 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B662111 : Blo 439778 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B662183 : Blo 439778 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B1678279 : Blo 439778 1678279 := bstep (se 1 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 1678279 = 2517419) B2517419
theorem B498631 : Blo 439778 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B2694313 : Blo 439778 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B990647 : Blo 439778 990647 := bstep (se 1 (by rfl) ⟨742985, by rfl⟩ : syracuseStep 990647 = 1485971) B1485971
theorem B990719 : Blo 439778 990719 := bstep (se 1 (by rfl) ⟨743039, by rfl⟩ : syracuseStep 990719 = 1486079) B1486079
theorem B5021351 : Blo 439778 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B9051857 : Blo 439778 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B1679737 : Blo 439778 1679737 := bstep (se 2 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 1679737 = 1259803) B1259803
theorem B664667 : Blo 439778 664667 := bstep (se 1 (by rfl) ⟨498500, by rfl⟩ : syracuseStep 664667 = 997001) B997001
theorem B1058231 : Blo 439778 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B665129 : Blo 439778 665129 := bstep (se 2 (by rfl) ⟨249423, by rfl⟩ : syracuseStep 665129 = 498847) B498847
theorem B1484459 : Blo 439778 1484459 := bstep (se 1 (by rfl) ⟨1113344, by rfl⟩ : syracuseStep 1484459 = 2226689) B2226689
theorem B665663 : Blo 439778 665663 := bstep (se 1 (by rfl) ⟨499247, by rfl⟩ : syracuseStep 665663 = 998495) B998495
theorem B1256057 : Blo 439778 1256057 := bstep (se 2 (by rfl) ⟨471021, by rfl⟩ : syracuseStep 1256057 = 942043) B942043
theorem B2240621 : Blo 439778 2240621 := bstep (se 3 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 2240621 = 840233) B840233
theorem B996065 : Blo 439778 996065 := bstep (se 2 (by rfl) ⟨373524, by rfl⟩ : syracuseStep 996065 = 747049) B747049
theorem B440091 : Blo 439778 440091 := bstep (se 1 (by rfl) ⟨330068, by rfl⟩ : syracuseStep 440091 = 660137) B660137
theorem B440175 : Blo 439778 440175 := bstep (se 1 (by rfl) ⟨330131, by rfl⟩ : syracuseStep 440175 = 660263) B660263
theorem B440231 : Blo 439778 440231 := bstep (se 1 (by rfl) ⟨330173, by rfl⟩ : syracuseStep 440231 = 660347) B660347
theorem B997631 : Blo 439778 997631 := bstep (se 1 (by rfl) ⟨748223, by rfl⟩ : syracuseStep 997631 = 1496447) B1496447
theorem B998171 : Blo 439778 998171 := bstep (se 1 (by rfl) ⟨748628, by rfl⟩ : syracuseStep 998171 = 1497257) B1497257
theorem B441151 : Blo 439778 441151 := bstep (se 1 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 441151 = 661727) B661727
theorem B441339 : Blo 439778 441339 := bstep (se 1 (by rfl) ⟨331004, by rfl⟩ : syracuseStep 441339 = 662009) B662009
theorem B441471 : Blo 439778 441471 := bstep (se 1 (by rfl) ⟨331103, by rfl⟩ : syracuseStep 441471 = 662207) B662207
theorem B441535 : Blo 439778 441535 := bstep (se 1 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 441535 = 662303) B662303
theorem B2505937 : Blo 439778 2505937 := bstep (se 2 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 2505937 = 1879453) B1879453
theorem B3194387 : Blo 439778 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B1490615 : Blo 439778 1490615 := bstep (se 1 (by rfl) ⟨1117961, by rfl⟩ : syracuseStep 1490615 = 2235923) B2235923
theorem B442215 : Blo 439778 442215 := bstep (se 1 (by rfl) ⟨331661, by rfl⟩ : syracuseStep 442215 = 663323) B663323
theorem B442363 : Blo 439778 442363 := bstep (se 1 (by rfl) ⟨331772, by rfl⟩ : syracuseStep 442363 = 663545) B663545
theorem B9584801 : Blo 439778 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B1065727 : Blo 439778 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1262719 : Blo 439778 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B3589535 : Blo 439778 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B9062441 : Blo 439778 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B2509127 : Blo 439778 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B743323 : Blo 439778 743323 := bstep (se 1 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 743323 = 1114985) B1114985
theorem B743735 : Blo 439778 743735 := bstep (se 1 (by rfl) ⟨557801, by rfl⟩ : syracuseStep 743735 = 1115603) B1115603
theorem B36329897 : Blo 439778 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B842231 : Blo 439778 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B1892423 : Blo 439778 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B1007815 : Blo 439778 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B9561017 : Blo 439778 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B4515455 : Blo 439778 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B3763007 : Blo 439778 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B3402607 : Blo 439778 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B29486227 : Blo 439778 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B6352505 : Blo 439778 6352505 := bstep (se 2 (by rfl) ⟨2382189, by rfl⟩ : syracuseStep 6352505 = 4764379) B4764379
theorem B3339791 : Blo 439778 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B2390795 : Blo 439778 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B25886213 : Blo 439778 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B5373449 : Blo 439778 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B30736219 : Blo 439778 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B6389867 : Blo 439778 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B1343753 : Blo 439778 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B1704503 : Blo 439778 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B2393023 : Blo 439778 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B1672751 : Blo 439778 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B1116139 : Blo 439778 1116139 := bstep (se 1 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 1116139 = 1674209) B1674209
theorem B2821949 : Blo 439778 2821949 := bstep (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) B1058231
theorem B495823 : Blo 439778 495823 := bstep (se 1 (by rfl) ⟨371867, by rfl⟩ : syracuseStep 495823 = 743735) B743735
theorem B24219931 : Blo 439778 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B561487 : Blo 439778 561487 := bstep (se 1 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 561487 = 842231) B842231
theorem B660431 : Blo 439778 660431 := bstep (se 1 (by rfl) ⟨495323, by rfl⟩ : syracuseStep 660431 = 990647) B990647
theorem B660479 : Blo 439778 660479 := bstep (se 1 (by rfl) ⟨495359, by rfl⟩ : syracuseStep 660479 = 990719) B990719
theorem B3347567 : Blo 439778 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B6034571 : Blo 439778 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B989639 : Blo 439778 989639 := bstep (se 1 (by rfl) ⟨742229, by rfl⟩ : syracuseStep 989639 = 1484459) B1484459
theorem B4235003 : Blo 439778 4235003 := bstep (se 1 (by rfl) ⟨3176252, by rfl⟩ : syracuseStep 4235003 = 6352505) B6352505
theorem B991097 : Blo 439778 991097 := bstep (se 2 (by rfl) ⟨371661, by rfl⟩ : syracuseStep 991097 = 743323) B743323
theorem B664043 : Blo 439778 664043 := bstep (se 1 (by rfl) ⟨498032, by rfl⟩ : syracuseStep 664043 = 996065) B996065
theorem B2237705 : Blo 439778 2237705 := bstep (se 2 (by rfl) ⟨839139, by rfl⟩ : syracuseStep 2237705 = 1678279) B1678279
theorem B664841 : Blo 439778 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B665087 : Blo 439778 665087 := bstep (se 1 (by rfl) ⟨498815, by rfl⟩ : syracuseStep 665087 = 997631) B997631
theorem B665447 : Blo 439778 665447 := bstep (se 1 (by rfl) ⟨499085, by rfl⟩ : syracuseStep 665447 = 998171) B998171
theorem B3582299 : Blo 439778 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B993743 : Blo 439778 993743 := bstep (se 1 (by rfl) ⟨745307, by rfl⟩ : syracuseStep 993743 = 1490615) B1490615
theorem B2239649 : Blo 439778 2239649 := bstep (se 2 (by rfl) ⟨839868, by rfl⟩ : syracuseStep 2239649 = 1679737) B1679737
theorem B6041627 : Blo 439778 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B10334303 : Blo 439778 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B1683625 : Blo 439778 1683625 := bstep (se 2 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 1683625 = 1262719) B1262719
theorem B3585151 : Blo 439778 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B439911 : Blo 439778 439911 := bstep (se 1 (by rfl) ⟨329933, by rfl⟩ : syracuseStep 439911 = 659867) B659867
theorem B440167 : Blo 439778 440167 := bstep (se 1 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 440167 = 660251) B660251
theorem B440575 : Blo 439778 440575 := bstep (se 1 (by rfl) ⟨330431, by rfl⟩ : syracuseStep 440575 = 660863) B660863
theorem B440767 : Blo 439778 440767 := bstep (se 1 (by rfl) ⟨330575, by rfl⟩ : syracuseStep 440767 = 661151) B661151
theorem B4536809 : Blo 439778 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B5683877 : Blo 439778 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B441087 : Blo 439778 441087 := bstep (se 1 (by rfl) ⟨330815, by rfl⟩ : syracuseStep 441087 = 661631) B661631
theorem B441115 : Blo 439778 441115 := bstep (se 1 (by rfl) ⟨330836, by rfl⟩ : syracuseStep 441115 = 661673) B661673
theorem B441215 : Blo 439778 441215 := bstep (se 1 (by rfl) ⟨330911, by rfl⟩ : syracuseStep 441215 = 661823) B661823
theorem B441343 : Blo 439778 441343 := bstep (se 1 (by rfl) ⟨331007, by rfl⟩ : syracuseStep 441343 = 662015) B662015
theorem B1752095 : Blo 439778 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B441407 : Blo 439778 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B441455 : Blo 439778 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B1261615 : Blo 439778 1261615 := bstep (se 1 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 1261615 = 1892423) B1892423
theorem B6374011 : Blo 439778 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B443111 : Blo 439778 443111 := bstep (se 1 (by rfl) ⟨332333, by rfl⟩ : syracuseStep 443111 = 664667) B664667
theorem B14369669 : Blo 439778 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B443419 : Blo 439778 443419 := bstep (se 1 (by rfl) ⟨332564, by rfl⟩ : syracuseStep 443419 = 665129) B665129
theorem B443775 : Blo 439778 443775 := bstep (se 1 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 443775 = 665663) B665663
theorem B837371 : Blo 439778 837371 := bstep (se 1 (by rfl) ⟨628028, by rfl⟩ : syracuseStep 837371 = 1256057) B1256057
theorem B2508671 : Blo 439778 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B1493747 : Blo 439778 1493747 := bstep (se 1 (by rfl) ⟨1120310, by rfl⟩ : syracuseStep 1493747 = 2240621) B2240621
theorem B1593863 : Blo 439778 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B17257475 : Blo 439778 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B40981625 : Blo 439778 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B744943 : Blo 439778 744943 := bstep (se 1 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 744943 = 1117415) B1117415
theorem B941863 : Blo 439778 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B39314969 : Blo 439778 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B3010303 : Blo 439778 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B6780025 : Blo 439778 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B2226527 : Blo 439778 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B3341249 : Blo 439778 3341249 := bstep (se 2 (by rfl) ⟨1252968, by rfl⟩ : syracuseStep 3341249 = 2505937) B2505937
theorem B2129591 : Blo 439778 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B4259911 : Blo 439778 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B1115167 : Blo 439778 1115167 := bstep (se 1 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 1115167 = 1672751) B1672751
theorem B558247 : Blo 439778 558247 := bstep (se 1 (by rfl) ⟨418685, by rfl⟩ : syracuseStep 558247 = 837371) B837371
theorem B1672447 : Blo 439778 1672447 := bstep (se 1 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 1672447 = 2508671) B2508671
theorem B2231711 : Blo 439778 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B659759 : Blo 439778 659759 := bstep (se 1 (by rfl) ⟨494819, by rfl⟩ : syracuseStep 659759 = 989639) B989639
theorem B2823335 : Blo 439778 2823335 := bstep (se 1 (by rfl) ⟨2117501, by rfl⟩ : syracuseStep 2823335 = 4235003) B4235003
theorem B660731 : Blo 439778 660731 := bstep (se 1 (by rfl) ⟨495548, by rfl⟩ : syracuseStep 660731 = 991097) B991097
theorem B661097 : Blo 439778 661097 := bstep (se 2 (by rfl) ⟨247911, by rfl⟩ : syracuseStep 661097 = 495823) B495823
theorem B662495 : Blo 439778 662495 := bstep (se 1 (by rfl) ⟨496871, by rfl⟩ : syracuseStep 662495 = 993743) B993743
theorem B6889535 : Blo 439778 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1484351 : Blo 439778 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B3024539 : Blo 439778 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B5678909 : Blo 439778 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B993257 : Blo 439778 993257 := bstep (se 2 (by rfl) ⟨372471, by rfl⟩ : syracuseStep 993257 = 744943) B744943
theorem B1255817 : Blo 439778 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B1682153 : Blo 439778 1682153 := bstep (se 2 (by rfl) ⟨630807, by rfl⟩ : syracuseStep 1682153 = 1261615) B1261615
theorem B895835 : Blo 439778 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B9579779 : Blo 439778 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B8498681 : Blo 439778 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B3190697 : Blo 439778 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B995831 : Blo 439778 995831 := bstep (se 1 (by rfl) ⟨746873, by rfl⟩ : syracuseStep 995831 = 1493747) B1493747
theorem B1881299 : Blo 439778 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B1488185 : Blo 439778 1488185 := bstep (se 2 (by rfl) ⟨558069, by rfl⟩ : syracuseStep 1488185 = 1116139) B1116139
theorem B46019933 : Blo 439778 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B1062575 : Blo 439778 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B440287 : Blo 439778 440287 := bstep (se 1 (by rfl) ⟨330215, by rfl⟩ : syracuseStep 440287 = 660431) B660431
theorem B440319 : Blo 439778 440319 := bstep (se 1 (by rfl) ⟨330239, by rfl⟩ : syracuseStep 440319 = 660479) B660479
theorem B2244833 : Blo 439778 2244833 := bstep (se 2 (by rfl) ⟨841812, by rfl⟩ : syracuseStep 2244833 = 1683625) B1683625
theorem B442695 : Blo 439778 442695 := bstep (se 1 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 442695 = 664043) B664043
theorem B32293241 : Blo 439778 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B19120805 : Blo 439778 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B1491803 : Blo 439778 1491803 := bstep (se 1 (by rfl) ⟨1118852, by rfl⟩ : syracuseStep 1491803 = 2237705) B2237705
theorem B443227 : Blo 439778 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B443391 : Blo 439778 443391 := bstep (se 1 (by rfl) ⟨332543, by rfl⟩ : syracuseStep 443391 = 665087) B665087
theorem B443631 : Blo 439778 443631 := bstep (se 1 (by rfl) ⟨332723, by rfl⟩ : syracuseStep 443631 = 665447) B665447
theorem B1493099 : Blo 439778 1493099 := bstep (se 1 (by rfl) ⟨1119824, by rfl⟩ : syracuseStep 1493099 = 2239649) B2239649
theorem B3789251 : Blo 439778 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B1168063 : Blo 439778 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B4545341 : Blo 439778 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B27321083 : Blo 439778 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B4023047 : Blo 439778 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B748649 : Blo 439778 748649 := bstep (se 2 (by rfl) ⟨280743, by rfl⟩ : syracuseStep 748649 = 561487) B561487
theorem B26209979 : Blo 439778 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B9040033 : Blo 439778 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B2388199 : Blo 439778 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B4027751 : Blo 439778 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B16054949 : Blo 439778 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B2227499 : Blo 439778 2227499 := bstep (se 1 (by rfl) ⟨1670624, by rfl⟩ : syracuseStep 2227499 = 3341249) B3341249
theorem B21528827 : Blo 439778 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B12747203 : Blo 439778 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B2229929 : Blo 439778 2229929 := bstep (se 2 (by rfl) ⟨836223, by rfl⟩ : syracuseStep 2229929 = 1672447) B1672447
theorem B2526167 : Blo 439778 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B6229669 : Blo 439778 6229669 := bstep (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) B1168063
theorem B4593023 : Blo 439778 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B3184265 : Blo 439778 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B989567 : Blo 439778 989567 := bstep (se 1 (by rfl) ⟨742175, by rfl⟩ : syracuseStep 989567 = 1484351) B1484351
theorem B662171 : Blo 439778 662171 := bstep (se 1 (by rfl) ⟨496628, by rfl⟩ : syracuseStep 662171 = 993257) B993257
theorem B1121435 : Blo 439778 1121435 := bstep (se 1 (by rfl) ⟨841076, by rfl⟩ : syracuseStep 1121435 = 1682153) B1682153
theorem B597223 : Blo 439778 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B499099 : Blo 439778 499099 := bstep (se 1 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 499099 = 748649) B748649
theorem B17473319 : Blo 439778 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B663887 : Blo 439778 663887 := bstep (se 1 (by rfl) ⟨497915, by rfl⟩ : syracuseStep 663887 = 995831) B995831
theorem B1254199 : Blo 439778 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B992123 : Blo 439778 992123 := bstep (se 1 (by rfl) ⟨744092, by rfl⟩ : syracuseStep 992123 = 1488185) B1488185
theorem B30679955 : Blo 439778 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B1484999 : Blo 439778 1484999 := bstep (se 1 (by rfl) ⟨1113749, by rfl⟩ : syracuseStep 1484999 = 2227499) B2227499
theorem B5679881 : Blo 439778 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B994535 : Blo 439778 994535 := bstep (se 1 (by rfl) ⟨745901, by rfl⟩ : syracuseStep 994535 = 1491803) B1491803
theorem B1486889 : Blo 439778 1486889 := bstep (se 2 (by rfl) ⟨557583, by rfl⟩ : syracuseStep 1486889 = 1115167) B1115167
theorem B995399 : Blo 439778 995399 := bstep (se 1 (by rfl) ⟨746549, by rfl⟩ : syracuseStep 995399 = 1493099) B1493099
theorem B10728125 : Blo 439778 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1487807 : Blo 439778 1487807 := bstep (se 1 (by rfl) ⟨1115855, by rfl⟩ : syracuseStep 1487807 = 2231711) B2231711
theorem B439839 : Blo 439778 439839 := bstep (se 1 (by rfl) ⟨329879, by rfl⟩ : syracuseStep 439839 = 659759) B659759
theorem B1882223 : Blo 439778 1882223 := bstep (se 1 (by rfl) ⟨1411667, by rfl⟩ : syracuseStep 1882223 = 2823335) B2823335
theorem B440487 : Blo 439778 440487 := bstep (se 1 (by rfl) ⟨330365, by rfl⟩ : syracuseStep 440487 = 660731) B660731
theorem B440731 : Blo 439778 440731 := bstep (se 1 (by rfl) ⟨330548, by rfl⟩ : syracuseStep 440731 = 661097) B661097
theorem B3030227 : Blo 439778 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B441663 : Blo 439778 441663 := bstep (se 1 (by rfl) ⟨331247, by rfl⟩ : syracuseStep 441663 = 662495) B662495
theorem B2016359 : Blo 439778 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B3785939 : Blo 439778 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B837211 : Blo 439778 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B708383 : Blo 439778 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B10703299 : Blo 439778 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B1496555 : Blo 439778 1496555 := bstep (se 1 (by rfl) ⟨1122416, by rfl⟩ : syracuseStep 1496555 = 2244833) B2244833
theorem B744329 : Blo 439778 744329 := bstep (se 2 (by rfl) ⟨279123, by rfl⟩ : syracuseStep 744329 = 558247) B558247
theorem B12053377 : Blo 439778 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B18214055 : Blo 439778 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B6386519 : Blo 439778 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B5665787 : Blo 439778 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B2127131 : Blo 439778 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B2685167 : Blo 439778 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B14352551 : Blo 439778 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B1344239 : Blo 439778 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B2523959 : Blo 439778 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B1672265 : Blo 439778 1672265 := bstep (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) B1254199
theorem B1116281 : Blo 439778 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B659711 : Blo 439778 659711 := bstep (se 1 (by rfl) ⟨494783, by rfl⟩ : syracuseStep 659711 = 989567) B989567
theorem B496219 : Blo 439778 496219 := bstep (se 1 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 496219 = 744329) B744329
theorem B661415 : Blo 439778 661415 := bstep (se 1 (by rfl) ⟨496061, by rfl⟩ : syracuseStep 661415 = 992123) B992123
theorem B20453303 : Blo 439778 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B3185189 : Blo 439778 3185189 := bstep (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) B597223
theorem B989999 : Blo 439778 989999 := bstep (se 1 (by rfl) ⟨742499, by rfl⟩ : syracuseStep 989999 = 1484999) B1484999
theorem B663023 : Blo 439778 663023 := bstep (se 1 (by rfl) ⟨497267, by rfl⟩ : syracuseStep 663023 = 994535) B994535
theorem B991259 : Blo 439778 991259 := bstep (se 1 (by rfl) ⟨743444, by rfl⟩ : syracuseStep 991259 = 1486889) B1486889
theorem B663599 : Blo 439778 663599 := bstep (se 1 (by rfl) ⟨497699, by rfl⟩ : syracuseStep 663599 = 995399) B995399
theorem B7152083 : Blo 439778 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B991871 : Blo 439778 991871 := bstep (se 1 (by rfl) ⟨743903, by rfl⟩ : syracuseStep 991871 = 1487807) B1487807
theorem B3777191 : Blo 439778 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B1418087 : Blo 439778 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1254815 : Blo 439778 1254815 := bstep (se 1 (by rfl) ⟨941111, by rfl⟩ : syracuseStep 1254815 = 1882223) B1882223
theorem B665465 : Blo 439778 665465 := bstep (se 2 (by rfl) ⟨249549, by rfl⟩ : syracuseStep 665465 = 499099) B499099
theorem B8498135 : Blo 439778 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B1486619 : Blo 439778 1486619 := bstep (se 1 (by rfl) ⟨1114964, by rfl⟩ : syracuseStep 1486619 = 2229929) B2229929
theorem B1684111 : Blo 439778 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B3062015 : Blo 439778 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B997703 : Blo 439778 997703 := bstep (se 1 (by rfl) ⟨748277, by rfl⟩ : syracuseStep 997703 = 1496555) B1496555
theorem B16071169 : Blo 439778 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B441447 : Blo 439778 441447 := bstep (se 1 (by rfl) ⟨331085, by rfl⟩ : syracuseStep 441447 = 662171) B662171
theorem B8306225 : Blo 439778 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B11648879 : Blo 439778 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B442591 : Blo 439778 442591 := bstep (se 1 (by rfl) ⟨331943, by rfl⟩ : syracuseStep 442591 = 663887) B663887
theorem B14271065 : Blo 439778 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B3786587 : Blo 439778 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B12142703 : Blo 439778 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B1790111 : Blo 439778 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B1889021 : Blo 439778 1889021 := bstep (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) B708383
theorem B2020151 : Blo 439778 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B2122843 : Blo 439778 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B747623 : Blo 439778 747623 := bstep (se 1 (by rfl) ⟨560717, by rfl⟩ : syracuseStep 747623 = 1121435) B1121435
theorem B4257679 : Blo 439778 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B9568367 : Blo 439778 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B1114843 : Blo 439778 1114843 := bstep (se 1 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 1114843 = 1672265) B1672265
theorem B2524391 : Blo 439778 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B8095135 : Blo 439778 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B13635535 : Blo 439778 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B659999 : Blo 439778 659999 := bstep (se 1 (by rfl) ⟨494999, by rfl⟩ : syracuseStep 659999 = 989999) B989999
theorem B660839 : Blo 439778 660839 := bstep (se 1 (by rfl) ⟨495629, by rfl⟩ : syracuseStep 660839 = 991259) B991259
theorem B661247 : Blo 439778 661247 := bstep (se 1 (by rfl) ⟨495935, by rfl⟩ : syracuseStep 661247 = 991871) B991871
theorem B661625 : Blo 439778 661625 := bstep (se 2 (by rfl) ⟨248109, by rfl⟩ : syracuseStep 661625 = 496219) B496219
theorem B498415 : Blo 439778 498415 := bstep (se 1 (by rfl) ⟨373811, by rfl⟩ : syracuseStep 498415 = 747623) B747623
theorem B991079 : Blo 439778 991079 := bstep (se 1 (by rfl) ⟨743309, by rfl⟩ : syracuseStep 991079 = 1486619) B1486619
theorem B5676905 : Blo 439778 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B2041343 : Blo 439778 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B665135 : Blo 439778 665135 := bstep (se 1 (by rfl) ⟨498851, by rfl⟩ : syracuseStep 665135 = 997703) B997703
theorem B9514043 : Blo 439778 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B896159 : Blo 439778 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B1682639 : Blo 439778 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B2830457 : Blo 439778 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B5387069 : Blo 439778 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B3781565 : Blo 439778 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B439807 : Blo 439778 439807 := bstep (se 1 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 439807 = 659711) B659711
theorem B440943 : Blo 439778 440943 := bstep (se 1 (by rfl) ⟨330707, by rfl⟩ : syracuseStep 440943 = 661415) B661415
theorem B442015 : Blo 439778 442015 := bstep (se 1 (by rfl) ⟨331511, by rfl⟩ : syracuseStep 442015 = 663023) B663023
theorem B442399 : Blo 439778 442399 := bstep (se 1 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 442399 = 663599) B663599
theorem B4768055 : Blo 439778 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B2245481 : Blo 439778 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B836543 : Blo 439778 836543 := bstep (se 1 (by rfl) ⟨627407, by rfl⟩ : syracuseStep 836543 = 1254815) B1254815
theorem B443643 : Blo 439778 443643 := bstep (se 1 (by rfl) ⟨332732, by rfl⟩ : syracuseStep 443643 = 665465) B665465
theorem B4773629 : Blo 439778 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B744187 : Blo 439778 744187 := bstep (se 1 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 744187 = 1116281) B1116281
theorem B5037389 : Blo 439778 5037389 := bstep (se 3 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 5037389 = 1889021) B1889021
theorem B2123459 : Blo 439778 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B2518127 : Blo 439778 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B5665423 : Blo 439778 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B21428225 : Blo 439778 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B5537483 : Blo 439778 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B7765919 : Blo 439778 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B3178703 : Blo 439778 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B557695 : Blo 439778 557695 := bstep (se 1 (by rfl) ⟨418271, by rfl⟩ : syracuseStep 557695 = 836543) B836543
theorem B3182419 : Blo 439778 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B660719 : Blo 439778 660719 := bstep (se 1 (by rfl) ⟨495539, by rfl⟩ : syracuseStep 660719 = 991079) B991079
theorem B1415639 : Blo 439778 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B1678751 : Blo 439778 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B597439 : Blo 439778 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B1121759 : Blo 439778 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B664553 : Blo 439778 664553 := bstep (se 2 (by rfl) ⟨249207, by rfl⟩ : syracuseStep 664553 = 498415) B498415
theorem B992249 : Blo 439778 992249 := bstep (se 2 (by rfl) ⟨372093, by rfl⟩ : syracuseStep 992249 = 744187) B744187
theorem B1682927 : Blo 439778 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B1486457 : Blo 439778 1486457 := bstep (se 2 (by rfl) ⟨557421, by rfl⟩ : syracuseStep 1486457 = 1114843) B1114843
theorem B10793513 : Blo 439778 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B439999 : Blo 439778 439999 := bstep (se 1 (by rfl) ⟨329999, by rfl⟩ : syracuseStep 439999 = 659999) B659999
theorem B440559 : Blo 439778 440559 := bstep (se 1 (by rfl) ⟨330419, by rfl⟩ : syracuseStep 440559 = 660839) B660839
theorem B440831 : Blo 439778 440831 := bstep (se 1 (by rfl) ⟨330623, by rfl⟩ : syracuseStep 440831 = 661247) B661247
theorem B441083 : Blo 439778 441083 := bstep (se 1 (by rfl) ⟨330812, by rfl⟩ : syracuseStep 441083 = 661625) B661625
theorem B3358259 : Blo 439778 3358259 := bstep (se 1 (by rfl) ⟨2518694, by rfl⟩ : syracuseStep 3358259 = 5037389) B5037389
theorem B3784603 : Blo 439778 3784603 := bstep (se 1 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 3784603 = 5676905) B5676905
theorem B7553897 : Blo 439778 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B1360895 : Blo 439778 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B443423 : Blo 439778 443423 := bstep (se 1 (by rfl) ⟨332567, by rfl⟩ : syracuseStep 443423 = 665135) B665135
theorem B6342695 : Blo 439778 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B1886971 : Blo 439778 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B3591379 : Blo 439778 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B3691655 : Blo 439778 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B6378911 : Blo 439778 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B1496987 : Blo 439778 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B18180713 : Blo 439778 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B2521043 : Blo 439778 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B14285483 : Blo 439778 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B5177279 : Blo 439778 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B4228463 : Blo 439778 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B2461103 : Blo 439778 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B4788505 : Blo 439778 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B1119167 : Blo 439778 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B661499 : Blo 439778 661499 := bstep (se 1 (by rfl) ⟨496124, by rfl⟩ : syracuseStep 661499 = 992249) B992249
theorem B1121951 : Blo 439778 1121951 := bstep (se 1 (by rfl) ⟨841463, by rfl⟩ : syracuseStep 1121951 = 1682927) B1682927
theorem B3186341 : Blo 439778 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B990971 : Blo 439778 990971 := bstep (se 1 (by rfl) ⟨743228, by rfl⟩ : syracuseStep 990971 = 1486457) B1486457
theorem B1680695 : Blo 439778 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B2238839 : Blo 439778 2238839 := bstep (se 1 (by rfl) ⟨1679129, by rfl⟩ : syracuseStep 2238839 = 3358259) B3358259
theorem B13806077 : Blo 439778 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B440479 : Blo 439778 440479 := bstep (se 1 (by rfl) ⟨330359, by rfl⟩ : syracuseStep 440479 = 660719) B660719
theorem B997991 : Blo 439778 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B4243225 : Blo 439778 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B443035 : Blo 439778 443035 := bstep (se 1 (by rfl) ⟨332276, by rfl⟩ : syracuseStep 443035 = 664553) B664553
theorem B7195675 : Blo 439778 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B9523655 : Blo 439778 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B2119135 : Blo 439778 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B5035931 : Blo 439778 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B743593 : Blo 439778 743593 := bstep (se 2 (by rfl) ⟨278847, by rfl⟩ : syracuseStep 743593 = 557695) B557695
theorem B3629053 : Blo 439778 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B4252607 : Blo 439778 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B2515961 : Blo 439778 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B943759 : Blo 439778 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B747839 : Blo 439778 747839 := bstep (se 1 (by rfl) ⟨560879, by rfl⟩ : syracuseStep 747839 = 1121759) B1121759
theorem B12120475 : Blo 439778 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B5046137 : Blo 439778 5046137 := bstep (se 2 (by rfl) ⟨1892301, by rfl⟩ : syracuseStep 5046137 = 3784603) B3784603
theorem B2818975 : Blo 439778 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B1640735 : Blo 439778 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B660647 : Blo 439778 660647 := bstep (se 1 (by rfl) ⟨495485, by rfl⟩ : syracuseStep 660647 = 990971) B990971
theorem B16160633 : Blo 439778 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B1677307 : Blo 439778 1677307 := bstep (se 1 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 1677307 = 2515961) B2515961
theorem B1120463 : Blo 439778 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B498559 : Blo 439778 498559 := bstep (se 1 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 498559 = 747839) B747839
theorem B2825513 : Blo 439778 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B991457 : Blo 439778 991457 := bstep (se 2 (by rfl) ⟨371796, by rfl⟩ : syracuseStep 991457 = 743593) B743593
theorem B665327 : Blo 439778 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B1258345 : Blo 439778 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B3357287 : Blo 439778 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B440999 : Blo 439778 440999 := bstep (se 1 (by rfl) ⟨330749, by rfl⟩ : syracuseStep 440999 = 661499) B661499
theorem B2835071 : Blo 439778 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B36816205 : Blo 439778 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B1492559 : Blo 439778 1492559 := bstep (se 1 (by rfl) ⟨1119419, by rfl⟩ : syracuseStep 1492559 = 2238839) B2238839
theorem B5657633 : Blo 439778 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B3364091 : Blo 439778 3364091 := bstep (se 1 (by rfl) ⟨2523068, by rfl⟩ : syracuseStep 3364091 = 5046137) B5046137
theorem B4838737 : Blo 439778 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B6349103 : Blo 439778 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B746111 : Blo 439778 746111 := bstep (se 1 (by rfl) ⟨559583, by rfl⟩ : syracuseStep 746111 = 1119167) B1119167
theorem B9594233 : Blo 439778 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B747967 : Blo 439778 747967 := bstep (se 1 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 747967 = 1121951) B1121951
theorem B2124227 : Blo 439778 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B6384673 : Blo 439778 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B49088273 : Blo 439778 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B3771755 : Blo 439778 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B660971 : Blo 439778 660971 := bstep (se 1 (by rfl) ⟨495728, by rfl⟩ : syracuseStep 660971 = 991457) B991457
theorem B4232735 : Blo 439778 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B497407 : Blo 439778 497407 := bstep (se 1 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 497407 = 746111) B746111
theorem B6396155 : Blo 439778 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B1677793 : Blo 439778 1677793 := bstep (se 2 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 1677793 = 1258345) B1258345
theorem B1416151 : Blo 439778 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B2236409 : Blo 439778 2236409 := bstep (se 2 (by rfl) ⟨838653, by rfl⟩ : syracuseStep 2236409 = 1677307) B1677307
theorem B664745 : Blo 439778 664745 := bstep (se 2 (by rfl) ⟨249279, by rfl⟩ : syracuseStep 664745 = 498559) B498559
theorem B2238191 : Blo 439778 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B995039 : Blo 439778 995039 := bstep (se 1 (by rfl) ⟨746279, by rfl⟩ : syracuseStep 995039 = 1492559) B1492559
theorem B1093823 : Blo 439778 1093823 := bstep (se 1 (by rfl) ⟨820367, by rfl⟩ : syracuseStep 1093823 = 1640735) B1640735
theorem B997289 : Blo 439778 997289 := bstep (se 2 (by rfl) ⟨373983, by rfl⟩ : syracuseStep 997289 = 747967) B747967
theorem B440431 : Blo 439778 440431 := bstep (se 1 (by rfl) ⟨330323, by rfl⟩ : syracuseStep 440431 = 660647) B660647
theorem B2242727 : Blo 439778 2242727 := bstep (se 1 (by rfl) ⟨1682045, by rfl⟩ : syracuseStep 2242727 = 3364091) B3364091
theorem B1883675 : Blo 439778 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B443551 : Blo 439778 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B1890047 : Blo 439778 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B3758633 : Blo 439778 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B10773755 : Blo 439778 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B8512897 : Blo 439778 8512897 := bstep (se 2 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 8512897 = 6384673) B6384673
theorem B746975 : Blo 439778 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B6451649 : Blo 439778 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B2821823 : Blo 439778 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B4264103 : Blo 439778 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B7182503 : Blo 439778 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B497983 : Blo 439778 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B663209 : Blo 439778 663209 := bstep (se 2 (by rfl) ⟨248703, by rfl⟩ : syracuseStep 663209 = 497407) B497407
theorem B663359 : Blo 439778 663359 := bstep (se 1 (by rfl) ⟨497519, by rfl⟩ : syracuseStep 663359 = 995039) B995039
theorem B729215 : Blo 439778 729215 := bstep (se 1 (by rfl) ⟨546911, by rfl⟩ : syracuseStep 729215 = 1093823) B1093823
theorem B523608245 : Blo 439778 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B4301099 : Blo 439778 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B2237057 : Blo 439778 2237057 := bstep (se 2 (by rfl) ⟨838896, by rfl⟩ : syracuseStep 2237057 = 1677793) B1677793
theorem B664859 : Blo 439778 664859 := bstep (se 1 (by rfl) ⟨498644, by rfl⟩ : syracuseStep 664859 = 997289) B997289
theorem B1255783 : Blo 439778 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B11350529 : Blo 439778 11350529 := bstep (se 2 (by rfl) ⟨4256448, by rfl⟩ : syracuseStep 11350529 = 8512897) B8512897
theorem B440647 : Blo 439778 440647 := bstep (se 1 (by rfl) ⟨330485, by rfl⟩ : syracuseStep 440647 = 660971) B660971
theorem B1260031 : Blo 439778 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B2505755 : Blo 439778 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B1490939 : Blo 439778 1490939 := bstep (se 1 (by rfl) ⟨1118204, by rfl⟩ : syracuseStep 1490939 = 2236409) B2236409
theorem B443163 : Blo 439778 443163 := bstep (se 1 (by rfl) ⟨332372, by rfl⟩ : syracuseStep 443163 = 664745) B664745
theorem B1492127 : Blo 439778 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B1888201 : Blo 439778 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1495151 : Blo 439778 1495151 := bstep (se 1 (by rfl) ⟨1121363, by rfl⟩ : syracuseStep 1495151 = 2242727) B2242727
theorem B2514503 : Blo 439778 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B1674377 : Blo 439778 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B4788335 : Blo 439778 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B1676335 : Blo 439778 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B663977 : Blo 439778 663977 := bstep (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) B497983
theorem B1680041 : Blo 439778 1680041 := bstep (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) B1260031
theorem B993959 : Blo 439778 993959 := bstep (se 1 (by rfl) ⟨745469, by rfl⟩ : syracuseStep 993959 = 1490939) B1490939
theorem B994751 : Blo 439778 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B1881215 : Blo 439778 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B996767 : Blo 439778 996767 := bstep (se 1 (by rfl) ⟨747575, by rfl⟩ : syracuseStep 996767 = 1495151) B1495151
theorem B442139 : Blo 439778 442139 := bstep (se 1 (by rfl) ⟨331604, by rfl⟩ : syracuseStep 442139 = 663209) B663209
theorem B442239 : Blo 439778 442239 := bstep (se 1 (by rfl) ⟨331679, by rfl⟩ : syracuseStep 442239 = 663359) B663359
theorem B2867399 : Blo 439778 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B1491371 : Blo 439778 1491371 := bstep (se 1 (by rfl) ⟨1118528, by rfl⟩ : syracuseStep 1491371 = 2237057) B2237057
theorem B443239 : Blo 439778 443239 := bstep (se 1 (by rfl) ⟨332429, by rfl⟩ : syracuseStep 443239 = 664859) B664859
theorem B2842735 : Blo 439778 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B2517601 : Blo 439778 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B486143 : Blo 439778 486143 := bstep (se 1 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 486143 = 729215) B729215
theorem B349072163 : Blo 439778 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B7567019 : Blo 439778 7567019 := bstep (se 1 (by rfl) ⟨5675264, by rfl⟩ : syracuseStep 7567019 = 11350529) B11350529
theorem B1670503 : Blo 439778 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B1116251 : Blo 439778 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B1120027 : Blo 439778 1120027 := bstep (se 1 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 1120027 = 1680041) B1680041
theorem B2235113 : Blo 439778 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B662639 : Blo 439778 662639 := bstep (se 1 (by rfl) ⟨496979, by rfl⟩ : syracuseStep 662639 = 993959) B993959
theorem B663167 : Blo 439778 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B1254143 : Blo 439778 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B664511 : Blo 439778 664511 := bstep (se 1 (by rfl) ⟨498383, by rfl⟩ : syracuseStep 664511 = 996767) B996767
theorem B1911599 : Blo 439778 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B994247 : Blo 439778 994247 := bstep (se 1 (by rfl) ⟨745685, by rfl⟩ : syracuseStep 994247 = 1491371) B1491371
theorem B3192223 : Blo 439778 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B3356801 : Blo 439778 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B442651 : Blo 439778 442651 := bstep (se 1 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 442651 = 663977) B663977
theorem B3790313 : Blo 439778 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B232714775 : Blo 439778 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B5044679 : Blo 439778 5044679 := bstep (se 1 (by rfl) ⟨3783509, by rfl⟩ : syracuseStep 5044679 = 7567019) B7567019
theorem B2227337 : Blo 439778 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B20742101 : Blo 439778 20742101 := bstep (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) B486143
theorem B2526875 : Blo 439778 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B662831 : Blo 439778 662831 := bstep (se 1 (by rfl) ⟨497123, by rfl⟩ : syracuseStep 662831 = 994247) B994247
theorem B2237867 : Blo 439778 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B1484891 : Blo 439778 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B1490075 : Blo 439778 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B441759 : Blo 439778 441759 := bstep (se 1 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 441759 = 662639) B662639
theorem B442111 : Blo 439778 442111 := bstep (se 1 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 442111 = 663167) B663167
theorem B836095 : Blo 439778 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B443007 : Blo 439778 443007 := bstep (se 1 (by rfl) ⟨332255, by rfl⟩ : syracuseStep 443007 = 664511) B664511
theorem B1493369 : Blo 439778 1493369 := bstep (se 2 (by rfl) ⟨560013, by rfl⟩ : syracuseStep 1493369 = 1120027) B1120027
theorem B155143183 : Blo 439778 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B3363119 : Blo 439778 3363119 := bstep (se 1 (by rfl) ⟨2522339, by rfl⟩ : syracuseStep 3363119 = 5044679) B5044679
theorem B744167 : Blo 439778 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B1274399 : Blo 439778 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B4256297 : Blo 439778 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B13828067 : Blo 439778 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B1114793 : Blo 439778 1114793 := bstep (se 2 (by rfl) ⟨418047, by rfl⟩ : syracuseStep 1114793 = 836095) B836095
theorem B496111 : Blo 439778 496111 := bstep (se 1 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 496111 = 744167) B744167
theorem B989927 : Blo 439778 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B993383 : Blo 439778 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B9218711 : Blo 439778 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B995579 : Blo 439778 995579 := bstep (se 1 (by rfl) ⟨746684, by rfl⟩ : syracuseStep 995579 = 1493369) B1493369
theorem B1684583 : Blo 439778 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B2242079 : Blo 439778 2242079 := bstep (se 1 (by rfl) ⟨1681559, by rfl⟩ : syracuseStep 2242079 = 3363119) B3363119
theorem B441887 : Blo 439778 441887 := bstep (se 1 (by rfl) ⟨331415, by rfl⟩ : syracuseStep 441887 = 662831) B662831
theorem B1491911 : Blo 439778 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B2837531 : Blo 439778 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B206857577 : Blo 439778 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B849599 : Blo 439778 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B659951 : Blo 439778 659951 := bstep (se 1 (by rfl) ⟨494963, by rfl⟩ : syracuseStep 659951 = 989927) B989927
theorem B661481 : Blo 439778 661481 := bstep (se 2 (by rfl) ⟨248055, by rfl⟩ : syracuseStep 661481 = 496111) B496111
theorem B662255 : Blo 439778 662255 := bstep (se 1 (by rfl) ⟨496691, by rfl⟩ : syracuseStep 662255 = 993383) B993383
theorem B663719 : Blo 439778 663719 := bstep (se 1 (by rfl) ⟨497789, by rfl⟩ : syracuseStep 663719 = 995579) B995579
theorem B1123055 : Blo 439778 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B566399 : Blo 439778 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B994607 : Blo 439778 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B137905051 : Blo 439778 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B6145807 : Blo 439778 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B1494719 : Blo 439778 1494719 := bstep (se 1 (by rfl) ⟨1121039, by rfl⟩ : syracuseStep 1494719 = 2242079) B2242079
theorem B743195 : Blo 439778 743195 := bstep (se 1 (by rfl) ⟨557396, by rfl⟩ : syracuseStep 743195 = 1114793) B1114793
theorem B1891687 : Blo 439778 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B8194409 : Blo 439778 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B1510397 : Blo 439778 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B495463 : Blo 439778 495463 := bstep (se 1 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 495463 = 743195) B743195
theorem B663071 : Blo 439778 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B183873401 : Blo 439778 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B996479 : Blo 439778 996479 := bstep (se 1 (by rfl) ⟨747359, by rfl⟩ : syracuseStep 996479 = 1494719) B1494719
theorem B439967 : Blo 439778 439967 := bstep (se 1 (by rfl) ⟨329975, by rfl⟩ : syracuseStep 439967 = 659951) B659951
theorem B440987 : Blo 439778 440987 := bstep (se 1 (by rfl) ⟨330740, by rfl⟩ : syracuseStep 440987 = 661481) B661481
theorem B441503 : Blo 439778 441503 := bstep (se 1 (by rfl) ⟨331127, by rfl⟩ : syracuseStep 441503 = 662255) B662255
theorem B442479 : Blo 439778 442479 := bstep (se 1 (by rfl) ⟨331859, by rfl⟩ : syracuseStep 442479 = 663719) B663719
theorem B748703 : Blo 439778 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B2522249 : Blo 439778 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B660617 : Blo 439778 660617 := bstep (se 2 (by rfl) ⟨247731, by rfl⟩ : syracuseStep 660617 = 495463) B495463
theorem B499135 : Blo 439778 499135 := bstep (se 1 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 499135 = 748703) B748703
theorem B664319 : Blo 439778 664319 := bstep (se 1 (by rfl) ⟨498239, by rfl⟩ : syracuseStep 664319 = 996479) B996479
theorem B1681499 : Blo 439778 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B442047 : Blo 439778 442047 := bstep (se 1 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 442047 = 663071) B663071
theorem B5462939 : Blo 439778 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B1006931 : Blo 439778 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B122582267 : Blo 439778 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B3641959 : Blo 439778 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B1120999 : Blo 439778 1120999 := bstep (se 1 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 1120999 = 1681499) B1681499
theorem B665513 : Blo 439778 665513 := bstep (se 2 (by rfl) ⟨249567, by rfl⟩ : syracuseStep 665513 = 499135) B499135
theorem B440411 : Blo 439778 440411 := bstep (se 1 (by rfl) ⟨330308, by rfl⟩ : syracuseStep 440411 = 660617) B660617
theorem B442879 : Blo 439778 442879 := bstep (se 1 (by rfl) ⟨332159, by rfl⟩ : syracuseStep 442879 = 664319) B664319
theorem B81721511 : Blo 439778 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B2685149 : Blo 439778 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B4855945 : Blo 439778 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B443675 : Blo 439778 443675 := bstep (se 1 (by rfl) ⟨332756, by rfl⟩ : syracuseStep 443675 = 665513) B665513
theorem B1494665 : Blo 439778 1494665 := bstep (se 2 (by rfl) ⟨560499, by rfl⟩ : syracuseStep 1494665 = 1120999) B1120999
theorem B54481007 : Blo 439778 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B1790099 : Blo 439778 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B996443 : Blo 439778 996443 := bstep (se 1 (by rfl) ⟨747332, by rfl⟩ : syracuseStep 996443 = 1494665) B1494665
theorem B36320671 : Blo 439778 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B1193399 : Blo 439778 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B6474593 : Blo 439778 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B664295 : Blo 439778 664295 := bstep (se 1 (by rfl) ⟨498221, by rfl⟩ : syracuseStep 664295 = 996443) B996443
theorem B795599 : Blo 439778 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B48427561 : Blo 439778 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B17265581 : Blo 439778 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B530399 : Blo 439778 530399 := bstep (se 1 (by rfl) ⟨397799, by rfl⟩ : syracuseStep 530399 = 795599) B795599
theorem B11510387 : Blo 439778 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B442863 : Blo 439778 442863 := bstep (se 1 (by rfl) ⟨332147, by rfl⟩ : syracuseStep 442863 = 664295) B664295
theorem B64570081 : Blo 439778 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B1414397 : Blo 439778 1414397 := bstep (se 3 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 1414397 = 530399) B530399
theorem B7673591 : Blo 439778 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B86093441 : Blo 439778 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B5115727 : Blo 439778 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B57395627 : Blo 439778 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B942931 : Blo 439778 942931 := bstep (se 1 (by rfl) ⟨707198, by rfl⟩ : syracuseStep 942931 = 1414397) B1414397
theorem B6820969 : Blo 439778 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B1257241 : Blo 439778 1257241 := bstep (se 2 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 1257241 = 942931) B942931
theorem B38263751 : Blo 439778 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B1676321 : Blo 439778 1676321 := bstep (se 2 (by rfl) ⟨628620, by rfl⟩ : syracuseStep 1676321 = 1257241) B1257241
theorem B25509167 : Blo 439778 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B9094625 : Blo 439778 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B6063083 : Blo 439778 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B1117547 : Blo 439778 1117547 := bstep (se 1 (by rfl) ⟨838160, by rfl⟩ : syracuseStep 1117547 = 1676321) B1676321
theorem B17006111 : Blo 439778 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B4042055 : Blo 439778 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B745031 : Blo 439778 745031 := bstep (se 1 (by rfl) ⟨558773, by rfl⟩ : syracuseStep 745031 = 1117547) B1117547
theorem B11337407 : Blo 439778 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B496687 : Blo 439778 496687 := bstep (se 1 (by rfl) ⟨372515, by rfl⟩ : syracuseStep 496687 = 745031) B745031
theorem B2694703 : Blo 439778 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B7558271 : Blo 439778 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B662249 : Blo 439778 662249 := bstep (se 2 (by rfl) ⟨248343, by rfl⟩ : syracuseStep 662249 = 496687) B496687
theorem B3592937 : Blo 439778 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B5038847 : Blo 439778 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B9581165 : Blo 439778 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B441499 : Blo 439778 441499 := bstep (se 1 (by rfl) ⟨331124, by rfl⟩ : syracuseStep 441499 = 662249) B662249
theorem B3359231 : Blo 439778 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B2239487 : Blo 439778 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B6387443 : Blo 439778 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B1492991 : Blo 439778 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B4258295 : Blo 439778 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B995327 : Blo 439778 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B2838863 : Blo 439778 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B663551 : Blo 439778 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B1892575 : Blo 439778 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B2523433 : Blo 439778 2523433 := bstep (se 2 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 2523433 = 1892575) B1892575
theorem B442367 : Blo 439778 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B3364577 : Blo 439778 3364577 := bstep (se 2 (by rfl) ⟨1261716, by rfl⟩ : syracuseStep 3364577 = 2523433) B2523433
theorem B2243051 : Blo 439778 2243051 := bstep (se 1 (by rfl) ⟨1682288, by rfl⟩ : syracuseStep 2243051 = 3364577) B3364577
theorem B1495367 : Blo 439778 1495367 := bstep (se 1 (by rfl) ⟨1121525, by rfl⟩ : syracuseStep 1495367 = 2243051) B2243051
theorem B996911 : Blo 439778 996911 := bstep (se 1 (by rfl) ⟨747683, by rfl⟩ : syracuseStep 996911 = 1495367) B1495367
theorem B664607 : Blo 439778 664607 := bstep (se 1 (by rfl) ⟨498455, by rfl⟩ : syracuseStep 664607 = 996911) B996911
theorem B443071 : Blo 439778 443071 := bstep (se 1 (by rfl) ⟨332303, by rfl⟩ : syracuseStep 443071 = 664607) B664607

theorem C0 (j : ℕ) (h1 : 109944 ≤ j) (h2 : j ≤ 110643) : Blo 439778 (4 * j + 3) := by
  interval_cases j
  · exact B439779
  · exact B439783
  · exact B439787
  · exact B439791
  · exact B439795
  · exact B439799
  · exact B439803
  · exact B439807
  · exact B439811
  · exact B439815
  · exact B439819
  · exact B439823
  · exact B439827
  · exact B439831
  · exact B439835
  · exact B439839
  · exact B439843
  · exact B439847
  · exact B439851
  · exact B439855
  · exact B439859
  · exact B439863
  · exact B439867
  · exact B439871
  · exact B439875
  · exact B439879
  · exact B439883
  · exact B439887
  · exact B439891
  · exact B439895
  · exact B439899
  · exact B439903
  · exact B439907
  · exact B439911
  · exact B439915
  · exact B439919
  · exact B439923
  · exact B439927
  · exact B439931
  · exact B439935
  · exact B439939
  · exact B439943
  · exact B439947
  · exact B439951
  · exact B439955
  · exact B439959
  · exact B439963
  · exact B439967
  · exact B439971
  · exact B439975
  · exact B439979
  · exact B439983
  · exact B439987
  · exact B439991
  · exact B439995
  · exact B439999
  · exact B440003
  · exact B440007
  · exact B440011
  · exact B440015
  · exact B440019
  · exact B440023
  · exact B440027
  · exact B440031
  · exact B440035
  · exact B440039
  · exact B440043
  · exact B440047
  · exact B440051
  · exact B440055
  · exact B440059
  · exact B440063
  · exact B440067
  · exact B440071
  · exact B440075
  · exact B440079
  · exact B440083
  · exact B440087
  · exact B440091
  · exact B440095
  · exact B440099
  · exact B440103
  · exact B440107
  · exact B440111
  · exact B440115
  · exact B440119
  · exact B440123
  · exact B440127
  · exact B440131
  · exact B440135
  · exact B440139
  · exact B440143
  · exact B440147
  · exact B440151
  · exact B440155
  · exact B440159
  · exact B440163
  · exact B440167
  · exact B440171
  · exact B440175
  · exact B440179
  · exact B440183
  · exact B440187
  · exact B440191
  · exact B440195
  · exact B440199
  · exact B440203
  · exact B440207
  · exact B440211
  · exact B440215
  · exact B440219
  · exact B440223
  · exact B440227
  · exact B440231
  · exact B440235
  · exact B440239
  · exact B440243
  · exact B440247
  · exact B440251
  · exact B440255
  · exact B440259
  · exact B440263
  · exact B440267
  · exact B440271
  · exact B440275
  · exact B440279
  · exact B440283
  · exact B440287
  · exact B440291
  · exact B440295
  · exact B440299
  · exact B440303
  · exact B440307
  · exact B440311
  · exact B440315
  · exact B440319
  · exact B440323
  · exact B440327
  · exact B440331
  · exact B440335
  · exact B440339
  · exact B440343
  · exact B440347
  · exact B440351
  · exact B440355
  · exact B440359
  · exact B440363
  · exact B440367
  · exact B440371
  · exact B440375
  · exact B440379
  · exact B440383
  · exact B440387
  · exact B440391
  · exact B440395
  · exact B440399
  · exact B440403
  · exact B440407
  · exact B440411
  · exact B440415
  · exact B440419
  · exact B440423
  · exact B440427
  · exact B440431
  · exact B440435
  · exact B440439
  · exact B440443
  · exact B440447
  · exact B440451
  · exact B440455
  · exact B440459
  · exact B440463
  · exact B440467
  · exact B440471
  · exact B440475
  · exact B440479
  · exact B440483
  · exact B440487
  · exact B440491
  · exact B440495
  · exact B440499
  · exact B440503
  · exact B440507
  · exact B440511
  · exact B440515
  · exact B440519
  · exact B440523
  · exact B440527
  · exact B440531
  · exact B440535
  · exact B440539
  · exact B440543
  · exact B440547
  · exact B440551
  · exact B440555
  · exact B440559
  · exact B440563
  · exact B440567
  · exact B440571
  · exact B440575
  · exact B440579
  · exact B440583
  · exact B440587
  · exact B440591
  · exact B440595
  · exact B440599
  · exact B440603
  · exact B440607
  · exact B440611
  · exact B440615
  · exact B440619
  · exact B440623
  · exact B440627
  · exact B440631
  · exact B440635
  · exact B440639
  · exact B440643
  · exact B440647
  · exact B440651
  · exact B440655
  · exact B440659
  · exact B440663
  · exact B440667
  · exact B440671
  · exact B440675
  · exact B440679
  · exact B440683
  · exact B440687
  · exact B440691
  · exact B440695
  · exact B440699
  · exact B440703
  · exact B440707
  · exact B440711
  · exact B440715
  · exact B440719
  · exact B440723
  · exact B440727
  · exact B440731
  · exact B440735
  · exact B440739
  · exact B440743
  · exact B440747
  · exact B440751
  · exact B440755
  · exact B440759
  · exact B440763
  · exact B440767
  · exact B440771
  · exact B440775
  · exact B440779
  · exact B440783
  · exact B440787
  · exact B440791
  · exact B440795
  · exact B440799
  · exact B440803
  · exact B440807
  · exact B440811
  · exact B440815
  · exact B440819
  · exact B440823
  · exact B440827
  · exact B440831
  · exact B440835
  · exact B440839
  · exact B440843
  · exact B440847
  · exact B440851
  · exact B440855
  · exact B440859
  · exact B440863
  · exact B440867
  · exact B440871
  · exact B440875
  · exact B440879
  · exact B440883
  · exact B440887
  · exact B440891
  · exact B440895
  · exact B440899
  · exact B440903
  · exact B440907
  · exact B440911
  · exact B440915
  · exact B440919
  · exact B440923
  · exact B440927
  · exact B440931
  · exact B440935
  · exact B440939
  · exact B440943
  · exact B440947
  · exact B440951
  · exact B440955
  · exact B440959
  · exact B440963
  · exact B440967
  · exact B440971
  · exact B440975
  · exact B440979
  · exact B440983
  · exact B440987
  · exact B440991
  · exact B440995
  · exact B440999
  · exact B441003
  · exact B441007
  · exact B441011
  · exact B441015
  · exact B441019
  · exact B441023
  · exact B441027
  · exact B441031
  · exact B441035
  · exact B441039
  · exact B441043
  · exact B441047
  · exact B441051
  · exact B441055
  · exact B441059
  · exact B441063
  · exact B441067
  · exact B441071
  · exact B441075
  · exact B441079
  · exact B441083
  · exact B441087
  · exact B441091
  · exact B441095
  · exact B441099
  · exact B441103
  · exact B441107
  · exact B441111
  · exact B441115
  · exact B441119
  · exact B441123
  · exact B441127
  · exact B441131
  · exact B441135
  · exact B441139
  · exact B441143
  · exact B441147
  · exact B441151
  · exact B441155
  · exact B441159
  · exact B441163
  · exact B441167
  · exact B441171
  · exact B441175
  · exact B441179
  · exact B441183
  · exact B441187
  · exact B441191
  · exact B441195
  · exact B441199
  · exact B441203
  · exact B441207
  · exact B441211
  · exact B441215
  · exact B441219
  · exact B441223
  · exact B441227
  · exact B441231
  · exact B441235
  · exact B441239
  · exact B441243
  · exact B441247
  · exact B441251
  · exact B441255
  · exact B441259
  · exact B441263
  · exact B441267
  · exact B441271
  · exact B441275
  · exact B441279
  · exact B441283
  · exact B441287
  · exact B441291
  · exact B441295
  · exact B441299
  · exact B441303
  · exact B441307
  · exact B441311
  · exact B441315
  · exact B441319
  · exact B441323
  · exact B441327
  · exact B441331
  · exact B441335
  · exact B441339
  · exact B441343
  · exact B441347
  · exact B441351
  · exact B441355
  · exact B441359
  · exact B441363
  · exact B441367
  · exact B441371
  · exact B441375
  · exact B441379
  · exact B441383
  · exact B441387
  · exact B441391
  · exact B441395
  · exact B441399
  · exact B441403
  · exact B441407
  · exact B441411
  · exact B441415
  · exact B441419
  · exact B441423
  · exact B441427
  · exact B441431
  · exact B441435
  · exact B441439
  · exact B441443
  · exact B441447
  · exact B441451
  · exact B441455
  · exact B441459
  · exact B441463
  · exact B441467
  · exact B441471
  · exact B441475
  · exact B441479
  · exact B441483
  · exact B441487
  · exact B441491
  · exact B441495
  · exact B441499
  · exact B441503
  · exact B441507
  · exact B441511
  · exact B441515
  · exact B441519
  · exact B441523
  · exact B441527
  · exact B441531
  · exact B441535
  · exact B441539
  · exact B441543
  · exact B441547
  · exact B441551
  · exact B441555
  · exact B441559
  · exact B441563
  · exact B441567
  · exact B441571
  · exact B441575
  · exact B441579
  · exact B441583
  · exact B441587
  · exact B441591
  · exact B441595
  · exact B441599
  · exact B441603
  · exact B441607
  · exact B441611
  · exact B441615
  · exact B441619
  · exact B441623
  · exact B441627
  · exact B441631
  · exact B441635
  · exact B441639
  · exact B441643
  · exact B441647
  · exact B441651
  · exact B441655
  · exact B441659
  · exact B441663
  · exact B441667
  · exact B441671
  · exact B441675
  · exact B441679
  · exact B441683
  · exact B441687
  · exact B441691
  · exact B441695
  · exact B441699
  · exact B441703
  · exact B441707
  · exact B441711
  · exact B441715
  · exact B441719
  · exact B441723
  · exact B441727
  · exact B441731
  · exact B441735
  · exact B441739
  · exact B441743
  · exact B441747
  · exact B441751
  · exact B441755
  · exact B441759
  · exact B441763
  · exact B441767
  · exact B441771
  · exact B441775
  · exact B441779
  · exact B441783
  · exact B441787
  · exact B441791
  · exact B441795
  · exact B441799
  · exact B441803
  · exact B441807
  · exact B441811
  · exact B441815
  · exact B441819
  · exact B441823
  · exact B441827
  · exact B441831
  · exact B441835
  · exact B441839
  · exact B441843
  · exact B441847
  · exact B441851
  · exact B441855
  · exact B441859
  · exact B441863
  · exact B441867
  · exact B441871
  · exact B441875
  · exact B441879
  · exact B441883
  · exact B441887
  · exact B441891
  · exact B441895
  · exact B441899
  · exact B441903
  · exact B441907
  · exact B441911
  · exact B441915
  · exact B441919
  · exact B441923
  · exact B441927
  · exact B441931
  · exact B441935
  · exact B441939
  · exact B441943
  · exact B441947
  · exact B441951
  · exact B441955
  · exact B441959
  · exact B441963
  · exact B441967
  · exact B441971
  · exact B441975
  · exact B441979
  · exact B441983
  · exact B441987
  · exact B441991
  · exact B441995
  · exact B441999
  · exact B442003
  · exact B442007
  · exact B442011
  · exact B442015
  · exact B442019
  · exact B442023
  · exact B442027
  · exact B442031
  · exact B442035
  · exact B442039
  · exact B442043
  · exact B442047
  · exact B442051
  · exact B442055
  · exact B442059
  · exact B442063
  · exact B442067
  · exact B442071
  · exact B442075
  · exact B442079
  · exact B442083
  · exact B442087
  · exact B442091
  · exact B442095
  · exact B442099
  · exact B442103
  · exact B442107
  · exact B442111
  · exact B442115
  · exact B442119
  · exact B442123
  · exact B442127
  · exact B442131
  · exact B442135
  · exact B442139
  · exact B442143
  · exact B442147
  · exact B442151
  · exact B442155
  · exact B442159
  · exact B442163
  · exact B442167
  · exact B442171
  · exact B442175
  · exact B442179
  · exact B442183
  · exact B442187
  · exact B442191
  · exact B442195
  · exact B442199
  · exact B442203
  · exact B442207
  · exact B442211
  · exact B442215
  · exact B442219
  · exact B442223
  · exact B442227
  · exact B442231
  · exact B442235
  · exact B442239
  · exact B442243
  · exact B442247
  · exact B442251
  · exact B442255
  · exact B442259
  · exact B442263
  · exact B442267
  · exact B442271
  · exact B442275
  · exact B442279
  · exact B442283
  · exact B442287
  · exact B442291
  · exact B442295
  · exact B442299
  · exact B442303
  · exact B442307
  · exact B442311
  · exact B442315
  · exact B442319
  · exact B442323
  · exact B442327
  · exact B442331
  · exact B442335
  · exact B442339
  · exact B442343
  · exact B442347
  · exact B442351
  · exact B442355
  · exact B442359
  · exact B442363
  · exact B442367
  · exact B442371
  · exact B442375
  · exact B442379
  · exact B442383
  · exact B442387
  · exact B442391
  · exact B442395
  · exact B442399
  · exact B442403
  · exact B442407
  · exact B442411
  · exact B442415
  · exact B442419
  · exact B442423
  · exact B442427
  · exact B442431
  · exact B442435
  · exact B442439
  · exact B442443
  · exact B442447
  · exact B442451
  · exact B442455
  · exact B442459
  · exact B442463
  · exact B442467
  · exact B442471
  · exact B442475
  · exact B442479
  · exact B442483
  · exact B442487
  · exact B442491
  · exact B442495
  · exact B442499
  · exact B442503
  · exact B442507
  · exact B442511
  · exact B442515
  · exact B442519
  · exact B442523
  · exact B442527
  · exact B442531
  · exact B442535
  · exact B442539
  · exact B442543
  · exact B442547
  · exact B442551
  · exact B442555
  · exact B442559
  · exact B442563
  · exact B442567
  · exact B442571
  · exact B442575

theorem C1 (j : ℕ) (h1 : 110644 ≤ j) (h2 : j ≤ 110943) : Blo 439778 (4 * j + 3) := by
  interval_cases j
  · exact B442579
  · exact B442583
  · exact B442587
  · exact B442591
  · exact B442595
  · exact B442599
  · exact B442603
  · exact B442607
  · exact B442611
  · exact B442615
  · exact B442619
  · exact B442623
  · exact B442627
  · exact B442631
  · exact B442635
  · exact B442639
  · exact B442643
  · exact B442647
  · exact B442651
  · exact B442655
  · exact B442659
  · exact B442663
  · exact B442667
  · exact B442671
  · exact B442675
  · exact B442679
  · exact B442683
  · exact B442687
  · exact B442691
  · exact B442695
  · exact B442699
  · exact B442703
  · exact B442707
  · exact B442711
  · exact B442715
  · exact B442719
  · exact B442723
  · exact B442727
  · exact B442731
  · exact B442735
  · exact B442739
  · exact B442743
  · exact B442747
  · exact B442751
  · exact B442755
  · exact B442759
  · exact B442763
  · exact B442767
  · exact B442771
  · exact B442775
  · exact B442779
  · exact B442783
  · exact B442787
  · exact B442791
  · exact B442795
  · exact B442799
  · exact B442803
  · exact B442807
  · exact B442811
  · exact B442815
  · exact B442819
  · exact B442823
  · exact B442827
  · exact B442831
  · exact B442835
  · exact B442839
  · exact B442843
  · exact B442847
  · exact B442851
  · exact B442855
  · exact B442859
  · exact B442863
  · exact B442867
  · exact B442871
  · exact B442875
  · exact B442879
  · exact B442883
  · exact B442887
  · exact B442891
  · exact B442895
  · exact B442899
  · exact B442903
  · exact B442907
  · exact B442911
  · exact B442915
  · exact B442919
  · exact B442923
  · exact B442927
  · exact B442931
  · exact B442935
  · exact B442939
  · exact B442943
  · exact B442947
  · exact B442951
  · exact B442955
  · exact B442959
  · exact B442963
  · exact B442967
  · exact B442971
  · exact B442975
  · exact B442979
  · exact B442983
  · exact B442987
  · exact B442991
  · exact B442995
  · exact B442999
  · exact B443003
  · exact B443007
  · exact B443011
  · exact B443015
  · exact B443019
  · exact B443023
  · exact B443027
  · exact B443031
  · exact B443035
  · exact B443039
  · exact B443043
  · exact B443047
  · exact B443051
  · exact B443055
  · exact B443059
  · exact B443063
  · exact B443067
  · exact B443071
  · exact B443075
  · exact B443079
  · exact B443083
  · exact B443087
  · exact B443091
  · exact B443095
  · exact B443099
  · exact B443103
  · exact B443107
  · exact B443111
  · exact B443115
  · exact B443119
  · exact B443123
  · exact B443127
  · exact B443131
  · exact B443135
  · exact B443139
  · exact B443143
  · exact B443147
  · exact B443151
  · exact B443155
  · exact B443159
  · exact B443163
  · exact B443167
  · exact B443171
  · exact B443175
  · exact B443179
  · exact B443183
  · exact B443187
  · exact B443191
  · exact B443195
  · exact B443199
  · exact B443203
  · exact B443207
  · exact B443211
  · exact B443215
  · exact B443219
  · exact B443223
  · exact B443227
  · exact B443231
  · exact B443235
  · exact B443239
  · exact B443243
  · exact B443247
  · exact B443251
  · exact B443255
  · exact B443259
  · exact B443263
  · exact B443267
  · exact B443271
  · exact B443275
  · exact B443279
  · exact B443283
  · exact B443287
  · exact B443291
  · exact B443295
  · exact B443299
  · exact B443303
  · exact B443307
  · exact B443311
  · exact B443315
  · exact B443319
  · exact B443323
  · exact B443327
  · exact B443331
  · exact B443335
  · exact B443339
  · exact B443343
  · exact B443347
  · exact B443351
  · exact B443355
  · exact B443359
  · exact B443363
  · exact B443367
  · exact B443371
  · exact B443375
  · exact B443379
  · exact B443383
  · exact B443387
  · exact B443391
  · exact B443395
  · exact B443399
  · exact B443403
  · exact B443407
  · exact B443411
  · exact B443415
  · exact B443419
  · exact B443423
  · exact B443427
  · exact B443431
  · exact B443435
  · exact B443439
  · exact B443443
  · exact B443447
  · exact B443451
  · exact B443455
  · exact B443459
  · exact B443463
  · exact B443467
  · exact B443471
  · exact B443475
  · exact B443479
  · exact B443483
  · exact B443487
  · exact B443491
  · exact B443495
  · exact B443499
  · exact B443503
  · exact B443507
  · exact B443511
  · exact B443515
  · exact B443519
  · exact B443523
  · exact B443527
  · exact B443531
  · exact B443535
  · exact B443539
  · exact B443543
  · exact B443547
  · exact B443551
  · exact B443555
  · exact B443559
  · exact B443563
  · exact B443567
  · exact B443571
  · exact B443575
  · exact B443579
  · exact B443583
  · exact B443587
  · exact B443591
  · exact B443595
  · exact B443599
  · exact B443603
  · exact B443607
  · exact B443611
  · exact B443615
  · exact B443619
  · exact B443623
  · exact B443627
  · exact B443631
  · exact B443635
  · exact B443639
  · exact B443643
  · exact B443647
  · exact B443651
  · exact B443655
  · exact B443659
  · exact B443663
  · exact B443667
  · exact B443671
  · exact B443675
  · exact B443679
  · exact B443683
  · exact B443687
  · exact B443691
  · exact B443695
  · exact B443699
  · exact B443703
  · exact B443707
  · exact B443711
  · exact B443715
  · exact B443719
  · exact B443723
  · exact B443727
  · exact B443731
  · exact B443735
  · exact B443739
  · exact B443743
  · exact B443747
  · exact B443751
  · exact B443755
  · exact B443759
  · exact B443763
  · exact B443767
  · exact B443771
  · exact B443775

theorem solution (m : ℕ) (hlo : 439778 ≤ m) (hhi : m ≤ 443778) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 109944 ≤ j := by omega
    have hj2 : j ≤ 110943 := by omega
    have hb : Blo 439778 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 110644 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
