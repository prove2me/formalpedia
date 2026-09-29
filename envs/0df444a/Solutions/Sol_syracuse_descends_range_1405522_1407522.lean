-- Prove2me | solution 1 for syracuse_descends_range_1405522_1407522
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:52.023886+00:00
-- url     : https://prove2.me/submissions/5467a2fb-8ddf-4a8a-882a-85b814dbbdfa

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


theorem B20561941 : Blo 1405522 20561941 := bbase (se 6 (by rfl) ⟨481920, by rfl⟩ : syracuseStep 20561941 = 963841) (by norm_num)
theorem B2138165 : Blo 1405522 2138165 := bbase (se 5 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 2138165 = 200453) (by norm_num)
theorem B2670661 : Blo 1405522 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B4006037 : Blo 1405522 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B1581241 : Blo 1405522 1581241 := bbase (se 2 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 1581241 = 1185931) (by norm_num)
theorem B1425605 : Blo 1405522 1425605 := bbase (se 4 (by rfl) ⟨133650, by rfl⟩ : syracuseStep 1425605 = 267301) (by norm_num)
theorem B1581277 : Blo 1405522 1581277 := bbase (se 3 (by rfl) ⟨296489, by rfl⟩ : syracuseStep 1581277 = 592979) (by norm_num)
theorem B1581313 : Blo 1405522 1581313 := bbase (se 2 (by rfl) ⟨592992, by rfl⟩ : syracuseStep 1581313 = 1185985) (by norm_num)
theorem B1581349 : Blo 1405522 1581349 := bbase (se 4 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 1581349 = 296503) (by norm_num)
theorem B3162437 : Blo 1405522 3162437 := bbase (se 4 (by rfl) ⟨296478, by rfl⟩ : syracuseStep 3162437 = 592957) (by norm_num)
theorem B1581385 : Blo 1405522 1581385 := bbase (se 2 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 1581385 = 1186039) (by norm_num)
theorem B34210133 : Blo 1405522 34210133 := bbase (se 10 (by rfl) ⟨50112, by rfl⟩ : syracuseStep 34210133 = 100225) (by norm_num)
theorem B1581421 : Blo 1405522 1581421 := bbase (se 3 (by rfl) ⟨296516, by rfl⟩ : syracuseStep 1581421 = 593033) (by norm_num)
theorem B2670965 : Blo 1405522 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B3162509 : Blo 1405522 3162509 := bbase (se 3 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 3162509 = 1185941) (by norm_num)
theorem B1581457 : Blo 1405522 1581457 := bbase (se 2 (by rfl) ⟨593046, by rfl⟩ : syracuseStep 1581457 = 1186093) (by norm_num)
theorem B1581493 : Blo 1405522 1581493 := bbase (se 5 (by rfl) ⟨74132, by rfl⟩ : syracuseStep 1581493 = 148265) (by norm_num)
theorem B3162581 : Blo 1405522 3162581 := bbase (se 7 (by rfl) ⟨37061, by rfl⟩ : syracuseStep 3162581 = 74123) (by norm_num)
theorem B1581529 : Blo 1405522 1581529 := bbase (se 2 (by rfl) ⟨593073, by rfl⟩ : syracuseStep 1581529 = 1186147) (by norm_num)
theorem B4506101 : Blo 1405522 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B1581565 : Blo 1405522 1581565 := bbase (se 3 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 1581565 = 593087) (by norm_num)
theorem B12829205 : Blo 1405522 12829205 := bbase (se 6 (by rfl) ⟨300684, by rfl⟩ : syracuseStep 12829205 = 601369) (by norm_num)
theorem B3162653 : Blo 1405522 3162653 := bbase (se 3 (by rfl) ⟨592997, by rfl⟩ : syracuseStep 3162653 = 1185995) (by norm_num)
theorem B1581601 : Blo 1405522 1581601 := bbase (se 2 (by rfl) ⟨593100, by rfl⟩ : syracuseStep 1581601 = 1186201) (by norm_num)
theorem B5341733 : Blo 1405522 5341733 := bbase (se 4 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 5341733 = 1001575) (by norm_num)
theorem B7119413 : Blo 1405522 7119413 := bbase (se 5 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 7119413 = 667445) (by norm_num)
theorem B1581637 : Blo 1405522 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B3162725 : Blo 1405522 3162725 := bbase (se 4 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 3162725 = 593011) (by norm_num)
theorem B1581673 : Blo 1405522 1581673 := bbase (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) (by norm_num)
theorem B1581709 : Blo 1405522 1581709 := bbase (se 3 (by rfl) ⟨296570, by rfl⟩ : syracuseStep 1581709 = 593141) (by norm_num)
theorem B4743845 : Blo 1405522 4743845 := bbase (se 4 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 4743845 = 889471) (by norm_num)
theorem B3162797 : Blo 1405522 3162797 := bbase (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) (by norm_num)
theorem B1581745 : Blo 1405522 1581745 := bbase (se 2 (by rfl) ⟨593154, by rfl⟩ : syracuseStep 1581745 = 1186309) (by norm_num)
theorem B1581781 : Blo 1405522 1581781 := bbase (se 7 (by rfl) ⟨18536, by rfl⟩ : syracuseStep 1581781 = 37073) (by norm_num)
theorem B3801829 : Blo 1405522 3801829 := bbase (se 4 (by rfl) ⟨356421, by rfl⟩ : syracuseStep 3801829 = 712843) (by norm_num)
theorem B3162869 : Blo 1405522 3162869 := bbase (se 5 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 3162869 = 296519) (by norm_num)
theorem B1581817 : Blo 1405522 1581817 := bbase (se 2 (by rfl) ⟨593181, by rfl⟩ : syracuseStep 1581817 = 1186363) (by norm_num)
theorem B1581853 : Blo 1405522 1581853 := bbase (se 3 (by rfl) ⟨296597, by rfl⟩ : syracuseStep 1581853 = 593195) (by norm_num)
theorem B1426205 : Blo 1405522 1426205 := bbase (se 3 (by rfl) ⟨267413, by rfl⟩ : syracuseStep 1426205 = 534827) (by norm_num)
theorem B3162941 : Blo 1405522 3162941 := bbase (se 3 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 3162941 = 1186103) (by norm_num)
theorem B1581889 : Blo 1405522 1581889 := bbase (se 2 (by rfl) ⟨593208, by rfl⟩ : syracuseStep 1581889 = 1186417) (by norm_num)
theorem B5342021 : Blo 1405522 5342021 := bbase (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) (by norm_num)
theorem B2253653 : Blo 1405522 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1581925 : Blo 1405522 1581925 := bbase (se 4 (by rfl) ⟨148305, by rfl⟩ : syracuseStep 1581925 = 296611) (by norm_num)
theorem B3163013 : Blo 1405522 3163013 := bbase (se 4 (by rfl) ⟨296532, by rfl⟩ : syracuseStep 3163013 = 593065) (by norm_num)
theorem B1581961 : Blo 1405522 1581961 := bbase (se 2 (by rfl) ⟨593235, by rfl⟩ : syracuseStep 1581961 = 1186471) (by norm_num)
theorem B1803173 : Blo 1405522 1803173 := bbase (se 4 (by rfl) ⟨169047, by rfl⟩ : syracuseStep 1803173 = 338095) (by norm_num)
theorem B1581997 : Blo 1405522 1581997 := bbase (se 3 (by rfl) ⟨296624, by rfl⟩ : syracuseStep 1581997 = 593249) (by norm_num)
theorem B2253749 : Blo 1405522 2253749 := bbase (se 5 (by rfl) ⟨105644, by rfl⟩ : syracuseStep 2253749 = 211289) (by norm_num)
theorem B3163085 : Blo 1405522 3163085 := bbase (se 3 (by rfl) ⟨593078, by rfl⟩ : syracuseStep 3163085 = 1186157) (by norm_num)
theorem B1582033 : Blo 1405522 1582033 := bbase (se 2 (by rfl) ⟨593262, by rfl⟩ : syracuseStep 1582033 = 1186525) (by norm_num)
theorem B2253781 : Blo 1405522 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B10134517 : Blo 1405522 10134517 := bbase (se 5 (by rfl) ⟨475055, by rfl⟩ : syracuseStep 10134517 = 950111) (by norm_num)
theorem B1582069 : Blo 1405522 1582069 := bbase (se 5 (by rfl) ⟨74159, by rfl⟩ : syracuseStep 1582069 = 148319) (by norm_num)
theorem B3163157 : Blo 1405522 3163157 := bbase (se 6 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 3163157 = 148273) (by norm_num)
theorem B1582105 : Blo 1405522 1582105 := bbase (se 2 (by rfl) ⟨593289, by rfl⟩ : syracuseStep 1582105 = 1186579) (by norm_num)
theorem B6947893 : Blo 1405522 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B1582141 : Blo 1405522 1582141 := bbase (se 3 (by rfl) ⟨296651, by rfl⟩ : syracuseStep 1582141 = 593303) (by norm_num)
theorem B1426505 : Blo 1405522 1426505 := bbase (se 2 (by rfl) ⟨534939, by rfl⟩ : syracuseStep 1426505 = 1069879) (by norm_num)
theorem B4744277 : Blo 1405522 4744277 := bbase (se 8 (by rfl) ⟨27798, by rfl⟩ : syracuseStep 4744277 = 55597) (by norm_num)
theorem B3163229 : Blo 1405522 3163229 := bbase (se 3 (by rfl) ⟨593105, by rfl⟩ : syracuseStep 3163229 = 1186211) (by norm_num)
theorem B1582177 : Blo 1405522 1582177 := bbase (se 2 (by rfl) ⟨593316, by rfl⟩ : syracuseStep 1582177 = 1186633) (by norm_num)
theorem B2671717 : Blo 1405522 2671717 := bbase (se 4 (by rfl) ⟨250473, by rfl⟩ : syracuseStep 2671717 = 500947) (by norm_num)
theorem B4007029 : Blo 1405522 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B1582213 : Blo 1405522 1582213 := bbase (se 4 (by rfl) ⟨148332, by rfl⟩ : syracuseStep 1582213 = 296665) (by norm_num)
theorem B3802261 : Blo 1405522 3802261 := bbase (se 6 (by rfl) ⟨89115, by rfl⟩ : syracuseStep 3802261 = 178231) (by norm_num)
theorem B3163301 : Blo 1405522 3163301 := bbase (se 4 (by rfl) ⟨296559, by rfl⟩ : syracuseStep 3163301 = 593119) (by norm_num)
theorem B1582249 : Blo 1405522 1582249 := bbase (se 2 (by rfl) ⟨593343, by rfl⟩ : syracuseStep 1582249 = 1186687) (by norm_num)
theorem B1582285 : Blo 1405522 1582285 := bbase (se 3 (by rfl) ⟨296678, by rfl⟩ : syracuseStep 1582285 = 593357) (by norm_num)
theorem B1778917 : Blo 1405522 1778917 := bbase (se 4 (by rfl) ⟨166773, by rfl⟩ : syracuseStep 1778917 = 333547) (by norm_num)
theorem B3163373 : Blo 1405522 3163373 := bbase (se 3 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 3163373 = 1186265) (by norm_num)
theorem B1582321 : Blo 1405522 1582321 := bbase (se 2 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 1582321 = 1186741) (by norm_num)
theorem B2671861 : Blo 1405522 2671861 := bbase (se 5 (by rfl) ⟨125243, by rfl⟩ : syracuseStep 2671861 = 250487) (by norm_num)
theorem B1582357 : Blo 1405522 1582357 := bbase (se 6 (by rfl) ⟨37086, by rfl⟩ : syracuseStep 1582357 = 74173) (by norm_num)
theorem B8013077 : Blo 1405522 8013077 := bbase (se 6 (by rfl) ⟨187806, by rfl⟩ : syracuseStep 8013077 = 375613) (by norm_num)
theorem B3163445 : Blo 1405522 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B1582393 : Blo 1405522 1582393 := bbase (se 2 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 1582393 = 1186795) (by norm_num)
theorem B1779013 : Blo 1405522 1779013 := bbase (se 4 (by rfl) ⟨166782, by rfl⟩ : syracuseStep 1779013 = 333565) (by norm_num)
theorem B1582429 : Blo 1405522 1582429 := bbase (se 3 (by rfl) ⟨296705, by rfl⟩ : syracuseStep 1582429 = 593411) (by norm_num)
theorem B4506997 : Blo 1405522 4506997 := bbase (se 5 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 4506997 = 422531) (by norm_num)
theorem B3163517 : Blo 1405522 3163517 := bbase (se 3 (by rfl) ⟨593159, by rfl⟩ : syracuseStep 3163517 = 1186319) (by norm_num)
theorem B1582465 : Blo 1405522 1582465 := bbase (se 2 (by rfl) ⟨593424, by rfl⟩ : syracuseStep 1582465 = 1186849) (by norm_num)
theorem B8005013 : Blo 1405522 8005013 := bbase (se 6 (by rfl) ⟨187617, by rfl⟩ : syracuseStep 8005013 = 375235) (by norm_num)
theorem B2672021 : Blo 1405522 2672021 := bbase (se 6 (by rfl) ⟨62625, by rfl⟩ : syracuseStep 2672021 = 125251) (by norm_num)
theorem B1582501 : Blo 1405522 1582501 := bbase (se 4 (by rfl) ⟨148359, by rfl⟩ : syracuseStep 1582501 = 296719) (by norm_num)
theorem B3163589 : Blo 1405522 3163589 := bbase (se 4 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 3163589 = 593173) (by norm_num)
theorem B1582537 : Blo 1405522 1582537 := bbase (se 2 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 1582537 = 1186903) (by norm_num)
theorem B1713613 : Blo 1405522 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B2704853 : Blo 1405522 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B1582573 : Blo 1405522 1582573 := bbase (se 3 (by rfl) ⟨296732, by rfl⟩ : syracuseStep 1582573 = 593465) (by norm_num)
theorem B1779185 : Blo 1405522 1779185 := bbase (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) (by norm_num)
theorem B4744709 : Blo 1405522 4744709 := bbase (se 4 (by rfl) ⟨444816, by rfl⟩ : syracuseStep 4744709 = 889633) (by norm_num)
theorem B3163661 : Blo 1405522 3163661 := bbase (se 3 (by rfl) ⟨593186, by rfl⟩ : syracuseStep 3163661 = 1186373) (by norm_num)
theorem B1582609 : Blo 1405522 1582609 := bbase (se 2 (by rfl) ⟨593478, by rfl⟩ : syracuseStep 1582609 = 1186957) (by norm_num)
theorem B1779241 : Blo 1405522 1779241 := bbase (se 2 (by rfl) ⟨667215, by rfl⟩ : syracuseStep 1779241 = 1334431) (by norm_num)
theorem B1582645 : Blo 1405522 1582645 := bbase (se 5 (by rfl) ⟨74186, by rfl⟩ : syracuseStep 1582645 = 148373) (by norm_num)
theorem B3163733 : Blo 1405522 3163733 := bbase (se 8 (by rfl) ⟨18537, by rfl⟩ : syracuseStep 3163733 = 37075) (by norm_num)
theorem B1582681 : Blo 1405522 1582681 := bbase (se 2 (by rfl) ⟨593505, by rfl⟩ : syracuseStep 1582681 = 1187011) (by norm_num)
theorem B2705005 : Blo 1405522 2705005 := bbase (se 3 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 2705005 = 1014377) (by norm_num)
theorem B1582717 : Blo 1405522 1582717 := bbase (se 3 (by rfl) ⟨296759, by rfl⟩ : syracuseStep 1582717 = 593519) (by norm_num)
theorem B1779337 : Blo 1405522 1779337 := bbase (se 2 (by rfl) ⟨667251, by rfl⟩ : syracuseStep 1779337 = 1334503) (by norm_num)
theorem B3163805 : Blo 1405522 3163805 := bbase (se 3 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 3163805 = 1186427) (by norm_num)
theorem B1582753 : Blo 1405522 1582753 := bbase (se 2 (by rfl) ⟨593532, by rfl⟩ : syracuseStep 1582753 = 1187065) (by norm_num)
theorem B1582789 : Blo 1405522 1582789 := bbase (se 4 (by rfl) ⟨148386, by rfl⟩ : syracuseStep 1582789 = 296773) (by norm_num)
theorem B14436053 : Blo 1405522 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B3163877 : Blo 1405522 3163877 := bbase (se 4 (by rfl) ⟨296613, by rfl⟩ : syracuseStep 3163877 = 593227) (by norm_num)
theorem B1582825 : Blo 1405522 1582825 := bbase (se 2 (by rfl) ⟨593559, by rfl⟩ : syracuseStep 1582825 = 1187119) (by norm_num)
theorem B4507397 : Blo 1405522 4507397 := bbase (se 4 (by rfl) ⟨422568, by rfl⟩ : syracuseStep 4507397 = 845137) (by norm_num)
theorem B1582861 : Blo 1405522 1582861 := bbase (se 3 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 1582861 = 593573) (by norm_num)
theorem B3163949 : Blo 1405522 3163949 := bbase (se 3 (by rfl) ⟨593240, by rfl⟩ : syracuseStep 3163949 = 1186481) (by norm_num)
theorem B1582897 : Blo 1405522 1582897 := bbase (se 2 (by rfl) ⟨593586, by rfl⟩ : syracuseStep 1582897 = 1187173) (by norm_num)
theorem B1779509 : Blo 1405522 1779509 := bbase (se 5 (by rfl) ⟨83414, by rfl⟩ : syracuseStep 1779509 = 166829) (by norm_num)
theorem B6006581 : Blo 1405522 6006581 := bbase (se 5 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 6006581 = 563117) (by norm_num)
theorem B13526837 : Blo 1405522 13526837 := bbase (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) (by norm_num)
theorem B7120709 : Blo 1405522 7120709 := bbase (se 4 (by rfl) ⟨667566, by rfl⟩ : syracuseStep 7120709 = 1335133) (by norm_num)
theorem B1582933 : Blo 1405522 1582933 := bbase (se 9 (by rfl) ⟨4637, by rfl⟩ : syracuseStep 1582933 = 9275) (by norm_num)
theorem B1779565 : Blo 1405522 1779565 := bbase (se 3 (by rfl) ⟨333668, by rfl⟩ : syracuseStep 1779565 = 667337) (by norm_num)
theorem B3164021 : Blo 1405522 3164021 := bbase (se 5 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 3164021 = 296627) (by norm_num)
theorem B1582969 : Blo 1405522 1582969 := bbase (se 2 (by rfl) ⟨593613, by rfl⟩ : syracuseStep 1582969 = 1187227) (by norm_num)
theorem B1828765 : Blo 1405522 1828765 := bbase (se 3 (by rfl) ⟨342893, by rfl⟩ : syracuseStep 1828765 = 685787) (by norm_num)
theorem B1583005 : Blo 1405522 1583005 := bbase (se 3 (by rfl) ⟨296813, by rfl⟩ : syracuseStep 1583005 = 593627) (by norm_num)
theorem B1689509 : Blo 1405522 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B4745141 : Blo 1405522 4745141 := bbase (se 5 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 4745141 = 444857) (by norm_num)
theorem B3164093 : Blo 1405522 3164093 := bbase (se 3 (by rfl) ⟨593267, by rfl⟩ : syracuseStep 3164093 = 1186535) (by norm_num)
theorem B1484737 : Blo 1405522 1484737 := bbase (se 2 (by rfl) ⟨556776, by rfl⟩ : syracuseStep 1484737 = 1113553) (by norm_num)
theorem B1583041 : Blo 1405522 1583041 := bbase (se 2 (by rfl) ⟨593640, by rfl⟩ : syracuseStep 1583041 = 1187281) (by norm_num)
theorem B1779661 : Blo 1405522 1779661 := bbase (se 3 (by rfl) ⟨333686, by rfl⟩ : syracuseStep 1779661 = 667373) (by norm_num)
theorem B6760421 : Blo 1405522 6760421 := bbase (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) (by norm_num)
theorem B1583077 : Blo 1405522 1583077 := bbase (se 4 (by rfl) ⟨148413, by rfl⟩ : syracuseStep 1583077 = 296827) (by norm_num)
theorem B5343205 : Blo 1405522 5343205 := bbase (se 4 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 5343205 = 1001851) (by norm_num)
theorem B3164165 : Blo 1405522 3164165 := bbase (se 4 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 3164165 = 593281) (by norm_num)
theorem B1583113 : Blo 1405522 1583113 := bbase (se 2 (by rfl) ⟨593667, by rfl⟩ : syracuseStep 1583113 = 1187335) (by norm_num)
theorem B1501201 : Blo 1405522 1501201 := bbase (se 2 (by rfl) ⟨562950, by rfl⟩ : syracuseStep 1501201 = 1125901) (by norm_num)
theorem B1583149 : Blo 1405522 1583149 := bbase (se 3 (by rfl) ⟨296840, by rfl⟩ : syracuseStep 1583149 = 593681) (by norm_num)
theorem B3164237 : Blo 1405522 3164237 := bbase (se 3 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 3164237 = 1186589) (by norm_num)
theorem B1583185 : Blo 1405522 1583185 := bbase (se 2 (by rfl) ⟨593694, by rfl⟩ : syracuseStep 1583185 = 1187389) (by norm_num)
theorem B6006869 : Blo 1405522 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B65874005 : Blo 1405522 65874005 := bbase (se 8 (by rfl) ⟨385980, by rfl⟩ : syracuseStep 65874005 = 771961) (by norm_num)
theorem B1501273 : Blo 1405522 1501273 := bbase (se 2 (by rfl) ⟨562977, by rfl⟩ : syracuseStep 1501273 = 1125955) (by norm_num)
theorem B1689697 : Blo 1405522 1689697 := bbase (se 2 (by rfl) ⟨633636, by rfl⟩ : syracuseStep 1689697 = 1267273) (by norm_num)
theorem B1583221 : Blo 1405522 1583221 := bbase (se 5 (by rfl) ⟨74213, by rfl⟩ : syracuseStep 1583221 = 148427) (by norm_num)
theorem B1779833 : Blo 1405522 1779833 := bbase (se 2 (by rfl) ⟨667437, by rfl⟩ : syracuseStep 1779833 = 1334875) (by norm_num)
theorem B3164309 : Blo 1405522 3164309 := bbase (se 6 (by rfl) ⟨74163, by rfl⟩ : syracuseStep 3164309 = 148327) (by norm_num)
theorem B1583257 : Blo 1405522 1583257 := bbase (se 2 (by rfl) ⟨593721, by rfl⟩ : syracuseStep 1583257 = 1187443) (by norm_num)
theorem B1779889 : Blo 1405522 1779889 := bbase (se 2 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 1779889 = 1334917) (by norm_num)
theorem B1583293 : Blo 1405522 1583293 := bbase (se 3 (by rfl) ⟨296867, by rfl⟩ : syracuseStep 1583293 = 593735) (by norm_num)
theorem B4008133 : Blo 1405522 4008133 := bbase (se 4 (by rfl) ⟨375762, by rfl⟩ : syracuseStep 4008133 = 751525) (by norm_num)
theorem B3164381 : Blo 1405522 3164381 := bbase (se 3 (by rfl) ⟨593321, by rfl⟩ : syracuseStep 3164381 = 1186643) (by norm_num)
theorem B1583329 : Blo 1405522 1583329 := bbase (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) (by norm_num)
theorem B1583365 : Blo 1405522 1583365 := bbase (se 4 (by rfl) ⟨148440, by rfl⟩ : syracuseStep 1583365 = 296881) (by norm_num)
theorem B1501453 : Blo 1405522 1501453 := bbase (se 3 (by rfl) ⟨281522, by rfl⟩ : syracuseStep 1501453 = 563045) (by norm_num)
theorem B1779985 : Blo 1405522 1779985 := bbase (se 2 (by rfl) ⟨667494, by rfl⟩ : syracuseStep 1779985 = 1334989) (by norm_num)
theorem B5343509 : Blo 1405522 5343509 := bbase (se 6 (by rfl) ⟨125238, by rfl⟩ : syracuseStep 5343509 = 250477) (by norm_num)
theorem B3164453 : Blo 1405522 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B3803429 : Blo 1405522 3803429 := bbase (se 4 (by rfl) ⟨356571, by rfl⟩ : syracuseStep 3803429 = 713143) (by norm_num)
theorem B1583401 : Blo 1405522 1583401 := bbase (se 2 (by rfl) ⟨593775, by rfl⟩ : syracuseStep 1583401 = 1187551) (by norm_num)
theorem B1689913 : Blo 1405522 1689913 := bbase (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) (by norm_num)
theorem B2853181 : Blo 1405522 2853181 := bbase (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) (by norm_num)
theorem B1583437 : Blo 1405522 1583437 := bbase (se 3 (by rfl) ⟨296894, by rfl⟩ : syracuseStep 1583437 = 593789) (by norm_num)
theorem B4745573 : Blo 1405522 4745573 := bbase (se 4 (by rfl) ⟨444897, by rfl⟩ : syracuseStep 4745573 = 889795) (by norm_num)
theorem B3164525 : Blo 1405522 3164525 := bbase (se 3 (by rfl) ⟨593348, by rfl⟩ : syracuseStep 3164525 = 1186697) (by norm_num)
theorem B3164597 : Blo 1405522 3164597 := bbase (se 5 (by rfl) ⟨148340, by rfl⟩ : syracuseStep 3164597 = 296681) (by norm_num)
theorem B8014261 : Blo 1405522 8014261 := bbase (se 5 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 8014261 = 751337) (by norm_num)
theorem B1780157 : Blo 1405522 1780157 := bbase (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) (by norm_num)
theorem B21121493 : Blo 1405522 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B1780213 : Blo 1405522 1780213 := bbase (se 5 (by rfl) ⟨83447, by rfl⟩ : syracuseStep 1780213 = 166895) (by norm_num)
theorem B3164669 : Blo 1405522 3164669 := bbase (se 3 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 3164669 = 1186751) (by norm_num)
theorem B3164741 : Blo 1405522 3164741 := bbase (se 4 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 3164741 = 593389) (by norm_num)
theorem B3557965 : Blo 1405522 3557965 := bbase (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) (by norm_num)
theorem B1780309 : Blo 1405522 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B32492117 : Blo 1405522 32492117 := bbase (se 8 (by rfl) ⟨190383, by rfl⟩ : syracuseStep 32492117 = 380767) (by norm_num)
theorem B1690201 : Blo 1405522 1690201 := bbase (se 2 (by rfl) ⟨633825, by rfl⟩ : syracuseStep 1690201 = 1267651) (by norm_num)
theorem B3164813 : Blo 1405522 3164813 := bbase (se 3 (by rfl) ⟨593402, by rfl⟩ : syracuseStep 3164813 = 1186805) (by norm_num)
theorem B1927837 : Blo 1405522 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B3558077 : Blo 1405522 3558077 := bbase (se 3 (by rfl) ⟨667139, by rfl⟩ : syracuseStep 3558077 = 1334279) (by norm_num)
theorem B1501897 : Blo 1405522 1501897 := bbase (se 2 (by rfl) ⟨563211, by rfl⟩ : syracuseStep 1501897 = 1126423) (by norm_num)
theorem B3164885 : Blo 1405522 3164885 := bbase (se 7 (by rfl) ⟨37088, by rfl⟩ : syracuseStep 3164885 = 74177) (by norm_num)
theorem B2001629 : Blo 1405522 2001629 := bbase (se 3 (by rfl) ⟨375305, by rfl⟩ : syracuseStep 2001629 = 750611) (by norm_num)
theorem B1780481 : Blo 1405522 1780481 := bbase (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) (by norm_num)
theorem B4746005 : Blo 1405522 4746005 := bbase (se 6 (by rfl) ⟨111234, by rfl⟩ : syracuseStep 4746005 = 222469) (by norm_num)
theorem B3164957 : Blo 1405522 3164957 := bbase (se 3 (by rfl) ⟨593429, by rfl⟩ : syracuseStep 3164957 = 1186859) (by norm_num)
theorem B2001709 : Blo 1405522 2001709 := bbase (se 3 (by rfl) ⟨375320, by rfl⟩ : syracuseStep 2001709 = 750641) (by norm_num)
theorem B1780537 : Blo 1405522 1780537 := bbase (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) (by norm_num)
theorem B6007621 : Blo 1405522 6007621 := bbase (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) (by norm_num)
theorem B1502021 : Blo 1405522 1502021 := bbase (se 4 (by rfl) ⟨140814, by rfl⟩ : syracuseStep 1502021 = 281629) (by norm_num)
theorem B3165029 : Blo 1405522 3165029 := bbase (se 4 (by rfl) ⟨296721, by rfl⟩ : syracuseStep 3165029 = 593443) (by norm_num)
theorem B2108285 : Blo 1405522 2108285 := bbase (se 3 (by rfl) ⟨395303, by rfl⟩ : syracuseStep 2108285 = 790607) (by norm_num)
theorem B3558269 : Blo 1405522 3558269 := bbase (se 3 (by rfl) ⟨667175, by rfl⟩ : syracuseStep 3558269 = 1334351) (by norm_num)
theorem B2108309 : Blo 1405522 2108309 := bbase (se 6 (by rfl) ⟨49413, by rfl⟩ : syracuseStep 2108309 = 98827) (by norm_num)
theorem B1780633 : Blo 1405522 1780633 := bbase (se 2 (by rfl) ⟨667737, by rfl⟩ : syracuseStep 1780633 = 1335475) (by norm_num)
theorem B2001829 : Blo 1405522 2001829 := bbase (se 4 (by rfl) ⟨187671, by rfl⟩ : syracuseStep 2001829 = 375343) (by norm_num)
theorem B2108333 : Blo 1405522 2108333 := bbase (se 3 (by rfl) ⟨395312, by rfl⟩ : syracuseStep 2108333 = 790625) (by norm_num)
theorem B3165101 : Blo 1405522 3165101 := bbase (se 3 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 3165101 = 1186913) (by norm_num)
theorem B2108357 : Blo 1405522 2108357 := bbase (se 4 (by rfl) ⟨197658, by rfl⟩ : syracuseStep 2108357 = 395317) (by norm_num)
theorem B1444825 : Blo 1405522 1444825 := bbase (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) (by norm_num)
theorem B2108381 : Blo 1405522 2108381 := bbase (se 3 (by rfl) ⟨395321, by rfl⟩ : syracuseStep 2108381 = 790643) (by norm_num)
theorem B2108405 : Blo 1405522 2108405 := bbase (se 5 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 2108405 = 197663) (by norm_num)
theorem B3165173 : Blo 1405522 3165173 := bbase (se 5 (by rfl) ⟨148367, by rfl⟩ : syracuseStep 3165173 = 296735) (by norm_num)
theorem B2001925 : Blo 1405522 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B2108429 : Blo 1405522 2108429 := bbase (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) (by norm_num)
theorem B2108453 : Blo 1405522 2108453 := bbase (se 4 (by rfl) ⟨197667, by rfl⟩ : syracuseStep 2108453 = 395335) (by norm_num)
theorem B2534437 : Blo 1405522 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B1805365 : Blo 1405522 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B2108477 : Blo 1405522 2108477 := bbase (se 3 (by rfl) ⟨395339, by rfl⟩ : syracuseStep 2108477 = 790679) (by norm_num)
theorem B3165245 : Blo 1405522 3165245 := bbase (se 3 (by rfl) ⟨593483, by rfl⟩ : syracuseStep 3165245 = 1186967) (by norm_num)
theorem B1502273 : Blo 1405522 1502273 := bbase (se 2 (by rfl) ⟨563352, by rfl⟩ : syracuseStep 1502273 = 1126705) (by norm_num)
theorem B1780805 : Blo 1405522 1780805 := bbase (se 4 (by rfl) ⟨166950, by rfl⟩ : syracuseStep 1780805 = 333901) (by norm_num)
theorem B2108501 : Blo 1405522 2108501 := bbase (se 8 (by rfl) ⟨12354, by rfl⟩ : syracuseStep 2108501 = 24709) (by norm_num)
theorem B13511765 : Blo 1405522 13511765 := bbase (se 8 (by rfl) ⟨79170, by rfl⟩ : syracuseStep 13511765 = 158341) (by norm_num)
theorem B7122005 : Blo 1405522 7122005 := bbase (se 8 (by rfl) ⟨41730, by rfl⟩ : syracuseStep 7122005 = 83461) (by norm_num)
theorem B2108525 : Blo 1405522 2108525 := bbase (se 3 (by rfl) ⟨395348, by rfl⟩ : syracuseStep 2108525 = 790697) (by norm_num)
theorem B1780861 : Blo 1405522 1780861 := bbase (se 3 (by rfl) ⟨333911, by rfl⟩ : syracuseStep 1780861 = 667823) (by norm_num)
theorem B2108549 : Blo 1405522 2108549 := bbase (se 4 (by rfl) ⟨197676, by rfl⟩ : syracuseStep 2108549 = 395353) (by norm_num)
theorem B3165317 : Blo 1405522 3165317 := bbase (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) (by norm_num)
theorem B2108573 : Blo 1405522 2108573 := bbase (se 3 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 2108573 = 790715) (by norm_num)
theorem B2108597 : Blo 1405522 2108597 := bbase (se 5 (by rfl) ⟨98840, by rfl⟩ : syracuseStep 2108597 = 197681) (by norm_num)
theorem B2534581 : Blo 1405522 2534581 := bbase (se 5 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 2534581 = 237617) (by norm_num)
theorem B3378365 : Blo 1405522 3378365 := bbase (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) (by norm_num)
theorem B4746437 : Blo 1405522 4746437 := bbase (se 4 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 4746437 = 889957) (by norm_num)
theorem B2108621 : Blo 1405522 2108621 := bbase (se 3 (by rfl) ⟨395366, by rfl⟩ : syracuseStep 2108621 = 790733) (by norm_num)
theorem B3165389 : Blo 1405522 3165389 := bbase (se 3 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 3165389 = 1187021) (by norm_num)
theorem B3558613 : Blo 1405522 3558613 := bbase (se 7 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 3558613 = 83405) (by norm_num)
theorem B1780957 : Blo 1405522 1780957 := bbase (se 3 (by rfl) ⟨333929, by rfl⟩ : syracuseStep 1780957 = 667859) (by norm_num)
theorem B2108645 : Blo 1405522 2108645 := bbase (se 4 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 2108645 = 395371) (by norm_num)
theorem B5139701 : Blo 1405522 5139701 := bbase (se 5 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 5139701 = 481847) (by norm_num)
theorem B2108669 : Blo 1405522 2108669 := bbase (se 3 (by rfl) ⟨395375, by rfl⟩ : syracuseStep 2108669 = 790751) (by norm_num)
theorem B2108693 : Blo 1405522 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B3165461 : Blo 1405522 3165461 := bbase (se 6 (by rfl) ⟨74190, by rfl⟩ : syracuseStep 3165461 = 148381) (by norm_num)
theorem B2108717 : Blo 1405522 2108717 := bbase (se 3 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 2108717 = 790769) (by norm_num)
theorem B2108741 : Blo 1405522 2108741 := bbase (se 4 (by rfl) ⟨197694, by rfl⟩ : syracuseStep 2108741 = 395389) (by norm_num)
theorem B3558725 : Blo 1405522 3558725 := bbase (se 4 (by rfl) ⟨333630, by rfl⟩ : syracuseStep 3558725 = 667261) (by norm_num)
theorem B2108765 : Blo 1405522 2108765 := bbase (se 3 (by rfl) ⟨395393, by rfl⟩ : syracuseStep 2108765 = 790787) (by norm_num)
theorem B3165533 : Blo 1405522 3165533 := bbase (se 3 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 3165533 = 1187075) (by norm_num)
theorem B2108789 : Blo 1405522 2108789 := bbase (se 5 (by rfl) ⟨98849, by rfl⟩ : syracuseStep 2108789 = 197699) (by norm_num)
theorem B3378557 : Blo 1405522 3378557 := bbase (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) (by norm_num)
theorem B1781129 : Blo 1405522 1781129 := bbase (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) (by norm_num)
theorem B2108813 : Blo 1405522 2108813 := bbase (se 3 (by rfl) ⟨395402, by rfl⟩ : syracuseStep 2108813 = 790805) (by norm_num)
theorem B2108837 : Blo 1405522 2108837 := bbase (se 4 (by rfl) ⟨197703, by rfl⟩ : syracuseStep 2108837 = 395407) (by norm_num)
theorem B3165605 : Blo 1405522 3165605 := bbase (se 4 (by rfl) ⟨296775, by rfl⟩ : syracuseStep 3165605 = 593551) (by norm_num)
theorem B2108861 : Blo 1405522 2108861 := bbase (se 3 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 2108861 = 790823) (by norm_num)
theorem B1781185 : Blo 1405522 1781185 := bbase (se 2 (by rfl) ⟨667944, by rfl⟩ : syracuseStep 1781185 = 1335889) (by norm_num)
theorem B2108885 : Blo 1405522 2108885 := bbase (se 7 (by rfl) ⟨24713, by rfl⟩ : syracuseStep 2108885 = 49427) (by norm_num)
theorem B2108909 : Blo 1405522 2108909 := bbase (se 3 (by rfl) ⟨395420, by rfl⟩ : syracuseStep 2108909 = 790841) (by norm_num)
theorem B3165677 : Blo 1405522 3165677 := bbase (se 3 (by rfl) ⟨593564, by rfl⟩ : syracuseStep 3165677 = 1187129) (by norm_num)
theorem B2002421 : Blo 1405522 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B1502717 : Blo 1405522 1502717 := bbase (se 3 (by rfl) ⟨281759, by rfl⟩ : syracuseStep 1502717 = 563519) (by norm_num)
theorem B2108933 : Blo 1405522 2108933 := bbase (se 4 (by rfl) ⟨197712, by rfl⟩ : syracuseStep 2108933 = 395425) (by norm_num)
theorem B3558917 : Blo 1405522 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B2108957 : Blo 1405522 2108957 := bbase (se 3 (by rfl) ⟨395429, by rfl⟩ : syracuseStep 2108957 = 790859) (by norm_num)
theorem B1781281 : Blo 1405522 1781281 := bbase (se 2 (by rfl) ⟨667980, by rfl⟩ : syracuseStep 1781281 = 1335961) (by norm_num)
theorem B6008357 : Blo 1405522 6008357 := bbase (se 4 (by rfl) ⟨563283, by rfl⟩ : syracuseStep 6008357 = 1126567) (by norm_num)
theorem B2108981 : Blo 1405522 2108981 := bbase (se 5 (by rfl) ⟨98858, by rfl⟩ : syracuseStep 2108981 = 197717) (by norm_num)
theorem B3165749 : Blo 1405522 3165749 := bbase (se 5 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 3165749 = 296789) (by norm_num)
theorem B2109005 : Blo 1405522 2109005 := bbase (se 3 (by rfl) ⟨395438, by rfl⟩ : syracuseStep 2109005 = 790877) (by norm_num)
theorem B2109029 : Blo 1405522 2109029 := bbase (se 4 (by rfl) ⟨197721, by rfl⟩ : syracuseStep 2109029 = 395443) (by norm_num)
theorem B4746869 : Blo 1405522 4746869 := bbase (se 5 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 4746869 = 445019) (by norm_num)
theorem B2109053 : Blo 1405522 2109053 := bbase (se 3 (by rfl) ⟨395447, by rfl⟩ : syracuseStep 2109053 = 790895) (by norm_num)
theorem B3165821 : Blo 1405522 3165821 := bbase (se 3 (by rfl) ⟨593591, by rfl⟩ : syracuseStep 3165821 = 1187183) (by norm_num)
theorem B11398805 : Blo 1405522 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B2109077 : Blo 1405522 2109077 := bbase (se 6 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 2109077 = 98863) (by norm_num)
theorem B2109101 : Blo 1405522 2109101 := bbase (se 3 (by rfl) ⟨395456, by rfl⟩ : syracuseStep 2109101 = 790913) (by norm_num)
theorem B2109125 : Blo 1405522 2109125 := bbase (se 4 (by rfl) ⟨197730, by rfl⟩ : syracuseStep 2109125 = 395461) (by norm_num)
theorem B3165893 : Blo 1405522 3165893 := bbase (se 4 (by rfl) ⟨296802, by rfl⟩ : syracuseStep 3165893 = 593605) (by norm_num)
theorem B2109149 : Blo 1405522 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B2109173 : Blo 1405522 2109173 := bbase (se 5 (by rfl) ⟨98867, by rfl⟩ : syracuseStep 2109173 = 197735) (by norm_num)
theorem B1502965 : Blo 1405522 1502965 := bbase (se 5 (by rfl) ⟨70451, by rfl⟩ : syracuseStep 1502965 = 140903) (by norm_num)
theorem B2109197 : Blo 1405522 2109197 := bbase (se 3 (by rfl) ⟨395474, by rfl⟩ : syracuseStep 2109197 = 790949) (by norm_num)
theorem B3165965 : Blo 1405522 3165965 := bbase (se 3 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 3165965 = 1187237) (by norm_num)
theorem B2109221 : Blo 1405522 2109221 := bbase (se 4 (by rfl) ⟨197739, by rfl⟩ : syracuseStep 2109221 = 395479) (by norm_num)
theorem B2109245 : Blo 1405522 2109245 := bbase (se 3 (by rfl) ⟨395483, by rfl⟩ : syracuseStep 2109245 = 790967) (by norm_num)
theorem B3002197 : Blo 1405522 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B2109269 : Blo 1405522 2109269 := bbase (se 9 (by rfl) ⟨6179, by rfl⟩ : syracuseStep 2109269 = 12359) (by norm_num)
theorem B3166037 : Blo 1405522 3166037 := bbase (se 9 (by rfl) ⟨9275, by rfl⟩ : syracuseStep 3166037 = 18551) (by norm_num)
theorem B6762325 : Blo 1405522 6762325 := bbase (se 9 (by rfl) ⟨19811, by rfl⟩ : syracuseStep 6762325 = 39623) (by norm_num)
theorem B3043165 : Blo 1405522 3043165 := bbase (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) (by norm_num)
theorem B3559261 : Blo 1405522 3559261 := bbase (se 3 (by rfl) ⟨667361, by rfl⟩ : syracuseStep 3559261 = 1334723) (by norm_num)
theorem B6762341 : Blo 1405522 6762341 := bbase (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) (by norm_num)
theorem B2109293 : Blo 1405522 2109293 := bbase (se 3 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 2109293 = 790985) (by norm_num)
theorem B2109317 : Blo 1405522 2109317 := bbase (se 4 (by rfl) ⟨197748, by rfl⟩ : syracuseStep 2109317 = 395497) (by norm_num)
theorem B2109341 : Blo 1405522 2109341 := bbase (se 3 (by rfl) ⟨395501, by rfl⟩ : syracuseStep 2109341 = 791003) (by norm_num)
theorem B3166109 : Blo 1405522 3166109 := bbase (se 3 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 3166109 = 1187291) (by norm_num)
theorem B2109365 : Blo 1405522 2109365 := bbase (se 5 (by rfl) ⟨98876, by rfl⟩ : syracuseStep 2109365 = 197753) (by norm_num)
theorem B3559373 : Blo 1405522 3559373 := bbase (se 3 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 3559373 = 1334765) (by norm_num)
theorem B2109389 : Blo 1405522 2109389 := bbase (se 3 (by rfl) ⟨395510, by rfl⟩ : syracuseStep 2109389 = 791021) (by norm_num)
theorem B3002341 : Blo 1405522 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B2109413 : Blo 1405522 2109413 := bbase (se 4 (by rfl) ⟨197757, by rfl⟩ : syracuseStep 2109413 = 395515) (by norm_num)
theorem B3166181 : Blo 1405522 3166181 := bbase (se 4 (by rfl) ⟨296829, by rfl⟩ : syracuseStep 3166181 = 593659) (by norm_num)
theorem B2109437 : Blo 1405522 2109437 := bbase (se 3 (by rfl) ⟨395519, by rfl⟩ : syracuseStep 2109437 = 791039) (by norm_num)
theorem B3043325 : Blo 1405522 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B2109461 : Blo 1405522 2109461 := bbase (se 6 (by rfl) ⟨49440, by rfl⟩ : syracuseStep 2109461 = 98881) (by norm_num)
theorem B2002973 : Blo 1405522 2002973 := bbase (se 3 (by rfl) ⟨375557, by rfl⟩ : syracuseStep 2002973 = 751115) (by norm_num)
theorem B4747301 : Blo 1405522 4747301 := bbase (se 4 (by rfl) ⟨445059, by rfl⟩ : syracuseStep 4747301 = 890119) (by norm_num)
theorem B2404397 : Blo 1405522 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B2109485 : Blo 1405522 2109485 := bbase (se 3 (by rfl) ⟨395528, by rfl⟩ : syracuseStep 2109485 = 791057) (by norm_num)
theorem B3166253 : Blo 1405522 3166253 := bbase (se 3 (by rfl) ⟨593672, by rfl⟩ : syracuseStep 3166253 = 1187345) (by norm_num)
theorem B2109509 : Blo 1405522 2109509 := bbase (se 4 (by rfl) ⟨197766, by rfl⟩ : syracuseStep 2109509 = 395533) (by norm_num)
theorem B2109533 : Blo 1405522 2109533 := bbase (se 3 (by rfl) ⟨395537, by rfl⟩ : syracuseStep 2109533 = 791075) (by norm_num)
theorem B2535533 : Blo 1405522 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B8548469 : Blo 1405522 8548469 := bbase (se 5 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 8548469 = 801419) (by norm_num)
theorem B2109557 : Blo 1405522 2109557 := bbase (se 5 (by rfl) ⟨98885, by rfl⟩ : syracuseStep 2109557 = 197771) (by norm_num)
theorem B3166325 : Blo 1405522 3166325 := bbase (se 5 (by rfl) ⟨148421, by rfl⟩ : syracuseStep 3166325 = 296843) (by norm_num)
theorem B3379325 : Blo 1405522 3379325 := bbase (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) (by norm_num)
theorem B3559565 : Blo 1405522 3559565 := bbase (se 3 (by rfl) ⟨667418, by rfl⟩ : syracuseStep 3559565 = 1334837) (by norm_num)
theorem B2109581 : Blo 1405522 2109581 := bbase (se 3 (by rfl) ⟨395546, by rfl⟩ : syracuseStep 2109581 = 791093) (by norm_num)
theorem B2109605 : Blo 1405522 2109605 := bbase (se 4 (by rfl) ⟨197775, by rfl⟩ : syracuseStep 2109605 = 395551) (by norm_num)
theorem B2535605 : Blo 1405522 2535605 := bbase (se 5 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 2535605 = 237713) (by norm_num)
theorem B2109629 : Blo 1405522 2109629 := bbase (se 3 (by rfl) ⟨395555, by rfl⟩ : syracuseStep 2109629 = 791111) (by norm_num)
theorem B3166397 : Blo 1405522 3166397 := bbase (se 3 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 3166397 = 1187399) (by norm_num)
theorem B2109653 : Blo 1405522 2109653 := bbase (se 7 (by rfl) ⟨24722, by rfl⟩ : syracuseStep 2109653 = 49445) (by norm_num)
theorem B2109677 : Blo 1405522 2109677 := bbase (se 3 (by rfl) ⟨395564, by rfl⟩ : syracuseStep 2109677 = 791129) (by norm_num)
theorem B12824821 : Blo 1405522 12824821 := bbase (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) (by norm_num)
theorem B2109701 : Blo 1405522 2109701 := bbase (se 4 (by rfl) ⟨197784, by rfl⟩ : syracuseStep 2109701 = 395569) (by norm_num)
theorem B3166469 : Blo 1405522 3166469 := bbase (se 4 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 3166469 = 593713) (by norm_num)
theorem B5067029 : Blo 1405522 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B2109725 : Blo 1405522 2109725 := bbase (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) (by norm_num)
theorem B2109749 : Blo 1405522 2109749 := bbase (se 5 (by rfl) ⟨98894, by rfl⟩ : syracuseStep 2109749 = 197789) (by norm_num)
theorem B2371909 : Blo 1405522 2371909 := bbase (se 4 (by rfl) ⟨222366, by rfl⟩ : syracuseStep 2371909 = 444733) (by norm_num)
theorem B2109773 : Blo 1405522 2109773 := bbase (se 3 (by rfl) ⟨395582, by rfl⟩ : syracuseStep 2109773 = 791165) (by norm_num)
theorem B3166541 : Blo 1405522 3166541 := bbase (se 3 (by rfl) ⟨593726, by rfl⟩ : syracuseStep 3166541 = 1187453) (by norm_num)
theorem B3002717 : Blo 1405522 3002717 := bbase (se 3 (by rfl) ⟨563009, by rfl⟩ : syracuseStep 3002717 = 1126019) (by norm_num)
theorem B2109797 : Blo 1405522 2109797 := bbase (se 4 (by rfl) ⟨197793, by rfl⟩ : syracuseStep 2109797 = 395587) (by norm_num)
theorem B7123301 : Blo 1405522 7123301 := bbase (se 4 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 7123301 = 1335619) (by norm_num)
theorem B8016245 : Blo 1405522 8016245 := bbase (se 5 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 8016245 = 751523) (by norm_num)
theorem B2109821 : Blo 1405522 2109821 := bbase (se 3 (by rfl) ⟨395591, by rfl⟩ : syracuseStep 2109821 = 791183) (by norm_num)
theorem B2109845 : Blo 1405522 2109845 := bbase (se 6 (by rfl) ⟨49449, by rfl⟩ : syracuseStep 2109845 = 98899) (by norm_num)
theorem B3166613 : Blo 1405522 3166613 := bbase (se 6 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 3166613 = 148435) (by norm_num)
theorem B2371997 : Blo 1405522 2371997 := bbase (se 3 (by rfl) ⟨444749, by rfl⟩ : syracuseStep 2371997 = 889499) (by norm_num)
theorem B2109869 : Blo 1405522 2109869 := bbase (se 3 (by rfl) ⟨395600, by rfl⟩ : syracuseStep 2109869 = 791201) (by norm_num)
theorem B2109893 : Blo 1405522 2109893 := bbase (se 4 (by rfl) ⟨197802, by rfl⟩ : syracuseStep 2109893 = 395605) (by norm_num)
theorem B4747733 : Blo 1405522 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B2109917 : Blo 1405522 2109917 := bbase (se 3 (by rfl) ⟨395609, by rfl⟩ : syracuseStep 2109917 = 791219) (by norm_num)
theorem B3166685 : Blo 1405522 3166685 := bbase (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) (by norm_num)
theorem B3559909 : Blo 1405522 3559909 := bbase (se 4 (by rfl) ⟨333741, by rfl⟩ : syracuseStep 3559909 = 667483) (by norm_num)
theorem B2109941 : Blo 1405522 2109941 := bbase (se 5 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 2109941 = 197807) (by norm_num)
theorem B2109965 : Blo 1405522 2109965 := bbase (se 3 (by rfl) ⟨395618, by rfl⟩ : syracuseStep 2109965 = 791237) (by norm_num)
theorem B20263445 : Blo 1405522 20263445 := bbase (se 6 (by rfl) ⟨474924, by rfl⟩ : syracuseStep 20263445 = 949849) (by norm_num)
theorem B2372125 : Blo 1405522 2372125 := bbase (se 3 (by rfl) ⟨444773, by rfl⟩ : syracuseStep 2372125 = 889547) (by norm_num)
theorem B2109989 : Blo 1405522 2109989 := bbase (se 4 (by rfl) ⟨197811, by rfl⟩ : syracuseStep 2109989 = 395623) (by norm_num)
theorem B3166757 : Blo 1405522 3166757 := bbase (se 4 (by rfl) ⟨296883, by rfl⟩ : syracuseStep 3166757 = 593767) (by norm_num)
theorem B8114741 : Blo 1405522 8114741 := bbase (se 5 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 8114741 = 760757) (by norm_num)
theorem B2110013 : Blo 1405522 2110013 := bbase (se 3 (by rfl) ⟨395627, by rfl⟩ : syracuseStep 2110013 = 791255) (by norm_num)
theorem B3560021 : Blo 1405522 3560021 := bbase (se 8 (by rfl) ⟨20859, by rfl⟩ : syracuseStep 3560021 = 41719) (by norm_num)
theorem B2110037 : Blo 1405522 2110037 := bbase (se 8 (by rfl) ⟨12363, by rfl⟩ : syracuseStep 2110037 = 24727) (by norm_num)
theorem B9015893 : Blo 1405522 9015893 := bbase (se 8 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 9015893 = 105655) (by norm_num)
theorem B2110061 : Blo 1405522 2110061 := bbase (se 3 (by rfl) ⟨395636, by rfl⟩ : syracuseStep 2110061 = 791273) (by norm_num)
theorem B3166829 : Blo 1405522 3166829 := bbase (se 3 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 3166829 = 1187561) (by norm_num)
theorem B2372213 : Blo 1405522 2372213 := bbase (se 5 (by rfl) ⟨111197, by rfl⟩ : syracuseStep 2372213 = 222395) (by norm_num)
theorem B2110085 : Blo 1405522 2110085 := bbase (se 4 (by rfl) ⟨197820, by rfl⟩ : syracuseStep 2110085 = 395641) (by norm_num)
theorem B2110109 : Blo 1405522 2110109 := bbase (se 3 (by rfl) ⟨395645, by rfl⟩ : syracuseStep 2110109 = 791291) (by norm_num)
theorem B2110133 : Blo 1405522 2110133 := bbase (se 5 (by rfl) ⟨98912, by rfl⟩ : syracuseStep 2110133 = 197825) (by norm_num)
theorem B3166901 : Blo 1405522 3166901 := bbase (se 5 (by rfl) ⟨148448, by rfl⟩ : syracuseStep 3166901 = 296897) (by norm_num)
theorem B3003085 : Blo 1405522 3003085 := bbase (se 3 (by rfl) ⟨563078, by rfl⟩ : syracuseStep 3003085 = 1126157) (by norm_num)
theorem B2110157 : Blo 1405522 2110157 := bbase (se 3 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 2110157 = 791309) (by norm_num)
theorem B2110181 : Blo 1405522 2110181 := bbase (se 4 (by rfl) ⟨197829, by rfl⟩ : syracuseStep 2110181 = 395659) (by norm_num)
theorem B2372341 : Blo 1405522 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B5337845 : Blo 1405522 5337845 := bbase (se 5 (by rfl) ⟨250211, by rfl⟩ : syracuseStep 5337845 = 500423) (by norm_num)
theorem B2110205 : Blo 1405522 2110205 := bbase (se 3 (by rfl) ⟨395663, by rfl⟩ : syracuseStep 2110205 = 791327) (by norm_num)
theorem B7115525 : Blo 1405522 7115525 := bbase (se 4 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 7115525 = 1334161) (by norm_num)
theorem B2003725 : Blo 1405522 2003725 := bbase (se 3 (by rfl) ⟨375698, by rfl⟩ : syracuseStep 2003725 = 751397) (by norm_num)
theorem B3560213 : Blo 1405522 3560213 := bbase (se 6 (by rfl) ⟨83442, by rfl⟩ : syracuseStep 3560213 = 166885) (by norm_num)
theorem B2110229 : Blo 1405522 2110229 := bbase (se 6 (by rfl) ⟨49458, by rfl⟩ : syracuseStep 2110229 = 98917) (by norm_num)
theorem B2110253 : Blo 1405522 2110253 := bbase (se 3 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 2110253 = 791345) (by norm_num)
theorem B2110277 : Blo 1405522 2110277 := bbase (se 4 (by rfl) ⟨197838, by rfl⟩ : syracuseStep 2110277 = 395677) (by norm_num)
theorem B2372429 : Blo 1405522 2372429 := bbase (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) (by norm_num)
theorem B2110301 : Blo 1405522 2110301 := bbase (se 3 (by rfl) ⟨395681, by rfl⟩ : syracuseStep 2110301 = 791363) (by norm_num)
theorem B2110325 : Blo 1405522 2110325 := bbase (se 5 (by rfl) ⟨98921, by rfl⟩ : syracuseStep 2110325 = 197843) (by norm_num)
theorem B4748165 : Blo 1405522 4748165 := bbase (se 4 (by rfl) ⟨445140, by rfl⟩ : syracuseStep 4748165 = 890281) (by norm_num)
theorem B2110349 : Blo 1405522 2110349 := bbase (se 3 (by rfl) ⟨395690, by rfl⟩ : syracuseStep 2110349 = 791381) (by norm_num)
theorem B2110373 : Blo 1405522 2110373 := bbase (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) (by norm_num)
theorem B2110397 : Blo 1405522 2110397 := bbase (se 3 (by rfl) ⟨395699, by rfl⟩ : syracuseStep 2110397 = 791399) (by norm_num)
theorem B2372557 : Blo 1405522 2372557 := bbase (se 3 (by rfl) ⟨444854, by rfl⟩ : syracuseStep 2372557 = 889709) (by norm_num)
theorem B2110421 : Blo 1405522 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B2110445 : Blo 1405522 2110445 := bbase (se 3 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 2110445 = 791417) (by norm_num)
theorem B2028541 : Blo 1405522 2028541 := bbase (se 3 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 2028541 = 760703) (by norm_num)
theorem B2110469 : Blo 1405522 2110469 := bbase (se 4 (by rfl) ⟨197856, by rfl⟩ : syracuseStep 2110469 = 395713) (by norm_num)
theorem B5338133 : Blo 1405522 5338133 := bbase (se 6 (by rfl) ⟨125112, by rfl⟩ : syracuseStep 5338133 = 250225) (by norm_num)
theorem B2110493 : Blo 1405522 2110493 := bbase (se 3 (by rfl) ⟨395717, by rfl⟩ : syracuseStep 2110493 = 791435) (by norm_num)
theorem B2372645 : Blo 1405522 2372645 := bbase (se 4 (by rfl) ⟨222435, by rfl⟩ : syracuseStep 2372645 = 444871) (by norm_num)
theorem B2110517 : Blo 1405522 2110517 := bbase (se 5 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 2110517 = 197861) (by norm_num)
theorem B2110541 : Blo 1405522 2110541 := bbase (se 3 (by rfl) ⟨395726, by rfl⟩ : syracuseStep 2110541 = 791453) (by norm_num)
theorem B2110565 : Blo 1405522 2110565 := bbase (se 4 (by rfl) ⟨197865, by rfl⟩ : syracuseStep 2110565 = 395731) (by norm_num)
theorem B3560557 : Blo 1405522 3560557 := bbase (se 3 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 3560557 = 1335209) (by norm_num)
theorem B2110589 : Blo 1405522 2110589 := bbase (se 3 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 2110589 = 791471) (by norm_num)
theorem B2110613 : Blo 1405522 2110613 := bbase (se 6 (by rfl) ⟨49467, by rfl⟩ : syracuseStep 2110613 = 98935) (by norm_num)
theorem B2372773 : Blo 1405522 2372773 := bbase (se 4 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 2372773 = 444895) (by norm_num)
theorem B2110637 : Blo 1405522 2110637 := bbase (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) (by norm_num)
theorem B2110661 : Blo 1405522 2110661 := bbase (se 4 (by rfl) ⟨197874, by rfl⟩ : syracuseStep 2110661 = 395749) (by norm_num)
theorem B3560669 : Blo 1405522 3560669 := bbase (se 3 (by rfl) ⟨667625, by rfl⟩ : syracuseStep 3560669 = 1335251) (by norm_num)
theorem B2110685 : Blo 1405522 2110685 := bbase (se 3 (by rfl) ⟨395753, by rfl⟩ : syracuseStep 2110685 = 791507) (by norm_num)
theorem B2110709 : Blo 1405522 2110709 := bbase (se 5 (by rfl) ⟨98939, by rfl⟩ : syracuseStep 2110709 = 197879) (by norm_num)
theorem B2372861 : Blo 1405522 2372861 := bbase (se 3 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 2372861 = 889823) (by norm_num)
theorem B3044621 : Blo 1405522 3044621 := bbase (se 3 (by rfl) ⟨570866, by rfl⟩ : syracuseStep 3044621 = 1141733) (by norm_num)
theorem B2110733 : Blo 1405522 2110733 := bbase (se 3 (by rfl) ⟨395762, by rfl⟩ : syracuseStep 2110733 = 791525) (by norm_num)
theorem B2110757 : Blo 1405522 2110757 := bbase (se 4 (by rfl) ⟨197883, by rfl⟩ : syracuseStep 2110757 = 395767) (by norm_num)
theorem B4748597 : Blo 1405522 4748597 := bbase (se 5 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 4748597 = 445181) (by norm_num)
theorem B2110781 : Blo 1405522 2110781 := bbase (se 3 (by rfl) ⟨395771, by rfl⟩ : syracuseStep 2110781 = 791543) (by norm_num)
theorem B2110805 : Blo 1405522 2110805 := bbase (se 13 (by rfl) ⟨386, by rfl⟩ : syracuseStep 2110805 = 773) (by norm_num)
theorem B2315621 : Blo 1405522 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B2110829 : Blo 1405522 2110829 := bbase (se 3 (by rfl) ⟨395780, by rfl⟩ : syracuseStep 2110829 = 791561) (by norm_num)
theorem B2372989 : Blo 1405522 2372989 := bbase (se 3 (by rfl) ⟨444935, by rfl⟩ : syracuseStep 2372989 = 889871) (by norm_num)
theorem B2110853 : Blo 1405522 2110853 := bbase (se 4 (by rfl) ⟨197892, by rfl⟩ : syracuseStep 2110853 = 395785) (by norm_num)
theorem B3560861 : Blo 1405522 3560861 := bbase (se 3 (by rfl) ⟨667661, by rfl⟩ : syracuseStep 3560861 = 1335323) (by norm_num)
theorem B2110877 : Blo 1405522 2110877 := bbase (se 3 (by rfl) ⟨395789, by rfl⟩ : syracuseStep 2110877 = 791579) (by norm_num)
theorem B2110901 : Blo 1405522 2110901 := bbase (se 5 (by rfl) ⟨98948, by rfl⟩ : syracuseStep 2110901 = 197897) (by norm_num)
theorem B2110925 : Blo 1405522 2110925 := bbase (se 3 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 2110925 = 791597) (by norm_num)
theorem B2373077 : Blo 1405522 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B2110949 : Blo 1405522 2110949 := bbase (se 4 (by rfl) ⟨197901, by rfl⟩ : syracuseStep 2110949 = 395803) (by norm_num)
theorem B2110973 : Blo 1405522 2110973 := bbase (se 3 (by rfl) ⟨395807, by rfl⟩ : syracuseStep 2110973 = 791615) (by norm_num)
theorem B2569733 : Blo 1405522 2569733 := bbase (se 4 (by rfl) ⟨240912, by rfl⟩ : syracuseStep 2569733 = 481825) (by norm_num)
theorem B2110997 : Blo 1405522 2110997 := bbase (se 6 (by rfl) ⟨49476, by rfl⟩ : syracuseStep 2110997 = 98953) (by norm_num)
theorem B2111021 : Blo 1405522 2111021 := bbase (se 3 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 2111021 = 791633) (by norm_num)
theorem B2111045 : Blo 1405522 2111045 := bbase (se 4 (by rfl) ⟨197910, by rfl⟩ : syracuseStep 2111045 = 395821) (by norm_num)
theorem B2373205 : Blo 1405522 2373205 := bbase (se 8 (by rfl) ⟨13905, by rfl⟩ : syracuseStep 2373205 = 27811) (by norm_num)
theorem B5781077 : Blo 1405522 5781077 := bbase (se 8 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 5781077 = 67747) (by norm_num)
theorem B2111069 : Blo 1405522 2111069 := bbase (se 3 (by rfl) ⟨395825, by rfl⟩ : syracuseStep 2111069 = 791651) (by norm_num)
theorem B7124597 : Blo 1405522 7124597 := bbase (se 5 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 7124597 = 667931) (by norm_num)
theorem B2111093 : Blo 1405522 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B2111117 : Blo 1405522 2111117 := bbase (se 3 (by rfl) ⟨395834, by rfl⟩ : syracuseStep 2111117 = 791669) (by norm_num)
theorem B7214741 : Blo 1405522 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B2111141 : Blo 1405522 2111141 := bbase (se 4 (by rfl) ⟨197919, by rfl⟩ : syracuseStep 2111141 = 395839) (by norm_num)
theorem B2373293 : Blo 1405522 2373293 := bbase (se 3 (by rfl) ⟨444992, by rfl⟩ : syracuseStep 2373293 = 889985) (by norm_num)
theorem B2111165 : Blo 1405522 2111165 := bbase (se 3 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 2111165 = 791687) (by norm_num)
theorem B2111189 : Blo 1405522 2111189 := bbase (se 7 (by rfl) ⟨24740, by rfl⟩ : syracuseStep 2111189 = 49481) (by norm_num)
theorem B4749029 : Blo 1405522 4749029 := bbase (se 4 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 4749029 = 890443) (by norm_num)
theorem B1603309 : Blo 1405522 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B2111213 : Blo 1405522 2111213 := bbase (se 3 (by rfl) ⟨395852, by rfl⟩ : syracuseStep 2111213 = 791705) (by norm_num)
theorem B3561205 : Blo 1405522 3561205 := bbase (se 5 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 3561205 = 333863) (by norm_num)
theorem B2111237 : Blo 1405522 2111237 := bbase (se 4 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 2111237 = 395857) (by norm_num)
theorem B2111261 : Blo 1405522 2111261 := bbase (se 3 (by rfl) ⟨395861, by rfl⟩ : syracuseStep 2111261 = 791723) (by norm_num)
theorem B2373421 : Blo 1405522 2373421 := bbase (se 3 (by rfl) ⟨445016, by rfl⟩ : syracuseStep 2373421 = 890033) (by norm_num)
theorem B3561317 : Blo 1405522 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B2373509 : Blo 1405522 2373509 := bbase (se 4 (by rfl) ⟨222516, by rfl⟩ : syracuseStep 2373509 = 445033) (by norm_num)
theorem B1603541 : Blo 1405522 1603541 := bbase (se 7 (by rfl) ⟨18791, by rfl⟩ : syracuseStep 1603541 = 37583) (by norm_num)
theorem B2373637 : Blo 1405522 2373637 := bbase (se 4 (by rfl) ⟨222528, by rfl⟩ : syracuseStep 2373637 = 445057) (by norm_num)
theorem B2668565 : Blo 1405522 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B7116821 : Blo 1405522 7116821 := bbase (se 6 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 7116821 = 333601) (by norm_num)
theorem B3561509 : Blo 1405522 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B9140309 : Blo 1405522 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B2373725 : Blo 1405522 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B4749461 : Blo 1405522 4749461 := bbase (se 6 (by rfl) ⟨111315, by rfl⟩ : syracuseStep 4749461 = 222631) (by norm_num)
theorem B2668717 : Blo 1405522 2668717 := bbase (se 3 (by rfl) ⟨500384, by rfl⟩ : syracuseStep 2668717 = 1000769) (by norm_num)
theorem B3004589 : Blo 1405522 3004589 := bbase (se 3 (by rfl) ⟨563360, by rfl⟩ : syracuseStep 3004589 = 1126721) (by norm_num)
theorem B3381421 : Blo 1405522 3381421 := bbase (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) (by norm_num)
theorem B5339317 : Blo 1405522 5339317 := bbase (se 5 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 5339317 = 500561) (by norm_num)
theorem B2373853 : Blo 1405522 2373853 := bbase (se 3 (by rfl) ⟨445097, by rfl⟩ : syracuseStep 2373853 = 890195) (by norm_num)
theorem B25680149 : Blo 1405522 25680149 := bbase (se 6 (by rfl) ⟨601878, by rfl⟩ : syracuseStep 25680149 = 1203757) (by norm_num)
theorem B1521973 : Blo 1405522 1521973 := bbase (se 5 (by rfl) ⟨71342, by rfl⟩ : syracuseStep 1521973 = 142685) (by norm_num)
theorem B2373941 : Blo 1405522 2373941 := bbase (se 5 (by rfl) ⟨111278, by rfl⟩ : syracuseStep 2373941 = 222557) (by norm_num)
theorem B3004733 : Blo 1405522 3004733 := bbase (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) (by norm_num)
theorem B1522033 : Blo 1405522 1522033 := bbase (se 2 (by rfl) ⟨570762, by rfl⟩ : syracuseStep 1522033 = 1141525) (by norm_num)
theorem B3561853 : Blo 1405522 3561853 := bbase (se 3 (by rfl) ⟨667847, by rfl⟩ : syracuseStep 3561853 = 1335695) (by norm_num)
theorem B4004261 : Blo 1405522 4004261 := bbase (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) (by norm_num)
theorem B2374069 : Blo 1405522 2374069 := bbase (se 5 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 2374069 = 222569) (by norm_num)
theorem B6756805 : Blo 1405522 6756805 := bbase (se 4 (by rfl) ⟨633450, by rfl⟩ : syracuseStep 6756805 = 1266901) (by norm_num)
theorem B2669021 : Blo 1405522 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B5339621 : Blo 1405522 5339621 := bbase (se 4 (by rfl) ⟨500589, by rfl⟩ : syracuseStep 5339621 = 1001179) (by norm_num)
theorem B3561965 : Blo 1405522 3561965 := bbase (se 3 (by rfl) ⟨667868, by rfl⟩ : syracuseStep 3561965 = 1335737) (by norm_num)
theorem B10680821 : Blo 1405522 10680821 := bbase (se 5 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 10680821 = 1001327) (by norm_num)
theorem B2374157 : Blo 1405522 2374157 := bbase (se 3 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 2374157 = 890309) (by norm_num)
theorem B1604125 : Blo 1405522 1604125 := bbase (se 3 (by rfl) ⟨300773, by rfl⟩ : syracuseStep 1604125 = 601547) (by norm_num)
theorem B4749893 : Blo 1405522 4749893 := bbase (se 4 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 4749893 = 890605) (by norm_num)
theorem B2374285 : Blo 1405522 2374285 := bbase (se 3 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 2374285 = 890357) (by norm_num)
theorem B3005093 : Blo 1405522 3005093 := bbase (se 4 (by rfl) ⟨281727, by rfl⟩ : syracuseStep 3005093 = 563455) (by norm_num)
theorem B3562157 : Blo 1405522 3562157 := bbase (se 3 (by rfl) ⟨667904, by rfl⟩ : syracuseStep 3562157 = 1335809) (by norm_num)
theorem B2374373 : Blo 1405522 2374373 := bbase (se 4 (by rfl) ⟨222597, by rfl⟩ : syracuseStep 2374373 = 445195) (by norm_num)
theorem B6011653 : Blo 1405522 6011653 := bbase (se 4 (by rfl) ⟨563592, by rfl⟩ : syracuseStep 6011653 = 1127185) (by norm_num)
theorem B2849573 : Blo 1405522 2849573 := bbase (se 4 (by rfl) ⟨267147, by rfl⟩ : syracuseStep 2849573 = 534295) (by norm_num)
theorem B4275013 : Blo 1405522 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B2374501 : Blo 1405522 2374501 := bbase (se 4 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 2374501 = 445219) (by norm_num)
theorem B2374589 : Blo 1405522 2374589 := bbase (se 3 (by rfl) ⟨445235, by rfl⟩ : syracuseStep 2374589 = 890471) (by norm_num)
theorem B4750325 : Blo 1405522 4750325 := bbase (se 5 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 4750325 = 445343) (by norm_num)
theorem B3562501 : Blo 1405522 3562501 := bbase (se 4 (by rfl) ⟨333984, by rfl⟩ : syracuseStep 3562501 = 667969) (by norm_num)
theorem B2374717 : Blo 1405522 2374717 := bbase (se 3 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 2374717 = 890519) (by norm_num)
theorem B3562613 : Blo 1405522 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B2407541 : Blo 1405522 2407541 := bbase (se 5 (by rfl) ⟨112853, by rfl⟩ : syracuseStep 2407541 = 225707) (by norm_num)
theorem B2374805 : Blo 1405522 2374805 := bbase (se 6 (by rfl) ⟨55659, by rfl⟩ : syracuseStep 2374805 = 111319) (by norm_num)
theorem B1604809 : Blo 1405522 1604809 := bbase (se 2 (by rfl) ⟨601803, by rfl⟩ : syracuseStep 1604809 = 1203607) (by norm_num)
theorem B2669773 : Blo 1405522 2669773 := bbase (se 3 (by rfl) ⟨500582, by rfl⟩ : syracuseStep 2669773 = 1001165) (by norm_num)
theorem B2374933 : Blo 1405522 2374933 := bbase (se 6 (by rfl) ⟨55662, by rfl⟩ : syracuseStep 2374933 = 111325) (by norm_num)
theorem B7118117 : Blo 1405522 7118117 := bbase (se 4 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 7118117 = 1334647) (by norm_num)
theorem B2669917 : Blo 1405522 2669917 := bbase (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) (by norm_num)
theorem B1899877 : Blo 1405522 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B2252141 : Blo 1405522 2252141 := bbase (se 3 (by rfl) ⟨422276, by rfl⟩ : syracuseStep 2252141 = 844553) (by norm_num)
theorem B2375021 : Blo 1405522 2375021 := bbase (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) (by norm_num)
theorem B18013589 : Blo 1405522 18013589 := bbase (se 6 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 18013589 = 844387) (by norm_num)
theorem B3710357 : Blo 1405522 3710357 := bbase (se 6 (by rfl) ⟨86961, by rfl⟩ : syracuseStep 3710357 = 173923) (by norm_num)
theorem B2375149 : Blo 1405522 2375149 := bbase (se 3 (by rfl) ⟨445340, by rfl⟩ : syracuseStep 2375149 = 890681) (by norm_num)
theorem B2670077 : Blo 1405522 2670077 := bbase (se 3 (by rfl) ⟨500639, by rfl⟩ : syracuseStep 2670077 = 1001279) (by norm_num)
theorem B3005981 : Blo 1405522 3005981 := bbase (se 3 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 3005981 = 1127243) (by norm_num)
theorem B2252333 : Blo 1405522 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B4005445 : Blo 1405522 4005445 := bbase (se 4 (by rfl) ⟨375510, by rfl⟩ : syracuseStep 4005445 = 751021) (by norm_num)
theorem B2670221 : Blo 1405522 2670221 := bbase (se 3 (by rfl) ⟨500666, by rfl⟩ : syracuseStep 2670221 = 1001333) (by norm_num)
theorem B4005605 : Blo 1405522 4005605 := bbase (se 4 (by rfl) ⟨375525, by rfl⟩ : syracuseStep 4005605 = 751051) (by norm_num)
theorem B12017429 : Blo 1405522 12017429 := bbase (se 6 (by rfl) ⟨281658, by rfl⟩ : syracuseStep 12017429 = 563317) (by norm_num)
theorem B100081493 : Blo 1405522 100081493 := bbase (se 9 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 100081493 = 586415) (by norm_num)
theorem B3252077 : Blo 1405522 3252077 := bbase (se 3 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 3252077 = 1219529) (by norm_num)
theorem B3800965 : Blo 1405522 3800965 := bbase (se 4 (by rfl) ⟨356340, by rfl⟩ : syracuseStep 3800965 = 712681) (by norm_num)
theorem B2670509 : Blo 1405522 2670509 := bbase (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) (by norm_num)
theorem B4005845 : Blo 1405522 4005845 := bbase (se 7 (by rfl) ⟨46943, by rfl⟩ : syracuseStep 4005845 = 93887) (by norm_num)
theorem B1900525 : Blo 1405522 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B1425443 : Blo 1405522 1425443 := bstep (se 1 (by rfl) ⟨1069082, by rfl⟩ : syracuseStep 1425443 = 2138165) B2138165
theorem B5341261 : Blo 1405522 5341261 := bstep (se 3 (by rfl) ⟨1001486, by rfl⟩ : syracuseStep 5341261 = 2002973) B2002973
theorem B2252929 : Blo 1405522 2252929 := bstep (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) B1689697
theorem B4006061 : Blo 1405522 4006061 := bstep (se 3 (by rfl) ⟨751136, by rfl⟩ : syracuseStep 4006061 = 1502273) B1502273
theorem B22806755 : Blo 1405522 22806755 := bstep (se 1 (by rfl) ⟨17105066, by rfl⟩ : syracuseStep 22806755 = 34210133) B34210133
theorem B7119089 : Blo 1405522 7119089 := bstep (se 2 (by rfl) ⟨2669658, by rfl⟩ : syracuseStep 7119089 = 5339317) B5339317
theorem B1581331 : Blo 1405522 1581331 := bstep (se 1 (by rfl) ⟨1185998, by rfl⟩ : syracuseStep 1581331 = 2371997) B2371997
theorem B13508963 : Blo 1405522 13508963 := bstep (se 1 (by rfl) ⟨10131722, by rfl⟩ : syracuseStep 13508963 = 20263445) B20263445
theorem B8552803 : Blo 1405522 8552803 := bstep (se 1 (by rfl) ⟨6414602, by rfl⟩ : syracuseStep 8552803 = 12829205) B12829205
theorem B10682765 : Blo 1405522 10682765 := bstep (se 3 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 10682765 = 4006037) B4006037
theorem B1581475 : Blo 1405522 1581475 := bstep (se 1 (by rfl) ⟨1186106, by rfl⟩ : syracuseStep 1581475 = 2372213) B2372213
theorem B3162545 : Blo 1405522 3162545 := bstep (se 2 (by rfl) ⟨1185954, by rfl⟩ : syracuseStep 3162545 = 2371909) B2371909
theorem B3162563 : Blo 1405522 3162563 := bstep (se 1 (by rfl) ⟨2371922, by rfl⟩ : syracuseStep 3162563 = 4743845) B4743845
theorem B4743683 : Blo 1405522 4743683 := bstep (se 1 (by rfl) ⟨3557762, by rfl⟩ : syracuseStep 4743683 = 7115525) B7115525
theorem B1581619 : Blo 1405522 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B14426693 : Blo 1405522 14426693 := bstep (se 4 (by rfl) ⟨1352502, by rfl⟩ : syracuseStep 14426693 = 2705005) B2705005
theorem B1581763 : Blo 1405522 1581763 := bstep (se 1 (by rfl) ⟨1186322, by rfl⟩ : syracuseStep 1581763 = 2372645) B2372645
theorem B3162833 : Blo 1405522 3162833 := bstep (se 2 (by rfl) ⟨1186062, by rfl⟩ : syracuseStep 3162833 = 2372125) B2372125
theorem B2138833 : Blo 1405522 2138833 := bstep (se 2 (by rfl) ⟨802062, by rfl⟩ : syracuseStep 2138833 = 1604125) B1604125
theorem B3162851 : Blo 1405522 3162851 := bstep (se 1 (by rfl) ⟨2372138, by rfl⟩ : syracuseStep 3162851 = 4744277) B4744277
theorem B4743953 : Blo 1405522 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B2253601 : Blo 1405522 2253601 := bstep (se 2 (by rfl) ⟨845100, by rfl⟩ : syracuseStep 2253601 = 1690201) B1690201
theorem B8012621 : Blo 1405522 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B1581907 : Blo 1405522 1581907 := bstep (se 1 (by rfl) ⟨1186430, by rfl⟩ : syracuseStep 1581907 = 2372861) B2372861
theorem B5342051 : Blo 1405522 5342051 := bstep (se 1 (by rfl) ⟨4006538, by rfl⟩ : syracuseStep 5342051 = 8013077) B8013077
theorem B13517765 : Blo 1405522 13517765 := bstep (se 4 (by rfl) ⟨1267290, by rfl⟩ : syracuseStep 13517765 = 2534581) B2534581
theorem B1803235 : Blo 1405522 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B1582051 : Blo 1405522 1582051 := bstep (se 1 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 1582051 = 2373077) B2373077
theorem B3163121 : Blo 1405522 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B3163139 : Blo 1405522 3163139 := bstep (se 1 (by rfl) ⟨2372354, by rfl⟩ : syracuseStep 3163139 = 4744709) B4744709
theorem B1713155 : Blo 1405522 1713155 := bstep (se 1 (by rfl) ⟨1284866, by rfl⟩ : syracuseStep 1713155 = 2569733) B2569733
theorem B2671633 : Blo 1405522 2671633 := bstep (se 2 (by rfl) ⟨1001862, by rfl⟩ : syracuseStep 2671633 = 2003725) B2003725
theorem B4809827 : Blo 1405522 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B1582195 : Blo 1405522 1582195 := bstep (se 1 (by rfl) ⟨1186646, by rfl⟩ : syracuseStep 1582195 = 2373293) B2373293
theorem B1582339 : Blo 1405522 1582339 := bstep (se 1 (by rfl) ⟨1186754, by rfl⟩ : syracuseStep 1582339 = 2373509) B2373509
theorem B3163409 : Blo 1405522 3163409 := bstep (se 2 (by rfl) ⟨1186278, by rfl⟩ : syracuseStep 3163409 = 2372557) B2372557
theorem B1926433 : Blo 1405522 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B3163427 : Blo 1405522 3163427 := bstep (se 1 (by rfl) ⟨2372570, by rfl⟩ : syracuseStep 3163427 = 4745141) B4745141
theorem B4744493 : Blo 1405522 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B36046133 : Blo 1405522 36046133 := bstep (se 5 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 36046133 = 3379325) B3379325
theorem B4506947 : Blo 1405522 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B4007245 : Blo 1405522 4007245 := bstep (se 3 (by rfl) ⟨751358, by rfl⟩ : syracuseStep 4007245 = 1502717) B1502717
theorem B2704721 : Blo 1405522 2704721 := bstep (se 2 (by rfl) ⟨1014270, by rfl⟩ : syracuseStep 2704721 = 2028541) B2028541
theorem B4744547 : Blo 1405522 4744547 := bstep (se 1 (by rfl) ⟨3558410, by rfl⟩ : syracuseStep 4744547 = 7116821) B7116821
theorem B1582483 : Blo 1405522 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B6006221 : Blo 1405522 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B5342705 : Blo 1405522 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1582627 : Blo 1405522 1582627 := bstep (se 1 (by rfl) ⟨1186970, by rfl⟩ : syracuseStep 1582627 = 2373941) B2373941
theorem B3163697 : Blo 1405522 3163697 := bstep (se 2 (by rfl) ⟨1186386, by rfl⟩ : syracuseStep 3163697 = 2372773) B2372773
theorem B3163715 : Blo 1405522 3163715 := bstep (se 1 (by rfl) ⟨2372786, by rfl⟩ : syracuseStep 3163715 = 4745573) B4745573
theorem B2139745 : Blo 1405522 2139745 := bstep (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) B1604809
theorem B4744817 : Blo 1405522 4744817 := bstep (se 2 (by rfl) ⟨1779306, by rfl⟩ : syracuseStep 4744817 = 3558613) B3558613
theorem B9012869 : Blo 1405522 9012869 := bstep (se 4 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 9012869 = 1689913) B1689913
theorem B1779347 : Blo 1405522 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B7120547 : Blo 1405522 7120547 := bstep (se 1 (by rfl) ⟨5340410, by rfl⟩ : syracuseStep 7120547 = 10680821) B10680821
theorem B1582771 : Blo 1405522 1582771 := bstep (se 1 (by rfl) ⟨1187078, by rfl⟩ : syracuseStep 1582771 = 2374157) B2374157
theorem B2533169 : Blo 1405522 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B1582915 : Blo 1405522 1582915 := bstep (se 1 (by rfl) ⟨1187186, by rfl⟩ : syracuseStep 1582915 = 2374373) B2374373
theorem B3163985 : Blo 1405522 3163985 := bstep (se 2 (by rfl) ⟨1186494, by rfl⟩ : syracuseStep 3163985 = 2372989) B2372989
theorem B3164003 : Blo 1405522 3164003 := bstep (se 1 (by rfl) ⟨2373002, by rfl⟩ : syracuseStep 3164003 = 4746005) B4746005
theorem B1583059 : Blo 1405522 1583059 := bstep (se 1 (by rfl) ⟨1187294, by rfl⟩ : syracuseStep 1583059 = 2374589) B2374589
theorem B15206453 : Blo 1405522 15206453 := bstep (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) B1425605
theorem B3803213 : Blo 1405522 3803213 := bstep (se 3 (by rfl) ⟨713102, by rfl⟩ : syracuseStep 3803213 = 1426205) B1426205
theorem B1583203 : Blo 1405522 1583203 := bstep (se 1 (by rfl) ⟨1187402, by rfl⟩ : syracuseStep 1583203 = 2374805) B2374805
theorem B3164273 : Blo 1405522 3164273 := bstep (se 2 (by rfl) ⟨1186602, by rfl⟩ : syracuseStep 3164273 = 2373205) B2373205
theorem B3164291 : Blo 1405522 3164291 := bstep (se 1 (by rfl) ⟨2373218, by rfl⟩ : syracuseStep 3164291 = 4746437) B4746437
theorem B4745357 : Blo 1405522 4745357 := bstep (se 3 (by rfl) ⟨889754, by rfl⟩ : syracuseStep 4745357 = 1779509) B1779509
theorem B3426467 : Blo 1405522 3426467 := bstep (se 1 (by rfl) ⟨2569850, by rfl⟩ : syracuseStep 3426467 = 5139701) B5139701
theorem B4745411 : Blo 1405522 4745411 := bstep (se 1 (by rfl) ⟨3559058, by rfl⟩ : syracuseStep 4745411 = 7118117) B7118117
theorem B1501427 : Blo 1405522 1501427 := bstep (se 1 (by rfl) ⟨1126070, by rfl⟩ : syracuseStep 1501427 = 2252141) B2252141
theorem B1583347 : Blo 1405522 1583347 := bstep (se 1 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 1583347 = 2375021) B2375021
theorem B1780051 : Blo 1405522 1780051 := bstep (se 1 (by rfl) ⟨1335038, by rfl⟩ : syracuseStep 1780051 = 2670077) B2670077
theorem B3164561 : Blo 1405522 3164561 := bstep (se 2 (by rfl) ⟨1186710, by rfl⟩ : syracuseStep 3164561 = 2373421) B2373421
theorem B3164579 : Blo 1405522 3164579 := bstep (se 1 (by rfl) ⟨2373434, by rfl⟩ : syracuseStep 3164579 = 4746869) B4746869
theorem B1780147 : Blo 1405522 1780147 := bstep (se 1 (by rfl) ⟨1335110, by rfl⟩ : syracuseStep 1780147 = 2670221) B2670221
theorem B7121357 : Blo 1405522 7121357 := bstep (se 3 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 7121357 = 2670509) B2670509
theorem B4057553 : Blo 1405522 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B4745681 : Blo 1405522 4745681 := bstep (se 2 (by rfl) ⟨1779630, by rfl⟩ : syracuseStep 4745681 = 3559261) B3559261
theorem B4508227 : Blo 1405522 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B2534033 : Blo 1405522 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B3164849 : Blo 1405522 3164849 := bstep (se 2 (by rfl) ⟨1186818, by rfl⟩ : syracuseStep 3164849 = 2373637) B2373637
theorem B2001601 : Blo 1405522 2001601 := bstep (se 2 (by rfl) ⟨750600, by rfl⟩ : syracuseStep 2001601 = 1501201) B1501201
theorem B3164867 : Blo 1405522 3164867 := bstep (se 1 (by rfl) ⟨2373650, by rfl⟩ : syracuseStep 3164867 = 4747301) B4747301
theorem B10676933 : Blo 1405522 10676933 := bstep (se 4 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 10676933 = 2001925) B2001925
theorem B1690355 : Blo 1405522 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B1690403 : Blo 1405522 1690403 := bstep (se 1 (by rfl) ⟨1267802, by rfl⟩ : syracuseStep 1690403 = 2535605) B2535605
theorem B3378019 : Blo 1405522 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B3804013 : Blo 1405522 3804013 := bstep (se 3 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 3804013 = 1426505) B1426505
theorem B2108291 : Blo 1405522 2108291 := bstep (se 1 (by rfl) ⟨1581218, by rfl⟩ : syracuseStep 2108291 = 3162437) B3162437
theorem B3558289 : Blo 1405522 3558289 := bstep (se 2 (by rfl) ⟨1334358, by rfl⟩ : syracuseStep 3558289 = 2668717) B2668717
theorem B4508561 : Blo 1405522 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B2108321 : Blo 1405522 2108321 := bstep (se 2 (by rfl) ⟨790620, by rfl⟩ : syracuseStep 2108321 = 1581241) B1581241
theorem B1780643 : Blo 1405522 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B5344163 : Blo 1405522 5344163 := bstep (se 1 (by rfl) ⟨4008122, by rfl⟩ : syracuseStep 5344163 = 8016245) B8016245
theorem B5344177 : Blo 1405522 5344177 := bstep (se 2 (by rfl) ⟨2004066, by rfl⟩ : syracuseStep 5344177 = 4008133) B4008133
theorem B2108339 : Blo 1405522 2108339 := bstep (se 1 (by rfl) ⟨1581254, by rfl⟩ : syracuseStep 2108339 = 3162509) B3162509
theorem B2108369 : Blo 1405522 2108369 := bstep (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) B1581277
theorem B3165137 : Blo 1405522 3165137 := bstep (se 2 (by rfl) ⟨1186926, by rfl⟩ : syracuseStep 3165137 = 2373853) B2373853
theorem B2108387 : Blo 1405522 2108387 := bstep (se 1 (by rfl) ⟨1581290, by rfl⟩ : syracuseStep 2108387 = 3162581) B3162581
theorem B3165155 : Blo 1405522 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B4746221 : Blo 1405522 4746221 := bstep (se 3 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 4746221 = 1779833) B1779833
theorem B17099761 : Blo 1405522 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B2108417 : Blo 1405522 2108417 := bstep (se 2 (by rfl) ⟨790656, by rfl⟩ : syracuseStep 2108417 = 1581313) B1581313
theorem B2001937 : Blo 1405522 2001937 := bstep (se 2 (by rfl) ⟨750726, by rfl⟩ : syracuseStep 2001937 = 1501453) B1501453
theorem B2108435 : Blo 1405522 2108435 := bstep (se 1 (by rfl) ⟨1581326, by rfl⟩ : syracuseStep 2108435 = 3162653) B3162653
theorem B5409827 : Blo 1405522 5409827 := bstep (se 1 (by rfl) ⟨4057370, by rfl⟩ : syracuseStep 5409827 = 8114741) B8114741
theorem B4746275 : Blo 1405522 4746275 := bstep (se 1 (by rfl) ⟨3559706, by rfl⟩ : syracuseStep 4746275 = 7119413) B7119413
theorem B2108465 : Blo 1405522 2108465 := bstep (se 2 (by rfl) ⟨790674, by rfl⟩ : syracuseStep 2108465 = 1581349) B1581349
theorem B2108483 : Blo 1405522 2108483 := bstep (se 1 (by rfl) ⟨1581362, by rfl⟩ : syracuseStep 2108483 = 3162725) B3162725
theorem B3804241 : Blo 1405522 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B2108513 : Blo 1405522 2108513 := bstep (se 2 (by rfl) ⟨790692, by rfl⟩ : syracuseStep 2108513 = 1581385) B1581385
theorem B2108531 : Blo 1405522 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B8006789 : Blo 1405522 8006789 := bstep (se 4 (by rfl) ⟨750636, by rfl⟩ : syracuseStep 8006789 = 1501273) B1501273
theorem B2108561 : Blo 1405522 2108561 := bstep (se 2 (by rfl) ⟨790710, by rfl⟩ : syracuseStep 2108561 = 1581421) B1581421
theorem B2108579 : Blo 1405522 2108579 := bstep (se 1 (by rfl) ⟨1581434, by rfl⟩ : syracuseStep 2108579 = 3162869) B3162869
theorem B3558563 : Blo 1405522 3558563 := bstep (se 1 (by rfl) ⟨2668922, by rfl⟩ : syracuseStep 3558563 = 5337845) B5337845
theorem B2108609 : Blo 1405522 2108609 := bstep (se 2 (by rfl) ⟨790728, by rfl⟩ : syracuseStep 2108609 = 1581457) B1581457
theorem B2108627 : Blo 1405522 2108627 := bstep (se 1 (by rfl) ⟨1581470, by rfl⟩ : syracuseStep 2108627 = 3162941) B3162941
theorem B1502435 : Blo 1405522 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B2108657 : Blo 1405522 2108657 := bstep (se 2 (by rfl) ⟨790746, by rfl⟩ : syracuseStep 2108657 = 1581493) B1581493
theorem B3165425 : Blo 1405522 3165425 := bstep (se 2 (by rfl) ⟨1187034, by rfl⟩ : syracuseStep 3165425 = 2374069) B2374069
theorem B10685681 : Blo 1405522 10685681 := bstep (se 2 (by rfl) ⟨4007130, by rfl⟩ : syracuseStep 10685681 = 8014261) B8014261
theorem B2108675 : Blo 1405522 2108675 := bstep (se 1 (by rfl) ⟨1581506, by rfl⟩ : syracuseStep 2108675 = 3163013) B3163013
theorem B3165443 : Blo 1405522 3165443 := bstep (se 1 (by rfl) ⟨2374082, by rfl⟩ : syracuseStep 3165443 = 4748165) B4748165
theorem B2108705 : Blo 1405522 2108705 := bstep (se 2 (by rfl) ⟨790764, by rfl⟩ : syracuseStep 2108705 = 1581529) B1581529
theorem B4746545 : Blo 1405522 4746545 := bstep (se 2 (by rfl) ⟨1779954, by rfl⟩ : syracuseStep 4746545 = 3559909) B3559909
theorem B2108723 : Blo 1405522 2108723 := bstep (se 1 (by rfl) ⟨1581542, by rfl⟩ : syracuseStep 2108723 = 3163085) B3163085
theorem B2108753 : Blo 1405522 2108753 := bstep (se 2 (by rfl) ⟨790782, by rfl⟩ : syracuseStep 2108753 = 1581565) B1581565
theorem B2108771 : Blo 1405522 2108771 := bstep (se 1 (by rfl) ⟨1581578, by rfl⟩ : syracuseStep 2108771 = 3163157) B3163157
theorem B3558755 : Blo 1405522 3558755 := bstep (se 1 (by rfl) ⟨2669066, by rfl⟩ : syracuseStep 3558755 = 5338133) B5338133
theorem B2108801 : Blo 1405522 2108801 := bstep (se 2 (by rfl) ⟨790800, by rfl⟩ : syracuseStep 2108801 = 1581601) B1581601
theorem B2108819 : Blo 1405522 2108819 := bstep (se 1 (by rfl) ⟨1581614, by rfl⟩ : syracuseStep 2108819 = 3163229) B3163229
theorem B2108849 : Blo 1405522 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B2108867 : Blo 1405522 2108867 := bstep (se 1 (by rfl) ⟨1581650, by rfl⟩ : syracuseStep 2108867 = 3163301) B3163301
theorem B2108897 : Blo 1405522 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B2108915 : Blo 1405522 2108915 := bstep (se 1 (by rfl) ⟨1581686, by rfl⟩ : syracuseStep 2108915 = 3163373) B3163373
theorem B2108945 : Blo 1405522 2108945 := bstep (se 2 (by rfl) ⟨790854, by rfl⟩ : syracuseStep 2108945 = 1581709) B1581709
theorem B3165713 : Blo 1405522 3165713 := bstep (se 2 (by rfl) ⟨1187142, by rfl⟩ : syracuseStep 3165713 = 2374285) B2374285
theorem B2108963 : Blo 1405522 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B3165731 : Blo 1405522 3165731 := bstep (se 1 (by rfl) ⟨2374298, by rfl⟩ : syracuseStep 3165731 = 4748597) B4748597
theorem B2108993 : Blo 1405522 2108993 := bstep (se 2 (by rfl) ⟨790872, by rfl⟩ : syracuseStep 2108993 = 1581745) B1581745
theorem B1543747 : Blo 1405522 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B8007245 : Blo 1405522 8007245 := bstep (se 3 (by rfl) ⟨1501358, by rfl⟩ : syracuseStep 8007245 = 3002717) B3002717
theorem B2109011 : Blo 1405522 2109011 := bstep (se 1 (by rfl) ⟨1581758, by rfl⟩ : syracuseStep 2109011 = 3163517) B3163517
theorem B2002529 : Blo 1405522 2002529 := bstep (se 2 (by rfl) ⟨750948, by rfl⟩ : syracuseStep 2002529 = 1501897) B1501897
theorem B5336675 : Blo 1405522 5336675 := bstep (se 1 (by rfl) ⟨4002506, by rfl⟩ : syracuseStep 5336675 = 8005013) B8005013
theorem B1781347 : Blo 1405522 1781347 := bstep (se 1 (by rfl) ⟨1336010, by rfl⟩ : syracuseStep 1781347 = 2672021) B2672021
theorem B2109041 : Blo 1405522 2109041 := bstep (se 2 (by rfl) ⟨790890, by rfl⟩ : syracuseStep 2109041 = 1581781) B1581781
theorem B2109059 : Blo 1405522 2109059 := bstep (se 1 (by rfl) ⟨1581794, by rfl⟩ : syracuseStep 2109059 = 3163589) B3163589
theorem B2109089 : Blo 1405522 2109089 := bstep (se 2 (by rfl) ⟨790908, by rfl⟩ : syracuseStep 2109089 = 1581817) B1581817
theorem B8015537 : Blo 1405522 8015537 := bstep (se 2 (by rfl) ⟨3005826, by rfl⟩ : syracuseStep 8015537 = 6011653) B6011653
theorem B2109107 : Blo 1405522 2109107 := bstep (se 1 (by rfl) ⟨1581830, by rfl⟩ : syracuseStep 2109107 = 3163661) B3163661
theorem B2109137 : Blo 1405522 2109137 := bstep (se 2 (by rfl) ⟨790926, by rfl⟩ : syracuseStep 2109137 = 1581853) B1581853
theorem B2109155 : Blo 1405522 2109155 := bstep (se 1 (by rfl) ⟨1581866, by rfl⟩ : syracuseStep 2109155 = 3163733) B3163733
theorem B3854051 : Blo 1405522 3854051 := bstep (se 1 (by rfl) ⟨2890538, by rfl⟩ : syracuseStep 3854051 = 5781077) B5781077
theorem B2109185 : Blo 1405522 2109185 := bstep (se 2 (by rfl) ⟨790944, by rfl⟩ : syracuseStep 2109185 = 1581889) B1581889
theorem B2109203 : Blo 1405522 2109203 := bstep (se 1 (by rfl) ⟨1581902, by rfl⟩ : syracuseStep 2109203 = 3163805) B3163805
theorem B2109233 : Blo 1405522 2109233 := bstep (se 2 (by rfl) ⟨790962, by rfl⟩ : syracuseStep 2109233 = 1581925) B1581925
theorem B3166001 : Blo 1405522 3166001 := bstep (se 2 (by rfl) ⟨1187250, by rfl⟩ : syracuseStep 3166001 = 2374501) B2374501
theorem B2109251 : Blo 1405522 2109251 := bstep (se 1 (by rfl) ⟨1581938, by rfl⟩ : syracuseStep 2109251 = 3163877) B3163877
theorem B3166019 : Blo 1405522 3166019 := bstep (se 1 (by rfl) ⟨2374514, by rfl⟩ : syracuseStep 3166019 = 4749029) B4749029
theorem B4747085 : Blo 1405522 4747085 := bstep (se 3 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 4747085 = 1780157) B1780157
theorem B2109281 : Blo 1405522 2109281 := bstep (se 2 (by rfl) ⟨790980, by rfl⟩ : syracuseStep 2109281 = 1581961) B1581961
theorem B2109299 : Blo 1405522 2109299 := bstep (se 1 (by rfl) ⟨1581974, by rfl⟩ : syracuseStep 2109299 = 3163949) B3163949
theorem B4747139 : Blo 1405522 4747139 := bstep (se 1 (by rfl) ⟨3560354, by rfl⟩ : syracuseStep 4747139 = 7120709) B7120709
theorem B56323981 : Blo 1405522 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B2109329 : Blo 1405522 2109329 := bstep (se 2 (by rfl) ⟨790998, by rfl⟩ : syracuseStep 2109329 = 1581997) B1581997
theorem B2109347 : Blo 1405522 2109347 := bstep (se 1 (by rfl) ⟨1582010, by rfl⟩ : syracuseStep 2109347 = 3164021) B3164021
theorem B2109377 : Blo 1405522 2109377 := bstep (se 2 (by rfl) ⟨791016, by rfl⟩ : syracuseStep 2109377 = 1582033) B1582033
theorem B2109395 : Blo 1405522 2109395 := bstep (se 1 (by rfl) ⟨1582046, by rfl⟩ : syracuseStep 2109395 = 3164093) B3164093
theorem B13512689 : Blo 1405522 13512689 := bstep (se 2 (by rfl) ⟨5067258, by rfl⟩ : syracuseStep 13512689 = 10134517) B10134517
theorem B2109425 : Blo 1405522 2109425 := bstep (se 2 (by rfl) ⟨791034, by rfl⟩ : syracuseStep 2109425 = 1582069) B1582069
theorem B2109443 : Blo 1405522 2109443 := bstep (se 1 (by rfl) ⟨1582082, by rfl⟩ : syracuseStep 2109443 = 3164165) B3164165
theorem B2109473 : Blo 1405522 2109473 := bstep (se 2 (by rfl) ⟨791052, by rfl⟩ : syracuseStep 2109473 = 1582105) B1582105
theorem B3379249 : Blo 1405522 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B2109491 : Blo 1405522 2109491 := bstep (se 1 (by rfl) ⟨1582118, by rfl⟩ : syracuseStep 2109491 = 3164237) B3164237
theorem B2109521 : Blo 1405522 2109521 := bstep (se 2 (by rfl) ⟨791070, by rfl⟩ : syracuseStep 2109521 = 1582141) B1582141
theorem B3166289 : Blo 1405522 3166289 := bstep (se 2 (by rfl) ⟨1187358, by rfl⟩ : syracuseStep 3166289 = 2374717) B2374717
theorem B2109539 : Blo 1405522 2109539 := bstep (se 1 (by rfl) ⟨1582154, by rfl⟩ : syracuseStep 2109539 = 3164309) B3164309
theorem B3166307 : Blo 1405522 3166307 := bstep (se 1 (by rfl) ⟨2374730, by rfl⟩ : syracuseStep 3166307 = 4749461) B4749461
theorem B2003059 : Blo 1405522 2003059 := bstep (se 1 (by rfl) ⟨1502294, by rfl⟩ : syracuseStep 2003059 = 3004589) B3004589
theorem B2109569 : Blo 1405522 2109569 := bstep (se 2 (by rfl) ⟨791088, by rfl⟩ : syracuseStep 2109569 = 1582177) B1582177
theorem B4747409 : Blo 1405522 4747409 := bstep (se 2 (by rfl) ⟨1780278, by rfl⟩ : syracuseStep 4747409 = 3560557) B3560557
theorem B2109587 : Blo 1405522 2109587 := bstep (se 1 (by rfl) ⟨1582190, by rfl⟩ : syracuseStep 2109587 = 3164381) B3164381
theorem B2109617 : Blo 1405522 2109617 := bstep (se 2 (by rfl) ⟨791106, by rfl⟩ : syracuseStep 2109617 = 1582213) B1582213
theorem B2109635 : Blo 1405522 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B2535619 : Blo 1405522 2535619 := bstep (se 1 (by rfl) ⟨1901714, by rfl⟩ : syracuseStep 2535619 = 3803429) B3803429
theorem B2109665 : Blo 1405522 2109665 := bstep (se 2 (by rfl) ⟨791124, by rfl⟩ : syracuseStep 2109665 = 1582249) B1582249
theorem B2109683 : Blo 1405522 2109683 := bstep (se 1 (by rfl) ⟨1582262, by rfl⟩ : syracuseStep 2109683 = 3164525) B3164525
theorem B3559697 : Blo 1405522 3559697 := bstep (se 2 (by rfl) ⟨1334886, by rfl⟩ : syracuseStep 3559697 = 2669773) B2669773
theorem B2109713 : Blo 1405522 2109713 := bstep (se 2 (by rfl) ⟨791142, by rfl⟩ : syracuseStep 2109713 = 1582285) B1582285
theorem B2109731 : Blo 1405522 2109731 := bstep (se 1 (by rfl) ⟨1582298, by rfl⟩ : syracuseStep 2109731 = 3164597) B3164597
theorem B2371889 : Blo 1405522 2371889 := bstep (se 2 (by rfl) ⟨889458, by rfl⟩ : syracuseStep 2371889 = 1778917) B1778917
theorem B2109761 : Blo 1405522 2109761 := bstep (se 2 (by rfl) ⟨791160, by rfl⟩ : syracuseStep 2109761 = 1582321) B1582321
theorem B3559747 : Blo 1405522 3559747 := bstep (se 1 (by rfl) ⟨2669810, by rfl⟩ : syracuseStep 3559747 = 5339621) B5339621
theorem B2109779 : Blo 1405522 2109779 := bstep (se 1 (by rfl) ⟨1582334, by rfl⟩ : syracuseStep 2109779 = 3164669) B3164669
theorem B2109809 : Blo 1405522 2109809 := bstep (se 2 (by rfl) ⟨791178, by rfl⟩ : syracuseStep 2109809 = 1582357) B1582357
theorem B3166577 : Blo 1405522 3166577 := bstep (se 2 (by rfl) ⟨1187466, by rfl⟩ : syracuseStep 3166577 = 2374933) B2374933
theorem B2109827 : Blo 1405522 2109827 := bstep (se 1 (by rfl) ⟨1582370, by rfl⟩ : syracuseStep 2109827 = 3164741) B3164741
theorem B3166595 : Blo 1405522 3166595 := bstep (se 1 (by rfl) ⟨2374946, by rfl⟩ : syracuseStep 3166595 = 4749893) B4749893
theorem B2109857 : Blo 1405522 2109857 := bstep (se 2 (by rfl) ⟨791196, by rfl⟩ : syracuseStep 2109857 = 1582393) B1582393
theorem B2372017 : Blo 1405522 2372017 := bstep (se 2 (by rfl) ⟨889506, by rfl⟩ : syracuseStep 2372017 = 1779013) B1779013
theorem B2109875 : Blo 1405522 2109875 := bstep (se 1 (by rfl) ⟨1582406, by rfl⟩ : syracuseStep 2109875 = 3164813) B3164813
theorem B2003395 : Blo 1405522 2003395 := bstep (se 1 (by rfl) ⟨1502546, by rfl⟩ : syracuseStep 2003395 = 3005093) B3005093
theorem B3559889 : Blo 1405522 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B2109905 : Blo 1405522 2109905 := bstep (se 2 (by rfl) ⟨791214, by rfl⟩ : syracuseStep 2109905 = 1582429) B1582429
theorem B2372051 : Blo 1405522 2372051 := bstep (se 1 (by rfl) ⟨1779038, by rfl⟩ : syracuseStep 2372051 = 3558077) B3558077
theorem B2109923 : Blo 1405522 2109923 := bstep (se 1 (by rfl) ⟨1582442, by rfl⟩ : syracuseStep 2109923 = 3164885) B3164885
theorem B6009329 : Blo 1405522 6009329 := bstep (se 2 (by rfl) ⟨2253498, by rfl⟩ : syracuseStep 6009329 = 4506997) B4506997
theorem B2109953 : Blo 1405522 2109953 := bstep (se 2 (by rfl) ⟨791232, by rfl⟩ : syracuseStep 2109953 = 1582465) B1582465
theorem B2109971 : Blo 1405522 2109971 := bstep (se 1 (by rfl) ⟨1582478, by rfl⟩ : syracuseStep 2109971 = 3164957) B3164957
theorem B2110001 : Blo 1405522 2110001 := bstep (se 2 (by rfl) ⟨791250, by rfl⟩ : syracuseStep 2110001 = 1582501) B1582501
theorem B2110019 : Blo 1405522 2110019 := bstep (se 1 (by rfl) ⟨1582514, by rfl⟩ : syracuseStep 2110019 = 3165029) B3165029
theorem B5337677 : Blo 1405522 5337677 := bstep (se 3 (by rfl) ⟨1000814, by rfl⟩ : syracuseStep 5337677 = 2001629) B2001629
theorem B1405523 : Blo 1405522 1405523 := bstep (se 1 (by rfl) ⟨1054142, by rfl⟩ : syracuseStep 1405523 = 2108285) B2108285
theorem B2372179 : Blo 1405522 2372179 := bstep (se 1 (by rfl) ⟨1779134, by rfl⟩ : syracuseStep 2372179 = 3558269) B3558269
theorem B2110049 : Blo 1405522 2110049 := bstep (se 2 (by rfl) ⟨791268, by rfl⟩ : syracuseStep 2110049 = 1582537) B1582537
theorem B1405539 : Blo 1405522 1405539 := bstep (se 1 (by rfl) ⟨1054154, by rfl⟩ : syracuseStep 1405539 = 2108309) B2108309
theorem B1405555 : Blo 1405522 1405555 := bstep (se 1 (by rfl) ⟨1054166, by rfl⟩ : syracuseStep 1405555 = 2108333) B2108333
theorem B2110067 : Blo 1405522 2110067 := bstep (se 1 (by rfl) ⟨1582550, by rfl⟩ : syracuseStep 2110067 = 3165101) B3165101
theorem B1405571 : Blo 1405522 1405571 := bstep (se 1 (by rfl) ⟨1054178, by rfl⟩ : syracuseStep 1405571 = 2108357) B2108357
theorem B2110097 : Blo 1405522 2110097 := bstep (se 2 (by rfl) ⟨791286, by rfl⟩ : syracuseStep 2110097 = 1582573) B1582573
theorem B3166865 : Blo 1405522 3166865 := bstep (se 2 (by rfl) ⟨1187574, by rfl⟩ : syracuseStep 3166865 = 2375149) B2375149
theorem B1405587 : Blo 1405522 1405587 := bstep (se 1 (by rfl) ⟨1054190, by rfl⟩ : syracuseStep 1405587 = 2108381) B2108381
theorem B1405603 : Blo 1405522 1405603 := bstep (se 1 (by rfl) ⟨1054202, by rfl⟩ : syracuseStep 1405603 = 2108405) B2108405
theorem B2110115 : Blo 1405522 2110115 := bstep (se 1 (by rfl) ⟨1582586, by rfl⟩ : syracuseStep 2110115 = 3165173) B3165173
theorem B3166883 : Blo 1405522 3166883 := bstep (se 1 (by rfl) ⟨2375162, by rfl⟩ : syracuseStep 3166883 = 4750325) B4750325
theorem B4747949 : Blo 1405522 4747949 := bstep (se 3 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 4747949 = 1780481) B1780481
theorem B1405619 : Blo 1405522 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B2110145 : Blo 1405522 2110145 := bstep (se 2 (by rfl) ⟨791304, by rfl⟩ : syracuseStep 2110145 = 1582609) B1582609
theorem B1405635 : Blo 1405522 1405635 := bstep (se 1 (by rfl) ⟨1054226, by rfl⟩ : syracuseStep 1405635 = 2108453) B2108453
theorem B1405651 : Blo 1405522 1405651 := bstep (se 1 (by rfl) ⟨1054238, by rfl⟩ : syracuseStep 1405651 = 2108477) B2108477
theorem B2110163 : Blo 1405522 2110163 := bstep (se 1 (by rfl) ⟨1582622, by rfl⟩ : syracuseStep 2110163 = 3165245) B3165245
theorem B2372321 : Blo 1405522 2372321 := bstep (se 2 (by rfl) ⟨889620, by rfl⟩ : syracuseStep 2372321 = 1779241) B1779241
theorem B1405667 : Blo 1405522 1405667 := bstep (se 1 (by rfl) ⟨1054250, by rfl⟩ : syracuseStep 1405667 = 2108501) B2108501
theorem B9007843 : Blo 1405522 9007843 := bstep (se 1 (by rfl) ⟨6755882, by rfl⟩ : syracuseStep 9007843 = 13511765) B13511765
theorem B4748003 : Blo 1405522 4748003 := bstep (se 1 (by rfl) ⟨3561002, by rfl⟩ : syracuseStep 4748003 = 7122005) B7122005
theorem B2110193 : Blo 1405522 2110193 := bstep (se 2 (by rfl) ⟨791322, by rfl⟩ : syracuseStep 2110193 = 1582645) B1582645
theorem B1405683 : Blo 1405522 1405683 := bstep (se 1 (by rfl) ⟨1054262, by rfl⟩ : syracuseStep 1405683 = 2108525) B2108525
theorem B1405699 : Blo 1405522 1405699 := bstep (se 1 (by rfl) ⟨1054274, by rfl⟩ : syracuseStep 1405699 = 2108549) B2108549
theorem B2110211 : Blo 1405522 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B1405715 : Blo 1405522 1405715 := bstep (se 1 (by rfl) ⟨1054286, by rfl⟩ : syracuseStep 1405715 = 2108573) B2108573
theorem B2110241 : Blo 1405522 2110241 := bstep (se 2 (by rfl) ⟨791340, by rfl⟩ : syracuseStep 2110241 = 1582681) B1582681
theorem B1405731 : Blo 1405522 1405731 := bstep (se 1 (by rfl) ⟨1054298, by rfl⟩ : syracuseStep 1405731 = 2108597) B2108597
theorem B1405747 : Blo 1405522 1405747 := bstep (se 1 (by rfl) ⟨1054310, by rfl⟩ : syracuseStep 1405747 = 2108621) B2108621
theorem B2110259 : Blo 1405522 2110259 := bstep (se 1 (by rfl) ⟨1582694, by rfl⟩ : syracuseStep 2110259 = 3165389) B3165389
theorem B1405763 : Blo 1405522 1405763 := bstep (se 1 (by rfl) ⟨1054322, by rfl⟩ : syracuseStep 1405763 = 2108645) B2108645
theorem B2110289 : Blo 1405522 2110289 := bstep (se 2 (by rfl) ⟨791358, by rfl⟩ : syracuseStep 2110289 = 1582717) B1582717
theorem B1405779 : Blo 1405522 1405779 := bstep (se 1 (by rfl) ⟨1054334, by rfl⟩ : syracuseStep 1405779 = 2108669) B2108669
theorem B2372449 : Blo 1405522 2372449 := bstep (se 2 (by rfl) ⟨889668, by rfl⟩ : syracuseStep 2372449 = 1779337) B1779337
theorem B1405795 : Blo 1405522 1405795 := bstep (se 1 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 1405795 = 2108693) B2108693
theorem B2110307 : Blo 1405522 2110307 := bstep (se 1 (by rfl) ⟨1582730, by rfl⟩ : syracuseStep 2110307 = 3165461) B3165461
theorem B1405811 : Blo 1405522 1405811 := bstep (se 1 (by rfl) ⟨1054358, by rfl⟩ : syracuseStep 1405811 = 2108717) B2108717
theorem B2110337 : Blo 1405522 2110337 := bstep (se 2 (by rfl) ⟨791376, by rfl⟩ : syracuseStep 2110337 = 1582753) B1582753
theorem B1405827 : Blo 1405522 1405827 := bstep (se 1 (by rfl) ⟨1054370, by rfl⟩ : syracuseStep 1405827 = 2108741) B2108741
theorem B2372483 : Blo 1405522 2372483 := bstep (se 1 (by rfl) ⟨1779362, by rfl⟩ : syracuseStep 2372483 = 3558725) B3558725
theorem B1405843 : Blo 1405522 1405843 := bstep (se 1 (by rfl) ⟨1054382, by rfl⟩ : syracuseStep 1405843 = 2108765) B2108765
theorem B2110355 : Blo 1405522 2110355 := bstep (se 1 (by rfl) ⟨1582766, by rfl⟩ : syracuseStep 2110355 = 3165533) B3165533
theorem B1405859 : Blo 1405522 1405859 := bstep (se 1 (by rfl) ⟨1054394, by rfl⟩ : syracuseStep 1405859 = 2108789) B2108789
theorem B2110385 : Blo 1405522 2110385 := bstep (se 2 (by rfl) ⟨791394, by rfl⟩ : syracuseStep 2110385 = 1582789) B1582789
theorem B1405875 : Blo 1405522 1405875 := bstep (se 1 (by rfl) ⟨1054406, by rfl⟩ : syracuseStep 1405875 = 2108813) B2108813
theorem B1405891 : Blo 1405522 1405891 := bstep (se 1 (by rfl) ⟨1054418, by rfl⟩ : syracuseStep 1405891 = 2108837) B2108837
theorem B2110403 : Blo 1405522 2110403 := bstep (se 1 (by rfl) ⟨1582802, by rfl⟩ : syracuseStep 2110403 = 3165605) B3165605
theorem B1405907 : Blo 1405522 1405907 := bstep (se 1 (by rfl) ⟨1054430, by rfl⟩ : syracuseStep 1405907 = 2108861) B2108861
theorem B2110433 : Blo 1405522 2110433 := bstep (se 2 (by rfl) ⟨791412, by rfl⟩ : syracuseStep 2110433 = 1582825) B1582825
theorem B1405923 : Blo 1405522 1405923 := bstep (se 1 (by rfl) ⟨1054442, by rfl⟩ : syracuseStep 1405923 = 2108885) B2108885
theorem B4748273 : Blo 1405522 4748273 := bstep (se 2 (by rfl) ⟨1780602, by rfl⟩ : syracuseStep 4748273 = 3561205) B3561205
theorem B1405939 : Blo 1405522 1405939 := bstep (se 1 (by rfl) ⟨1054454, by rfl⟩ : syracuseStep 1405939 = 2108909) B2108909
theorem B2110451 : Blo 1405522 2110451 := bstep (se 1 (by rfl) ⟨1582838, by rfl⟩ : syracuseStep 2110451 = 3165677) B3165677
theorem B2003953 : Blo 1405522 2003953 := bstep (se 2 (by rfl) ⟨751482, by rfl⟩ : syracuseStep 2003953 = 1502965) B1502965
theorem B1405955 : Blo 1405522 1405955 := bstep (se 1 (by rfl) ⟨1054466, by rfl⟩ : syracuseStep 1405955 = 2108933) B2108933
theorem B2372611 : Blo 1405522 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B7918597 : Blo 1405522 7918597 := bstep (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) B1484737
theorem B2110481 : Blo 1405522 2110481 := bstep (se 2 (by rfl) ⟨791430, by rfl⟩ : syracuseStep 2110481 = 1582861) B1582861
theorem B1405971 : Blo 1405522 1405971 := bstep (se 1 (by rfl) ⟨1054478, by rfl⟩ : syracuseStep 1405971 = 2108957) B2108957
theorem B2003987 : Blo 1405522 2003987 := bstep (se 1 (by rfl) ⟨1502990, by rfl⟩ : syracuseStep 2003987 = 3005981) B3005981
theorem B1405987 : Blo 1405522 1405987 := bstep (se 1 (by rfl) ⟨1054490, by rfl⟩ : syracuseStep 1405987 = 2108981) B2108981
theorem B2110499 : Blo 1405522 2110499 := bstep (se 1 (by rfl) ⟨1582874, by rfl⟩ : syracuseStep 2110499 = 3165749) B3165749
theorem B1406003 : Blo 1405522 1406003 := bstep (se 1 (by rfl) ⟨1054502, by rfl⟩ : syracuseStep 1406003 = 2109005) B2109005
theorem B2110529 : Blo 1405522 2110529 := bstep (se 2 (by rfl) ⟨791448, by rfl⟩ : syracuseStep 2110529 = 1582897) B1582897
theorem B1406019 : Blo 1405522 1406019 := bstep (se 1 (by rfl) ⟨1054514, by rfl⟩ : syracuseStep 1406019 = 2109029) B2109029
theorem B1406035 : Blo 1405522 1406035 := bstep (se 1 (by rfl) ⟨1054526, by rfl⟩ : syracuseStep 1406035 = 2109053) B2109053
theorem B2110547 : Blo 1405522 2110547 := bstep (se 1 (by rfl) ⟨1582910, by rfl⟩ : syracuseStep 2110547 = 3165821) B3165821
theorem B7599203 : Blo 1405522 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B1406051 : Blo 1405522 1406051 := bstep (se 1 (by rfl) ⟨1054538, by rfl⟩ : syracuseStep 1406051 = 2109077) B2109077
theorem B4002929 : Blo 1405522 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B1406067 : Blo 1405522 1406067 := bstep (se 1 (by rfl) ⟨1054550, by rfl⟩ : syracuseStep 1406067 = 2109101) B2109101
theorem B2110577 : Blo 1405522 2110577 := bstep (se 2 (by rfl) ⟨791466, by rfl⟩ : syracuseStep 2110577 = 1582933) B1582933
theorem B9016433 : Blo 1405522 9016433 := bstep (se 2 (by rfl) ⟨3381162, by rfl⟩ : syracuseStep 9016433 = 6762325) B6762325
theorem B1406083 : Blo 1405522 1406083 := bstep (se 1 (by rfl) ⟨1054562, by rfl⟩ : syracuseStep 1406083 = 2109125) B2109125
theorem B2110595 : Blo 1405522 2110595 := bstep (se 1 (by rfl) ⟨1582946, by rfl⟩ : syracuseStep 2110595 = 3165893) B3165893
theorem B6009997 : Blo 1405522 6009997 := bstep (se 3 (by rfl) ⟨1126874, by rfl⟩ : syracuseStep 6009997 = 2253749) B2253749
theorem B2372753 : Blo 1405522 2372753 := bstep (se 2 (by rfl) ⟨889782, by rfl⟩ : syracuseStep 2372753 = 1779565) B1779565
theorem B1406099 : Blo 1405522 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B2110625 : Blo 1405522 2110625 := bstep (se 2 (by rfl) ⟨791484, by rfl⟩ : syracuseStep 2110625 = 1582969) B1582969
theorem B1406115 : Blo 1405522 1406115 := bstep (se 1 (by rfl) ⟨1054586, by rfl⟩ : syracuseStep 1406115 = 2109173) B2109173
theorem B5067953 : Blo 1405522 5067953 := bstep (se 2 (by rfl) ⟨1900482, by rfl⟩ : syracuseStep 5067953 = 3800965) B3800965
theorem B1406131 : Blo 1405522 1406131 := bstep (se 1 (by rfl) ⟨1054598, by rfl⟩ : syracuseStep 1406131 = 2109197) B2109197
theorem B2110643 : Blo 1405522 2110643 := bstep (se 1 (by rfl) ⟨1582982, by rfl⟩ : syracuseStep 2110643 = 3165965) B3165965
theorem B1406147 : Blo 1405522 1406147 := bstep (se 1 (by rfl) ⟨1054610, by rfl⟩ : syracuseStep 1406147 = 2109221) B2109221
theorem B2438353 : Blo 1405522 2438353 := bstep (se 2 (by rfl) ⟨914382, by rfl⟩ : syracuseStep 2438353 = 1828765) B1828765
theorem B2110673 : Blo 1405522 2110673 := bstep (se 2 (by rfl) ⟨791502, by rfl⟩ : syracuseStep 2110673 = 1583005) B1583005
theorem B1406163 : Blo 1405522 1406163 := bstep (se 1 (by rfl) ⟨1054622, by rfl⟩ : syracuseStep 1406163 = 2109245) B2109245
theorem B66720995 : Blo 1405522 66720995 := bstep (se 1 (by rfl) ⟨50040746, by rfl⟩ : syracuseStep 66720995 = 100081493) B100081493
theorem B1406179 : Blo 1405522 1406179 := bstep (se 1 (by rfl) ⟨1054634, by rfl⟩ : syracuseStep 1406179 = 2109269) B2109269
theorem B2110691 : Blo 1405522 2110691 := bstep (se 1 (by rfl) ⟨1583018, by rfl⟩ : syracuseStep 2110691 = 3166037) B3166037
theorem B1406195 : Blo 1405522 1406195 := bstep (se 1 (by rfl) ⟨1054646, by rfl⟩ : syracuseStep 1406195 = 2109293) B2109293
theorem B2168051 : Blo 1405522 2168051 := bstep (se 1 (by rfl) ⟨1626038, by rfl⟩ : syracuseStep 2168051 = 3252077) B3252077
theorem B1406211 : Blo 1405522 1406211 := bstep (se 1 (by rfl) ⟨1054658, by rfl⟩ : syracuseStep 1406211 = 2109317) B2109317
theorem B2110721 : Blo 1405522 2110721 := bstep (se 2 (by rfl) ⟨791520, by rfl⟩ : syracuseStep 2110721 = 1583041) B1583041
theorem B2372881 : Blo 1405522 2372881 := bstep (se 2 (by rfl) ⟨889830, by rfl⟩ : syracuseStep 2372881 = 1779661) B1779661
theorem B1406227 : Blo 1405522 1406227 := bstep (se 1 (by rfl) ⟨1054670, by rfl⟩ : syracuseStep 1406227 = 2109341) B2109341
theorem B2110739 : Blo 1405522 2110739 := bstep (se 1 (by rfl) ⟨1583054, by rfl⟩ : syracuseStep 2110739 = 3166109) B3166109
theorem B1406243 : Blo 1405522 1406243 := bstep (se 1 (by rfl) ⟨1054682, by rfl⟩ : syracuseStep 1406243 = 2109365) B2109365
theorem B4003121 : Blo 1405522 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B2110769 : Blo 1405522 2110769 := bstep (se 2 (by rfl) ⟨791538, by rfl⟩ : syracuseStep 2110769 = 1583077) B1583077
theorem B2372915 : Blo 1405522 2372915 := bstep (se 1 (by rfl) ⟨1779686, by rfl⟩ : syracuseStep 2372915 = 3559373) B3559373
theorem B1406259 : Blo 1405522 1406259 := bstep (se 1 (by rfl) ⟨1054694, by rfl⟩ : syracuseStep 1406259 = 2109389) B2109389
theorem B7124273 : Blo 1405522 7124273 := bstep (se 2 (by rfl) ⟨2671602, by rfl⟩ : syracuseStep 7124273 = 5343205) B5343205
theorem B1406275 : Blo 1405522 1406275 := bstep (se 1 (by rfl) ⟨1054706, by rfl⟩ : syracuseStep 1406275 = 2109413) B2109413
theorem B2110787 : Blo 1405522 2110787 := bstep (se 1 (by rfl) ⟨1583090, by rfl⟩ : syracuseStep 2110787 = 3166181) B3166181
theorem B2028883 : Blo 1405522 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B1406291 : Blo 1405522 1406291 := bstep (se 1 (by rfl) ⟨1054718, by rfl⟩ : syracuseStep 1406291 = 2109437) B2109437
theorem B2110817 : Blo 1405522 2110817 := bstep (se 2 (by rfl) ⟨791556, by rfl⟩ : syracuseStep 2110817 = 1583113) B1583113
theorem B1406307 : Blo 1405522 1406307 := bstep (se 1 (by rfl) ⟨1054730, by rfl⟩ : syracuseStep 1406307 = 2109461) B2109461
theorem B27415921 : Blo 1405522 27415921 := bstep (se 2 (by rfl) ⟨10280970, by rfl⟩ : syracuseStep 27415921 = 20561941) B20561941
theorem B1602931 : Blo 1405522 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1406323 : Blo 1405522 1406323 := bstep (se 1 (by rfl) ⟨1054742, by rfl⟩ : syracuseStep 1406323 = 2109485) B2109485
theorem B2110835 : Blo 1405522 2110835 := bstep (se 1 (by rfl) ⟨1583126, by rfl⟩ : syracuseStep 2110835 = 3166253) B3166253
theorem B1406339 : Blo 1405522 1406339 := bstep (se 1 (by rfl) ⟨1054754, by rfl⟩ : syracuseStep 1406339 = 2109509) B2109509
theorem B7116173 : Blo 1405522 7116173 := bstep (se 3 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 7116173 = 2668565) B2668565
theorem B2110865 : Blo 1405522 2110865 := bstep (se 2 (by rfl) ⟨791574, by rfl⟩ : syracuseStep 2110865 = 1583149) B1583149
theorem B1406355 : Blo 1405522 1406355 := bstep (se 1 (by rfl) ⟨1054766, by rfl⟩ : syracuseStep 1406355 = 2109533) B2109533
theorem B5698979 : Blo 1405522 5698979 := bstep (se 1 (by rfl) ⟨4274234, by rfl⟩ : syracuseStep 5698979 = 8548469) B8548469
theorem B1406371 : Blo 1405522 1406371 := bstep (se 1 (by rfl) ⟨1054778, by rfl⟩ : syracuseStep 1406371 = 2109557) B2109557
theorem B2110883 : Blo 1405522 2110883 := bstep (se 1 (by rfl) ⟨1583162, by rfl⟩ : syracuseStep 2110883 = 3166325) B3166325
theorem B3560881 : Blo 1405522 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B2373043 : Blo 1405522 2373043 := bstep (se 1 (by rfl) ⟨1779782, by rfl⟩ : syracuseStep 2373043 = 3559565) B3559565
theorem B1406387 : Blo 1405522 1406387 := bstep (se 1 (by rfl) ⟨1054790, by rfl⟩ : syracuseStep 1406387 = 2109581) B2109581
theorem B2110913 : Blo 1405522 2110913 := bstep (se 2 (by rfl) ⟨791592, by rfl⟩ : syracuseStep 2110913 = 1583185) B1583185
theorem B1406403 : Blo 1405522 1406403 := bstep (se 1 (by rfl) ⟨1054802, by rfl⟩ : syracuseStep 1406403 = 2109605) B2109605
theorem B1406419 : Blo 1405522 1406419 := bstep (se 1 (by rfl) ⟨1054814, by rfl⟩ : syracuseStep 1406419 = 2109629) B2109629
theorem B2110931 : Blo 1405522 2110931 := bstep (se 1 (by rfl) ⟨1583198, by rfl⟩ : syracuseStep 2110931 = 3166397) B3166397
theorem B1406435 : Blo 1405522 1406435 := bstep (se 1 (by rfl) ⟨1054826, by rfl⟩ : syracuseStep 1406435 = 2109653) B2109653
theorem B2110961 : Blo 1405522 2110961 := bstep (se 2 (by rfl) ⟨791610, by rfl⟩ : syracuseStep 2110961 = 1583221) B1583221
theorem B1406451 : Blo 1405522 1406451 := bstep (se 1 (by rfl) ⟨1054838, by rfl⟩ : syracuseStep 1406451 = 2109677) B2109677
theorem B1406467 : Blo 1405522 1406467 := bstep (se 1 (by rfl) ⟨1054850, by rfl⟩ : syracuseStep 1406467 = 2109701) B2109701
theorem B2110979 : Blo 1405522 2110979 := bstep (se 1 (by rfl) ⟨1583234, by rfl⟩ : syracuseStep 2110979 = 3166469) B3166469
theorem B4748813 : Blo 1405522 4748813 := bstep (se 3 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 4748813 = 1780805) B1780805
theorem B1406483 : Blo 1405522 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B1406499 : Blo 1405522 1406499 := bstep (se 1 (by rfl) ⟨1054874, by rfl⟩ : syracuseStep 1406499 = 2109749) B2109749
theorem B2111009 : Blo 1405522 2111009 := bstep (se 2 (by rfl) ⟨791628, by rfl⟩ : syracuseStep 2111009 = 1583257) B1583257
theorem B1406515 : Blo 1405522 1406515 := bstep (se 1 (by rfl) ⟨1054886, by rfl⟩ : syracuseStep 1406515 = 2109773) B2109773
theorem B2111027 : Blo 1405522 2111027 := bstep (se 1 (by rfl) ⟨1583270, by rfl⟩ : syracuseStep 2111027 = 3166541) B3166541
theorem B2373185 : Blo 1405522 2373185 := bstep (se 2 (by rfl) ⟨889944, by rfl⟩ : syracuseStep 2373185 = 1779889) B1779889
theorem B1406531 : Blo 1405522 1406531 := bstep (se 1 (by rfl) ⟨1054898, by rfl⟩ : syracuseStep 1406531 = 2109797) B2109797
theorem B4748867 : Blo 1405522 4748867 := bstep (se 1 (by rfl) ⟨3561650, by rfl⟩ : syracuseStep 4748867 = 7123301) B7123301
theorem B2111057 : Blo 1405522 2111057 := bstep (se 2 (by rfl) ⟨791646, by rfl⟩ : syracuseStep 2111057 = 1583293) B1583293
theorem B1406547 : Blo 1405522 1406547 := bstep (se 1 (by rfl) ⟨1054910, by rfl⟩ : syracuseStep 1406547 = 2109821) B2109821
theorem B1406563 : Blo 1405522 1406563 := bstep (se 1 (by rfl) ⟨1054922, by rfl⟩ : syracuseStep 1406563 = 2109845) B2109845
theorem B2111075 : Blo 1405522 2111075 := bstep (se 1 (by rfl) ⟨1583306, by rfl⟩ : syracuseStep 2111075 = 3166613) B3166613
theorem B1406579 : Blo 1405522 1406579 := bstep (se 1 (by rfl) ⟨1054934, by rfl⟩ : syracuseStep 1406579 = 2109869) B2109869
theorem B2111105 : Blo 1405522 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1406595 : Blo 1405522 1406595 := bstep (se 1 (by rfl) ⟨1054946, by rfl⟩ : syracuseStep 1406595 = 2109893) B2109893
theorem B6420109 : Blo 1405522 6420109 := bstep (se 3 (by rfl) ⟨1203770, by rfl⟩ : syracuseStep 6420109 = 2407541) B2407541
theorem B1406611 : Blo 1405522 1406611 := bstep (se 1 (by rfl) ⟨1054958, by rfl⟩ : syracuseStep 1406611 = 2109917) B2109917
theorem B2111123 : Blo 1405522 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B3004067 : Blo 1405522 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B1406627 : Blo 1405522 1406627 := bstep (se 1 (by rfl) ⟨1054970, by rfl⟩ : syracuseStep 1406627 = 2109941) B2109941
theorem B1406643 : Blo 1405522 1406643 := bstep (se 1 (by rfl) ⟨1054982, by rfl⟩ : syracuseStep 1406643 = 2109965) B2109965
theorem B2111153 : Blo 1405522 2111153 := bstep (se 2 (by rfl) ⟨791682, by rfl⟩ : syracuseStep 2111153 = 1583365) B1583365
theorem B2373313 : Blo 1405522 2373313 := bstep (se 2 (by rfl) ⟨889992, by rfl⟩ : syracuseStep 2373313 = 1779985) B1779985
theorem B1406659 : Blo 1405522 1406659 := bstep (se 1 (by rfl) ⟨1054994, by rfl⟩ : syracuseStep 1406659 = 2109989) B2109989
theorem B3561155 : Blo 1405522 3561155 := bstep (se 1 (by rfl) ⟨2670866, by rfl⟩ : syracuseStep 3561155 = 5341733) B5341733
theorem B2111171 : Blo 1405522 2111171 := bstep (se 1 (by rfl) ⟨1583378, by rfl⟩ : syracuseStep 2111171 = 3166757) B3166757
theorem B1406675 : Blo 1405522 1406675 := bstep (se 1 (by rfl) ⟨1055006, by rfl⟩ : syracuseStep 1406675 = 2110013) B2110013
theorem B2111201 : Blo 1405522 2111201 := bstep (se 2 (by rfl) ⟨791700, by rfl⟩ : syracuseStep 2111201 = 1583401) B1583401
theorem B2373347 : Blo 1405522 2373347 := bstep (se 1 (by rfl) ⟨1780010, by rfl⟩ : syracuseStep 2373347 = 3560021) B3560021
theorem B1406691 : Blo 1405522 1406691 := bstep (se 1 (by rfl) ⟨1055018, by rfl⟩ : syracuseStep 1406691 = 2110037) B2110037
theorem B6010595 : Blo 1405522 6010595 := bstep (se 1 (by rfl) ⟨4507946, by rfl⟩ : syracuseStep 6010595 = 9015893) B9015893
theorem B2029297 : Blo 1405522 2029297 := bstep (se 2 (by rfl) ⟨760986, by rfl⟩ : syracuseStep 2029297 = 1521973) B1521973
theorem B1406707 : Blo 1405522 1406707 := bstep (se 1 (by rfl) ⟨1055030, by rfl⟩ : syracuseStep 1406707 = 2110061) B2110061
theorem B2111219 : Blo 1405522 2111219 := bstep (se 1 (by rfl) ⟨1583414, by rfl⟩ : syracuseStep 2111219 = 3166829) B3166829
theorem B1406723 : Blo 1405522 1406723 := bstep (se 1 (by rfl) ⟨1055042, by rfl⟩ : syracuseStep 1406723 = 2110085) B2110085
theorem B2111249 : Blo 1405522 2111249 := bstep (se 2 (by rfl) ⟨791718, by rfl⟩ : syracuseStep 2111249 = 1583437) B1583437
theorem B1406739 : Blo 1405522 1406739 := bstep (se 1 (by rfl) ⟨1055054, by rfl⟩ : syracuseStep 1406739 = 2110109) B2110109
theorem B1406755 : Blo 1405522 1406755 := bstep (se 1 (by rfl) ⟨1055066, by rfl⟩ : syracuseStep 1406755 = 2110133) B2110133
theorem B2111267 : Blo 1405522 2111267 := bstep (se 1 (by rfl) ⟨1583450, by rfl⟩ : syracuseStep 2111267 = 3166901) B3166901
theorem B1406771 : Blo 1405522 1406771 := bstep (se 1 (by rfl) ⟨1055078, by rfl⟩ : syracuseStep 1406771 = 2110157) B2110157
theorem B1406787 : Blo 1405522 1406787 := bstep (se 1 (by rfl) ⟨1055090, by rfl⟩ : syracuseStep 1406787 = 2110181) B2110181
theorem B4749137 : Blo 1405522 4749137 := bstep (se 2 (by rfl) ⟨1780926, by rfl⟩ : syracuseStep 4749137 = 3561853) B3561853
theorem B1406803 : Blo 1405522 1406803 := bstep (se 1 (by rfl) ⟨1055102, by rfl⟩ : syracuseStep 1406803 = 2110205) B2110205
theorem B2373475 : Blo 1405522 2373475 := bstep (se 1 (by rfl) ⟨1780106, by rfl⟩ : syracuseStep 2373475 = 3560213) B3560213
theorem B1406819 : Blo 1405522 1406819 := bstep (se 1 (by rfl) ⟨1055114, by rfl⟩ : syracuseStep 1406819 = 2110229) B2110229
theorem B1406835 : Blo 1405522 1406835 := bstep (se 1 (by rfl) ⟨1055126, by rfl⟩ : syracuseStep 1406835 = 2110253) B2110253
theorem B1406851 : Blo 1405522 1406851 := bstep (se 1 (by rfl) ⟨1055138, by rfl⟩ : syracuseStep 1406851 = 2110277) B2110277
theorem B3561347 : Blo 1405522 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B1406867 : Blo 1405522 1406867 := bstep (se 1 (by rfl) ⟨1055150, by rfl⟩ : syracuseStep 1406867 = 2110301) B2110301
theorem B1406883 : Blo 1405522 1406883 := bstep (se 1 (by rfl) ⟨1055162, by rfl⟩ : syracuseStep 1406883 = 2110325) B2110325
theorem B9009073 : Blo 1405522 9009073 := bstep (se 2 (by rfl) ⟨3378402, by rfl⟩ : syracuseStep 9009073 = 6756805) B6756805
theorem B1406899 : Blo 1405522 1406899 := bstep (se 1 (by rfl) ⟨1055174, by rfl⟩ : syracuseStep 1406899 = 2110349) B2110349
theorem B1406915 : Blo 1405522 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B1406931 : Blo 1405522 1406931 := bstep (se 1 (by rfl) ⟨1055198, by rfl⟩ : syracuseStep 1406931 = 2110397) B2110397
theorem B1406947 : Blo 1405522 1406947 := bstep (se 1 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 1406947 = 2110421) B2110421
theorem B2373617 : Blo 1405522 2373617 := bstep (se 2 (by rfl) ⟨890106, by rfl⟩ : syracuseStep 2373617 = 1780213) B1780213
theorem B1406963 : Blo 1405522 1406963 := bstep (se 1 (by rfl) ⟨1055222, by rfl⟩ : syracuseStep 1406963 = 2110445) B2110445
theorem B1406979 : Blo 1405522 1406979 := bstep (se 1 (by rfl) ⟨1055234, by rfl⟩ : syracuseStep 1406979 = 2110469) B2110469
theorem B1406995 : Blo 1405522 1406995 := bstep (se 1 (by rfl) ⟨1055246, by rfl⟩ : syracuseStep 1406995 = 2110493) B2110493
theorem B1407011 : Blo 1405522 1407011 := bstep (se 1 (by rfl) ⟨1055258, by rfl⟩ : syracuseStep 1407011 = 2110517) B2110517
theorem B1407027 : Blo 1405522 1407027 := bstep (se 1 (by rfl) ⟨1055270, by rfl⟩ : syracuseStep 1407027 = 2110541) B2110541
theorem B1407043 : Blo 1405522 1407043 := bstep (se 1 (by rfl) ⟨1055282, by rfl⟩ : syracuseStep 1407043 = 2110565) B2110565
theorem B1407059 : Blo 1405522 1407059 := bstep (se 1 (by rfl) ⟨1055294, by rfl⟩ : syracuseStep 1407059 = 2110589) B2110589
theorem B1407075 : Blo 1405522 1407075 := bstep (se 1 (by rfl) ⟨1055306, by rfl⟩ : syracuseStep 1407075 = 2110613) B2110613
theorem B2373745 : Blo 1405522 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B1407091 : Blo 1405522 1407091 := bstep (se 1 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 1407091 = 2110637) B2110637
theorem B1407107 : Blo 1405522 1407107 := bstep (se 1 (by rfl) ⟨1055330, by rfl⟩ : syracuseStep 1407107 = 2110661) B2110661
theorem B2373779 : Blo 1405522 2373779 := bstep (se 1 (by rfl) ⟨1780334, by rfl⟩ : syracuseStep 2373779 = 3560669) B3560669
theorem B1407123 : Blo 1405522 1407123 := bstep (se 1 (by rfl) ⟨1055342, by rfl⟩ : syracuseStep 1407123 = 2110685) B2110685
theorem B1407139 : Blo 1405522 1407139 := bstep (se 1 (by rfl) ⟨1055354, by rfl⟩ : syracuseStep 1407139 = 2110709) B2110709
theorem B2029747 : Blo 1405522 2029747 := bstep (se 1 (by rfl) ⟨1522310, by rfl⟩ : syracuseStep 2029747 = 3044621) B3044621
theorem B1407155 : Blo 1405522 1407155 := bstep (se 1 (by rfl) ⟨1055366, by rfl⟩ : syracuseStep 1407155 = 2110733) B2110733
theorem B1407171 : Blo 1405522 1407171 := bstep (se 1 (by rfl) ⟨1055378, by rfl⟩ : syracuseStep 1407171 = 2110757) B2110757
theorem B2570449 : Blo 1405522 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B1407187 : Blo 1405522 1407187 := bstep (se 1 (by rfl) ⟨1055390, by rfl⟩ : syracuseStep 1407187 = 2110781) B2110781
theorem B1407203 : Blo 1405522 1407203 := bstep (se 1 (by rfl) ⟨1055402, by rfl⟩ : syracuseStep 1407203 = 2110805) B2110805
theorem B1407219 : Blo 1405522 1407219 := bstep (se 1 (by rfl) ⟨1055414, by rfl⟩ : syracuseStep 1407219 = 2110829) B2110829
theorem B1407235 : Blo 1405522 1407235 := bstep (se 1 (by rfl) ⟨1055426, by rfl⟩ : syracuseStep 1407235 = 2110853) B2110853
theorem B4004113 : Blo 1405522 4004113 := bstep (se 2 (by rfl) ⟨1501542, by rfl⟩ : syracuseStep 4004113 = 3003085) B3003085
theorem B2373907 : Blo 1405522 2373907 := bstep (se 1 (by rfl) ⟨1780430, by rfl⟩ : syracuseStep 2373907 = 3560861) B3560861
theorem B1407251 : Blo 1405522 1407251 := bstep (se 1 (by rfl) ⟨1055438, by rfl⟩ : syracuseStep 1407251 = 2110877) B2110877
theorem B1407267 : Blo 1405522 1407267 := bstep (se 1 (by rfl) ⟨1055450, by rfl⟩ : syracuseStep 1407267 = 2110901) B2110901
theorem B5069105 : Blo 1405522 5069105 := bstep (se 2 (by rfl) ⟨1900914, by rfl⟩ : syracuseStep 5069105 = 3801829) B3801829
theorem B1407283 : Blo 1405522 1407283 := bstep (se 1 (by rfl) ⟨1055462, by rfl⟩ : syracuseStep 1407283 = 2110925) B2110925
theorem B1407299 : Blo 1405522 1407299 := bstep (se 1 (by rfl) ⟨1055474, by rfl⟩ : syracuseStep 1407299 = 2110949) B2110949
theorem B1407315 : Blo 1405522 1407315 := bstep (se 1 (by rfl) ⟨1055486, by rfl⟩ : syracuseStep 1407315 = 2110973) B2110973
theorem B1407331 : Blo 1405522 1407331 := bstep (se 1 (by rfl) ⟨1055498, by rfl⟩ : syracuseStep 1407331 = 2110997) B2110997
theorem B4749677 : Blo 1405522 4749677 := bstep (se 3 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 4749677 = 1781129) B1781129
theorem B1407347 : Blo 1405522 1407347 := bstep (se 1 (by rfl) ⟨1055510, by rfl⟩ : syracuseStep 1407347 = 2111021) B2111021
theorem B1407363 : Blo 1405522 1407363 := bstep (se 1 (by rfl) ⟨1055522, by rfl⟩ : syracuseStep 1407363 = 2111045) B2111045
theorem B2668945 : Blo 1405522 2668945 := bstep (se 2 (by rfl) ⟨1000854, by rfl⟩ : syracuseStep 2668945 = 2001709) B2001709
theorem B1407379 : Blo 1405522 1407379 := bstep (se 1 (by rfl) ⟨1055534, by rfl⟩ : syracuseStep 1407379 = 2111069) B2111069
theorem B2374049 : Blo 1405522 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B4749731 : Blo 1405522 4749731 := bstep (se 1 (by rfl) ⟨3562298, by rfl⟩ : syracuseStep 4749731 = 7124597) B7124597
theorem B1407395 : Blo 1405522 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B5700017 : Blo 1405522 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B8010161 : Blo 1405522 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B1407411 : Blo 1405522 1407411 := bstep (se 1 (by rfl) ⟨1055558, by rfl⟩ : syracuseStep 1407411 = 2111117) B2111117
theorem B1407427 : Blo 1405522 1407427 := bstep (se 1 (by rfl) ⟨1055570, by rfl⟩ : syracuseStep 1407427 = 2111141) B2111141
theorem B1407443 : Blo 1405522 1407443 := bstep (se 1 (by rfl) ⟨1055582, by rfl⟩ : syracuseStep 1407443 = 2111165) B2111165
theorem B9624035 : Blo 1405522 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B1407459 : Blo 1405522 1407459 := bstep (se 1 (by rfl) ⟨1055594, by rfl⟩ : syracuseStep 1407459 = 2111189) B2111189
theorem B1407475 : Blo 1405522 1407475 := bstep (se 1 (by rfl) ⟨1055606, by rfl⟩ : syracuseStep 1407475 = 2111213) B2111213
theorem B3004931 : Blo 1405522 3004931 := bstep (se 1 (by rfl) ⟨2253698, by rfl⟩ : syracuseStep 3004931 = 4507397) B4507397
theorem B1407491 : Blo 1405522 1407491 := bstep (se 1 (by rfl) ⟨1055618, by rfl⟩ : syracuseStep 1407491 = 2111237) B2111237
theorem B1407507 : Blo 1405522 1407507 := bstep (se 1 (by rfl) ⟨1055630, by rfl⟩ : syracuseStep 1407507 = 2111261) B2111261
theorem B2374177 : Blo 1405522 2374177 := bstep (se 2 (by rfl) ⟨890316, by rfl⟩ : syracuseStep 2374177 = 1780633) B1780633
theorem B4004387 : Blo 1405522 4004387 := bstep (se 1 (by rfl) ⟨3003290, by rfl⟩ : syracuseStep 4004387 = 6006581) B6006581
theorem B9017891 : Blo 1405522 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B2669105 : Blo 1405522 2669105 := bstep (se 2 (by rfl) ⟨1000914, by rfl⟩ : syracuseStep 2669105 = 2001829) B2001829
theorem B2374211 : Blo 1405522 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B3005041 : Blo 1405522 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B5339789 : Blo 1405522 5339789 := bstep (se 3 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 5339789 = 2002421) B2002421
theorem B4750001 : Blo 1405522 4750001 := bstep (se 2 (by rfl) ⟨1781250, by rfl⟩ : syracuseStep 4750001 = 3562501) B3562501
theorem B2374339 : Blo 1405522 2374339 := bstep (se 1 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 2374339 = 3561509) B3561509
theorem B4004579 : Blo 1405522 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B43916003 : Blo 1405522 43916003 := bstep (se 1 (by rfl) ⟨32937002, by rfl⟩ : syracuseStep 43916003 = 65874005) B65874005
theorem B6093539 : Blo 1405522 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B9263857 : Blo 1405522 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B2407153 : Blo 1405522 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B3562289 : Blo 1405522 3562289 := bstep (se 2 (by rfl) ⟨1335858, by rfl⟩ : syracuseStep 3562289 = 2671717) B2671717
theorem B2374481 : Blo 1405522 2374481 := bstep (se 2 (by rfl) ⟨890430, by rfl⟩ : syracuseStep 2374481 = 1780861) B1780861
theorem B3562339 : Blo 1405522 3562339 := bstep (se 1 (by rfl) ⟨2671754, by rfl⟩ : syracuseStep 3562339 = 5343509) B5343509
theorem B17120099 : Blo 1405522 17120099 := bstep (se 1 (by rfl) ⟨12840074, by rfl⟩ : syracuseStep 17120099 = 25680149) B25680149
theorem B5069681 : Blo 1405522 5069681 := bstep (se 2 (by rfl) ⟨1901130, by rfl⟩ : syracuseStep 5069681 = 3802261) B3802261
theorem B86645645 : Blo 1405522 86645645 := bstep (se 3 (by rfl) ⟨16246058, by rfl⟩ : syracuseStep 86645645 = 32492117) B32492117
theorem B2669507 : Blo 1405522 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B2374609 : Blo 1405522 2374609 := bstep (se 2 (by rfl) ⟨890478, by rfl⟩ : syracuseStep 2374609 = 1780957) B1780957
theorem B3562481 : Blo 1405522 3562481 := bstep (se 2 (by rfl) ⟨1335930, by rfl⟩ : syracuseStep 3562481 = 2671861) B2671861
theorem B2374643 : Blo 1405522 2374643 := bstep (se 1 (by rfl) ⟨1780982, by rfl⟩ : syracuseStep 2374643 = 3561965) B3561965
theorem B19233845 : Blo 1405522 19233845 := bstep (se 5 (by rfl) ⟨901586, by rfl⟩ : syracuseStep 19233845 = 1803173) B1803173
theorem B2374771 : Blo 1405522 2374771 := bstep (se 1 (by rfl) ⟨1781078, by rfl⟩ : syracuseStep 2374771 = 3562157) B3562157
theorem B1899715 : Blo 1405522 1899715 := bstep (se 1 (by rfl) ⟨1424786, by rfl⟩ : syracuseStep 1899715 = 2849573) B2849573
theorem B2374913 : Blo 1405522 2374913 := bstep (se 2 (by rfl) ⟨890592, by rfl⟩ : syracuseStep 2374913 = 1781185) B1781185
theorem B8117509 : Blo 1405522 8117509 := bstep (se 4 (by rfl) ⟨761016, by rfl⟩ : syracuseStep 8117509 = 1522033) B1522033
theorem B2284817 : Blo 1405522 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B2375041 : Blo 1405522 2375041 := bstep (se 2 (by rfl) ⟨890640, by rfl⟩ : syracuseStep 2375041 = 1781281) B1781281
theorem B2375075 : Blo 1405522 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B5340593 : Blo 1405522 5340593 := bstep (se 2 (by rfl) ⟨2002722, by rfl⟩ : syracuseStep 5340593 = 4005445) B4005445
theorem B2252243 : Blo 1405522 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B4005389 : Blo 1405522 4005389 := bstep (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) B1502021
theorem B2252371 : Blo 1405522 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B12009059 : Blo 1405522 12009059 := bstep (se 1 (by rfl) ⟨9006794, by rfl⟩ : syracuseStep 12009059 = 18013589) B18013589
theorem B2473571 : Blo 1405522 2473571 := bstep (se 1 (by rfl) ⟨1855178, by rfl⟩ : syracuseStep 2473571 = 3710357) B3710357
theorem B2137745 : Blo 1405522 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B4005571 : Blo 1405522 4005571 := bstep (se 1 (by rfl) ⟨3004178, by rfl⟩ : syracuseStep 4005571 = 6008357) B6008357
theorem B4505357 : Blo 1405522 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B2670403 : Blo 1405522 2670403 := bstep (se 1 (by rfl) ⟨2002802, by rfl⟩ : syracuseStep 2670403 = 4005605) B4005605
theorem B8011619 : Blo 1405522 8011619 := bstep (se 1 (by rfl) ⟨6008714, by rfl⟩ : syracuseStep 8011619 = 12017429) B12017429
theorem B4276109 : Blo 1405522 4276109 := bstep (se 3 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 4276109 = 1603541) B1603541
theorem B2670563 : Blo 1405522 2670563 := bstep (se 1 (by rfl) ⟨2002922, by rfl⟩ : syracuseStep 2670563 = 4005845) B4005845
theorem B4505665 : Blo 1405522 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B3801181 : Blo 1405522 3801181 := bstep (se 3 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 3801181 = 1425443) B1425443
theorem B2670707 : Blo 1405522 2670707 := bstep (se 1 (by rfl) ⟨2003030, by rfl⟩ : syracuseStep 2670707 = 4006061) B4006061
theorem B15204503 : Blo 1405522 15204503 := bstep (se 1 (by rfl) ⟨11403377, by rfl⟩ : syracuseStep 15204503 = 22806755) B22806755
theorem B2670745 : Blo 1405522 2670745 := bstep (se 2 (by rfl) ⟨1001529, by rfl⟩ : syracuseStep 2670745 = 2003059) B2003059
theorem B24371381 : Blo 1405522 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B1581259 : Blo 1405522 1581259 := bstep (se 1 (by rfl) ⟨1185944, by rfl⟩ : syracuseStep 1581259 = 2371889) B2371889
theorem B1581367 : Blo 1405522 1581367 := bstep (se 1 (by rfl) ⟨1186025, by rfl⟩ : syracuseStep 1581367 = 2372051) B2372051
theorem B3162455 : Blo 1405522 3162455 := bstep (se 1 (by rfl) ⟨2371841, by rfl⟩ : syracuseStep 3162455 = 4743683) B4743683
theorem B24043877 : Blo 1405522 24043877 := bstep (se 4 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 24043877 = 4508227) B4508227
theorem B9617795 : Blo 1405522 9617795 := bstep (se 1 (by rfl) ⟨7213346, by rfl⟩ : syracuseStep 9617795 = 14426693) B14426693
theorem B11403737 : Blo 1405522 11403737 := bstep (se 2 (by rfl) ⟨4276401, by rfl⟩ : syracuseStep 11403737 = 8552803) B8552803
theorem B1581547 : Blo 1405522 1581547 := bstep (se 1 (by rfl) ⟨1186160, by rfl⟩ : syracuseStep 1581547 = 2372321) B2372321
theorem B3162635 : Blo 1405522 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B5341747 : Blo 1405522 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B3162689 : Blo 1405522 3162689 := bstep (se 2 (by rfl) ⟨1186008, by rfl⟩ : syracuseStep 3162689 = 2372017) B2372017
theorem B1581655 : Blo 1405522 1581655 := bstep (se 1 (by rfl) ⟨1186241, by rfl⟩ : syracuseStep 1581655 = 2372483) B2372483
theorem B2671193 : Blo 1405522 2671193 := bstep (se 2 (by rfl) ⟨1001697, by rfl⟩ : syracuseStep 2671193 = 2003395) B2003395
theorem B4006493 : Blo 1405522 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B9011843 : Blo 1405522 9011843 := bstep (se 1 (by rfl) ⟨6758882, by rfl⟩ : syracuseStep 9011843 = 13517765) B13517765
theorem B1581835 : Blo 1405522 1581835 := bstep (se 1 (by rfl) ⟨1186376, by rfl⟩ : syracuseStep 1581835 = 2372753) B2372753
theorem B3162905 : Blo 1405522 3162905 := bstep (se 2 (by rfl) ⟨1186089, by rfl⟩ : syracuseStep 3162905 = 2372179) B2372179
theorem B10674989 : Blo 1405522 10674989 := bstep (se 3 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 10674989 = 4003121) B4003121
theorem B4006721 : Blo 1405522 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B3162995 : Blo 1405522 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B1581943 : Blo 1405522 1581943 := bstep (se 1 (by rfl) ⟨1186457, by rfl⟩ : syracuseStep 1581943 = 2372915) B2372915
theorem B3163031 : Blo 1405522 3163031 := bstep (se 1 (by rfl) ⟨2372273, by rfl⟩ : syracuseStep 3163031 = 4744547) B4744547
theorem B4744115 : Blo 1405522 4744115 := bstep (se 1 (by rfl) ⟨3558086, by rfl⟩ : syracuseStep 4744115 = 7116173) B7116173
theorem B2851777 : Blo 1405522 2851777 := bstep (se 2 (by rfl) ⟨1069416, by rfl⟩ : syracuseStep 2851777 = 2138833) B2138833
theorem B12010457 : Blo 1405522 12010457 := bstep (se 2 (by rfl) ⟨4503921, by rfl⟩ : syracuseStep 12010457 = 9007843) B9007843
theorem B1582123 : Blo 1405522 1582123 := bstep (se 1 (by rfl) ⟨1186592, by rfl⟩ : syracuseStep 1582123 = 2373185) B2373185
theorem B3163211 : Blo 1405522 3163211 := bstep (se 1 (by rfl) ⟨2372408, by rfl⟩ : syracuseStep 3163211 = 4744817) B4744817
theorem B3163265 : Blo 1405522 3163265 := bstep (se 2 (by rfl) ⟨1186224, by rfl⟩ : syracuseStep 3163265 = 2372449) B2372449
theorem B1582231 : Blo 1405522 1582231 := bstep (se 1 (by rfl) ⟨1186673, by rfl⟩ : syracuseStep 1582231 = 2373347) B2373347
theorem B4007063 : Blo 1405522 4007063 := bstep (se 1 (by rfl) ⟨3005297, by rfl⟩ : syracuseStep 4007063 = 6010595) B6010595
theorem B4744385 : Blo 1405522 4744385 := bstep (se 2 (by rfl) ⟨1779144, by rfl⟩ : syracuseStep 4744385 = 3558289) B3558289
theorem B1688779 : Blo 1405522 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B6005981 : Blo 1405522 6005981 := bstep (se 3 (by rfl) ⟨1126121, by rfl⟩ : syracuseStep 6005981 = 2252243) B2252243
theorem B16024877 : Blo 1405522 16024877 := bstep (se 3 (by rfl) ⟨3004664, by rfl⟩ : syracuseStep 16024877 = 6009329) B6009329
theorem B22799681 : Blo 1405522 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B2671937 : Blo 1405522 2671937 := bstep (se 2 (by rfl) ⟨1001976, by rfl⟩ : syracuseStep 2671937 = 2003953) B2003953
theorem B1582411 : Blo 1405522 1582411 := bstep (se 1 (by rfl) ⟨1186808, by rfl⟩ : syracuseStep 1582411 = 2373617) B2373617
theorem B3163481 : Blo 1405522 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B3163571 : Blo 1405522 3163571 := bstep (se 1 (by rfl) ⟨2372678, by rfl⟩ : syracuseStep 3163571 = 4745357) B4745357
theorem B1582519 : Blo 1405522 1582519 := bstep (se 1 (by rfl) ⟨1186889, by rfl⟩ : syracuseStep 1582519 = 2373779) B2373779
theorem B5072321 : Blo 1405522 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B3163607 : Blo 1405522 3163607 := bstep (se 1 (by rfl) ⟨2372705, by rfl⟩ : syracuseStep 3163607 = 4745411) B4745411
theorem B12019205 : Blo 1405522 12019205 := bstep (se 4 (by rfl) ⟨1126800, by rfl⟩ : syracuseStep 12019205 = 2253601) B2253601
theorem B8013329 : Blo 1405522 8013329 := bstep (se 2 (by rfl) ⟨3004998, by rfl⟩ : syracuseStep 8013329 = 6009997) B6009997
theorem B2532953 : Blo 1405522 2532953 := bstep (se 2 (by rfl) ⟨949857, by rfl⟩ : syracuseStep 2532953 = 1899715) B1899715
theorem B6596189 : Blo 1405522 6596189 := bstep (se 3 (by rfl) ⟨1236785, by rfl⟩ : syracuseStep 6596189 = 2473571) B2473571
theorem B1582699 : Blo 1405522 1582699 := bstep (se 1 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 1582699 = 2374049) B2374049
theorem B3163787 : Blo 1405522 3163787 := bstep (se 1 (by rfl) ⟨2372840, by rfl⟩ : syracuseStep 3163787 = 4745681) B4745681
theorem B6416023 : Blo 1405522 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B10823345 : Blo 1405522 10823345 := bstep (se 2 (by rfl) ⟨4058754, by rfl⟩ : syracuseStep 10823345 = 8117509) B8117509
theorem B3163841 : Blo 1405522 3163841 := bstep (se 2 (by rfl) ⟨1186440, by rfl⟩ : syracuseStep 3163841 = 2372881) B2372881
theorem B1779403 : Blo 1405522 1779403 := bstep (se 1 (by rfl) ⟨1334552, by rfl⟩ : syracuseStep 1779403 = 2669105) B2669105
theorem B1582807 : Blo 1405522 1582807 := bstep (se 1 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 1582807 = 2374211) B2374211
theorem B4744925 : Blo 1405522 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B1689355 : Blo 1405522 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B5342993 : Blo 1405522 5342993 := bstep (se 2 (by rfl) ⟨2003622, by rfl⟩ : syracuseStep 5342993 = 4007245) B4007245
theorem B2705177 : Blo 1405522 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B36554561 : Blo 1405522 36554561 := bstep (se 2 (by rfl) ⟨13707960, by rfl⟩ : syracuseStep 36554561 = 27415921) B27415921
theorem B1582987 : Blo 1405522 1582987 := bstep (se 1 (by rfl) ⟨1187240, by rfl⟩ : syracuseStep 1582987 = 2374481) B2374481
theorem B11413399 : Blo 1405522 11413399 := bstep (se 1 (by rfl) ⟨8560049, by rfl⟩ : syracuseStep 11413399 = 17120099) B17120099
theorem B3164057 : Blo 1405522 3164057 := bstep (se 2 (by rfl) ⟨1186521, by rfl⟩ : syracuseStep 3164057 = 2373043) B2373043
theorem B57763763 : Blo 1405522 57763763 := bstep (se 1 (by rfl) ⟨43322822, by rfl⟩ : syracuseStep 57763763 = 86645645) B86645645
theorem B1779671 : Blo 1405522 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B4507613 : Blo 1405522 4507613 := bstep (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) B1690355
theorem B3164147 : Blo 1405522 3164147 := bstep (se 1 (by rfl) ⟨2373110, by rfl⟩ : syracuseStep 3164147 = 4746221) B4746221
theorem B1583095 : Blo 1405522 1583095 := bstep (se 1 (by rfl) ⟨1187321, by rfl⟩ : syracuseStep 1583095 = 2374643) B2374643
theorem B3606551 : Blo 1405522 3606551 := bstep (se 1 (by rfl) ⟨2704913, by rfl⟩ : syracuseStep 3606551 = 5409827) B5409827
theorem B3164183 : Blo 1405522 3164183 := bstep (se 1 (by rfl) ⟨2373137, by rfl⟩ : syracuseStep 3164183 = 4746275) B4746275
theorem B12822563 : Blo 1405522 12822563 := bstep (se 1 (by rfl) ⟨9616922, by rfl⟩ : syracuseStep 12822563 = 19233845) B19233845
theorem B300394565 : Blo 1405522 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B2058329 : Blo 1405522 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B4507741 : Blo 1405522 4507741 := bstep (se 3 (by rfl) ⟨845201, by rfl⟩ : syracuseStep 4507741 = 1690403) B1690403
theorem B2852993 : Blo 1405522 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B1583275 : Blo 1405522 1583275 := bstep (se 1 (by rfl) ⟨1187456, by rfl⟩ : syracuseStep 1583275 = 2374913) B2374913
theorem B3164363 : Blo 1405522 3164363 := bstep (se 1 (by rfl) ⟨2373272, by rfl⟩ : syracuseStep 3164363 = 4746545) B4746545
theorem B3164417 : Blo 1405522 3164417 := bstep (se 2 (by rfl) ⟨1186656, by rfl⟩ : syracuseStep 3164417 = 2373313) B2373313
theorem B1583383 : Blo 1405522 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B2705729 : Blo 1405522 2705729 := bstep (se 2 (by rfl) ⟨1014648, by rfl⟩ : syracuseStep 2705729 = 2029297) B2029297
theorem B3557783 : Blo 1405522 3557783 := bstep (se 1 (by rfl) ⟨2668337, by rfl⟩ : syracuseStep 3557783 = 5336675) B5336675
theorem B8006039 : Blo 1405522 8006039 := bstep (se 1 (by rfl) ⟨6004529, by rfl⟩ : syracuseStep 8006039 = 12009059) B12009059
theorem B5343691 : Blo 1405522 5343691 := bstep (se 1 (by rfl) ⟨4007768, by rfl⟩ : syracuseStep 5343691 = 8015537) B8015537
theorem B3164633 : Blo 1405522 3164633 := bstep (se 2 (by rfl) ⟨1186737, by rfl⟩ : syracuseStep 3164633 = 2373475) B2373475
theorem B3164723 : Blo 1405522 3164723 := bstep (se 1 (by rfl) ⟨2373542, by rfl⟩ : syracuseStep 3164723 = 4747085) B4747085
theorem B12012097 : Blo 1405522 12012097 := bstep (se 2 (by rfl) ⟨4504536, by rfl⟩ : syracuseStep 12012097 = 9009073) B9009073
theorem B3164759 : Blo 1405522 3164759 := bstep (se 1 (by rfl) ⟨2373569, by rfl⟩ : syracuseStep 3164759 = 4747139) B4747139
theorem B1780375 : Blo 1405522 1780375 := bstep (se 1 (by rfl) ⟨1335281, by rfl⟩ : syracuseStep 1780375 = 2670563) B2670563
theorem B5343965 : Blo 1405522 5343965 := bstep (se 3 (by rfl) ⟨1001993, by rfl⟩ : syracuseStep 5343965 = 2003987) B2003987
theorem B3164939 : Blo 1405522 3164939 := bstep (se 1 (by rfl) ⟨2373704, by rfl⟩ : syracuseStep 3164939 = 4747409) B4747409
theorem B7121681 : Blo 1405522 7121681 := bstep (se 2 (by rfl) ⟨2670630, by rfl⟩ : syracuseStep 7121681 = 5341261) B5341261
theorem B3164993 : Blo 1405522 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B4746059 : Blo 1405522 4746059 := bstep (se 1 (by rfl) ⟨3559544, by rfl⟩ : syracuseStep 4746059 = 7119089) B7119089
theorem B9005975 : Blo 1405522 9005975 := bstep (se 1 (by rfl) ⟨6754481, by rfl⟩ : syracuseStep 9005975 = 13508963) B13508963
theorem B2706329 : Blo 1405522 2706329 := bstep (se 2 (by rfl) ⟨1014873, by rfl⟩ : syracuseStep 2706329 = 2029747) B2029747
theorem B7121843 : Blo 1405522 7121843 := bstep (se 1 (by rfl) ⟨5341382, by rfl⟩ : syracuseStep 7121843 = 10682765) B10682765
theorem B3427265 : Blo 1405522 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B2108363 : Blo 1405522 2108363 := bstep (se 1 (by rfl) ⟨1581272, by rfl⟩ : syracuseStep 2108363 = 3162545) B3162545
theorem B2108375 : Blo 1405522 2108375 := bstep (se 1 (by rfl) ⟨1581281, by rfl⟩ : syracuseStep 2108375 = 3162563) B3162563
theorem B2108441 : Blo 1405522 2108441 := bstep (se 2 (by rfl) ⟨790665, by rfl⟩ : syracuseStep 2108441 = 1581331) B1581331
theorem B3165209 : Blo 1405522 3165209 := bstep (se 2 (by rfl) ⟨1186953, by rfl⟩ : syracuseStep 3165209 = 2373907) B2373907
theorem B3558451 : Blo 1405522 3558451 := bstep (se 1 (by rfl) ⟨2668838, by rfl⟩ : syracuseStep 3558451 = 5337677) B5337677
theorem B4746329 : Blo 1405522 4746329 := bstep (se 2 (by rfl) ⟨1779873, by rfl⟩ : syracuseStep 4746329 = 3559747) B3559747
theorem B9137245 : Blo 1405522 9137245 := bstep (se 3 (by rfl) ⟨1713233, by rfl⟩ : syracuseStep 9137245 = 3426467) B3426467
theorem B3165299 : Blo 1405522 3165299 := bstep (se 1 (by rfl) ⟨2373974, by rfl⟩ : syracuseStep 3165299 = 4747949) B4747949
theorem B2108555 : Blo 1405522 2108555 := bstep (se 1 (by rfl) ⟨1581416, by rfl⟩ : syracuseStep 2108555 = 3162833) B3162833
theorem B2108567 : Blo 1405522 2108567 := bstep (se 1 (by rfl) ⟨1581425, by rfl⟩ : syracuseStep 2108567 = 3162851) B3162851
theorem B3165335 : Blo 1405522 3165335 := bstep (se 1 (by rfl) ⟨2374001, by rfl⟩ : syracuseStep 3165335 = 4748003) B4748003
theorem B3558593 : Blo 1405522 3558593 := bstep (se 2 (by rfl) ⟨1334472, by rfl⟩ : syracuseStep 3558593 = 2668945) B2668945
theorem B2108633 : Blo 1405522 2108633 := bstep (se 2 (by rfl) ⟨790737, by rfl⟩ : syracuseStep 2108633 = 1581475) B1581475
theorem B2108747 : Blo 1405522 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B3165515 : Blo 1405522 3165515 := bstep (se 1 (by rfl) ⟨2374136, by rfl⟩ : syracuseStep 3165515 = 4748273) B4748273
theorem B2108759 : Blo 1405522 2108759 := bstep (se 1 (by rfl) ⟨1581569, by rfl⟩ : syracuseStep 2108759 = 3163139) B3163139
theorem B3165569 : Blo 1405522 3165569 := bstep (se 2 (by rfl) ⟨1187088, by rfl⟩ : syracuseStep 3165569 = 2374177) B2374177
theorem B5066135 : Blo 1405522 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B2108825 : Blo 1405522 2108825 := bstep (se 2 (by rfl) ⟨790809, by rfl⟩ : syracuseStep 2108825 = 1581619) B1581619
theorem B3378635 : Blo 1405522 3378635 := bstep (se 1 (by rfl) ⟨2533976, by rfl⟩ : syracuseStep 3378635 = 5067953) B5067953
theorem B2108939 : Blo 1405522 2108939 := bstep (se 1 (by rfl) ⟨1581704, by rfl⟩ : syracuseStep 2108939 = 3163409) B3163409
theorem B2108951 : Blo 1405522 2108951 := bstep (se 1 (by rfl) ⟨1581713, by rfl⟩ : syracuseStep 2108951 = 3163427) B3163427
theorem B24030755 : Blo 1405522 24030755 := bstep (se 1 (by rfl) ⟨18023066, by rfl⟩ : syracuseStep 24030755 = 36046133) B36046133
theorem B2109017 : Blo 1405522 2109017 := bstep (se 2 (by rfl) ⟨790881, by rfl⟩ : syracuseStep 2109017 = 1581763) B1581763
theorem B3165785 : Blo 1405522 3165785 := bstep (se 2 (by rfl) ⟨1187169, by rfl⟩ : syracuseStep 3165785 = 2374339) B2374339
theorem B3165875 : Blo 1405522 3165875 := bstep (se 1 (by rfl) ⟨2374406, by rfl⟩ : syracuseStep 3165875 = 4748813) B4748813
theorem B2109131 : Blo 1405522 2109131 := bstep (se 1 (by rfl) ⟨1581848, by rfl⟩ : syracuseStep 2109131 = 3163697) B3163697
theorem B2109143 : Blo 1405522 2109143 := bstep (se 1 (by rfl) ⟨1581857, by rfl⟩ : syracuseStep 2109143 = 3163715) B3163715
theorem B3165911 : Blo 1405522 3165911 := bstep (se 1 (by rfl) ⟨2374433, by rfl⟩ : syracuseStep 3165911 = 4748867) B4748867
theorem B6008579 : Blo 1405522 6008579 := bstep (se 1 (by rfl) ⟨4506434, by rfl⟩ : syracuseStep 6008579 = 9012869) B9012869
theorem B4747031 : Blo 1405522 4747031 := bstep (se 1 (by rfl) ⟨3560273, by rfl⟩ : syracuseStep 4747031 = 7120547) B7120547
theorem B2109209 : Blo 1405522 2109209 := bstep (se 2 (by rfl) ⟨790953, by rfl⟩ : syracuseStep 2109209 = 1581907) B1581907
theorem B15200045 : Blo 1405522 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B2109323 : Blo 1405522 2109323 := bstep (se 1 (by rfl) ⟨1581992, by rfl⟩ : syracuseStep 2109323 = 3163985) B3163985
theorem B3166091 : Blo 1405522 3166091 := bstep (se 1 (by rfl) ⟨2374568, by rfl⟩ : syracuseStep 3166091 = 4749137) B4749137
theorem B2109335 : Blo 1405522 2109335 := bstep (se 1 (by rfl) ⟨1582001, by rfl⟩ : syracuseStep 2109335 = 3164003) B3164003
theorem B3166145 : Blo 1405522 3166145 := bstep (se 2 (by rfl) ⟨1187304, by rfl⟩ : syracuseStep 3166145 = 2374609) B2374609
theorem B2404313 : Blo 1405522 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B2109401 : Blo 1405522 2109401 := bstep (se 2 (by rfl) ⟨791025, by rfl⟩ : syracuseStep 2109401 = 1582051) B1582051
theorem B10137635 : Blo 1405522 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B2535475 : Blo 1405522 2535475 := bstep (se 1 (by rfl) ⟨1901606, by rfl⟩ : syracuseStep 2535475 = 3803213) B3803213
theorem B2109515 : Blo 1405522 2109515 := bstep (se 1 (by rfl) ⟨1582136, by rfl⟩ : syracuseStep 2109515 = 3164273) B3164273
theorem B2109527 : Blo 1405522 2109527 := bstep (se 1 (by rfl) ⟨1582145, by rfl⟩ : syracuseStep 2109527 = 3164291) B3164291
theorem B2109593 : Blo 1405522 2109593 := bstep (se 2 (by rfl) ⟨791097, by rfl⟩ : syracuseStep 2109593 = 1582195) B1582195
theorem B3166361 : Blo 1405522 3166361 := bstep (se 2 (by rfl) ⟨1187385, by rfl⟩ : syracuseStep 3166361 = 2374771) B2374771
theorem B3379403 : Blo 1405522 3379403 := bstep (se 1 (by rfl) ⟨2534552, by rfl⟩ : syracuseStep 3379403 = 5069105) B5069105
theorem B3166451 : Blo 1405522 3166451 := bstep (se 1 (by rfl) ⟨2374838, by rfl⟩ : syracuseStep 3166451 = 4749677) B4749677
theorem B2109707 : Blo 1405522 2109707 := bstep (se 1 (by rfl) ⟨1582280, by rfl⟩ : syracuseStep 2109707 = 3164561) B3164561
theorem B2109719 : Blo 1405522 2109719 := bstep (se 1 (by rfl) ⟨1582289, by rfl⟩ : syracuseStep 2109719 = 3164579) B3164579
theorem B3166487 : Blo 1405522 3166487 := bstep (se 1 (by rfl) ⟨2374865, by rfl⟩ : syracuseStep 3166487 = 4749731) B4749731
theorem B4747571 : Blo 1405522 4747571 := bstep (se 1 (by rfl) ⟨3560678, by rfl⟩ : syracuseStep 4747571 = 7121357) B7121357
theorem B2003287 : Blo 1405522 2003287 := bstep (se 1 (by rfl) ⟨1502465, by rfl⟩ : syracuseStep 2003287 = 3004931) B3004931
theorem B2109785 : Blo 1405522 2109785 := bstep (se 2 (by rfl) ⟨791169, by rfl⟩ : syracuseStep 2109785 = 1582339) B1582339
theorem B2568577 : Blo 1405522 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3559859 : Blo 1405522 3559859 := bstep (se 1 (by rfl) ⟨2669894, by rfl⟩ : syracuseStep 3559859 = 5339789) B5339789
theorem B2109899 : Blo 1405522 2109899 := bstep (se 1 (by rfl) ⟨1582424, by rfl⟩ : syracuseStep 2109899 = 3164849) B3164849
theorem B3166667 : Blo 1405522 3166667 := bstep (se 1 (by rfl) ⟨2375000, by rfl⟩ : syracuseStep 3166667 = 4750001) B4750001
theorem B2109911 : Blo 1405522 2109911 := bstep (se 1 (by rfl) ⟨1582433, by rfl⟩ : syracuseStep 2109911 = 3164867) B3164867
theorem B3166721 : Blo 1405522 3166721 := bstep (se 2 (by rfl) ⟨1187520, by rfl⟩ : syracuseStep 3166721 = 2375041) B2375041
theorem B2109977 : Blo 1405522 2109977 := bstep (se 2 (by rfl) ⟨791241, by rfl⟩ : syracuseStep 2109977 = 1582483) B1582483
theorem B4747841 : Blo 1405522 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B20288069 : Blo 1405522 20288069 := bstep (se 4 (by rfl) ⟨1902006, by rfl⟩ : syracuseStep 20288069 = 3804013) B3804013
theorem B3379787 : Blo 1405522 3379787 := bstep (se 1 (by rfl) ⟨2534840, by rfl⟩ : syracuseStep 3379787 = 5069681) B5069681
theorem B1405527 : Blo 1405522 1405527 := bstep (se 1 (by rfl) ⟨1054145, by rfl⟩ : syracuseStep 1405527 = 2108291) B2108291
theorem B10678877 : Blo 1405522 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B1405547 : Blo 1405522 1405547 := bstep (se 1 (by rfl) ⟨1054160, by rfl⟩ : syracuseStep 1405547 = 2108321) B2108321
theorem B1405559 : Blo 1405522 1405559 := bstep (se 1 (by rfl) ⟨1054169, by rfl⟩ : syracuseStep 1405559 = 2108339) B2108339
theorem B1405579 : Blo 1405522 1405579 := bstep (se 1 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 1405579 = 2108369) B2108369
theorem B2110091 : Blo 1405522 2110091 := bstep (se 1 (by rfl) ⟨1582568, by rfl⟩ : syracuseStep 2110091 = 3165137) B3165137
theorem B1405591 : Blo 1405522 1405591 := bstep (se 1 (by rfl) ⟨1054193, by rfl⟩ : syracuseStep 1405591 = 2108387) B2108387
theorem B2110103 : Blo 1405522 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B1405611 : Blo 1405522 1405611 := bstep (se 1 (by rfl) ⟨1054208, by rfl⟩ : syracuseStep 1405611 = 2108417) B2108417
theorem B1405623 : Blo 1405522 1405623 := bstep (se 1 (by rfl) ⟨1054217, by rfl⟩ : syracuseStep 1405623 = 2108435) B2108435
theorem B1405643 : Blo 1405522 1405643 := bstep (se 1 (by rfl) ⟨1054232, by rfl⟩ : syracuseStep 1405643 = 2108465) B2108465
theorem B1405655 : Blo 1405522 1405655 := bstep (se 1 (by rfl) ⟨1054241, by rfl⟩ : syracuseStep 1405655 = 2108483) B2108483
theorem B2110169 : Blo 1405522 2110169 := bstep (se 2 (by rfl) ⟨791313, by rfl⟩ : syracuseStep 2110169 = 1582627) B1582627
theorem B1405675 : Blo 1405522 1405675 := bstep (se 1 (by rfl) ⟨1054256, by rfl⟩ : syracuseStep 1405675 = 2108513) B2108513
theorem B1405687 : Blo 1405522 1405687 := bstep (se 1 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 1405687 = 2108531) B2108531
theorem B5337859 : Blo 1405522 5337859 := bstep (se 1 (by rfl) ⟨4003394, by rfl⟩ : syracuseStep 5337859 = 8006789) B8006789
theorem B1405707 : Blo 1405522 1405707 := bstep (se 1 (by rfl) ⟨1054280, by rfl⟩ : syracuseStep 1405707 = 2108561) B2108561
theorem B1405719 : Blo 1405522 1405719 := bstep (se 1 (by rfl) ⟨1054289, by rfl⟩ : syracuseStep 1405719 = 2108579) B2108579
theorem B2372375 : Blo 1405522 2372375 := bstep (se 1 (by rfl) ⟨1779281, by rfl⟩ : syracuseStep 2372375 = 3558563) B3558563
theorem B3003161 : Blo 1405522 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B1405739 : Blo 1405522 1405739 := bstep (se 1 (by rfl) ⟨1054304, by rfl⟩ : syracuseStep 1405739 = 2108609) B2108609
theorem B1405751 : Blo 1405522 1405751 := bstep (se 1 (by rfl) ⟨1054313, by rfl⟩ : syracuseStep 1405751 = 2108627) B2108627
theorem B1405771 : Blo 1405522 1405771 := bstep (se 1 (by rfl) ⟨1054328, by rfl⟩ : syracuseStep 1405771 = 2108657) B2108657
theorem B2110283 : Blo 1405522 2110283 := bstep (se 1 (by rfl) ⟨1582712, by rfl⟩ : syracuseStep 2110283 = 3165425) B3165425
theorem B7123787 : Blo 1405522 7123787 := bstep (se 1 (by rfl) ⟨5342840, by rfl⟩ : syracuseStep 7123787 = 10685681) B10685681
theorem B1405783 : Blo 1405522 1405783 := bstep (se 1 (by rfl) ⟨1054337, by rfl⟩ : syracuseStep 1405783 = 2108675) B2108675
theorem B2110295 : Blo 1405522 2110295 := bstep (se 1 (by rfl) ⟨1582721, by rfl⟩ : syracuseStep 2110295 = 3165443) B3165443
theorem B1405803 : Blo 1405522 1405803 := bstep (se 1 (by rfl) ⟨1054352, by rfl⟩ : syracuseStep 1405803 = 2108705) B2108705
theorem B1405815 : Blo 1405522 1405815 := bstep (se 1 (by rfl) ⟨1054361, by rfl⟩ : syracuseStep 1405815 = 2108723) B2108723
theorem B1405835 : Blo 1405522 1405835 := bstep (se 1 (by rfl) ⟨1054376, by rfl⟩ : syracuseStep 1405835 = 2108753) B2108753
theorem B1405847 : Blo 1405522 1405847 := bstep (se 1 (by rfl) ⟨1054385, by rfl⟩ : syracuseStep 1405847 = 2108771) B2108771
theorem B2372503 : Blo 1405522 2372503 := bstep (se 1 (by rfl) ⟨1779377, by rfl⟩ : syracuseStep 2372503 = 3558755) B3558755
theorem B2110361 : Blo 1405522 2110361 := bstep (se 2 (by rfl) ⟨791385, by rfl⟩ : syracuseStep 2110361 = 1582771) B1582771
theorem B1405867 : Blo 1405522 1405867 := bstep (se 1 (by rfl) ⟨1054400, by rfl⟩ : syracuseStep 1405867 = 2108801) B2108801
theorem B1405879 : Blo 1405522 1405879 := bstep (se 1 (by rfl) ⟨1054409, by rfl⟩ : syracuseStep 1405879 = 2108819) B2108819
theorem B1405899 : Blo 1405522 1405899 := bstep (se 1 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 1405899 = 2108849) B2108849
theorem B3560395 : Blo 1405522 3560395 := bstep (se 1 (by rfl) ⟨2670296, by rfl⟩ : syracuseStep 3560395 = 5340593) B5340593
theorem B1405911 : Blo 1405522 1405911 := bstep (se 1 (by rfl) ⟨1054433, by rfl⟩ : syracuseStep 1405911 = 2108867) B2108867
theorem B1405931 : Blo 1405522 1405931 := bstep (se 1 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 1405931 = 2108897) B2108897
theorem B1405943 : Blo 1405522 1405943 := bstep (se 1 (by rfl) ⟨1054457, by rfl⟩ : syracuseStep 1405943 = 2108915) B2108915
theorem B1405963 : Blo 1405522 1405963 := bstep (se 1 (by rfl) ⟨1054472, by rfl⟩ : syracuseStep 1405963 = 2108945) B2108945
theorem B2110475 : Blo 1405522 2110475 := bstep (se 1 (by rfl) ⟨1582856, by rfl⟩ : syracuseStep 2110475 = 3165713) B3165713
theorem B1405975 : Blo 1405522 1405975 := bstep (se 1 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 1405975 = 2108963) B2108963
theorem B2110487 : Blo 1405522 2110487 := bstep (se 1 (by rfl) ⟨1582865, by rfl⟩ : syracuseStep 2110487 = 3165731) B3165731
theorem B1405995 : Blo 1405522 1405995 := bstep (se 1 (by rfl) ⟨1054496, by rfl⟩ : syracuseStep 1405995 = 2108993) B2108993
theorem B12022829 : Blo 1405522 12022829 := bstep (se 3 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 12022829 = 4508561) B4508561
theorem B5338163 : Blo 1405522 5338163 := bstep (se 1 (by rfl) ⟨4003622, by rfl⟩ : syracuseStep 5338163 = 8007245) B8007245
theorem B1406007 : Blo 1405522 1406007 := bstep (se 1 (by rfl) ⟨1054505, by rfl⟩ : syracuseStep 1406007 = 2109011) B2109011
theorem B1406027 : Blo 1405522 1406027 := bstep (se 1 (by rfl) ⟨1054520, by rfl⟩ : syracuseStep 1406027 = 2109041) B2109041
theorem B1406039 : Blo 1405522 1406039 := bstep (se 1 (by rfl) ⟨1054529, by rfl⟩ : syracuseStep 1406039 = 2109059) B2109059
theorem B3560537 : Blo 1405522 3560537 := bstep (se 2 (by rfl) ⟨1335201, by rfl⟩ : syracuseStep 3560537 = 2670403) B2670403
theorem B2110553 : Blo 1405522 2110553 := bstep (se 2 (by rfl) ⟨791457, by rfl⟩ : syracuseStep 2110553 = 1582915) B1582915
theorem B4748381 : Blo 1405522 4748381 := bstep (se 3 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 4748381 = 1780643) B1780643
theorem B1406059 : Blo 1405522 1406059 := bstep (se 1 (by rfl) ⟨1054544, by rfl⟩ : syracuseStep 1406059 = 2109089) B2109089
theorem B1406071 : Blo 1405522 1406071 := bstep (se 1 (by rfl) ⟨1054553, by rfl⟩ : syracuseStep 1406071 = 2109107) B2109107
theorem B1406091 : Blo 1405522 1406091 := bstep (se 1 (by rfl) ⟨1054568, by rfl⟩ : syracuseStep 1406091 = 2109137) B2109137
theorem B1406103 : Blo 1405522 1406103 := bstep (se 1 (by rfl) ⟨1054577, by rfl⟩ : syracuseStep 1406103 = 2109155) B2109155
theorem B2569367 : Blo 1405522 2569367 := bstep (se 1 (by rfl) ⟨1927025, by rfl⟩ : syracuseStep 2569367 = 3854051) B3854051
theorem B1406123 : Blo 1405522 1406123 := bstep (se 1 (by rfl) ⟨1054592, by rfl⟩ : syracuseStep 1406123 = 2109185) B2109185
theorem B3003571 : Blo 1405522 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B1406135 : Blo 1405522 1406135 := bstep (se 1 (by rfl) ⟨1054601, by rfl⟩ : syracuseStep 1406135 = 2109203) B2109203
theorem B1406155 : Blo 1405522 1406155 := bstep (se 1 (by rfl) ⟨1054616, by rfl⟩ : syracuseStep 1406155 = 2109233) B2109233
theorem B2110667 : Blo 1405522 2110667 := bstep (se 1 (by rfl) ⟨1583000, by rfl⟩ : syracuseStep 2110667 = 3166001) B3166001
theorem B1406167 : Blo 1405522 1406167 := bstep (se 1 (by rfl) ⟨1054625, by rfl⟩ : syracuseStep 1406167 = 2109251) B2109251
theorem B2110679 : Blo 1405522 2110679 := bstep (se 1 (by rfl) ⟨1583009, by rfl⟩ : syracuseStep 2110679 = 3166019) B3166019
theorem B1406187 : Blo 1405522 1406187 := bstep (se 1 (by rfl) ⟨1054640, by rfl⟩ : syracuseStep 1406187 = 2109281) B2109281
theorem B1406199 : Blo 1405522 1406199 := bstep (se 1 (by rfl) ⟨1054649, by rfl⟩ : syracuseStep 1406199 = 2109299) B2109299
theorem B1406219 : Blo 1405522 1406219 := bstep (se 1 (by rfl) ⟨1054664, by rfl⟩ : syracuseStep 1406219 = 2109329) B2109329
theorem B1406231 : Blo 1405522 1406231 := bstep (se 1 (by rfl) ⟨1054673, by rfl⟩ : syracuseStep 1406231 = 2109347) B2109347
theorem B2110745 : Blo 1405522 2110745 := bstep (se 2 (by rfl) ⟨791529, by rfl⟩ : syracuseStep 2110745 = 1583059) B1583059
theorem B1406251 : Blo 1405522 1406251 := bstep (se 1 (by rfl) ⟨1054688, by rfl⟩ : syracuseStep 1406251 = 2109377) B2109377
theorem B2111255 : Blo 1405522 2111255 := bstep (se 1 (by rfl) ⟨1583441, by rfl⟩ : syracuseStep 2111255 = 3166883) B3166883
theorem B1406263 : Blo 1405522 1406263 := bstep (se 1 (by rfl) ⟨1054697, by rfl⟩ : syracuseStep 1406263 = 2109395) B2109395
theorem B9008459 : Blo 1405522 9008459 := bstep (se 1 (by rfl) ⟨6756344, by rfl⟩ : syracuseStep 9008459 = 13512689) B13512689
theorem B1406283 : Blo 1405522 1406283 := bstep (se 1 (by rfl) ⟨1054712, by rfl⟩ : syracuseStep 1406283 = 2109425) B2109425
theorem B1406295 : Blo 1405522 1406295 := bstep (se 1 (by rfl) ⟨1054721, by rfl⟩ : syracuseStep 1406295 = 2109443) B2109443
theorem B4568413 : Blo 1405522 4568413 := bstep (se 3 (by rfl) ⟨856577, by rfl⟩ : syracuseStep 4568413 = 1713155) B1713155
theorem B1406315 : Blo 1405522 1406315 := bstep (se 1 (by rfl) ⟨1054736, by rfl⟩ : syracuseStep 1406315 = 2109473) B2109473
theorem B1406327 : Blo 1405522 1406327 := bstep (se 1 (by rfl) ⟨1054745, by rfl⟩ : syracuseStep 1406327 = 2109491) B2109491
theorem B1406347 : Blo 1405522 1406347 := bstep (se 1 (by rfl) ⟨1054760, by rfl⟩ : syracuseStep 1406347 = 2109521) B2109521
theorem B2110859 : Blo 1405522 2110859 := bstep (se 1 (by rfl) ⟨1583144, by rfl⟩ : syracuseStep 2110859 = 3166289) B3166289
theorem B1406359 : Blo 1405522 1406359 := bstep (se 1 (by rfl) ⟨1054769, by rfl⟩ : syracuseStep 1406359 = 2109539) B2109539
theorem B2110871 : Blo 1405522 2110871 := bstep (se 1 (by rfl) ⟨1583153, by rfl⟩ : syracuseStep 2110871 = 3166307) B3166307
theorem B1406379 : Blo 1405522 1406379 := bstep (se 1 (by rfl) ⟨1054784, by rfl⟩ : syracuseStep 1406379 = 2109569) B2109569
theorem B1406391 : Blo 1405522 1406391 := bstep (se 1 (by rfl) ⟨1054793, by rfl⟩ : syracuseStep 1406391 = 2109587) B2109587
theorem B1406411 : Blo 1405522 1406411 := bstep (se 1 (by rfl) ⟨1054808, by rfl⟩ : syracuseStep 1406411 = 2109617) B2109617
theorem B1406423 : Blo 1405522 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B2110937 : Blo 1405522 2110937 := bstep (se 2 (by rfl) ⟨791601, by rfl⟩ : syracuseStep 2110937 = 1583203) B1583203
theorem B1406443 : Blo 1405522 1406443 := bstep (se 1 (by rfl) ⟨1054832, by rfl⟩ : syracuseStep 1406443 = 2109665) B2109665
theorem B1406455 : Blo 1405522 1406455 := bstep (se 1 (by rfl) ⟨1054841, by rfl⟩ : syracuseStep 1406455 = 2109683) B2109683
theorem B3003905 : Blo 1405522 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B2373131 : Blo 1405522 2373131 := bstep (se 1 (by rfl) ⟨1779848, by rfl⟩ : syracuseStep 2373131 = 3559697) B3559697
theorem B1406475 : Blo 1405522 1406475 := bstep (se 1 (by rfl) ⟨1054856, by rfl⟩ : syracuseStep 1406475 = 2109713) B2109713
theorem B1406487 : Blo 1405522 1406487 := bstep (se 1 (by rfl) ⟨1054865, by rfl⟩ : syracuseStep 1406487 = 2109731) B2109731
theorem B1406507 : Blo 1405522 1406507 := bstep (se 1 (by rfl) ⟨1054880, by rfl⟩ : syracuseStep 1406507 = 2109761) B2109761
theorem B1406519 : Blo 1405522 1406519 := bstep (se 1 (by rfl) ⟨1054889, by rfl⟩ : syracuseStep 1406519 = 2109779) B2109779
theorem B1406539 : Blo 1405522 1406539 := bstep (se 1 (by rfl) ⟨1054904, by rfl⟩ : syracuseStep 1406539 = 2109809) B2109809
theorem B2111051 : Blo 1405522 2111051 := bstep (se 1 (by rfl) ⟨1583288, by rfl⟩ : syracuseStep 2111051 = 3166577) B3166577
theorem B1406551 : Blo 1405522 1406551 := bstep (se 1 (by rfl) ⟨1054913, by rfl⟩ : syracuseStep 1406551 = 2109827) B2109827
theorem B3380825 : Blo 1405522 3380825 := bstep (se 2 (by rfl) ⟨1267809, by rfl⟩ : syracuseStep 3380825 = 2535619) B2535619
theorem B2111063 : Blo 1405522 2111063 := bstep (se 1 (by rfl) ⟨1583297, by rfl⟩ : syracuseStep 2111063 = 3166595) B3166595
theorem B12826205 : Blo 1405522 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B1406571 : Blo 1405522 1406571 := bstep (se 1 (by rfl) ⟨1054928, by rfl⟩ : syracuseStep 1406571 = 2109857) B2109857
theorem B1406583 : Blo 1405522 1406583 := bstep (se 1 (by rfl) ⟨1054937, by rfl⟩ : syracuseStep 1406583 = 2109875) B2109875
theorem B2373259 : Blo 1405522 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B1406603 : Blo 1405522 1406603 := bstep (se 1 (by rfl) ⟨1054952, by rfl⟩ : syracuseStep 1406603 = 2109905) B2109905
theorem B1406615 : Blo 1405522 1406615 := bstep (se 1 (by rfl) ⟨1054961, by rfl⟩ : syracuseStep 1406615 = 2109923) B2109923
theorem B2111129 : Blo 1405522 2111129 := bstep (se 2 (by rfl) ⟨791673, by rfl⟩ : syracuseStep 2111129 = 1583347) B1583347
theorem B1406635 : Blo 1405522 1406635 := bstep (se 1 (by rfl) ⟨1054976, by rfl⟩ : syracuseStep 1406635 = 2109953) B2109953
theorem B1406647 : Blo 1405522 1406647 := bstep (se 1 (by rfl) ⟨1054985, by rfl⟩ : syracuseStep 1406647 = 2109971) B2109971
theorem B5338817 : Blo 1405522 5338817 := bstep (se 2 (by rfl) ⟨2002056, by rfl⟩ : syracuseStep 5338817 = 4004113) B4004113
theorem B1406667 : Blo 1405522 1406667 := bstep (se 1 (by rfl) ⟨1055000, by rfl⟩ : syracuseStep 1406667 = 2110001) B2110001
theorem B1406679 : Blo 1405522 1406679 := bstep (se 1 (by rfl) ⟨1055009, by rfl⟩ : syracuseStep 1406679 = 2110019) B2110019
theorem B1406699 : Blo 1405522 1406699 := bstep (se 1 (by rfl) ⟨1055024, by rfl⟩ : syracuseStep 1406699 = 2110049) B2110049
theorem B1406711 : Blo 1405522 1406711 := bstep (se 1 (by rfl) ⟨1055033, by rfl⟩ : syracuseStep 1406711 = 2110067) B2110067
theorem B1406731 : Blo 1405522 1406731 := bstep (se 1 (by rfl) ⟨1055048, by rfl⟩ : syracuseStep 1406731 = 2110097) B2110097
theorem B2111243 : Blo 1405522 2111243 := bstep (se 1 (by rfl) ⟨1583432, by rfl⟩ : syracuseStep 2111243 = 3166865) B3166865
theorem B1406743 : Blo 1405522 1406743 := bstep (se 1 (by rfl) ⟨1055057, by rfl⟩ : syracuseStep 1406743 = 2110115) B2110115
theorem B2373401 : Blo 1405522 2373401 := bstep (se 2 (by rfl) ⟨890025, by rfl⟩ : syracuseStep 2373401 = 1780051) B1780051
theorem B1406763 : Blo 1405522 1406763 := bstep (se 1 (by rfl) ⟨1055072, by rfl⟩ : syracuseStep 1406763 = 2110145) B2110145
theorem B1406775 : Blo 1405522 1406775 := bstep (se 1 (by rfl) ⟨1055081, by rfl⟩ : syracuseStep 1406775 = 2110163) B2110163
theorem B1406795 : Blo 1405522 1406795 := bstep (se 1 (by rfl) ⟨1055096, by rfl⟩ : syracuseStep 1406795 = 2110193) B2110193
theorem B1406807 : Blo 1405522 1406807 := bstep (se 1 (by rfl) ⟨1055105, by rfl⟩ : syracuseStep 1406807 = 2110211) B2110211
theorem B1406827 : Blo 1405522 1406827 := bstep (se 1 (by rfl) ⟨1055120, by rfl⟩ : syracuseStep 1406827 = 2110241) B2110241
theorem B1406839 : Blo 1405522 1406839 := bstep (se 1 (by rfl) ⟨1055129, by rfl⟩ : syracuseStep 1406839 = 2110259) B2110259
theorem B1406859 : Blo 1405522 1406859 := bstep (se 1 (by rfl) ⟨1055144, by rfl⟩ : syracuseStep 1406859 = 2110289) B2110289
theorem B1406871 : Blo 1405522 1406871 := bstep (se 1 (by rfl) ⟨1055153, by rfl⟩ : syracuseStep 1406871 = 2110307) B2110307
theorem B3561367 : Blo 1405522 3561367 := bstep (se 1 (by rfl) ⟨2671025, by rfl⟩ : syracuseStep 3561367 = 5342051) B5342051
theorem B2373529 : Blo 1405522 2373529 := bstep (se 2 (by rfl) ⟨890073, by rfl⟩ : syracuseStep 2373529 = 1780147) B1780147
theorem B1406891 : Blo 1405522 1406891 := bstep (se 1 (by rfl) ⟨1055168, by rfl⟩ : syracuseStep 1406891 = 2110337) B2110337
theorem B1406903 : Blo 1405522 1406903 := bstep (se 1 (by rfl) ⟨1055177, by rfl⟩ : syracuseStep 1406903 = 2110355) B2110355
theorem B1406923 : Blo 1405522 1406923 := bstep (se 1 (by rfl) ⟨1055192, by rfl⟩ : syracuseStep 1406923 = 2110385) B2110385
theorem B1406935 : Blo 1405522 1406935 := bstep (se 1 (by rfl) ⟨1055201, by rfl⟩ : syracuseStep 1406935 = 2110403) B2110403
theorem B4003805 : Blo 1405522 4003805 := bstep (se 3 (by rfl) ⟨750713, by rfl⟩ : syracuseStep 4003805 = 1501427) B1501427
theorem B5781469 : Blo 1405522 5781469 := bstep (se 3 (by rfl) ⟨1084025, by rfl⟩ : syracuseStep 5781469 = 2168051) B2168051
theorem B1406955 : Blo 1405522 1406955 := bstep (se 1 (by rfl) ⟨1055216, by rfl⟩ : syracuseStep 1406955 = 2110433) B2110433
theorem B1406967 : Blo 1405522 1406967 := bstep (se 1 (by rfl) ⟨1055225, by rfl⟩ : syracuseStep 1406967 = 2110451) B2110451
theorem B1406987 : Blo 1405522 1406987 := bstep (se 1 (by rfl) ⟨1055240, by rfl⟩ : syracuseStep 1406987 = 2110481) B2110481
theorem B1406999 : Blo 1405522 1406999 := bstep (se 1 (by rfl) ⟨1055249, by rfl⟩ : syracuseStep 1406999 = 2110499) B2110499
theorem B1407019 : Blo 1405522 1407019 := bstep (se 1 (by rfl) ⟨1055264, by rfl⟩ : syracuseStep 1407019 = 2110529) B2110529
theorem B1407031 : Blo 1405522 1407031 := bstep (se 1 (by rfl) ⟨1055273, by rfl⟩ : syracuseStep 1407031 = 2110547) B2110547
theorem B2668619 : Blo 1405522 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B1407051 : Blo 1405522 1407051 := bstep (se 1 (by rfl) ⟨1055288, by rfl⟩ : syracuseStep 1407051 = 2110577) B2110577
theorem B6010955 : Blo 1405522 6010955 := bstep (se 1 (by rfl) ⟨4508216, by rfl⟩ : syracuseStep 6010955 = 9016433) B9016433
theorem B1407063 : Blo 1405522 1407063 := bstep (se 1 (by rfl) ⟨1055297, by rfl⟩ : syracuseStep 1407063 = 2110595) B2110595
theorem B1407083 : Blo 1405522 1407083 := bstep (se 1 (by rfl) ⟨1055312, by rfl⟩ : syracuseStep 1407083 = 2110625) B2110625
theorem B1407095 : Blo 1405522 1407095 := bstep (se 1 (by rfl) ⟨1055321, by rfl⟩ : syracuseStep 1407095 = 2110643) B2110643
theorem B1407115 : Blo 1405522 1407115 := bstep (se 1 (by rfl) ⟨1055336, by rfl⟩ : syracuseStep 1407115 = 2110673) B2110673
theorem B44480663 : Blo 1405522 44480663 := bstep (se 1 (by rfl) ⟨33360497, by rfl⟩ : syracuseStep 44480663 = 66720995) B66720995
theorem B1407127 : Blo 1405522 1407127 := bstep (se 1 (by rfl) ⟨1055345, by rfl⟩ : syracuseStep 1407127 = 2110691) B2110691
theorem B1407147 : Blo 1405522 1407147 := bstep (se 1 (by rfl) ⟨1055360, by rfl⟩ : syracuseStep 1407147 = 2110721) B2110721
theorem B28850357 : Blo 1405522 28850357 := bstep (se 5 (by rfl) ⟨1352360, by rfl⟩ : syracuseStep 28850357 = 2704721) B2704721
theorem B1407159 : Blo 1405522 1407159 := bstep (se 1 (by rfl) ⟨1055369, by rfl⟩ : syracuseStep 1407159 = 2110739) B2110739
theorem B1407179 : Blo 1405522 1407179 := bstep (se 1 (by rfl) ⟨1055384, by rfl⟩ : syracuseStep 1407179 = 2110769) B2110769
theorem B4749515 : Blo 1405522 4749515 := bstep (se 1 (by rfl) ⟨3562136, by rfl⟩ : syracuseStep 4749515 = 7124273) B7124273
theorem B3004631 : Blo 1405522 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B1407191 : Blo 1405522 1407191 := bstep (se 1 (by rfl) ⟨1055393, by rfl⟩ : syracuseStep 1407191 = 2110787) B2110787
theorem B1407211 : Blo 1405522 1407211 := bstep (se 1 (by rfl) ⟨1055408, by rfl⟩ : syracuseStep 1407211 = 2110817) B2110817
theorem B1407223 : Blo 1405522 1407223 := bstep (se 1 (by rfl) ⟨1055417, by rfl⟩ : syracuseStep 1407223 = 2110835) B2110835
theorem B2668801 : Blo 1405522 2668801 := bstep (se 2 (by rfl) ⟨1000800, by rfl⟩ : syracuseStep 2668801 = 2001601) B2001601
theorem B1407243 : Blo 1405522 1407243 := bstep (se 1 (by rfl) ⟨1055432, by rfl⟩ : syracuseStep 1407243 = 2110865) B2110865
theorem B3799319 : Blo 1405522 3799319 := bstep (se 1 (by rfl) ⟨2849489, by rfl⟩ : syracuseStep 3799319 = 5698979) B5698979
theorem B1407255 : Blo 1405522 1407255 := bstep (se 1 (by rfl) ⟨1055441, by rfl⟩ : syracuseStep 1407255 = 2110883) B2110883
theorem B1407275 : Blo 1405522 1407275 := bstep (se 1 (by rfl) ⟨1055456, by rfl⟩ : syracuseStep 1407275 = 2110913) B2110913
theorem B4004147 : Blo 1405522 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B1407287 : Blo 1405522 1407287 := bstep (se 1 (by rfl) ⟨1055465, by rfl⟩ : syracuseStep 1407287 = 2110931) B2110931
theorem B12351809 : Blo 1405522 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B3209537 : Blo 1405522 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B3561803 : Blo 1405522 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1407307 : Blo 1405522 1407307 := bstep (se 1 (by rfl) ⟨1055480, by rfl⟩ : syracuseStep 1407307 = 2110961) B2110961
theorem B1407319 : Blo 1405522 1407319 := bstep (se 1 (by rfl) ⟨1055489, by rfl⟩ : syracuseStep 1407319 = 2110979) B2110979
theorem B1407339 : Blo 1405522 1407339 := bstep (se 1 (by rfl) ⟨1055504, by rfl⟩ : syracuseStep 1407339 = 2111009) B2111009
theorem B1407351 : Blo 1405522 1407351 := bstep (se 1 (by rfl) ⟨1055513, by rfl⟩ : syracuseStep 1407351 = 2111027) B2111027
theorem B1407371 : Blo 1405522 1407371 := bstep (se 1 (by rfl) ⟨1055528, by rfl⟩ : syracuseStep 1407371 = 2111057) B2111057
theorem B1407383 : Blo 1405522 1407383 := bstep (se 1 (by rfl) ⟨1055537, by rfl⟩ : syracuseStep 1407383 = 2111075) B2111075
theorem B1407403 : Blo 1405522 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B1407415 : Blo 1405522 1407415 := bstep (se 1 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 1407415 = 2111123) B2111123
theorem B1407435 : Blo 1405522 1407435 := bstep (se 1 (by rfl) ⟨1055576, by rfl⟩ : syracuseStep 1407435 = 2111153) B2111153
theorem B2374103 : Blo 1405522 2374103 := bstep (se 1 (by rfl) ⟨1780577, by rfl⟩ : syracuseStep 2374103 = 3561155) B3561155
theorem B1407447 : Blo 1405522 1407447 := bstep (se 1 (by rfl) ⟨1055585, by rfl⟩ : syracuseStep 1407447 = 2111171) B2111171
theorem B4504025 : Blo 1405522 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B4749785 : Blo 1405522 4749785 := bstep (se 2 (by rfl) ⟨1781169, by rfl⟩ : syracuseStep 4749785 = 3562339) B3562339
theorem B1407467 : Blo 1405522 1407467 := bstep (se 1 (by rfl) ⟨1055600, by rfl⟩ : syracuseStep 1407467 = 2111201) B2111201
theorem B1407479 : Blo 1405522 1407479 := bstep (se 1 (by rfl) ⟨1055609, by rfl⟩ : syracuseStep 1407479 = 2111219) B2111219
theorem B1407499 : Blo 1405522 1407499 := bstep (se 1 (by rfl) ⟨1055624, by rfl⟩ : syracuseStep 1407499 = 2111249) B2111249
theorem B1407511 : Blo 1405522 1407511 := bstep (se 1 (by rfl) ⟨1055633, by rfl⟩ : syracuseStep 1407511 = 2111267) B2111267
theorem B10820141 : Blo 1405522 10820141 := bstep (se 3 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 10820141 = 4057553) B4057553
theorem B7125569 : Blo 1405522 7125569 := bstep (se 2 (by rfl) ⟨2672088, by rfl⟩ : syracuseStep 7125569 = 5344177) B5344177
theorem B2374231 : Blo 1405522 2374231 := bstep (se 1 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 2374231 = 3561347) B3561347
theorem B10558129 : Blo 1405522 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B2669249 : Blo 1405522 2669249 := bstep (se 2 (by rfl) ⟨1000968, by rfl⟩ : syracuseStep 2669249 = 2001937) B2001937
theorem B3562177 : Blo 1405522 3562177 := bstep (se 2 (by rfl) ⟨1335816, by rfl⟩ : syracuseStep 3562177 = 2671633) B2671633
theorem B5340077 : Blo 1405522 5340077 := bstep (se 3 (by rfl) ⟨1001264, by rfl⟩ : syracuseStep 5340077 = 2002529) B2002529
theorem B3251137 : Blo 1405522 3251137 := bstep (se 2 (by rfl) ⟨1219176, by rfl⟩ : syracuseStep 3251137 = 2438353) B2438353
theorem B5340107 : Blo 1405522 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B2669591 : Blo 1405522 2669591 := bstep (se 1 (by rfl) ⟨2002193, by rfl⟩ : syracuseStep 2669591 = 4004387) B4004387
theorem B6011927 : Blo 1405522 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B8010845 : Blo 1405522 8010845 := bstep (se 3 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 8010845 = 3004067) B3004067
theorem B7117955 : Blo 1405522 7117955 := bstep (se 1 (by rfl) ⟨5338466, by rfl⟩ : syracuseStep 7117955 = 10676933) B10676933
theorem B29277335 : Blo 1405522 29277335 := bstep (se 1 (by rfl) ⟨21958001, by rfl⟩ : syracuseStep 29277335 = 43916003) B43916003
theorem B4062359 : Blo 1405522 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B2137241 : Blo 1405522 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B2374859 : Blo 1405522 2374859 := bstep (se 1 (by rfl) ⟨1781144, by rfl⟩ : syracuseStep 2374859 = 3562289) B3562289
theorem B3562775 : Blo 1405522 3562775 := bstep (se 1 (by rfl) ⟨2672081, by rfl⟩ : syracuseStep 3562775 = 5344163) B5344163
theorem B2374987 : Blo 1405522 2374987 := bstep (se 1 (by rfl) ⟨1781240, by rfl⟩ : syracuseStep 2374987 = 3562481) B3562481
theorem B2375129 : Blo 1405522 2375129 := bstep (se 2 (by rfl) ⟨890673, by rfl⟩ : syracuseStep 2375129 = 1781347) B1781347
theorem B8560145 : Blo 1405522 8560145 := bstep (se 2 (by rfl) ⟨3210054, by rfl⟩ : syracuseStep 8560145 = 6420109) B6420109
theorem B5340761 : Blo 1405522 5340761 := bstep (se 2 (by rfl) ⟨2002785, by rfl⟩ : syracuseStep 5340761 = 4005571) B4005571
theorem B2670259 : Blo 1405522 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B11402957 : Blo 1405522 11402957 := bstep (se 3 (by rfl) ⟨2138054, by rfl⟩ : syracuseStep 11402957 = 4276109) B4276109
theorem B1425163 : Blo 1405522 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B5341079 : Blo 1405522 5341079 := bstep (se 1 (by rfl) ⟨4005809, by rfl⟩ : syracuseStep 5341079 = 8011619) B8011619
theorem B6758423 : Blo 1405522 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B2252935 : Blo 1405522 2252935 := bstep (se 1 (by rfl) ⟨1689701, by rfl⟩ : syracuseStep 2252935 = 3379403) B3379403
theorem B5488877 : Blo 1405522 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B7602491 : Blo 1405522 7602491 := bstep (se 1 (by rfl) ⟨5701868, by rfl⟩ : syracuseStep 7602491 = 11403737) B11403737
theorem B13525379 : Blo 1405522 13525379 := bstep (se 1 (by rfl) ⟨10144034, by rfl⟩ : syracuseStep 13525379 = 20288069) B20288069
theorem B2253191 : Blo 1405522 2253191 := bstep (se 1 (by rfl) ⟨1689893, by rfl⟩ : syracuseStep 2253191 = 3379787) B3379787
theorem B7119251 : Blo 1405522 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B2670995 : Blo 1405522 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B2671049 : Blo 1405522 2671049 := bstep (se 2 (by rfl) ⟨1001643, by rfl⟩ : syracuseStep 2671049 = 2003287) B2003287
theorem B3424769 : Blo 1405522 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1581583 : Blo 1405522 1581583 := bstep (se 1 (by rfl) ⟨1186187, by rfl⟩ : syracuseStep 1581583 = 2372375) B2372375
theorem B2671147 : Blo 1405522 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B3162743 : Blo 1405522 3162743 := bstep (se 1 (by rfl) ⟨2372057, by rfl⟩ : syracuseStep 3162743 = 4744115) B4744115
theorem B28861109 : Blo 1405522 28861109 := bstep (se 5 (by rfl) ⟨1352864, by rfl⟩ : syracuseStep 28861109 = 2705729) B2705729
theorem B16016129 : Blo 1405522 16016129 := bstep (se 2 (by rfl) ⟨6006048, by rfl⟩ : syracuseStep 16016129 = 12012097) B12012097
theorem B1712911 : Blo 1405522 1712911 := bstep (se 1 (by rfl) ⟨1284683, by rfl⟩ : syracuseStep 1712911 = 2569367) B2569367
theorem B2671375 : Blo 1405522 2671375 := bstep (se 1 (by rfl) ⟨2003531, by rfl⟩ : syracuseStep 2671375 = 4007063) B4007063
theorem B3162923 : Blo 1405522 3162923 := bstep (se 1 (by rfl) ⟨2372192, by rfl⟩ : syracuseStep 3162923 = 4744385) B4744385
theorem B10683251 : Blo 1405522 10683251 := bstep (se 1 (by rfl) ⟨8012438, by rfl⟩ : syracuseStep 10683251 = 16024877) B16024877
theorem B6005639 : Blo 1405522 6005639 := bstep (se 1 (by rfl) ⟨4504229, by rfl⟩ : syracuseStep 6005639 = 9008459) B9008459
theorem B8012803 : Blo 1405522 8012803 := bstep (se 1 (by rfl) ⟨6009602, by rfl⟩ : syracuseStep 8012803 = 12019205) B12019205
theorem B1582087 : Blo 1405522 1582087 := bstep (se 1 (by rfl) ⟨1186565, by rfl⟩ : syracuseStep 1582087 = 2373131) B2373131
theorem B5342219 : Blo 1405522 5342219 := bstep (se 1 (by rfl) ⟨4006664, by rfl⟩ : syracuseStep 5342219 = 8013329) B8013329
theorem B1688635 : Blo 1405522 1688635 := bstep (se 1 (by rfl) ⟨1266476, by rfl⟩ : syracuseStep 1688635 = 2532953) B2532953
theorem B3163283 : Blo 1405522 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B1582267 : Blo 1405522 1582267 := bstep (se 1 (by rfl) ⟨1186700, by rfl⟩ : syracuseStep 1582267 = 2373401) B2373401
theorem B3163337 : Blo 1405522 3163337 := bstep (se 2 (by rfl) ⟨1186251, by rfl⟩ : syracuseStep 3163337 = 2372503) B2372503
theorem B4334849 : Blo 1405522 4334849 := bstep (se 2 (by rfl) ⟨1625568, by rfl⟩ : syracuseStep 4334849 = 3251137) B3251137
theorem B200263043 : Blo 1405522 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B1779079 : Blo 1405522 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B4007303 : Blo 1405522 4007303 := bstep (se 1 (by rfl) ⟨3005477, by rfl⟩ : syracuseStep 4007303 = 6010955) B6010955
theorem B4744601 : Blo 1405522 4744601 := bstep (se 2 (by rfl) ⟨1779225, by rfl⟩ : syracuseStep 4744601 = 3558451) B3558451
theorem B12182993 : Blo 1405522 12182993 := bstep (se 2 (by rfl) ⟨4568622, by rfl⟩ : syracuseStep 12182993 = 9137245) B9137245
theorem B2139691 : Blo 1405522 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B1582735 : Blo 1405522 1582735 := bstep (se 1 (by rfl) ⟨1187051, by rfl⟩ : syracuseStep 1582735 = 2374103) B2374103
theorem B1779499 : Blo 1405522 1779499 := bstep (se 1 (by rfl) ⟨1334624, by rfl⟩ : syracuseStep 1779499 = 2669249) B2669249
theorem B3164039 : Blo 1405522 3164039 := bstep (se 1 (by rfl) ⟨2373029, by rfl⟩ : syracuseStep 3164039 = 4746059) B4746059
theorem B1804219 : Blo 1405522 1804219 := bstep (se 1 (by rfl) ⟨1353164, by rfl⟩ : syracuseStep 1804219 = 2706329) B2706329
theorem B1779727 : Blo 1405522 1779727 := bstep (se 1 (by rfl) ⟨1334795, by rfl⟩ : syracuseStep 1779727 = 2669591) B2669591
theorem B4007951 : Blo 1405522 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B3164219 : Blo 1405522 3164219 := bstep (se 1 (by rfl) ⟨2373164, by rfl⟩ : syracuseStep 3164219 = 4746329) B4746329
theorem B4745303 : Blo 1405522 4745303 := bstep (se 1 (by rfl) ⟨3558977, by rfl⟩ : syracuseStep 4745303 = 7117955) B7117955
theorem B1583239 : Blo 1405522 1583239 := bstep (se 1 (by rfl) ⟨1187429, by rfl⟩ : syracuseStep 1583239 = 2374859) B2374859
theorem B3164345 : Blo 1405522 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B8554697 : Blo 1405522 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B3377423 : Blo 1405522 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B1583419 : Blo 1405522 1583419 := bstep (se 1 (by rfl) ⟨1187564, by rfl⟩ : syracuseStep 1583419 = 2375129) B2375129
theorem B3164687 : Blo 1405522 3164687 := bstep (se 1 (by rfl) ⟨2373515, by rfl⟩ : syracuseStep 3164687 = 4747031) B4747031
theorem B3164705 : Blo 1405522 3164705 := bstep (se 2 (by rfl) ⟨1186764, by rfl⟩ : syracuseStep 3164705 = 2373529) B2373529
theorem B4745789 : Blo 1405522 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B1780471 : Blo 1405522 1780471 := bstep (se 1 (by rfl) ⟨1335353, by rfl⟩ : syracuseStep 1780471 = 2670707) B2670707
theorem B6007553 : Blo 1405522 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B10136335 : Blo 1405522 10136335 := bstep (se 1 (by rfl) ⟨7602251, by rfl⟩ : syracuseStep 10136335 = 15204503) B15204503
theorem B3165047 : Blo 1405522 3165047 := bstep (se 1 (by rfl) ⟨2373785, by rfl⟩ : syracuseStep 3165047 = 4747571) B4747571
theorem B2108303 : Blo 1405522 2108303 := bstep (se 1 (by rfl) ⟨1581227, by rfl⟩ : syracuseStep 2108303 = 3162455) B3162455
theorem B2108345 : Blo 1405522 2108345 := bstep (se 2 (by rfl) ⟨790629, by rfl⟩ : syracuseStep 2108345 = 1581259) B1581259
theorem B3558401 : Blo 1405522 3558401 := bstep (se 2 (by rfl) ⟨1334400, by rfl⟩ : syracuseStep 3558401 = 2668801) B2668801
theorem B2108423 : Blo 1405522 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B2108459 : Blo 1405522 2108459 := bstep (se 1 (by rfl) ⟨1581344, by rfl⟩ : syracuseStep 2108459 = 3162689) B3162689
theorem B3165227 : Blo 1405522 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B1780795 : Blo 1405522 1780795 := bstep (se 1 (by rfl) ⟨1335596, by rfl⟩ : syracuseStep 1780795 = 2671193) B2671193
theorem B78072893 : Blo 1405522 78072893 := bstep (se 3 (by rfl) ⟨14638667, by rfl⟩ : syracuseStep 78072893 = 29277335) B29277335
theorem B2108489 : Blo 1405522 2108489 := bstep (se 2 (by rfl) ⟨790683, by rfl⟩ : syracuseStep 2108489 = 1581367) B1581367
theorem B6007895 : Blo 1405522 6007895 := bstep (se 1 (by rfl) ⟨4505921, by rfl⟩ : syracuseStep 6007895 = 9011843) B9011843
theorem B76934285 : Blo 1405522 76934285 := bstep (se 3 (by rfl) ⟨14425178, by rfl⟩ : syracuseStep 76934285 = 28850357) B28850357
theorem B64990349 : Blo 1405522 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B2108603 : Blo 1405522 2108603 := bstep (se 1 (by rfl) ⟨1581452, by rfl⟩ : syracuseStep 2108603 = 3162905) B3162905
theorem B2108663 : Blo 1405522 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B2108687 : Blo 1405522 2108687 := bstep (se 1 (by rfl) ⟨1581515, by rfl⟩ : syracuseStep 2108687 = 3163031) B3163031
theorem B2108729 : Blo 1405522 2108729 := bstep (se 2 (by rfl) ⟨790773, by rfl⟩ : syracuseStep 2108729 = 1581547) B1581547
theorem B8006971 : Blo 1405522 8006971 := bstep (se 1 (by rfl) ⟨6005228, by rfl⟩ : syracuseStep 8006971 = 12010457) B12010457
theorem B8015219 : Blo 1405522 8015219 := bstep (se 1 (by rfl) ⟨6011414, by rfl⟩ : syracuseStep 8015219 = 12022829) B12022829
theorem B3558775 : Blo 1405522 3558775 := bstep (se 1 (by rfl) ⟨2669081, by rfl⟩ : syracuseStep 3558775 = 5338163) B5338163
theorem B2108807 : Blo 1405522 2108807 := bstep (se 1 (by rfl) ⟨1581605, by rfl⟩ : syracuseStep 2108807 = 3163211) B3163211
theorem B3165587 : Blo 1405522 3165587 := bstep (se 1 (by rfl) ⟨2374190, by rfl⟩ : syracuseStep 3165587 = 4748381) B4748381
theorem B7122329 : Blo 1405522 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B2108843 : Blo 1405522 2108843 := bstep (se 1 (by rfl) ⟨1581632, by rfl⟩ : syracuseStep 2108843 = 3163265) B3163265
theorem B2108873 : Blo 1405522 2108873 := bstep (se 2 (by rfl) ⟨790827, by rfl⟩ : syracuseStep 2108873 = 1581655) B1581655
theorem B3165641 : Blo 1405522 3165641 := bstep (se 2 (by rfl) ⟨1187115, by rfl⟩ : syracuseStep 3165641 = 2374231) B2374231
theorem B15199787 : Blo 1405522 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B1781291 : Blo 1405522 1781291 := bstep (se 1 (by rfl) ⟨1335968, by rfl⟩ : syracuseStep 1781291 = 2671937) B2671937
theorem B2108987 : Blo 1405522 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B14077505 : Blo 1405522 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B16019045 : Blo 1405522 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B2109047 : Blo 1405522 2109047 := bstep (se 1 (by rfl) ⟨1581785, by rfl⟩ : syracuseStep 2109047 = 3163571) B3163571
theorem B2109071 : Blo 1405522 2109071 := bstep (se 1 (by rfl) ⟨1581803, by rfl⟩ : syracuseStep 2109071 = 3163607) B3163607
theorem B2109113 : Blo 1405522 2109113 := bstep (se 2 (by rfl) ⟨790917, by rfl⟩ : syracuseStep 2109113 = 1581835) B1581835
theorem B2109191 : Blo 1405522 2109191 := bstep (se 1 (by rfl) ⟨1581893, by rfl⟩ : syracuseStep 2109191 = 3163787) B3163787
theorem B3559211 : Blo 1405522 3559211 := bstep (se 1 (by rfl) ⟨2669408, by rfl⟩ : syracuseStep 3559211 = 5338817) B5338817
theorem B2109227 : Blo 1405522 2109227 := bstep (se 1 (by rfl) ⟨1581920, by rfl⟩ : syracuseStep 2109227 = 3163841) B3163841
theorem B2109257 : Blo 1405522 2109257 := bstep (se 2 (by rfl) ⟨790971, by rfl⟩ : syracuseStep 2109257 = 1581943) B1581943
theorem B4747193 : Blo 1405522 4747193 := bstep (se 2 (by rfl) ⟨1780197, by rfl⟩ : syracuseStep 4747193 = 3560395) B3560395
theorem B2109371 : Blo 1405522 2109371 := bstep (se 1 (by rfl) ⟨1582028, by rfl⟩ : syracuseStep 2109371 = 3164057) B3164057
theorem B2109431 : Blo 1405522 2109431 := bstep (se 1 (by rfl) ⟨1582073, by rfl⟩ : syracuseStep 2109431 = 3164147) B3164147
theorem B2404367 : Blo 1405522 2404367 := bstep (se 1 (by rfl) ⟨1803275, by rfl⟩ : syracuseStep 2404367 = 3606551) B3606551
theorem B2109455 : Blo 1405522 2109455 := bstep (se 1 (by rfl) ⟨1582091, by rfl⟩ : syracuseStep 2109455 = 3164183) B3164183
theorem B8548375 : Blo 1405522 8548375 := bstep (se 1 (by rfl) ⟨6411281, by rfl⟩ : syracuseStep 8548375 = 12822563) B12822563
theorem B2109497 : Blo 1405522 2109497 := bstep (se 2 (by rfl) ⟨791061, by rfl⟩ : syracuseStep 2109497 = 1582123) B1582123
theorem B2109575 : Blo 1405522 2109575 := bstep (se 1 (by rfl) ⟨1582181, by rfl⟩ : syracuseStep 2109575 = 3164363) B3164363
theorem B3166343 : Blo 1405522 3166343 := bstep (se 1 (by rfl) ⟨2374757, by rfl⟩ : syracuseStep 3166343 = 4749515) B4749515
theorem B2003087 : Blo 1405522 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B2109611 : Blo 1405522 2109611 := bstep (se 1 (by rfl) ⟨1582208, by rfl⟩ : syracuseStep 2109611 = 3164417) B3164417
theorem B2109641 : Blo 1405522 2109641 := bstep (se 2 (by rfl) ⟨791115, by rfl⟩ : syracuseStep 2109641 = 1582231) B1582231
theorem B9015533 : Blo 1405522 9015533 := bstep (se 3 (by rfl) ⟨1690412, by rfl⟩ : syracuseStep 9015533 = 3380825) B3380825
theorem B2371855 : Blo 1405522 2371855 := bstep (se 1 (by rfl) ⟨1778891, by rfl⟩ : syracuseStep 2371855 = 3557783) B3557783
theorem B5337359 : Blo 1405522 5337359 := bstep (se 1 (by rfl) ⟨4003019, by rfl⟩ : syracuseStep 5337359 = 8006039) B8006039
theorem B3002683 : Blo 1405522 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B2109755 : Blo 1405522 2109755 := bstep (se 1 (by rfl) ⟨1582316, by rfl⟩ : syracuseStep 2109755 = 3164633) B3164633
theorem B3166523 : Blo 1405522 3166523 := bstep (se 1 (by rfl) ⟨2374892, by rfl⟩ : syracuseStep 3166523 = 4749785) B4749785
theorem B7213427 : Blo 1405522 7213427 := bstep (se 1 (by rfl) ⟨5410070, by rfl⟩ : syracuseStep 7213427 = 10820141) B10820141
theorem B2109815 : Blo 1405522 2109815 := bstep (se 1 (by rfl) ⟨1582361, by rfl⟩ : syracuseStep 2109815 = 3164723) B3164723
theorem B2109839 : Blo 1405522 2109839 := bstep (se 1 (by rfl) ⟨1582379, by rfl⟩ : syracuseStep 2109839 = 3164759) B3164759
theorem B2109881 : Blo 1405522 2109881 := bstep (se 2 (by rfl) ⟨791205, by rfl⟩ : syracuseStep 2109881 = 1582411) B1582411
theorem B3166649 : Blo 1405522 3166649 := bstep (se 2 (by rfl) ⟨1187493, by rfl⟩ : syracuseStep 3166649 = 2374987) B2374987
theorem B6091217 : Blo 1405522 6091217 := bstep (se 2 (by rfl) ⟨2284206, by rfl⟩ : syracuseStep 6091217 = 4568413) B4568413
theorem B2109959 : Blo 1405522 2109959 := bstep (se 1 (by rfl) ⟨1582469, by rfl⟩ : syracuseStep 2109959 = 3164939) B3164939
theorem B4747787 : Blo 1405522 4747787 := bstep (se 1 (by rfl) ⟨3560840, by rfl⟩ : syracuseStep 4747787 = 7121681) B7121681
theorem B2109995 : Blo 1405522 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B2110025 : Blo 1405522 2110025 := bstep (se 2 (by rfl) ⟨791259, by rfl⟩ : syracuseStep 2110025 = 1582519) B1582519
theorem B3560051 : Blo 1405522 3560051 := bstep (se 1 (by rfl) ⟨2670038, by rfl⟩ : syracuseStep 3560051 = 5340077) B5340077
theorem B4747895 : Blo 1405522 4747895 := bstep (se 1 (by rfl) ⟨3560921, by rfl⟩ : syracuseStep 4747895 = 7121843) B7121843
theorem B1405575 : Blo 1405522 1405575 := bstep (se 1 (by rfl) ⟨1054181, by rfl⟩ : syracuseStep 1405575 = 2108363) B2108363
theorem B3560071 : Blo 1405522 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B1405583 : Blo 1405522 1405583 := bstep (se 1 (by rfl) ⟨1054187, by rfl⟩ : syracuseStep 1405583 = 2108375) B2108375
theorem B1405627 : Blo 1405522 1405627 := bstep (se 1 (by rfl) ⟨1054220, by rfl⟩ : syracuseStep 1405627 = 2108441) B2108441
theorem B2110139 : Blo 1405522 2110139 := bstep (se 1 (by rfl) ⟨1582604, by rfl⟩ : syracuseStep 2110139 = 3165209) B3165209
theorem B7213805 : Blo 1405522 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B8008429 : Blo 1405522 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B2110199 : Blo 1405522 2110199 := bstep (se 1 (by rfl) ⟨1582649, by rfl⟩ : syracuseStep 2110199 = 3165299) B3165299
theorem B1405703 : Blo 1405522 1405703 := bstep (se 1 (by rfl) ⟨1054277, by rfl⟩ : syracuseStep 1405703 = 2108555) B2108555
theorem B1405711 : Blo 1405522 1405711 := bstep (se 1 (by rfl) ⟨1054283, by rfl⟩ : syracuseStep 1405711 = 2108567) B2108567
theorem B2110223 : Blo 1405522 2110223 := bstep (se 1 (by rfl) ⟨1582667, by rfl⟩ : syracuseStep 2110223 = 3165335) B3165335
theorem B2708239 : Blo 1405522 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B2372395 : Blo 1405522 2372395 := bstep (se 1 (by rfl) ⟨1779296, by rfl⟩ : syracuseStep 2372395 = 3558593) B3558593
theorem B2110265 : Blo 1405522 2110265 := bstep (se 2 (by rfl) ⟨791349, by rfl⟩ : syracuseStep 2110265 = 1582699) B1582699
theorem B1405755 : Blo 1405522 1405755 := bstep (se 1 (by rfl) ⟨1054316, by rfl⟩ : syracuseStep 1405755 = 2108633) B2108633
theorem B1405831 : Blo 1405522 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B2110343 : Blo 1405522 2110343 := bstep (se 1 (by rfl) ⟨1582757, by rfl⟩ : syracuseStep 2110343 = 3165515) B3165515
theorem B1405839 : Blo 1405522 1405839 := bstep (se 1 (by rfl) ⟨1054379, by rfl⟩ : syracuseStep 1405839 = 2108759) B2108759
theorem B3560345 : Blo 1405522 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B2110379 : Blo 1405522 2110379 := bstep (se 1 (by rfl) ⟨1582784, by rfl⟩ : syracuseStep 2110379 = 3165569) B3165569
theorem B2372537 : Blo 1405522 2372537 := bstep (se 2 (by rfl) ⟨889701, by rfl⟩ : syracuseStep 2372537 = 1779403) B1779403
theorem B1405883 : Blo 1405522 1405883 := bstep (se 1 (by rfl) ⟨1054412, by rfl⟩ : syracuseStep 1405883 = 2108825) B2108825
theorem B2110409 : Blo 1405522 2110409 := bstep (se 2 (by rfl) ⟨791403, by rfl⟩ : syracuseStep 2110409 = 1582807) B1582807
theorem B15209477 : Blo 1405522 15209477 := bstep (se 4 (by rfl) ⟨1425888, by rfl⟩ : syracuseStep 15209477 = 2851777) B2851777
theorem B1405959 : Blo 1405522 1405959 := bstep (se 1 (by rfl) ⟨1054469, by rfl⟩ : syracuseStep 1405959 = 2108939) B2108939
theorem B5706763 : Blo 1405522 5706763 := bstep (se 1 (by rfl) ⟨4280072, by rfl⟩ : syracuseStep 5706763 = 8560145) B8560145
theorem B1405967 : Blo 1405522 1405967 := bstep (se 1 (by rfl) ⟨1054475, by rfl⟩ : syracuseStep 1405967 = 2108951) B2108951
theorem B16020503 : Blo 1405522 16020503 := bstep (se 1 (by rfl) ⟨12015377, by rfl⟩ : syracuseStep 16020503 = 24030755) B24030755
theorem B1406011 : Blo 1405522 1406011 := bstep (se 1 (by rfl) ⟨1054508, by rfl⟩ : syracuseStep 1406011 = 2109017) B2109017
theorem B3560507 : Blo 1405522 3560507 := bstep (se 1 (by rfl) ⟨2670380, by rfl⟩ : syracuseStep 3560507 = 5340761) B5340761
theorem B2110523 : Blo 1405522 2110523 := bstep (se 1 (by rfl) ⟨1582892, by rfl⟩ : syracuseStep 2110523 = 3165785) B3165785
theorem B2110583 : Blo 1405522 2110583 := bstep (se 1 (by rfl) ⟨1582937, by rfl⟩ : syracuseStep 2110583 = 3165875) B3165875
theorem B1406087 : Blo 1405522 1406087 := bstep (se 1 (by rfl) ⟨1054565, by rfl⟩ : syracuseStep 1406087 = 2109131) B2109131
theorem B1406095 : Blo 1405522 1406095 := bstep (se 1 (by rfl) ⟨1054571, by rfl⟩ : syracuseStep 1406095 = 2109143) B2109143
theorem B2110607 : Blo 1405522 2110607 := bstep (se 1 (by rfl) ⟨1582955, by rfl⟩ : syracuseStep 2110607 = 3165911) B3165911
theorem B2110649 : Blo 1405522 2110649 := bstep (se 2 (by rfl) ⟨791493, by rfl⟩ : syracuseStep 2110649 = 1582987) B1582987
theorem B1406139 : Blo 1405522 1406139 := bstep (se 1 (by rfl) ⟨1054604, by rfl⟩ : syracuseStep 1406139 = 2109209) B2109209
theorem B4748489 : Blo 1405522 4748489 := bstep (se 2 (by rfl) ⟨1780683, by rfl⟩ : syracuseStep 4748489 = 3561367) B3561367
theorem B15217865 : Blo 1405522 15217865 := bstep (se 2 (by rfl) ⟨5706699, by rfl⟩ : syracuseStep 15217865 = 11413399) B11413399
theorem B1406215 : Blo 1405522 1406215 := bstep (se 1 (by rfl) ⟨1054661, by rfl⟩ : syracuseStep 1406215 = 2109323) B2109323
theorem B2110727 : Blo 1405522 2110727 := bstep (se 1 (by rfl) ⟨1583045, by rfl⟩ : syracuseStep 2110727 = 3166091) B3166091
theorem B1406223 : Blo 1405522 1406223 := bstep (se 1 (by rfl) ⟨1054667, by rfl⟩ : syracuseStep 1406223 = 2109335) B2109335
theorem B3560719 : Blo 1405522 3560719 := bstep (se 1 (by rfl) ⟨2670539, by rfl⟩ : syracuseStep 3560719 = 5341079) B5341079
theorem B2110763 : Blo 1405522 2110763 := bstep (se 1 (by rfl) ⟨1583072, by rfl⟩ : syracuseStep 2110763 = 3166145) B3166145
theorem B1602875 : Blo 1405522 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B1406267 : Blo 1405522 1406267 := bstep (se 1 (by rfl) ⟨1054700, by rfl⟩ : syracuseStep 1406267 = 2109401) B2109401
theorem B2110793 : Blo 1405522 2110793 := bstep (se 2 (by rfl) ⟨791547, by rfl⟩ : syracuseStep 2110793 = 1583095) B1583095
theorem B1406343 : Blo 1405522 1406343 := bstep (se 1 (by rfl) ⟨1054757, by rfl⟩ : syracuseStep 1406343 = 2109515) B2109515
theorem B1406351 : Blo 1405522 1406351 := bstep (se 1 (by rfl) ⟨1054763, by rfl⟩ : syracuseStep 1406351 = 2109527) B2109527
theorem B3380633 : Blo 1405522 3380633 := bstep (se 2 (by rfl) ⟨1267737, by rfl⟩ : syracuseStep 3380633 = 2535475) B2535475
theorem B1406395 : Blo 1405522 1406395 := bstep (se 1 (by rfl) ⟨1054796, by rfl⟩ : syracuseStep 1406395 = 2109593) B2109593
theorem B2110907 : Blo 1405522 2110907 := bstep (se 1 (by rfl) ⟨1583180, by rfl⟩ : syracuseStep 2110907 = 3166361) B3166361
theorem B5068241 : Blo 1405522 5068241 := bstep (se 2 (by rfl) ⟨1900590, by rfl⟩ : syracuseStep 5068241 = 3801181) B3801181
theorem B6010321 : Blo 1405522 6010321 := bstep (se 2 (by rfl) ⟨2253870, by rfl⟩ : syracuseStep 6010321 = 4507741) B4507741
theorem B2110967 : Blo 1405522 2110967 := bstep (se 1 (by rfl) ⟨1583225, by rfl⟩ : syracuseStep 2110967 = 3166451) B3166451
theorem B1406471 : Blo 1405522 1406471 := bstep (se 1 (by rfl) ⟨1054853, by rfl⟩ : syracuseStep 1406471 = 2109707) B2109707
theorem B1406479 : Blo 1405522 1406479 := bstep (se 1 (by rfl) ⟨1054859, by rfl⟩ : syracuseStep 1406479 = 2109719) B2109719
theorem B2110991 : Blo 1405522 2110991 := bstep (se 1 (by rfl) ⟨1583243, by rfl⟩ : syracuseStep 2110991 = 3166487) B3166487
theorem B3560993 : Blo 1405522 3560993 := bstep (se 2 (by rfl) ⟨1335372, by rfl⟩ : syracuseStep 3560993 = 2670745) B2670745
theorem B2111033 : Blo 1405522 2111033 := bstep (se 2 (by rfl) ⟨791637, by rfl⟩ : syracuseStep 2111033 = 1583275) B1583275
theorem B1406523 : Blo 1405522 1406523 := bstep (se 1 (by rfl) ⟨1054892, by rfl⟩ : syracuseStep 1406523 = 2109785) B2109785
theorem B16029251 : Blo 1405522 16029251 := bstep (se 1 (by rfl) ⟨12021938, by rfl⟩ : syracuseStep 16029251 = 24043877) B24043877
theorem B6411863 : Blo 1405522 6411863 := bstep (se 1 (by rfl) ⟨4808897, by rfl⟩ : syracuseStep 6411863 = 9617795) B9617795
theorem B2373239 : Blo 1405522 2373239 := bstep (se 1 (by rfl) ⟨1779929, by rfl⟩ : syracuseStep 2373239 = 3559859) B3559859
theorem B1406599 : Blo 1405522 1406599 := bstep (se 1 (by rfl) ⟨1054949, by rfl⟩ : syracuseStep 1406599 = 2109899) B2109899
theorem B2111111 : Blo 1405522 2111111 := bstep (se 1 (by rfl) ⟨1583333, by rfl⟩ : syracuseStep 2111111 = 3166667) B3166667
theorem B1406607 : Blo 1405522 1406607 := bstep (se 1 (by rfl) ⟨1054955, by rfl⟩ : syracuseStep 1406607 = 2109911) B2109911
theorem B7607981 : Blo 1405522 7607981 := bstep (se 3 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 7607981 = 2852993) B2852993
theorem B2111147 : Blo 1405522 2111147 := bstep (se 1 (by rfl) ⟨1583360, by rfl⟩ : syracuseStep 2111147 = 3166721) B3166721
theorem B1406651 : Blo 1405522 1406651 := bstep (se 1 (by rfl) ⟨1054988, by rfl⟩ : syracuseStep 1406651 = 2109977) B2109977
theorem B2111177 : Blo 1405522 2111177 := bstep (se 2 (by rfl) ⟨791691, by rfl⟩ : syracuseStep 2111177 = 1583383) B1583383
theorem B1406727 : Blo 1405522 1406727 := bstep (se 1 (by rfl) ⟨1055045, by rfl⟩ : syracuseStep 1406727 = 2110091) B2110091
theorem B1406735 : Blo 1405522 1406735 := bstep (se 1 (by rfl) ⟨1055051, by rfl⟩ : syracuseStep 1406735 = 2110103) B2110103
theorem B1406779 : Blo 1405522 1406779 := bstep (se 1 (by rfl) ⟨1055084, by rfl⟩ : syracuseStep 1406779 = 2110169) B2110169
theorem B7116659 : Blo 1405522 7116659 := bstep (se 1 (by rfl) ⟨5337494, by rfl⟩ : syracuseStep 7116659 = 10674989) B10674989
theorem B1406855 : Blo 1405522 1406855 := bstep (se 1 (by rfl) ⟨1055141, by rfl⟩ : syracuseStep 1406855 = 2110283) B2110283
theorem B4749191 : Blo 1405522 4749191 := bstep (se 1 (by rfl) ⟨3561893, by rfl⟩ : syracuseStep 4749191 = 7123787) B7123787
theorem B1406863 : Blo 1405522 1406863 := bstep (se 1 (by rfl) ⟨1055147, by rfl⟩ : syracuseStep 1406863 = 2110295) B2110295
theorem B7124921 : Blo 1405522 7124921 := bstep (se 2 (by rfl) ⟨2671845, by rfl⟩ : syracuseStep 7124921 = 5343691) B5343691
theorem B1406907 : Blo 1405522 1406907 := bstep (se 1 (by rfl) ⟨1055180, by rfl⟩ : syracuseStep 1406907 = 2110361) B2110361
theorem B1406983 : Blo 1405522 1406983 := bstep (se 1 (by rfl) ⟨1055237, by rfl⟩ : syracuseStep 1406983 = 2110475) B2110475
theorem B1406991 : Blo 1405522 1406991 := bstep (se 1 (by rfl) ⟨1055243, by rfl⟩ : syracuseStep 1406991 = 2110487) B2110487
theorem B2373691 : Blo 1405522 2373691 := bstep (se 1 (by rfl) ⟨1780268, by rfl⟩ : syracuseStep 2373691 = 3560537) B3560537
theorem B1407035 : Blo 1405522 1407035 := bstep (se 1 (by rfl) ⟨1055276, by rfl⟩ : syracuseStep 1407035 = 2110553) B2110553
theorem B10131517 : Blo 1405522 10131517 := bstep (se 3 (by rfl) ⟨1899659, by rfl⟩ : syracuseStep 10131517 = 3799319) B3799319
theorem B1407111 : Blo 1405522 1407111 := bstep (se 1 (by rfl) ⟨1055333, by rfl⟩ : syracuseStep 1407111 = 2110667) B2110667
theorem B1407119 : Blo 1405522 1407119 := bstep (se 1 (by rfl) ⟨1055339, by rfl⟩ : syracuseStep 1407119 = 2110679) B2110679
theorem B4003987 : Blo 1405522 4003987 := bstep (se 1 (by rfl) ⟨3002990, by rfl⟩ : syracuseStep 4003987 = 6005981) B6005981
theorem B32938157 : Blo 1405522 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B1407163 : Blo 1405522 1407163 := bstep (se 1 (by rfl) ⟨1055372, by rfl⟩ : syracuseStep 1407163 = 2110745) B2110745
theorem B2373833 : Blo 1405522 2373833 := bstep (se 2 (by rfl) ⟨890187, by rfl⟩ : syracuseStep 2373833 = 1780375) B1780375
theorem B4749569 : Blo 1405522 4749569 := bstep (se 2 (by rfl) ⟨1781088, by rfl⟩ : syracuseStep 4749569 = 3562177) B3562177
theorem B1407239 : Blo 1405522 1407239 := bstep (se 1 (by rfl) ⟨1055429, by rfl⟩ : syracuseStep 1407239 = 2110859) B2110859
theorem B1407247 : Blo 1405522 1407247 := bstep (se 1 (by rfl) ⟨1055435, by rfl⟩ : syracuseStep 1407247 = 2110871) B2110871
theorem B3381547 : Blo 1405522 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B1407291 : Blo 1405522 1407291 := bstep (se 1 (by rfl) ⟨1055468, by rfl⟩ : syracuseStep 1407291 = 2110937) B2110937
theorem B7117145 : Blo 1405522 7117145 := bstep (se 2 (by rfl) ⟨2668929, by rfl⟩ : syracuseStep 7117145 = 5337859) B5337859
theorem B1407367 : Blo 1405522 1407367 := bstep (se 1 (by rfl) ⟨1055525, by rfl⟩ : syracuseStep 1407367 = 2111051) B2111051
theorem B1407375 : Blo 1405522 1407375 := bstep (se 1 (by rfl) ⟨1055531, by rfl⟩ : syracuseStep 1407375 = 2111063) B2111063
theorem B8550803 : Blo 1405522 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B4397459 : Blo 1405522 4397459 := bstep (se 1 (by rfl) ⟨3298094, by rfl⟩ : syracuseStep 4397459 = 6596189) B6596189
theorem B1407419 : Blo 1405522 1407419 := bstep (se 1 (by rfl) ⟨1055564, by rfl⟩ : syracuseStep 1407419 = 2111129) B2111129
theorem B7215563 : Blo 1405522 7215563 := bstep (se 1 (by rfl) ⟨5411672, by rfl⟩ : syracuseStep 7215563 = 10823345) B10823345
theorem B1407495 : Blo 1405522 1407495 := bstep (se 1 (by rfl) ⟨1055621, by rfl⟩ : syracuseStep 1407495 = 2111243) B2111243
theorem B3561995 : Blo 1405522 3561995 := bstep (se 1 (by rfl) ⟨2671496, by rfl⟩ : syracuseStep 3561995 = 5342993) B5342993
theorem B1407503 : Blo 1405522 1407503 := bstep (se 1 (by rfl) ⟨1055627, by rfl⟩ : syracuseStep 1407503 = 2111255) B2111255
theorem B24369707 : Blo 1405522 24369707 := bstep (se 1 (by rfl) ⟨18277280, by rfl⟩ : syracuseStep 24369707 = 36554561) B36554561
theorem B38509175 : Blo 1405522 38509175 := bstep (se 1 (by rfl) ⟨28881881, by rfl⟩ : syracuseStep 38509175 = 57763763) B57763763
theorem B2669203 : Blo 1405522 2669203 := bstep (se 1 (by rfl) ⟨2001902, by rfl⟩ : syracuseStep 2669203 = 4003805) B4003805
theorem B3005075 : Blo 1405522 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B8010413 : Blo 1405522 8010413 := bstep (se 3 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 8010413 = 3003905) B3003905
theorem B9009893 : Blo 1405522 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B29653775 : Blo 1405522 29653775 := bstep (se 1 (by rfl) ⟨22240331, by rfl⟩ : syracuseStep 29653775 = 44480663) B44480663
theorem B2669431 : Blo 1405522 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B2374535 : Blo 1405522 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B2251705 : Blo 1405522 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B4750379 : Blo 1405522 4750379 := bstep (se 1 (by rfl) ⟨3562784, by rfl⟩ : syracuseStep 4750379 = 7125569) B7125569
theorem B3562643 : Blo 1405522 3562643 := bstep (se 1 (by rfl) ⟨2671982, by rfl⟩ : syracuseStep 3562643 = 5343965) B5343965
theorem B6003983 : Blo 1405522 6003983 := bstep (se 1 (by rfl) ⟨4502987, by rfl⟩ : syracuseStep 6003983 = 9005975) B9005975
theorem B2284843 : Blo 1405522 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B5340563 : Blo 1405522 5340563 := bstep (se 1 (by rfl) ⟨4005422, by rfl⟩ : syracuseStep 5340563 = 8010845) B8010845
theorem B1424827 : Blo 1405522 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B2375183 : Blo 1405522 2375183 := bstep (se 1 (by rfl) ⟨1781387, by rfl⟩ : syracuseStep 2375183 = 3562775) B3562775
theorem B2252423 : Blo 1405522 2252423 := bstep (se 1 (by rfl) ⟨1689317, by rfl⟩ : syracuseStep 2252423 = 3378635) B3378635
theorem B1900217 : Blo 1405522 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B7601971 : Blo 1405522 7601971 := bstep (se 1 (by rfl) ⟨5701478, by rfl⟩ : syracuseStep 7601971 = 11402957) B11402957
theorem B4005719 : Blo 1405522 4005719 := bstep (se 1 (by rfl) ⟨3004289, by rfl⟩ : syracuseStep 4005719 = 6008579) B6008579
theorem B10133363 : Blo 1405522 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B7708625 : Blo 1405522 7708625 := bstep (se 2 (by rfl) ⟨2890734, by rfl⟩ : syracuseStep 7708625 = 5781469) B5781469
theorem B4505615 : Blo 1405522 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B13508689 : Blo 1405522 13508689 := bstep (se 2 (by rfl) ⟨5065758, by rfl⟩ : syracuseStep 13508689 = 10131517) B10131517
theorem B4808951 : Blo 1405522 4808951 := bstep (se 1 (by rfl) ⟨3606713, by rfl⟩ : syracuseStep 4808951 = 7213427) B7213427
theorem B3162473 : Blo 1405522 3162473 := bstep (se 2 (by rfl) ⟨1185927, by rfl⟩ : syracuseStep 3162473 = 2371855) B2371855
theorem B5341565 : Blo 1405522 5341565 := bstep (se 3 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 5341565 = 2003087) B2003087
theorem B4809203 : Blo 1405522 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B1581691 : Blo 1405522 1581691 := bstep (se 1 (by rfl) ⟨1186268, by rfl⟩ : syracuseStep 1581691 = 2372537) B2372537
theorem B2671535 : Blo 1405522 2671535 := bstep (se 1 (by rfl) ⟨2003651, by rfl⟩ : syracuseStep 2671535 = 4007303) B4007303
theorem B3163067 : Blo 1405522 3163067 := bstep (se 1 (by rfl) ⟨2372300, by rfl⟩ : syracuseStep 3163067 = 4744601) B4744601
theorem B2253755 : Blo 1405522 2253755 := bstep (se 1 (by rfl) ⟨1690316, by rfl⟩ : syracuseStep 2253755 = 3380633) B3380633
theorem B3163193 : Blo 1405522 3163193 := bstep (se 2 (by rfl) ⟨1186197, by rfl⟩ : syracuseStep 3163193 = 2372395) B2372395
theorem B1582159 : Blo 1405522 1582159 := bstep (se 1 (by rfl) ⟨1186619, by rfl⟩ : syracuseStep 1582159 = 2373239) B2373239
theorem B5071987 : Blo 1405522 5071987 := bstep (se 1 (by rfl) ⟨3803990, by rfl⟩ : syracuseStep 5071987 = 7607981) B7607981
theorem B4744439 : Blo 1405522 4744439 := bstep (se 1 (by rfl) ⟨3558329, by rfl⟩ : syracuseStep 4744439 = 7116659) B7116659
theorem B10683737 : Blo 1405522 10683737 := bstep (se 2 (by rfl) ⟨4006401, by rfl⟩ : syracuseStep 10683737 = 8012803) B8012803
theorem B2671967 : Blo 1405522 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B3163535 : Blo 1405522 3163535 := bstep (se 1 (by rfl) ⟨2372651, by rfl⟩ : syracuseStep 3163535 = 4745303) B4745303
theorem B5703131 : Blo 1405522 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B1582555 : Blo 1405522 1582555 := bstep (se 1 (by rfl) ⟨1186916, by rfl⟩ : syracuseStep 1582555 = 2373833) B2373833
theorem B4744763 : Blo 1405522 4744763 := bstep (se 1 (by rfl) ⟨3558572, by rfl⟩ : syracuseStep 4744763 = 7117145) B7117145
theorem B4810375 : Blo 1405522 4810375 := bstep (se 1 (by rfl) ⟨3607781, by rfl⟩ : syracuseStep 4810375 = 7215563) B7215563
theorem B3163859 : Blo 1405522 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B10675961 : Blo 1405522 10675961 := bstep (se 2 (by rfl) ⟨4003485, by rfl⟩ : syracuseStep 10675961 = 8006971) B8006971
theorem B4745033 : Blo 1405522 4745033 := bstep (se 2 (by rfl) ⟨1779387, by rfl⟩ : syracuseStep 4745033 = 3558775) B3558775
theorem B19769183 : Blo 1405522 19769183 := bstep (se 1 (by rfl) ⟨14826887, by rfl⟩ : syracuseStep 19769183 = 29653775) B29653775
theorem B1583023 : Blo 1405522 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B8013761 : Blo 1405522 8013761 := bstep (se 2 (by rfl) ⟨3005160, by rfl⟩ : syracuseStep 8013761 = 6010321) B6010321
theorem B2852921 : Blo 1405522 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B5343479 : Blo 1405522 5343479 := bstep (se 1 (by rfl) ⟨4007609, by rfl⟩ : syracuseStep 5343479 = 8015219) B8015219
theorem B1583455 : Blo 1405522 1583455 := bstep (se 1 (by rfl) ⟨1187591, by rfl⟩ : syracuseStep 1583455 = 2375183) B2375183
theorem B10135961 : Blo 1405522 10135961 := bstep (se 2 (by rfl) ⟨3800985, by rfl⟩ : syracuseStep 10135961 = 7601971) B7601971
theorem B1501615 : Blo 1405522 1501615 := bstep (se 1 (by rfl) ⟨1126211, by rfl⟩ : syracuseStep 1501615 = 2252423) B2252423
theorem B3164795 : Blo 1405522 3164795 := bstep (se 1 (by rfl) ⟨2373596, by rfl⟩ : syracuseStep 3164795 = 4747193) B4747193
theorem B5139083 : Blo 1405522 5139083 := bstep (se 1 (by rfl) ⟨3854312, by rfl⟩ : syracuseStep 5139083 = 7708625) B7708625
theorem B11397833 : Blo 1405522 11397833 := bstep (se 2 (by rfl) ⟨4274187, by rfl⟩ : syracuseStep 11397833 = 8548375) B8548375
theorem B30436069 : Blo 1405522 30436069 := bstep (se 4 (by rfl) ⟨2853381, by rfl⟩ : syracuseStep 30436069 = 5706763) B5706763
theorem B3164921 : Blo 1405522 3164921 := bstep (se 2 (by rfl) ⟨1186845, by rfl⟩ : syracuseStep 3164921 = 2373691) B2373691
theorem B3558239 : Blo 1405522 3558239 := bstep (se 1 (by rfl) ⟨2668679, by rfl⟩ : syracuseStep 3558239 = 5337359) B5337359
theorem B4746167 : Blo 1405522 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B1780699 : Blo 1405522 1780699 := bstep (se 1 (by rfl) ⟨1335524, by rfl⟩ : syracuseStep 1780699 = 2671049) B2671049
theorem B3165191 : Blo 1405522 3165191 := bstep (se 1 (by rfl) ⟨2373893, by rfl⟩ : syracuseStep 3165191 = 4747787) B4747787
theorem B4508729 : Blo 1405522 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B2108495 : Blo 1405522 2108495 := bstep (se 1 (by rfl) ⟨1581371, by rfl⟩ : syracuseStep 2108495 = 3162743) B3162743
theorem B3165263 : Blo 1405522 3165263 := bstep (se 1 (by rfl) ⟨2373947, by rfl⟩ : syracuseStep 3165263 = 4747895) B4747895
theorem B10677419 : Blo 1405522 10677419 := bstep (se 1 (by rfl) ⟨8008064, by rfl⟩ : syracuseStep 10677419 = 16016129) B16016129
theorem B2108615 : Blo 1405522 2108615 := bstep (se 1 (by rfl) ⟨1581461, by rfl⟩ : syracuseStep 2108615 = 3162923) B3162923
theorem B7122167 : Blo 1405522 7122167 := bstep (se 1 (by rfl) ⟨5341625, by rfl⟩ : syracuseStep 7122167 = 10683251) B10683251
theorem B2108777 : Blo 1405522 2108777 := bstep (se 2 (by rfl) ⟨790791, by rfl⟩ : syracuseStep 2108777 = 1581583) B1581583
theorem B9006461 : Blo 1405522 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B2108855 : Blo 1405522 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B2108891 : Blo 1405522 2108891 := bstep (se 1 (by rfl) ⟨1581668, by rfl⟩ : syracuseStep 2108891 = 3163337) B3163337
theorem B3165659 : Blo 1405522 3165659 := bstep (se 1 (by rfl) ⟨2374244, by rfl⟩ : syracuseStep 3165659 = 4748489) B4748489
theorem B10145243 : Blo 1405522 10145243 := bstep (se 1 (by rfl) ⟨7608932, by rfl⟩ : syracuseStep 10145243 = 15217865) B15217865
theorem B4746761 : Blo 1405522 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B3558937 : Blo 1405522 3558937 := bstep (se 2 (by rfl) ⟨1334601, by rfl⟩ : syracuseStep 3558937 = 2669203) B2669203
theorem B3378827 : Blo 1405522 3378827 := bstep (se 1 (by rfl) ⟨2534120, by rfl⟩ : syracuseStep 3378827 = 5068241) B5068241
theorem B8121995 : Blo 1405522 8121995 := bstep (se 1 (by rfl) ⟨6091496, by rfl⟩ : syracuseStep 8121995 = 12182993) B12182993
theorem B10677905 : Blo 1405522 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B6008509 : Blo 1405522 6008509 := bstep (se 3 (by rfl) ⟨1126595, by rfl⟩ : syracuseStep 6008509 = 2253191) B2253191
theorem B10686167 : Blo 1405522 10686167 := bstep (se 1 (by rfl) ⟨8014625, by rfl⟩ : syracuseStep 10686167 = 16029251) B16029251
theorem B22802141 : Blo 1405522 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B7122653 : Blo 1405522 7122653 := bstep (se 3 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 7122653 = 2670995) B2670995
theorem B3559241 : Blo 1405522 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B38490005 : Blo 1405522 38490005 := bstep (se 6 (by rfl) ⟨902109, by rfl⟩ : syracuseStep 38490005 = 1804219) B1804219
theorem B3002273 : Blo 1405522 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B2109359 : Blo 1405522 2109359 := bstep (se 1 (by rfl) ⟨1582019, by rfl⟩ : syracuseStep 2109359 = 3164039) B3164039
theorem B3166127 : Blo 1405522 3166127 := bstep (se 1 (by rfl) ⟨2374595, by rfl⟩ : syracuseStep 3166127 = 4749191) B4749191
theorem B2109449 : Blo 1405522 2109449 := bstep (se 2 (by rfl) ⟨791043, by rfl⟩ : syracuseStep 2109449 = 1582087) B1582087
theorem B2109479 : Blo 1405522 2109479 := bstep (se 1 (by rfl) ⟨1582109, by rfl⟩ : syracuseStep 2109479 = 3164219) B3164219
theorem B21958771 : Blo 1405522 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B2109563 : Blo 1405522 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B3166379 : Blo 1405522 3166379 := bstep (se 1 (by rfl) ⟨2374784, by rfl⟩ : syracuseStep 3166379 = 4749569) B4749569
theorem B2109689 : Blo 1405522 2109689 := bstep (se 2 (by rfl) ⟨791133, by rfl⟩ : syracuseStep 2109689 = 1582267) B1582267
theorem B2109791 : Blo 1405522 2109791 := bstep (se 1 (by rfl) ⟨1582343, by rfl⟩ : syracuseStep 2109791 = 3164687) B3164687
theorem B4747625 : Blo 1405522 4747625 := bstep (se 2 (by rfl) ⟨1780359, by rfl⟩ : syracuseStep 4747625 = 3560719) B3560719
theorem B2109803 : Blo 1405522 2109803 := bstep (se 1 (by rfl) ⟨1582352, by rfl⟩ : syracuseStep 2109803 = 3164705) B3164705
theorem B2003383 : Blo 1405522 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B5067245 : Blo 1405522 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B2372105 : Blo 1405522 2372105 := bstep (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) B1779079
theorem B2110031 : Blo 1405522 2110031 := bstep (se 1 (by rfl) ⟨1582523, by rfl⟩ : syracuseStep 2110031 = 3165047) B3165047
theorem B1405535 : Blo 1405522 1405535 := bstep (se 1 (by rfl) ⟨1054151, by rfl⟩ : syracuseStep 1405535 = 2108303) B2108303
theorem B1405563 : Blo 1405522 1405563 := bstep (se 1 (by rfl) ⟨1054172, by rfl⟩ : syracuseStep 1405563 = 2108345) B2108345
theorem B2372267 : Blo 1405522 2372267 := bstep (se 1 (by rfl) ⟨1779200, by rfl⟩ : syracuseStep 2372267 = 3558401) B3558401
theorem B1405615 : Blo 1405522 1405615 := bstep (se 1 (by rfl) ⟨1054211, by rfl⟩ : syracuseStep 1405615 = 2108423) B2108423
theorem B1405639 : Blo 1405522 1405639 := bstep (se 1 (by rfl) ⟨1054229, by rfl⟩ : syracuseStep 1405639 = 2108459) B2108459
theorem B2110151 : Blo 1405522 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B3166919 : Blo 1405522 3166919 := bstep (se 1 (by rfl) ⟨2375189, by rfl⟩ : syracuseStep 3166919 = 4750379) B4750379
theorem B52048595 : Blo 1405522 52048595 := bstep (se 1 (by rfl) ⟨39036446, by rfl⟩ : syracuseStep 52048595 = 78072893) B78072893
theorem B1405659 : Blo 1405522 1405659 := bstep (se 1 (by rfl) ⟨1054244, by rfl⟩ : syracuseStep 1405659 = 2108489) B2108489
theorem B1405735 : Blo 1405522 1405735 := bstep (se 1 (by rfl) ⟨1054301, by rfl⟩ : syracuseStep 1405735 = 2108603) B2108603
theorem B1405775 : Blo 1405522 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B4002655 : Blo 1405522 4002655 := bstep (se 1 (by rfl) ⟨3001991, by rfl⟩ : syracuseStep 4002655 = 6003983) B6003983
theorem B1405791 : Blo 1405522 1405791 := bstep (se 1 (by rfl) ⟨1054343, by rfl⟩ : syracuseStep 1405791 = 2108687) B2108687
theorem B2110313 : Blo 1405522 2110313 := bstep (se 2 (by rfl) ⟨791367, by rfl⟩ : syracuseStep 2110313 = 1582735) B1582735
theorem B1405819 : Blo 1405522 1405819 := bstep (se 1 (by rfl) ⟨1054364, by rfl⟩ : syracuseStep 1405819 = 2108729) B2108729
theorem B1405871 : Blo 1405522 1405871 := bstep (se 1 (by rfl) ⟨1054403, by rfl⟩ : syracuseStep 1405871 = 2108807) B2108807
theorem B3560375 : Blo 1405522 3560375 := bstep (se 1 (by rfl) ⟨2670281, by rfl⟩ : syracuseStep 3560375 = 5340563) B5340563
theorem B2110391 : Blo 1405522 2110391 := bstep (se 1 (by rfl) ⟨1582793, by rfl⟩ : syracuseStep 2110391 = 3165587) B3165587
theorem B4748219 : Blo 1405522 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B1405895 : Blo 1405522 1405895 := bstep (se 1 (by rfl) ⟨1054421, by rfl⟩ : syracuseStep 1405895 = 2108843) B2108843
theorem B1405915 : Blo 1405522 1405915 := bstep (se 1 (by rfl) ⟨1054436, by rfl⟩ : syracuseStep 1405915 = 2108873) B2108873
theorem B2110427 : Blo 1405522 2110427 := bstep (se 1 (by rfl) ⟨1582820, by rfl⟩ : syracuseStep 2110427 = 3165641) B3165641
theorem B1405991 : Blo 1405522 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B9385003 : Blo 1405522 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B2372665 : Blo 1405522 2372665 := bstep (se 2 (by rfl) ⟨889749, by rfl⟩ : syracuseStep 2372665 = 1779499) B1779499
theorem B10679363 : Blo 1405522 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B1406031 : Blo 1405522 1406031 := bstep (se 1 (by rfl) ⟨1054523, by rfl⟩ : syracuseStep 1406031 = 2109047) B2109047
theorem B1406047 : Blo 1405522 1406047 := bstep (se 1 (by rfl) ⟨1054535, by rfl⟩ : syracuseStep 1406047 = 2109071) B2109071
theorem B1406075 : Blo 1405522 1406075 := bstep (se 1 (by rfl) ⟨1054556, by rfl⟩ : syracuseStep 1406075 = 2109113) B2109113
theorem B1406127 : Blo 1405522 1406127 := bstep (se 1 (by rfl) ⟨1054595, by rfl⟩ : syracuseStep 1406127 = 2109191) B2109191
theorem B2372807 : Blo 1405522 2372807 := bstep (se 1 (by rfl) ⟨1779605, by rfl⟩ : syracuseStep 2372807 = 3559211) B3559211
theorem B1406151 : Blo 1405522 1406151 := bstep (se 1 (by rfl) ⟨1054613, by rfl⟩ : syracuseStep 1406151 = 2109227) B2109227
theorem B1406171 : Blo 1405522 1406171 := bstep (se 1 (by rfl) ⟨1054628, by rfl⟩ : syracuseStep 1406171 = 2109257) B2109257
theorem B6755575 : Blo 1405522 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B1406247 : Blo 1405522 1406247 := bstep (se 1 (by rfl) ⟨1054685, by rfl⟩ : syracuseStep 1406247 = 2109371) B2109371
theorem B1406287 : Blo 1405522 1406287 := bstep (se 1 (by rfl) ⟨1054715, by rfl⟩ : syracuseStep 1406287 = 2109431) B2109431
theorem B1602911 : Blo 1405522 1602911 := bstep (se 1 (by rfl) ⟨1202183, by rfl⟩ : syracuseStep 1602911 = 2404367) B2404367
theorem B1406303 : Blo 1405522 1406303 := bstep (se 1 (by rfl) ⟨1054727, by rfl⟩ : syracuseStep 1406303 = 2109455) B2109455
theorem B2372969 : Blo 1405522 2372969 := bstep (se 2 (by rfl) ⟨889863, by rfl⟩ : syracuseStep 2372969 = 1779727) B1779727
theorem B1406331 : Blo 1405522 1406331 := bstep (se 1 (by rfl) ⟨1054748, by rfl⟩ : syracuseStep 1406331 = 2109497) B2109497
theorem B1406383 : Blo 1405522 1406383 := bstep (se 1 (by rfl) ⟨1054787, by rfl⟩ : syracuseStep 1406383 = 2109575) B2109575
theorem B2110895 : Blo 1405522 2110895 := bstep (se 1 (by rfl) ⟨1583171, by rfl⟩ : syracuseStep 2110895 = 3166343) B3166343
theorem B1406407 : Blo 1405522 1406407 := bstep (se 1 (by rfl) ⟨1054805, by rfl⟩ : syracuseStep 1406407 = 2109611) B2109611
theorem B1406427 : Blo 1405522 1406427 := bstep (se 1 (by rfl) ⟨1054820, by rfl⟩ : syracuseStep 1406427 = 2109641) B2109641
theorem B3659251 : Blo 1405522 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B6010355 : Blo 1405522 6010355 := bstep (se 1 (by rfl) ⟨4507766, by rfl⟩ : syracuseStep 6010355 = 9015533) B9015533
theorem B3003913 : Blo 1405522 3003913 := bstep (se 2 (by rfl) ⟨1126467, by rfl⟩ : syracuseStep 3003913 = 2252935) B2252935
theorem B2110985 : Blo 1405522 2110985 := bstep (se 2 (by rfl) ⟨791619, by rfl⟩ : syracuseStep 2110985 = 1583239) B1583239
theorem B5338649 : Blo 1405522 5338649 := bstep (se 2 (by rfl) ⟨2001993, by rfl⟩ : syracuseStep 5338649 = 4003987) B4003987
theorem B5068327 : Blo 1405522 5068327 := bstep (se 1 (by rfl) ⟨3801245, by rfl⟩ : syracuseStep 5068327 = 7602491) B7602491
theorem B1406503 : Blo 1405522 1406503 := bstep (se 1 (by rfl) ⟨1054877, by rfl⟩ : syracuseStep 1406503 = 2109755) B2109755
theorem B2111015 : Blo 1405522 2111015 := bstep (se 1 (by rfl) ⟨1583261, by rfl⟩ : syracuseStep 2111015 = 3166523) B3166523
theorem B1406543 : Blo 1405522 1406543 := bstep (se 1 (by rfl) ⟨1054907, by rfl⟩ : syracuseStep 1406543 = 2109815) B2109815
theorem B9016919 : Blo 1405522 9016919 := bstep (se 1 (by rfl) ⟨6762689, by rfl⟩ : syracuseStep 9016919 = 13525379) B13525379
theorem B1406559 : Blo 1405522 1406559 := bstep (se 1 (by rfl) ⟨1054919, by rfl⟩ : syracuseStep 1406559 = 2109839) B2109839
theorem B1406587 : Blo 1405522 1406587 := bstep (se 1 (by rfl) ⟨1054940, by rfl⟩ : syracuseStep 1406587 = 2109881) B2109881
theorem B2111099 : Blo 1405522 2111099 := bstep (se 1 (by rfl) ⟨1583324, by rfl⟩ : syracuseStep 2111099 = 3166649) B3166649
theorem B4060811 : Blo 1405522 4060811 := bstep (se 1 (by rfl) ⟨3045608, by rfl⟩ : syracuseStep 4060811 = 6091217) B6091217
theorem B2283179 : Blo 1405522 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1406639 : Blo 1405522 1406639 := bstep (se 1 (by rfl) ⟨1054979, by rfl⟩ : syracuseStep 1406639 = 2109959) B2109959
theorem B1406663 : Blo 1405522 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B1406683 : Blo 1405522 1406683 := bstep (se 1 (by rfl) ⟨1055012, by rfl⟩ : syracuseStep 1406683 = 2110025) B2110025
theorem B2373367 : Blo 1405522 2373367 := bstep (se 1 (by rfl) ⟨1780025, by rfl⟩ : syracuseStep 2373367 = 3560051) B3560051
theorem B4003577 : Blo 1405522 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B2111225 : Blo 1405522 2111225 := bstep (se 2 (by rfl) ⟨791709, by rfl⟩ : syracuseStep 2111225 = 1583419) B1583419
theorem B19240739 : Blo 1405522 19240739 := bstep (se 1 (by rfl) ⟨14430554, by rfl⟩ : syracuseStep 19240739 = 28861109) B28861109
theorem B1406759 : Blo 1405522 1406759 := bstep (se 1 (by rfl) ⟨1055069, by rfl⟩ : syracuseStep 1406759 = 2110139) B2110139
theorem B1406799 : Blo 1405522 1406799 := bstep (se 1 (by rfl) ⟨1055099, by rfl⟩ : syracuseStep 1406799 = 2110199) B2110199
theorem B1406815 : Blo 1405522 1406815 := bstep (se 1 (by rfl) ⟨1055111, by rfl⟩ : syracuseStep 1406815 = 2110223) B2110223
theorem B1406843 : Blo 1405522 1406843 := bstep (se 1 (by rfl) ⟨1055132, by rfl⟩ : syracuseStep 1406843 = 2110265) B2110265
theorem B4003759 : Blo 1405522 4003759 := bstep (se 1 (by rfl) ⟨3002819, by rfl⟩ : syracuseStep 4003759 = 6005639) B6005639
theorem B1406895 : Blo 1405522 1406895 := bstep (se 1 (by rfl) ⟨1055171, by rfl⟩ : syracuseStep 1406895 = 2110343) B2110343
theorem B2373563 : Blo 1405522 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B1406919 : Blo 1405522 1406919 := bstep (se 1 (by rfl) ⟨1055189, by rfl⟩ : syracuseStep 1406919 = 2110379) B2110379
theorem B1406939 : Blo 1405522 1406939 := bstep (se 1 (by rfl) ⟨1055204, by rfl⟩ : syracuseStep 1406939 = 2110409) B2110409
theorem B10139651 : Blo 1405522 10139651 := bstep (se 1 (by rfl) ⟨7604738, by rfl⟩ : syracuseStep 10139651 = 15209477) B15209477
theorem B3561479 : Blo 1405522 3561479 := bstep (se 1 (by rfl) ⟨2671109, by rfl⟩ : syracuseStep 3561479 = 5342219) B5342219
theorem B10680335 : Blo 1405522 10680335 := bstep (se 1 (by rfl) ⟨8010251, by rfl⟩ : syracuseStep 10680335 = 16020503) B16020503
theorem B2373671 : Blo 1405522 2373671 := bstep (se 1 (by rfl) ⟨1780253, by rfl⟩ : syracuseStep 2373671 = 3560507) B3560507
theorem B1407015 : Blo 1405522 1407015 := bstep (se 1 (by rfl) ⟨1055261, by rfl⟩ : syracuseStep 1407015 = 2110523) B2110523
theorem B3561529 : Blo 1405522 3561529 := bstep (se 2 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 3561529 = 2671147) B2671147
theorem B1407055 : Blo 1405522 1407055 := bstep (se 1 (by rfl) ⟨1055291, by rfl⟩ : syracuseStep 1407055 = 2110583) B2110583
theorem B1407071 : Blo 1405522 1407071 := bstep (se 1 (by rfl) ⟨1055303, by rfl⟩ : syracuseStep 1407071 = 2110607) B2110607
theorem B1407099 : Blo 1405522 1407099 := bstep (se 1 (by rfl) ⟨1055324, by rfl⟩ : syracuseStep 1407099 = 2110649) B2110649
theorem B4274333 : Blo 1405522 4274333 := bstep (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) B1602875
theorem B2889899 : Blo 1405522 2889899 := bstep (se 1 (by rfl) ⟨2167424, by rfl⟩ : syracuseStep 2889899 = 4334849) B4334849
theorem B1407151 : Blo 1405522 1407151 := bstep (se 1 (by rfl) ⟨1055363, by rfl⟩ : syracuseStep 1407151 = 2110727) B2110727
theorem B1407175 : Blo 1405522 1407175 := bstep (se 1 (by rfl) ⟨1055381, by rfl⟩ : syracuseStep 1407175 = 2110763) B2110763
theorem B1407195 : Blo 1405522 1407195 := bstep (se 1 (by rfl) ⟨1055396, by rfl⟩ : syracuseStep 1407195 = 2110793) B2110793
theorem B1407271 : Blo 1405522 1407271 := bstep (se 1 (by rfl) ⟨1055453, by rfl⟩ : syracuseStep 1407271 = 2110907) B2110907
theorem B2373961 : Blo 1405522 2373961 := bstep (se 2 (by rfl) ⟨890235, by rfl⟩ : syracuseStep 2373961 = 1780471) B1780471
theorem B1407311 : Blo 1405522 1407311 := bstep (se 1 (by rfl) ⟨1055483, by rfl⟩ : syracuseStep 1407311 = 2110967) B2110967
theorem B534034781 : Blo 1405522 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B1407327 : Blo 1405522 1407327 := bstep (se 1 (by rfl) ⟨1055495, by rfl⟩ : syracuseStep 1407327 = 2110991) B2110991
theorem B13515113 : Blo 1405522 13515113 := bstep (se 2 (by rfl) ⟨5068167, by rfl⟩ : syracuseStep 13515113 = 10136335) B10136335
theorem B2283881 : Blo 1405522 2283881 := bstep (se 2 (by rfl) ⟨856455, by rfl⟩ : syracuseStep 2283881 = 1712911) B1712911
theorem B2373995 : Blo 1405522 2373995 := bstep (se 1 (by rfl) ⟨1780496, by rfl⟩ : syracuseStep 2373995 = 3560993) B3560993
theorem B3561833 : Blo 1405522 3561833 := bstep (se 2 (by rfl) ⟨1335687, by rfl⟩ : syracuseStep 3561833 = 2671375) B2671375
theorem B3610985 : Blo 1405522 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B1407355 : Blo 1405522 1407355 := bstep (se 1 (by rfl) ⟨1055516, by rfl⟩ : syracuseStep 1407355 = 2111033) B2111033
theorem B4274575 : Blo 1405522 4274575 := bstep (se 1 (by rfl) ⟨3205931, by rfl⟩ : syracuseStep 4274575 = 6411863) B6411863
theorem B1407407 : Blo 1405522 1407407 := bstep (se 1 (by rfl) ⟨1055555, by rfl⟩ : syracuseStep 1407407 = 2111111) B2111111
theorem B1407431 : Blo 1405522 1407431 := bstep (se 1 (by rfl) ⟨1055573, by rfl⟩ : syracuseStep 1407431 = 2111147) B2111147
theorem B1407451 : Blo 1405522 1407451 := bstep (se 1 (by rfl) ⟨1055588, by rfl⟩ : syracuseStep 1407451 = 2111177) B2111177
theorem B4749947 : Blo 1405522 4749947 := bstep (se 1 (by rfl) ⟨3562460, by rfl⟩ : syracuseStep 4749947 = 7124921) B7124921
theorem B2251513 : Blo 1405522 2251513 := bstep (se 2 (by rfl) ⟨844317, by rfl⟩ : syracuseStep 2251513 = 1688635) B1688635
theorem B2374393 : Blo 1405522 2374393 := bstep (se 2 (by rfl) ⟨890397, by rfl⟩ : syracuseStep 2374393 = 1780795) B1780795
theorem B64985885 : Blo 1405522 64985885 := bstep (se 3 (by rfl) ⟨12184853, by rfl⟩ : syracuseStep 64985885 = 24369707) B24369707
theorem B4750109 : Blo 1405522 4750109 := bstep (se 3 (by rfl) ⟨890645, by rfl⟩ : syracuseStep 4750109 = 1781291) B1781291
theorem B46906229 : Blo 1405522 46906229 := bstep (se 5 (by rfl) ⟨2198729, by rfl⟩ : syracuseStep 46906229 = 4397459) B4397459
theorem B2374663 : Blo 1405522 2374663 := bstep (se 1 (by rfl) ⟨1780997, by rfl⟩ : syracuseStep 2374663 = 3561995) B3561995
theorem B3046457 : Blo 1405522 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B25672783 : Blo 1405522 25672783 := bstep (se 1 (by rfl) ⟨19254587, by rfl⟩ : syracuseStep 25672783 = 38509175) B38509175
theorem B5340275 : Blo 1405522 5340275 := bstep (se 1 (by rfl) ⟨4005206, by rfl⟩ : syracuseStep 5340275 = 8010413) B8010413
theorem B4005035 : Blo 1405522 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B1899769 : Blo 1405522 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B24026381 : Blo 1405522 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B4005263 : Blo 1405522 4005263 := bstep (se 1 (by rfl) ⟨3003947, by rfl⟩ : syracuseStep 4005263 = 6007895) B6007895
theorem B51289523 : Blo 1405522 51289523 := bstep (se 1 (by rfl) ⟨38467142, by rfl⟩ : syracuseStep 51289523 = 76934285) B76934285
theorem B43326899 : Blo 1405522 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B2375095 : Blo 1405522 2375095 := bstep (se 1 (by rfl) ⟨1781321, by rfl⟩ : syracuseStep 2375095 = 3562643) B3562643
theorem B10133191 : Blo 1405522 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B2670479 : Blo 1405522 2670479 := bstep (se 1 (by rfl) ⟨2002859, by rfl⟩ : syracuseStep 2670479 = 4005719) B4005719
theorem B29278361 : Blo 1405522 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B1581403 : Blo 1405522 1581403 := bstep (se 1 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 1581403 = 2372105) B2372105
theorem B1581511 : Blo 1405522 1581511 := bstep (se 1 (by rfl) ⟨1186133, by rfl⟩ : syracuseStep 1581511 = 2372267) B2372267
theorem B7119575 : Blo 1405522 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B1581871 : Blo 1405522 1581871 := bstep (se 1 (by rfl) ⟨1186403, by rfl⟩ : syracuseStep 1581871 = 2372807) B2372807
theorem B3162959 : Blo 1405522 3162959 := bstep (se 1 (by rfl) ⟨2372219, by rfl⟩ : syracuseStep 3162959 = 4744439) B4744439
theorem B1581979 : Blo 1405522 1581979 := bstep (se 1 (by rfl) ⟨1186484, by rfl⟩ : syracuseStep 1581979 = 2372969) B2372969
theorem B3802087 : Blo 1405522 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B4006903 : Blo 1405522 4006903 := bstep (se 1 (by rfl) ⟨3005177, by rfl⟩ : syracuseStep 4006903 = 6010355) B6010355
theorem B3163175 : Blo 1405522 3163175 := bstep (se 1 (by rfl) ⟨2372381, by rfl⟩ : syracuseStep 3163175 = 4744763) B4744763
theorem B3163355 : Blo 1405522 3163355 := bstep (se 1 (by rfl) ⟨2372516, by rfl⟩ : syracuseStep 3163355 = 4745033) B4745033
theorem B1582375 : Blo 1405522 1582375 := bstep (se 1 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 1582375 = 2373563) B2373563
theorem B5342507 : Blo 1405522 5342507 := bstep (se 1 (by rfl) ⟨4006880, by rfl⟩ : syracuseStep 5342507 = 8013761) B8013761
theorem B6759767 : Blo 1405522 6759767 := bstep (se 1 (by rfl) ⟨5069825, by rfl⟩ : syracuseStep 6759767 = 10139651) B10139651
theorem B7120223 : Blo 1405522 7120223 := bstep (se 1 (by rfl) ⟨5340167, by rfl⟩ : syracuseStep 7120223 = 10680335) B10680335
theorem B1582447 : Blo 1405522 1582447 := bstep (se 1 (by rfl) ⟨1186835, by rfl⟩ : syracuseStep 1582447 = 2373671) B2373671
theorem B3163553 : Blo 1405522 3163553 := bstep (se 2 (by rfl) ⟨1186332, by rfl⟩ : syracuseStep 3163553 = 2372665) B2372665
theorem B1926599 : Blo 1405522 1926599 := bstep (se 1 (by rfl) ⟨1444949, by rfl⟩ : syracuseStep 1926599 = 2889899) B2889899
theorem B1582663 : Blo 1405522 1582663 := bstep (se 1 (by rfl) ⟨1186997, by rfl⟩ : syracuseStep 1582663 = 2373995) B2373995
theorem B2533025 : Blo 1405522 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B6088477 : Blo 1405522 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B31270819 : Blo 1405522 31270819 := bstep (se 1 (by rfl) ⟨23453114, by rfl⟩ : syracuseStep 31270819 = 46906229) B46906229
theorem B3164111 : Blo 1405522 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B4745249 : Blo 1405522 4745249 := bstep (se 2 (by rfl) ⟨1779468, by rfl⟩ : syracuseStep 4745249 = 3558937) B3558937
theorem B16017587 : Blo 1405522 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B13510921 : Blo 1405522 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B10684709 : Blo 1405522 10684709 := bstep (se 4 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 10684709 = 2003383) B2003383
theorem B3164489 : Blo 1405522 3164489 := bstep (se 2 (by rfl) ⟨1186683, by rfl⟩ : syracuseStep 3164489 = 2373367) B2373367
theorem B3164507 : Blo 1405522 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B1780319 : Blo 1405522 1780319 := bstep (se 1 (by rfl) ⟨1335239, by rfl⟩ : syracuseStep 1780319 = 2670479) B2670479
theorem B25660003 : Blo 1405522 25660003 := bstep (se 1 (by rfl) ⟨19245002, by rfl⟩ : syracuseStep 25660003 = 38490005) B38490005
theorem B2001515 : Blo 1405522 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B2108315 : Blo 1405522 2108315 := bstep (se 1 (by rfl) ⟨1581236, by rfl⟩ : syracuseStep 2108315 = 3162473) B3162473
theorem B3165083 : Blo 1405522 3165083 := bstep (se 1 (by rfl) ⟨2373812, by rfl⟩ : syracuseStep 3165083 = 4747625) B4747625
theorem B3206135 : Blo 1405522 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B3165281 : Blo 1405522 3165281 := bstep (se 2 (by rfl) ⟨1186980, by rfl⟩ : syracuseStep 3165281 = 2373961) B2373961
theorem B2002153 : Blo 1405522 2002153 := bstep (se 2 (by rfl) ⟨750807, by rfl⟩ : syracuseStep 2002153 = 1501615) B1501615
theorem B1781023 : Blo 1405522 1781023 := bstep (se 1 (by rfl) ⟨1335767, by rfl⟩ : syracuseStep 1781023 = 2671535) B2671535
theorem B2108711 : Blo 1405522 2108711 := bstep (se 1 (by rfl) ⟨1581533, by rfl⟩ : syracuseStep 2108711 = 3163067) B3163067
theorem B3165479 : Blo 1405522 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B2108795 : Blo 1405522 2108795 := bstep (se 1 (by rfl) ⟨1581596, by rfl⟩ : syracuseStep 2108795 = 3163193) B3163193
theorem B2108921 : Blo 1405522 2108921 := bstep (se 2 (by rfl) ⟨790845, by rfl⟩ : syracuseStep 2108921 = 1581691) B1581691
theorem B7122491 : Blo 1405522 7122491 := bstep (se 1 (by rfl) ⟨5341868, by rfl⟩ : syracuseStep 7122491 = 10683737) B10683737
theorem B2109023 : Blo 1405522 2109023 := bstep (se 1 (by rfl) ⟨1581767, by rfl⟩ : syracuseStep 2109023 = 3163535) B3163535
theorem B6090349 : Blo 1405522 6090349 := bstep (se 3 (by rfl) ⟨1141940, by rfl⟩ : syracuseStep 6090349 = 2283881) B2283881
theorem B9629293 : Blo 1405522 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B3002017 : Blo 1405522 3002017 := bstep (se 2 (by rfl) ⟨1125756, by rfl⟩ : syracuseStep 3002017 = 2251513) B2251513
theorem B3165857 : Blo 1405522 3165857 := bstep (se 2 (by rfl) ⟨1187196, by rfl⟩ : syracuseStep 3165857 = 2374393) B2374393
theorem B3559099 : Blo 1405522 3559099 := bstep (se 1 (by rfl) ⟨2669324, by rfl⟩ : syracuseStep 3559099 = 5338649) B5338649
theorem B5336873 : Blo 1405522 5336873 := bstep (se 2 (by rfl) ⟨2001327, by rfl⟩ : syracuseStep 5336873 = 4002655) B4002655
theorem B2109239 : Blo 1405522 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B13512653 : Blo 1405522 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B3166217 : Blo 1405522 3166217 := bstep (se 2 (by rfl) ⟨1187331, by rfl⟩ : syracuseStep 3166217 = 2374663) B2374663
theorem B12513337 : Blo 1405522 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B2109545 : Blo 1405522 2109545 := bstep (se 2 (by rfl) ⟨791079, by rfl⟩ : syracuseStep 2109545 = 1582159) B1582159
theorem B34230377 : Blo 1405522 34230377 := bstep (se 2 (by rfl) ⟨12836391, by rfl⟩ : syracuseStep 34230377 = 25672783) B25672783
theorem B6762649 : Blo 1405522 6762649 := bstep (se 2 (by rfl) ⟨2535993, by rfl⟩ : syracuseStep 6762649 = 5071987) B5071987
theorem B9007433 : Blo 1405522 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B2109863 : Blo 1405522 2109863 := bstep (se 1 (by rfl) ⟨1582397, by rfl⟩ : syracuseStep 2109863 = 3164795) B3164795
theorem B3166631 : Blo 1405522 3166631 := bstep (se 1 (by rfl) ⟨2374973, by rfl⟩ : syracuseStep 3166631 = 4749947) B4749947
theorem B7598555 : Blo 1405522 7598555 := bstep (se 1 (by rfl) ⟨5698916, by rfl⟩ : syracuseStep 7598555 = 11397833) B11397833
theorem B2109947 : Blo 1405522 2109947 := bstep (se 1 (by rfl) ⟨1582460, by rfl⟩ : syracuseStep 2109947 = 3164921) B3164921
theorem B43323923 : Blo 1405522 43323923 := bstep (se 1 (by rfl) ⟨32492942, by rfl⟩ : syracuseStep 43323923 = 64985885) B64985885
theorem B3166739 : Blo 1405522 3166739 := bstep (se 1 (by rfl) ⟨2375054, by rfl⟩ : syracuseStep 3166739 = 4750109) B4750109
theorem B2372159 : Blo 1405522 2372159 := bstep (se 1 (by rfl) ⟨1779119, by rfl⟩ : syracuseStep 2372159 = 3558239) B3558239
theorem B3166793 : Blo 1405522 3166793 := bstep (se 2 (by rfl) ⟨1187547, by rfl⟩ : syracuseStep 3166793 = 2375095) B2375095
theorem B2110073 : Blo 1405522 2110073 := bstep (se 2 (by rfl) ⟨791277, by rfl⟩ : syracuseStep 2110073 = 1582555) B1582555
theorem B4879001 : Blo 1405522 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B2110127 : Blo 1405522 2110127 := bstep (se 1 (by rfl) ⟨1582595, by rfl⟩ : syracuseStep 2110127 = 3165191) B3165191
theorem B1405663 : Blo 1405522 1405663 := bstep (se 1 (by rfl) ⟨1054247, by rfl⟩ : syracuseStep 1405663 = 2108495) B2108495
theorem B2110175 : Blo 1405522 2110175 := bstep (se 1 (by rfl) ⟨1582631, by rfl⟩ : syracuseStep 2110175 = 3165263) B3165263
theorem B3560183 : Blo 1405522 3560183 := bstep (se 1 (by rfl) ⟨2670137, by rfl⟩ : syracuseStep 3560183 = 5340275) B5340275
theorem B1405743 : Blo 1405522 1405743 := bstep (se 1 (by rfl) ⟨1054307, by rfl⟩ : syracuseStep 1405743 = 2108615) B2108615
theorem B4748111 : Blo 1405522 4748111 := bstep (se 1 (by rfl) ⟨3561083, by rfl⟩ : syracuseStep 4748111 = 7122167) B7122167
theorem B1405851 : Blo 1405522 1405851 := bstep (se 1 (by rfl) ⟨1054388, by rfl⟩ : syracuseStep 1405851 = 2108777) B2108777
theorem B1405903 : Blo 1405522 1405903 := bstep (se 1 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 1405903 = 2108855) B2108855
theorem B1405927 : Blo 1405522 1405927 := bstep (se 1 (by rfl) ⟨1054445, by rfl⟩ : syracuseStep 1405927 = 2108891) B2108891
theorem B2110439 : Blo 1405522 2110439 := bstep (se 1 (by rfl) ⟨1582829, by rfl⟩ : syracuseStep 2110439 = 3165659) B3165659
theorem B6763495 : Blo 1405522 6763495 := bstep (se 1 (by rfl) ⟨5072621, by rfl⟩ : syracuseStep 6763495 = 10145243) B10145243
theorem B7124111 : Blo 1405522 7124111 := bstep (se 1 (by rfl) ⟨5343083, by rfl⟩ : syracuseStep 7124111 = 10686167) B10686167
theorem B15201427 : Blo 1405522 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B4748435 : Blo 1405522 4748435 := bstep (se 1 (by rfl) ⟨3561326, by rfl⟩ : syracuseStep 4748435 = 7122653) B7122653
theorem B6010013 : Blo 1405522 6010013 := bstep (se 3 (by rfl) ⟨1126877, by rfl⟩ : syracuseStep 6010013 = 2253755) B2253755
theorem B2372827 : Blo 1405522 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B5338345 : Blo 1405522 5338345 := bstep (se 2 (by rfl) ⟨2001879, by rfl⟩ : syracuseStep 5338345 = 4003759) B4003759
theorem B2110697 : Blo 1405522 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B51295477 : Blo 1405522 51295477 := bstep (se 5 (by rfl) ⟨2404475, by rfl⟩ : syracuseStep 51295477 = 4808951) B4808951
theorem B1406239 : Blo 1405522 1406239 := bstep (se 1 (by rfl) ⟨1054679, by rfl⟩ : syracuseStep 1406239 = 2109359) B2109359
theorem B2110751 : Blo 1405522 2110751 := bstep (se 1 (by rfl) ⟨1583063, by rfl⟩ : syracuseStep 2110751 = 3166127) B3166127
theorem B1406299 : Blo 1405522 1406299 := bstep (se 1 (by rfl) ⟨1054724, by rfl⟩ : syracuseStep 1406299 = 2109449) B2109449
theorem B3003743 : Blo 1405522 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B1406319 : Blo 1405522 1406319 := bstep (se 1 (by rfl) ⟨1054739, by rfl⟩ : syracuseStep 1406319 = 2109479) B2109479
theorem B4748705 : Blo 1405522 4748705 := bstep (se 2 (by rfl) ⟨1780764, by rfl⟩ : syracuseStep 4748705 = 3561529) B3561529
theorem B1406375 : Blo 1405522 1406375 := bstep (se 1 (by rfl) ⟨1054781, by rfl⟩ : syracuseStep 1406375 = 2109563) B2109563
theorem B18011585 : Blo 1405522 18011585 := bstep (se 2 (by rfl) ⟨6754344, by rfl⟩ : syracuseStep 18011585 = 13508689) B13508689
theorem B2110919 : Blo 1405522 2110919 := bstep (se 1 (by rfl) ⟨1583189, by rfl⟩ : syracuseStep 2110919 = 3166379) B3166379
theorem B8123885 : Blo 1405522 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B7607789 : Blo 1405522 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B1406459 : Blo 1405522 1406459 := bstep (se 1 (by rfl) ⟨1054844, by rfl⟩ : syracuseStep 1406459 = 2109689) B2109689
theorem B1406527 : Blo 1405522 1406527 := bstep (se 1 (by rfl) ⟨1054895, by rfl⟩ : syracuseStep 1406527 = 2109791) B2109791
theorem B1406535 : Blo 1405522 1406535 := bstep (se 1 (by rfl) ⟨1054901, by rfl⟩ : syracuseStep 1406535 = 2109803) B2109803
theorem B3561043 : Blo 1405522 3561043 := bstep (se 1 (by rfl) ⟨2670782, by rfl⟩ : syracuseStep 3561043 = 5341565) B5341565
theorem B1406687 : Blo 1405522 1406687 := bstep (se 1 (by rfl) ⟨1055015, by rfl⟩ : syracuseStep 1406687 = 2110031) B2110031
theorem B2111273 : Blo 1405522 2111273 := bstep (se 2 (by rfl) ⟨791727, by rfl⟩ : syracuseStep 2111273 = 1583455) B1583455
theorem B1406767 : Blo 1405522 1406767 := bstep (se 1 (by rfl) ⟨1055075, by rfl⟩ : syracuseStep 1406767 = 2110151) B2110151
theorem B2111279 : Blo 1405522 2111279 := bstep (se 1 (by rfl) ⟨1583459, by rfl⟩ : syracuseStep 2111279 = 3166919) B3166919
theorem B34699063 : Blo 1405522 34699063 := bstep (se 1 (by rfl) ⟨26024297, by rfl⟩ : syracuseStep 34699063 = 52048595) B52048595
theorem B1406875 : Blo 1405522 1406875 := bstep (se 1 (by rfl) ⟨1055156, by rfl⟩ : syracuseStep 1406875 = 2110313) B2110313
theorem B2373583 : Blo 1405522 2373583 := bstep (se 1 (by rfl) ⟨1780187, by rfl⟩ : syracuseStep 2373583 = 3560375) B3560375
theorem B1406927 : Blo 1405522 1406927 := bstep (se 1 (by rfl) ⟨1055195, by rfl⟩ : syracuseStep 1406927 = 2110391) B2110391
theorem B1406951 : Blo 1405522 1406951 := bstep (se 1 (by rfl) ⟨1055213, by rfl⟩ : syracuseStep 1406951 = 2110427) B2110427
theorem B4274429 : Blo 1405522 4274429 := bstep (se 3 (by rfl) ⟨801455, by rfl⟩ : syracuseStep 4274429 = 1602911) B1602911
theorem B7125245 : Blo 1405522 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B1407263 : Blo 1405522 1407263 := bstep (se 1 (by rfl) ⟨1055447, by rfl⟩ : syracuseStep 1407263 = 2110895) B2110895
theorem B40581425 : Blo 1405522 40581425 := bstep (se 2 (by rfl) ⟨15218034, by rfl⟩ : syracuseStep 40581425 = 30436069) B30436069
theorem B1407323 : Blo 1405522 1407323 := bstep (se 1 (by rfl) ⟨1055492, by rfl⟩ : syracuseStep 1407323 = 2110985) B2110985
theorem B1407343 : Blo 1405522 1407343 := bstep (se 1 (by rfl) ⟨1055507, by rfl⟩ : syracuseStep 1407343 = 2111015) B2111015
theorem B6011279 : Blo 1405522 6011279 := bstep (se 1 (by rfl) ⟨4508459, by rfl⟩ : syracuseStep 6011279 = 9016919) B9016919
theorem B1407399 : Blo 1405522 1407399 := bstep (se 1 (by rfl) ⟨1055549, by rfl⟩ : syracuseStep 1407399 = 2111099) B2111099
theorem B7117307 : Blo 1405522 7117307 := bstep (se 1 (by rfl) ⟨5337980, by rfl⟩ : syracuseStep 7117307 = 10675961) B10675961
theorem B2669051 : Blo 1405522 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B1407483 : Blo 1405522 1407483 := bstep (se 1 (by rfl) ⟨1055612, by rfl⟩ : syracuseStep 1407483 = 2111225) B2111225
theorem B12827159 : Blo 1405522 12827159 := bstep (se 1 (by rfl) ⟨9620369, by rfl⟩ : syracuseStep 12827159 = 19240739) B19240739
theorem B13179455 : Blo 1405522 13179455 := bstep (se 1 (by rfl) ⟨9884591, by rfl⟩ : syracuseStep 13179455 = 19769183) B19769183
theorem B2374265 : Blo 1405522 2374265 := bstep (se 2 (by rfl) ⟨890349, by rfl⟩ : syracuseStep 2374265 = 1780699) B1780699
theorem B2374319 : Blo 1405522 2374319 := bstep (se 1 (by rfl) ⟨1780739, by rfl⟩ : syracuseStep 2374319 = 3561479) B3561479
theorem B2849555 : Blo 1405522 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B3562319 : Blo 1405522 3562319 := bstep (se 1 (by rfl) ⟨2671739, by rfl⟩ : syracuseStep 3562319 = 5343479) B5343479
theorem B356023187 : Blo 1405522 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B9010075 : Blo 1405522 9010075 := bstep (se 1 (by rfl) ⟨6757556, by rfl⟩ : syracuseStep 9010075 = 13515113) B13515113
theorem B2374555 : Blo 1405522 2374555 := bstep (se 1 (by rfl) ⟨1780916, by rfl⟩ : syracuseStep 2374555 = 3561833) B3561833
theorem B6757307 : Blo 1405522 6757307 := bstep (se 1 (by rfl) ⟨5067980, by rfl⟩ : syracuseStep 6757307 = 10135961) B10135961
theorem B13704221 : Blo 1405522 13704221 := bstep (se 3 (by rfl) ⟨2569541, by rfl⟩ : syracuseStep 13704221 = 5139083) B5139083
theorem B10828829 : Blo 1405522 10828829 := bstep (se 3 (by rfl) ⟨2030405, by rfl⟩ : syracuseStep 10828829 = 4060811) B4060811
theorem B4005217 : Blo 1405522 4005217 := bstep (se 2 (by rfl) ⟨1501956, by rfl⟩ : syracuseStep 4005217 = 3003913) B3003913
theorem B3005819 : Blo 1405522 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B6757769 : Blo 1405522 6757769 := bstep (se 2 (by rfl) ⟨2534163, by rfl⟩ : syracuseStep 6757769 = 5068327) B5068327
theorem B22797733 : Blo 1405522 22797733 := bstep (se 4 (by rfl) ⟨2137287, by rfl⟩ : syracuseStep 22797733 = 4274575) B4274575
theorem B7118279 : Blo 1405522 7118279 := bstep (se 1 (by rfl) ⟨5338709, by rfl⟩ : syracuseStep 7118279 = 10677419) B10677419
theorem B2670023 : Blo 1405522 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B6413833 : Blo 1405522 6413833 := bstep (se 2 (by rfl) ⟨2405187, by rfl⟩ : syracuseStep 6413833 = 4810375) B4810375
theorem B8011345 : Blo 1405522 8011345 := bstep (se 2 (by rfl) ⟨3004254, by rfl⟩ : syracuseStep 8011345 = 6008509) B6008509
theorem B6004307 : Blo 1405522 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B2670175 : Blo 1405522 2670175 := bstep (se 1 (by rfl) ⟨2002631, by rfl⟩ : syracuseStep 2670175 = 4005263) B4005263
theorem B34193015 : Blo 1405522 34193015 := bstep (se 1 (by rfl) ⟨25644761, by rfl⟩ : syracuseStep 34193015 = 51289523) B51289523
theorem B28884599 : Blo 1405522 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B2252551 : Blo 1405522 2252551 := bstep (se 1 (by rfl) ⟨1689413, by rfl⟩ : syracuseStep 2252551 = 3378827) B3378827
theorem B5414663 : Blo 1405522 5414663 := bstep (se 1 (by rfl) ⟨4060997, by rfl⟩ : syracuseStep 5414663 = 8121995) B8121995
theorem B7118603 : Blo 1405522 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B6004955 : Blo 1405522 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B18014561 : Blo 1405522 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B1581439 : Blo 1405522 1581439 := bstep (se 1 (by rfl) ⟨1186079, by rfl⟩ : syracuseStep 1581439 = 2372159) B2372159
theorem B3252667 : Blo 1405522 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B4006675 : Blo 1405522 4006675 := bstep (se 1 (by rfl) ⟨3005006, by rfl⟩ : syracuseStep 4006675 = 6010013) B6010013
theorem B4506511 : Blo 1405522 4506511 := bstep (se 1 (by rfl) ⟨3379883, by rfl⟩ : syracuseStep 4506511 = 6759767) B6759767
theorem B5415923 : Blo 1405522 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B5071859 : Blo 1405522 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B1688683 : Blo 1405522 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B5137597 : Blo 1405522 5137597 := bstep (se 3 (by rfl) ⟨963299, by rfl⟩ : syracuseStep 5137597 = 1926599) B1926599
theorem B7120061 : Blo 1405522 7120061 := bstep (se 3 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 7120061 = 2670023) B2670023
theorem B5342537 : Blo 1405522 5342537 := bstep (se 2 (by rfl) ⟨2003451, by rfl⟩ : syracuseStep 5342537 = 4006903) B4006903
theorem B3163499 : Blo 1405522 3163499 := bstep (se 1 (by rfl) ⟨2372624, by rfl⟩ : syracuseStep 3163499 = 4745249) B4745249
theorem B20268569 : Blo 1405522 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B4007519 : Blo 1405522 4007519 := bstep (se 1 (by rfl) ⟨3005639, by rfl⟩ : syracuseStep 4007519 = 6011279) B6011279
theorem B3163769 : Blo 1405522 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B4744871 : Blo 1405522 4744871 := bstep (se 1 (by rfl) ⟨3558653, by rfl⟩ : syracuseStep 4744871 = 7117307) B7117307
theorem B1582843 : Blo 1405522 1582843 := bstep (se 1 (by rfl) ⟨1187132, by rfl⟩ : syracuseStep 1582843 = 2374265) B2374265
theorem B1582879 : Blo 1405522 1582879 := bstep (se 1 (by rfl) ⟨1187159, by rfl⟩ : syracuseStep 1582879 = 2374319) B2374319
theorem B237348791 : Blo 1405522 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B9136147 : Blo 1405522 9136147 := bstep (se 1 (by rfl) ⟨6852110, by rfl⟩ : syracuseStep 9136147 = 13704221) B13704221
theorem B7219219 : Blo 1405522 7219219 := bstep (se 1 (by rfl) ⟨5414414, by rfl⟩ : syracuseStep 7219219 = 10828829) B10828829
theorem B8120465 : Blo 1405522 8120465 := bstep (se 2 (by rfl) ⟨3045174, by rfl⟩ : syracuseStep 8120465 = 6090349) B6090349
theorem B12839057 : Blo 1405522 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B4745465 : Blo 1405522 4745465 := bstep (se 2 (by rfl) ⟨1779549, by rfl⟩ : syracuseStep 4745465 = 3559099) B3559099
theorem B4745519 : Blo 1405522 4745519 := bstep (se 1 (by rfl) ⟨3559139, by rfl⟩ : syracuseStep 4745519 = 7118279) B7118279
theorem B4745735 : Blo 1405522 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B3557915 : Blo 1405522 3557915 := bstep (se 1 (by rfl) ⟨2668436, by rfl⟩ : syracuseStep 3557915 = 5336873) B5336873
theorem B3164777 : Blo 1405522 3164777 := bstep (se 2 (by rfl) ⟨1186791, by rfl⟩ : syracuseStep 3164777 = 2373583) B2373583
theorem B5065703 : Blo 1405522 5065703 := bstep (se 1 (by rfl) ⟨3799277, by rfl⟩ : syracuseStep 5065703 = 7598555) B7598555
theorem B2108537 : Blo 1405522 2108537 := bstep (se 2 (by rfl) ⟨790701, by rfl⟩ : syracuseStep 2108537 = 1581403) B1581403
theorem B4746383 : Blo 1405522 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B2108639 : Blo 1405522 2108639 := bstep (se 1 (by rfl) ⟨1581479, by rfl⟩ : syracuseStep 2108639 = 3162959) B3162959
theorem B3165407 : Blo 1405522 3165407 := bstep (se 1 (by rfl) ⟨2374055, by rfl⟩ : syracuseStep 3165407 = 4748111) B4748111
theorem B2108681 : Blo 1405522 2108681 := bstep (se 2 (by rfl) ⟨790755, by rfl⟩ : syracuseStep 2108681 = 1581511) B1581511
theorem B11398477 : Blo 1405522 11398477 := bstep (se 3 (by rfl) ⟨2137214, by rfl⟩ : syracuseStep 11398477 = 4274429) B4274429
theorem B2108783 : Blo 1405522 2108783 := bstep (se 1 (by rfl) ⟨1581587, by rfl⟩ : syracuseStep 2108783 = 3163175) B3163175
theorem B3165623 : Blo 1405522 3165623 := bstep (se 1 (by rfl) ⟨2374217, by rfl⟩ : syracuseStep 3165623 = 4748435) B4748435
theorem B34213337 : Blo 1405522 34213337 := bstep (se 2 (by rfl) ⟨12830001, by rfl⟩ : syracuseStep 34213337 = 25660003) B25660003
theorem B2108903 : Blo 1405522 2108903 := bstep (se 1 (by rfl) ⟨1581677, by rfl⟩ : syracuseStep 2108903 = 3163355) B3163355
theorem B2002495 : Blo 1405522 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B4746815 : Blo 1405522 4746815 := bstep (se 1 (by rfl) ⟨3560111, by rfl⟩ : syracuseStep 4746815 = 7120223) B7120223
theorem B2109035 : Blo 1405522 2109035 := bstep (se 1 (by rfl) ⟨1581776, by rfl⟩ : syracuseStep 2109035 = 3163553) B3163553
theorem B3165803 : Blo 1405522 3165803 := bstep (se 1 (by rfl) ⟨2374352, by rfl⟩ : syracuseStep 3165803 = 4748705) B4748705
theorem B2109161 : Blo 1405522 2109161 := bstep (se 2 (by rfl) ⟨790935, by rfl⟩ : syracuseStep 2109161 = 1581871) B1581871
theorem B2109305 : Blo 1405522 2109305 := bstep (se 2 (by rfl) ⟨790989, by rfl⟩ : syracuseStep 2109305 = 1581979) B1581979
theorem B12013433 : Blo 1405522 12013433 := bstep (se 2 (by rfl) ⟨4505037, by rfl⟩ : syracuseStep 12013433 = 9010075) B9010075
theorem B3166073 : Blo 1405522 3166073 := bstep (se 2 (by rfl) ⟨1187277, by rfl⟩ : syracuseStep 3166073 = 2374555) B2374555
theorem B2109407 : Blo 1405522 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B10678391 : Blo 1405522 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B7123139 : Blo 1405522 7123139 := bstep (se 1 (by rfl) ⟨5342354, by rfl⟩ : syracuseStep 7123139 = 10684709) B10684709
theorem B27054283 : Blo 1405522 27054283 := bstep (se 1 (by rfl) ⟨20290712, by rfl⟩ : syracuseStep 27054283 = 40581425) B40581425
theorem B2109659 : Blo 1405522 2109659 := bstep (se 1 (by rfl) ⟨1582244, by rfl⟩ : syracuseStep 2109659 = 3164489) B3164489
theorem B2109671 : Blo 1405522 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B4747517 : Blo 1405522 4747517 := bstep (se 3 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 4747517 = 1780319) B1780319
theorem B5337373 : Blo 1405522 5337373 := bstep (se 3 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 5337373 = 2001515) B2001515
theorem B8786303 : Blo 1405522 8786303 := bstep (se 1 (by rfl) ⟨6589727, by rfl⟩ : syracuseStep 8786303 = 13179455) B13179455
theorem B2109833 : Blo 1405522 2109833 := bstep (se 2 (by rfl) ⟨791187, by rfl⟩ : syracuseStep 2109833 = 1582375) B1582375
theorem B2109929 : Blo 1405522 2109929 := bstep (se 2 (by rfl) ⟨791223, by rfl⟩ : syracuseStep 2109929 = 1582447) B1582447
theorem B30396977 : Blo 1405522 30396977 := bstep (se 2 (by rfl) ⟨11398866, by rfl⟩ : syracuseStep 30396977 = 22797733) B22797733
theorem B1405543 : Blo 1405522 1405543 := bstep (se 1 (by rfl) ⟨1054157, by rfl⟩ : syracuseStep 1405543 = 2108315) B2108315
theorem B2110055 : Blo 1405522 2110055 := bstep (se 1 (by rfl) ⟨1582541, by rfl⟩ : syracuseStep 2110055 = 3165083) B3165083
theorem B2110187 : Blo 1405522 2110187 := bstep (se 1 (by rfl) ⟨1582640, by rfl⟩ : syracuseStep 2110187 = 3165281) B3165281
theorem B2110217 : Blo 1405522 2110217 := bstep (se 2 (by rfl) ⟨791331, by rfl⟩ : syracuseStep 2110217 = 1582663) B1582663
theorem B4748057 : Blo 1405522 4748057 := bstep (se 2 (by rfl) ⟨1780521, by rfl⟩ : syracuseStep 4748057 = 3561043) B3561043
theorem B3560233 : Blo 1405522 3560233 := bstep (se 2 (by rfl) ⟨1335087, by rfl⟩ : syracuseStep 3560233 = 2670175) B2670175
theorem B1405807 : Blo 1405522 1405807 := bstep (se 1 (by rfl) ⟨1054355, by rfl⟩ : syracuseStep 1405807 = 2108711) B2108711
theorem B2110319 : Blo 1405522 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B4002689 : Blo 1405522 4002689 := bstep (se 2 (by rfl) ⟨1501008, by rfl⟩ : syracuseStep 4002689 = 3002017) B3002017
theorem B1405863 : Blo 1405522 1405863 := bstep (se 1 (by rfl) ⟨1054397, by rfl⟩ : syracuseStep 1405863 = 2108795) B2108795
theorem B2003879 : Blo 1405522 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B1405947 : Blo 1405522 1405947 := bstep (se 1 (by rfl) ⟨1054460, by rfl⟩ : syracuseStep 1405947 = 2108921) B2108921
theorem B3003401 : Blo 1405522 3003401 := bstep (se 2 (by rfl) ⟨1126275, by rfl⟩ : syracuseStep 3003401 = 2252551) B2252551
theorem B4748327 : Blo 1405522 4748327 := bstep (se 1 (by rfl) ⟨3561245, by rfl⟩ : syracuseStep 4748327 = 7122491) B7122491
theorem B4002871 : Blo 1405522 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B1406015 : Blo 1405522 1406015 := bstep (se 1 (by rfl) ⟨1054511, by rfl⟩ : syracuseStep 1406015 = 2109023) B2109023
theorem B46265417 : Blo 1405522 46265417 := bstep (se 2 (by rfl) ⟨17349531, by rfl⟩ : syracuseStep 46265417 = 34699063) B34699063
theorem B22795343 : Blo 1405522 22795343 := bstep (se 1 (by rfl) ⟨17096507, by rfl⟩ : syracuseStep 22795343 = 34193015) B34193015
theorem B19256399 : Blo 1405522 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B2110571 : Blo 1405522 2110571 := bstep (se 1 (by rfl) ⟨1582928, by rfl⟩ : syracuseStep 2110571 = 3165857) B3165857
theorem B3609775 : Blo 1405522 3609775 := bstep (se 1 (by rfl) ⟨2707331, by rfl⟩ : syracuseStep 3609775 = 5414663) B5414663
theorem B1406159 : Blo 1405522 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B41694425 : Blo 1405522 41694425 := bstep (se 2 (by rfl) ⟨15635409, by rfl⟩ : syracuseStep 41694425 = 31270819) B31270819
theorem B9008435 : Blo 1405522 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B2110811 : Blo 1405522 2110811 := bstep (se 1 (by rfl) ⟨1583108, by rfl⟩ : syracuseStep 2110811 = 3166217) B3166217
theorem B34207109 : Blo 1405522 34207109 := bstep (se 4 (by rfl) ⟨3206916, by rfl⟩ : syracuseStep 34207109 = 6413833) B6413833
theorem B1406363 : Blo 1405522 1406363 := bstep (se 1 (by rfl) ⟨1054772, by rfl⟩ : syracuseStep 1406363 = 2109545) B2109545
theorem B22820251 : Blo 1405522 22820251 := bstep (se 1 (by rfl) ⟨17115188, by rfl⟩ : syracuseStep 22820251 = 34230377) B34230377
theorem B19518907 : Blo 1405522 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B9016865 : Blo 1405522 9016865 := bstep (se 2 (by rfl) ⟨3381324, by rfl⟩ : syracuseStep 9016865 = 6762649) B6762649
theorem B1406575 : Blo 1405522 1406575 := bstep (se 1 (by rfl) ⟨1054931, by rfl⟩ : syracuseStep 1406575 = 2109863) B2109863
theorem B2111087 : Blo 1405522 2111087 := bstep (se 1 (by rfl) ⟨1583315, by rfl⟩ : syracuseStep 2111087 = 3166631) B3166631
theorem B1406631 : Blo 1405522 1406631 := bstep (se 1 (by rfl) ⟨1054973, by rfl⟩ : syracuseStep 1406631 = 2109947) B2109947
theorem B28882615 : Blo 1405522 28882615 := bstep (se 1 (by rfl) ⟨21661961, by rfl⟩ : syracuseStep 28882615 = 43323923) B43323923
theorem B2111159 : Blo 1405522 2111159 := bstep (se 1 (by rfl) ⟨1583369, by rfl⟩ : syracuseStep 2111159 = 3166739) B3166739
theorem B2111195 : Blo 1405522 2111195 := bstep (se 1 (by rfl) ⟨1583396, by rfl⟩ : syracuseStep 2111195 = 3166793) B3166793
theorem B1406715 : Blo 1405522 1406715 := bstep (se 1 (by rfl) ⟨1055036, by rfl⟩ : syracuseStep 1406715 = 2110073) B2110073
theorem B1406751 : Blo 1405522 1406751 := bstep (se 1 (by rfl) ⟨1055063, by rfl⟩ : syracuseStep 1406751 = 2110127) B2110127
theorem B1406783 : Blo 1405522 1406783 := bstep (se 1 (by rfl) ⟨1055087, by rfl⟩ : syracuseStep 1406783 = 2110175) B2110175
theorem B2373455 : Blo 1405522 2373455 := bstep (se 1 (by rfl) ⟨1780091, by rfl⟩ : syracuseStep 2373455 = 3560183) B3560183
theorem B1406959 : Blo 1405522 1406959 := bstep (se 1 (by rfl) ⟨1055219, by rfl⟩ : syracuseStep 1406959 = 2110439) B2110439
theorem B4749407 : Blo 1405522 4749407 := bstep (se 1 (by rfl) ⟨3562055, by rfl⟩ : syracuseStep 4749407 = 7124111) B7124111
theorem B1407131 : Blo 1405522 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B1407167 : Blo 1405522 1407167 := bstep (se 1 (by rfl) ⟨1055375, by rfl⟩ : syracuseStep 1407167 = 2110751) B2110751
theorem B3561671 : Blo 1405522 3561671 := bstep (se 1 (by rfl) ⟨2671253, by rfl⟩ : syracuseStep 3561671 = 5342507) B5342507
theorem B12007723 : Blo 1405522 12007723 := bstep (se 1 (by rfl) ⟨9005792, by rfl⟩ : syracuseStep 12007723 = 18011585) B18011585
theorem B1407279 : Blo 1405522 1407279 := bstep (se 1 (by rfl) ⟨1055459, by rfl⟩ : syracuseStep 1407279 = 2110919) B2110919
theorem B266951189 : Blo 1405522 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B1407515 : Blo 1405522 1407515 := bstep (se 1 (by rfl) ⟨1055636, by rfl⟩ : syracuseStep 1407515 = 2111273) B2111273
theorem B1407519 : Blo 1405522 1407519 := bstep (se 1 (by rfl) ⟨1055639, by rfl⟩ : syracuseStep 1407519 = 2111279) B2111279
theorem B5069449 : Blo 1405522 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B9017993 : Blo 1405522 9017993 := bstep (se 2 (by rfl) ⟨3381747, by rfl⟩ : syracuseStep 9017993 = 6763495) B6763495
theorem B7117469 : Blo 1405522 7117469 := bstep (se 3 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 7117469 = 2669051) B2669051
theorem B4750163 : Blo 1405522 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B7117793 : Blo 1405522 7117793 := bstep (se 2 (by rfl) ⟨2669172, by rfl⟩ : syracuseStep 7117793 = 5338345) B5338345
theorem B2669537 : Blo 1405522 2669537 := bstep (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) B2002153
theorem B68393969 : Blo 1405522 68393969 := bstep (se 2 (by rfl) ⟨25647738, by rfl⟩ : syracuseStep 68393969 = 51295477) B51295477
theorem B8551439 : Blo 1405522 8551439 := bstep (se 1 (by rfl) ⟨6413579, by rfl⟩ : syracuseStep 8551439 = 12827159) B12827159
theorem B2374697 : Blo 1405522 2374697 := bstep (se 2 (by rfl) ⟨890511, by rfl⟩ : syracuseStep 2374697 = 1781023) B1781023
theorem B5340289 : Blo 1405522 5340289 := bstep (se 2 (by rfl) ⟨2002608, by rfl⟩ : syracuseStep 5340289 = 4005217) B4005217
theorem B1899703 : Blo 1405522 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B2374879 : Blo 1405522 2374879 := bstep (se 1 (by rfl) ⟨1781159, by rfl⟩ : syracuseStep 2374879 = 3562319) B3562319
theorem B4504871 : Blo 1405522 4504871 := bstep (se 1 (by rfl) ⟨3378653, by rfl⟩ : syracuseStep 4504871 = 6757307) B6757307
theorem B2137423 : Blo 1405522 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B10681793 : Blo 1405522 10681793 := bstep (se 2 (by rfl) ⟨4005672, by rfl⟩ : syracuseStep 10681793 = 8011345) B8011345
theorem B4505179 : Blo 1405522 4505179 := bstep (se 1 (by rfl) ⟨3378884, by rfl⟩ : syracuseStep 4505179 = 6757769) B6757769
theorem B8117969 : Blo 1405522 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B12181529 : Blo 1405522 12181529 := bstep (se 2 (by rfl) ⟨4568073, by rfl⟩ : syracuseStep 12181529 = 9136147) B9136147
theorem B9625625 : Blo 1405522 9625625 := bstep (se 2 (by rfl) ⟨3609609, by rfl⟩ : syracuseStep 9625625 = 7219219) B7219219
theorem B7118927 : Blo 1405522 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B12009707 : Blo 1405522 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B5857535 : Blo 1405522 5857535 := bstep (se 1 (by rfl) ⟨4393151, by rfl⟩ : syracuseStep 5857535 = 8786303) B8786303
theorem B30843611 : Blo 1405522 30843611 := bstep (se 1 (by rfl) ⟨23132708, by rfl⟩ : syracuseStep 30843611 = 46265417) B46265417
theorem B15196895 : Blo 1405522 15196895 := bstep (se 1 (by rfl) ⟨11397671, by rfl⟩ : syracuseStep 15196895 = 22795343) B22795343
theorem B12837599 : Blo 1405522 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B27796283 : Blo 1405522 27796283 := bstep (se 1 (by rfl) ⟨20847212, by rfl⟩ : syracuseStep 27796283 = 41694425) B41694425
theorem B6005623 : Blo 1405522 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B5342233 : Blo 1405522 5342233 := bstep (se 2 (by rfl) ⟨2003337, by rfl⟩ : syracuseStep 5342233 = 4006675) B4006675
theorem B2671679 : Blo 1405522 2671679 := bstep (se 1 (by rfl) ⟨2003759, by rfl⟩ : syracuseStep 2671679 = 4007519) B4007519
theorem B3163247 : Blo 1405522 3163247 := bstep (se 1 (by rfl) ⟨2372435, by rfl⟩ : syracuseStep 3163247 = 4744871) B4744871
theorem B1582303 : Blo 1405522 1582303 := bstep (se 1 (by rfl) ⟨1186727, by rfl⟩ : syracuseStep 1582303 = 2373455) B2373455
theorem B3163643 : Blo 1405522 3163643 := bstep (se 1 (by rfl) ⟨2372732, by rfl⟩ : syracuseStep 3163643 = 4745465) B4745465
theorem B7120385 : Blo 1405522 7120385 := bstep (se 2 (by rfl) ⟨2670144, by rfl⟩ : syracuseStep 7120385 = 5340289) B5340289
theorem B3163679 : Blo 1405522 3163679 := bstep (se 1 (by rfl) ⟨2372759, by rfl⟩ : syracuseStep 3163679 = 4745519) B4745519
theorem B6850129 : Blo 1405522 6850129 := bstep (se 2 (by rfl) ⟨2568798, by rfl⟩ : syracuseStep 6850129 = 5137597) B5137597
theorem B3163823 : Blo 1405522 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B15197969 : Blo 1405522 15197969 := bstep (se 2 (by rfl) ⟨5699238, by rfl⟩ : syracuseStep 15197969 = 11398477) B11398477
theorem B4744979 : Blo 1405522 4744979 := bstep (se 1 (by rfl) ⟨3558734, by rfl⟩ : syracuseStep 4744979 = 7117469) B7117469
theorem B30427001 : Blo 1405522 30427001 := bstep (se 2 (by rfl) ⟨11410125, by rfl⟩ : syracuseStep 30427001 = 22820251) B22820251
theorem B4745195 : Blo 1405522 4745195 := bstep (se 1 (by rfl) ⟨3558896, by rfl⟩ : syracuseStep 4745195 = 7117793) B7117793
theorem B3377135 : Blo 1405522 3377135 := bstep (se 1 (by rfl) ⟨2532851, by rfl⟩ : syracuseStep 3377135 = 5065703) B5065703
theorem B1583131 : Blo 1405522 1583131 := bstep (se 1 (by rfl) ⟨1187348, by rfl⟩ : syracuseStep 1583131 = 2374697) B2374697
theorem B3164255 : Blo 1405522 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B6006905 : Blo 1405522 6006905 := bstep (se 2 (by rfl) ⟨2252589, by rfl⟩ : syracuseStep 6006905 = 4505179) B4505179
theorem B7121195 : Blo 1405522 7121195 := bstep (se 1 (by rfl) ⟨5340896, by rfl⟩ : syracuseStep 7121195 = 10681793) B10681793
theorem B22808891 : Blo 1405522 22808891 := bstep (se 1 (by rfl) ⟨17106668, by rfl⟩ : syracuseStep 22808891 = 34213337) B34213337
theorem B3164543 : Blo 1405522 3164543 := bstep (se 1 (by rfl) ⟨2373407, by rfl⟩ : syracuseStep 3164543 = 4746815) B4746815
theorem B5343677 : Blo 1405522 5343677 := bstep (se 3 (by rfl) ⟨1001939, by rfl⟩ : syracuseStep 5343677 = 2003879) B2003879
theorem B2110715 : Blo 1405522 2110715 := bstep (se 1 (by rfl) ⟨1583036, by rfl⟩ : syracuseStep 2110715 = 3166073) B3166073
theorem B3165011 : Blo 1405522 3165011 := bstep (se 1 (by rfl) ⟨2373758, by rfl⟩ : syracuseStep 3165011 = 4747517) B4747517
theorem B36072377 : Blo 1405522 36072377 := bstep (se 2 (by rfl) ⟨13527141, by rfl⟩ : syracuseStep 36072377 = 27054283) B27054283
theorem B16010297 : Blo 1405522 16010297 := bstep (se 2 (by rfl) ⟨6003861, by rfl⟩ : syracuseStep 16010297 = 12007723) B12007723
theorem B2108585 : Blo 1405522 2108585 := bstep (se 2 (by rfl) ⟨790719, by rfl⟩ : syracuseStep 2108585 = 1581439) B1581439
theorem B3165371 : Blo 1405522 3165371 := bstep (se 1 (by rfl) ⟨2374028, by rfl⟩ : syracuseStep 3165371 = 4748057) B4748057
theorem B2002267 : Blo 1405522 2002267 := bstep (se 1 (by rfl) ⟨1501700, by rfl⟩ : syracuseStep 2002267 = 3003401) B3003401
theorem B3165551 : Blo 1405522 3165551 := bstep (se 1 (by rfl) ⟨2374163, by rfl⟩ : syracuseStep 3165551 = 4748327) B4748327
theorem B27037061 : Blo 1405522 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B4746707 : Blo 1405522 4746707 := bstep (se 1 (by rfl) ⟨3560030, by rfl⟩ : syracuseStep 4746707 = 7120061) B7120061
theorem B2108999 : Blo 1405522 2108999 := bstep (se 1 (by rfl) ⟨1581749, by rfl⟩ : syracuseStep 2108999 = 3163499) B3163499
theorem B4746977 : Blo 1405522 4746977 := bstep (se 2 (by rfl) ⟨1780116, by rfl⟩ : syracuseStep 4746977 = 3560233) B3560233
theorem B2109179 : Blo 1405522 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B6008681 : Blo 1405522 6008681 := bstep (se 2 (by rfl) ⟨2253255, by rfl⟩ : syracuseStep 6008681 = 4506511) B4506511
theorem B69390229 : Blo 1405522 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B158232527 : Blo 1405522 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B3166271 : Blo 1405522 3166271 := bstep (se 1 (by rfl) ⟨2374703, by rfl⟩ : syracuseStep 3166271 = 4749407) B4749407
theorem B5337161 : Blo 1405522 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B4813033 : Blo 1405522 4813033 := bstep (se 2 (by rfl) ⟨1804887, by rfl⟩ : syracuseStep 4813033 = 3609775) B3609775
theorem B3166505 : Blo 1405522 3166505 := bstep (se 2 (by rfl) ⟨1187439, by rfl⟩ : syracuseStep 3166505 = 2374879) B2374879
theorem B177967459 : Blo 1405522 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B2371943 : Blo 1405522 2371943 := bstep (se 1 (by rfl) ⟨1778957, by rfl⟩ : syracuseStep 2371943 = 3557915) B3557915
theorem B2109851 : Blo 1405522 2109851 := bstep (se 1 (by rfl) ⟨1582388, by rfl⟩ : syracuseStep 2109851 = 3164777) B3164777
theorem B21647917 : Blo 1405522 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B3166775 : Blo 1405522 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B1405691 : Blo 1405522 1405691 := bstep (se 1 (by rfl) ⟨1054268, by rfl⟩ : syracuseStep 1405691 = 2108537) B2108537
theorem B1405759 : Blo 1405522 1405759 := bstep (se 1 (by rfl) ⟨1054319, by rfl⟩ : syracuseStep 1405759 = 2108639) B2108639
theorem B2110271 : Blo 1405522 2110271 := bstep (se 1 (by rfl) ⟨1582703, by rfl⟩ : syracuseStep 2110271 = 3165407) B3165407
theorem B1405787 : Blo 1405522 1405787 := bstep (se 1 (by rfl) ⟨1054340, by rfl⟩ : syracuseStep 1405787 = 2108681) B2108681
theorem B3003247 : Blo 1405522 3003247 := bstep (se 1 (by rfl) ⟨2252435, by rfl⟩ : syracuseStep 3003247 = 4504871) B4504871
theorem B1405855 : Blo 1405522 1405855 := bstep (se 1 (by rfl) ⟨1054391, by rfl⟩ : syracuseStep 1405855 = 2108783) B2108783
theorem B2110415 : Blo 1405522 2110415 := bstep (se 1 (by rfl) ⟨1582811, by rfl⟩ : syracuseStep 2110415 = 3165623) B3165623
theorem B1405935 : Blo 1405522 1405935 := bstep (se 1 (by rfl) ⟨1054451, by rfl⟩ : syracuseStep 1405935 = 2108903) B2108903
theorem B2110457 : Blo 1405522 2110457 := bstep (se 2 (by rfl) ⟨791421, by rfl⟩ : syracuseStep 2110457 = 1582843) B1582843
theorem B2110505 : Blo 1405522 2110505 := bstep (se 2 (by rfl) ⟨791439, by rfl⟩ : syracuseStep 2110505 = 1582879) B1582879
theorem B1406023 : Blo 1405522 1406023 := bstep (se 1 (by rfl) ⟨1054517, by rfl⟩ : syracuseStep 1406023 = 2109035) B2109035
theorem B2110535 : Blo 1405522 2110535 := bstep (se 1 (by rfl) ⟨1582901, by rfl⟩ : syracuseStep 2110535 = 3165803) B3165803
theorem B1406107 : Blo 1405522 1406107 := bstep (se 1 (by rfl) ⟨1054580, by rfl⟩ : syracuseStep 1406107 = 2109161) B2109161
theorem B8008955 : Blo 1405522 8008955 := bstep (se 1 (by rfl) ⟨6006716, by rfl⟩ : syracuseStep 8008955 = 12013433) B12013433
theorem B1406203 : Blo 1405522 1406203 := bstep (se 1 (by rfl) ⟨1054652, by rfl⟩ : syracuseStep 1406203 = 2109305) B2109305
theorem B1406271 : Blo 1405522 1406271 := bstep (se 1 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 1406271 = 2109407) B2109407
theorem B4748759 : Blo 1405522 4748759 := bstep (se 1 (by rfl) ⟨3561569, by rfl⟩ : syracuseStep 4748759 = 7123139) B7123139
theorem B1406439 : Blo 1405522 1406439 := bstep (se 1 (by rfl) ⟨1054829, by rfl⟩ : syracuseStep 1406439 = 2109659) B2109659
theorem B1406447 : Blo 1405522 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B1406555 : Blo 1405522 1406555 := bstep (se 1 (by rfl) ⟨1054916, by rfl⟩ : syracuseStep 1406555 = 2109833) B2109833
theorem B1406619 : Blo 1405522 1406619 := bstep (se 1 (by rfl) ⟨1054964, by rfl⟩ : syracuseStep 1406619 = 2109929) B2109929
theorem B20264651 : Blo 1405522 20264651 := bstep (se 1 (by rfl) ⟨15198488, by rfl⟩ : syracuseStep 20264651 = 30396977) B30396977
theorem B7116497 : Blo 1405522 7116497 := bstep (se 2 (by rfl) ⟨2668686, by rfl⟩ : syracuseStep 7116497 = 5337373) B5337373
theorem B1406703 : Blo 1405522 1406703 := bstep (se 1 (by rfl) ⟨1055027, by rfl⟩ : syracuseStep 1406703 = 2110055) B2110055
theorem B1406791 : Blo 1405522 1406791 := bstep (se 1 (by rfl) ⟨1055093, by rfl⟩ : syracuseStep 1406791 = 2110187) B2110187
theorem B1406811 : Blo 1405522 1406811 := bstep (se 1 (by rfl) ⟨1055108, by rfl⟩ : syracuseStep 1406811 = 2110217) B2110217
theorem B16013213 : Blo 1405522 16013213 := bstep (se 3 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 16013213 = 6004955) B6004955
theorem B1406879 : Blo 1405522 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B2668459 : Blo 1405522 2668459 := bstep (se 1 (by rfl) ⟨2001344, by rfl⟩ : syracuseStep 2668459 = 4002689) B4002689
theorem B3381239 : Blo 1405522 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B1407047 : Blo 1405522 1407047 := bstep (se 1 (by rfl) ⟨1055285, by rfl⟩ : syracuseStep 1407047 = 2110571) B2110571
theorem B3561691 : Blo 1405522 3561691 := bstep (se 1 (by rfl) ⟨2671268, by rfl⟩ : syracuseStep 3561691 = 5342537) B5342537
theorem B1407207 : Blo 1405522 1407207 := bstep (se 1 (by rfl) ⟨1055405, by rfl⟩ : syracuseStep 1407207 = 2110811) B2110811
theorem B22804739 : Blo 1405522 22804739 := bstep (se 1 (by rfl) ⟨17103554, by rfl⟩ : syracuseStep 22804739 = 34207109) B34207109
theorem B10131749 : Blo 1405522 10131749 := bstep (se 4 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 10131749 = 1899703) B1899703
theorem B6011243 : Blo 1405522 6011243 := bstep (se 1 (by rfl) ⟨4508432, by rfl⟩ : syracuseStep 6011243 = 9016865) B9016865
theorem B1407391 : Blo 1405522 1407391 := bstep (se 1 (by rfl) ⟨1055543, by rfl⟩ : syracuseStep 1407391 = 2111087) B2111087
theorem B1407439 : Blo 1405522 1407439 := bstep (se 1 (by rfl) ⟨1055579, by rfl⟩ : syracuseStep 1407439 = 2111159) B2111159
theorem B1407463 : Blo 1405522 1407463 := bstep (se 1 (by rfl) ⟨1055597, by rfl⟩ : syracuseStep 1407463 = 2111195) B2111195
theorem B54049517 : Blo 1405522 54049517 := bstep (se 3 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 54049517 = 20268569) B20268569
theorem B5413643 : Blo 1405522 5413643 := bstep (se 1 (by rfl) ⟨4060232, by rfl⟩ : syracuseStep 5413643 = 8120465) B8120465
theorem B8559371 : Blo 1405522 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B2374447 : Blo 1405522 2374447 := bstep (se 1 (by rfl) ⟨1780835, by rfl⟩ : syracuseStep 2374447 = 3561671) B3561671
theorem B2251577 : Blo 1405522 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B6011995 : Blo 1405522 6011995 := bstep (se 1 (by rfl) ⟨4508996, by rfl⟩ : syracuseStep 6011995 = 9017993) B9017993
theorem B2849897 : Blo 1405522 2849897 := bstep (se 2 (by rfl) ⟨1068711, by rfl⟩ : syracuseStep 2849897 = 2137423) B2137423
theorem B26025209 : Blo 1405522 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B45595979 : Blo 1405522 45595979 := bstep (se 1 (by rfl) ⟨34196984, by rfl⟩ : syracuseStep 45595979 = 68393969) B68393969
theorem B5700959 : Blo 1405522 5700959 := bstep (se 1 (by rfl) ⟨4275719, by rfl⟩ : syracuseStep 5700959 = 8551439) B8551439
theorem B2669993 : Blo 1405522 2669993 := bstep (se 2 (by rfl) ⟨1001247, by rfl⟩ : syracuseStep 2669993 = 2002495) B2002495
theorem B38510153 : Blo 1405522 38510153 := bstep (se 2 (by rfl) ⟨14441307, by rfl⟩ : syracuseStep 38510153 = 28882615) B28882615
theorem B7118765 : Blo 1405522 7118765 := bstep (se 3 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 7118765 = 2669537) B2669537
theorem B14442461 : Blo 1405522 14442461 := bstep (se 3 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 14442461 = 5415923) B5415923
theorem B1581295 : Blo 1405522 1581295 := bstep (se 1 (by rfl) ⟨1185971, by rfl⟩ : syracuseStep 1581295 = 2371943) B2371943
theorem B237289945 : Blo 1405522 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B20562407 : Blo 1405522 20562407 := bstep (se 1 (by rfl) ⟨15421805, by rfl⟩ : syracuseStep 20562407 = 30843611) B30843611
theorem B18530855 : Blo 1405522 18530855 := bstep (se 1 (by rfl) ⟨13898141, by rfl⟩ : syracuseStep 18530855 = 27796283) B27796283
theorem B13509767 : Blo 1405522 13509767 := bstep (se 1 (by rfl) ⟨10132325, by rfl⟩ : syracuseStep 13509767 = 20264651) B20264651
theorem B4744331 : Blo 1405522 4744331 := bstep (se 1 (by rfl) ⟨3558248, by rfl⟩ : syracuseStep 4744331 = 7116497) B7116497
theorem B3163319 : Blo 1405522 3163319 := bstep (se 1 (by rfl) ⟨2372489, by rfl⟩ : syracuseStep 3163319 = 4744979) B4744979
theorem B20284667 : Blo 1405522 20284667 := bstep (se 1 (by rfl) ⟨15213500, by rfl⟩ : syracuseStep 20284667 = 30427001) B30427001
theorem B10675475 : Blo 1405522 10675475 := bstep (se 1 (by rfl) ⟨8006606, by rfl⟩ : syracuseStep 10675475 = 16013213) B16013213
theorem B3163463 : Blo 1405522 3163463 := bstep (se 1 (by rfl) ⟨2372597, by rfl⟩ : syracuseStep 3163463 = 4745195) B4745195
theorem B2254159 : Blo 1405522 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B15205927 : Blo 1405522 15205927 := bstep (se 1 (by rfl) ⟨11404445, by rfl⟩ : syracuseStep 15205927 = 22808891) B22808891
theorem B4007495 : Blo 1405522 4007495 := bstep (se 1 (by rfl) ⟨3005621, by rfl⟩ : syracuseStep 4007495 = 6011243) B6011243
theorem B18024707 : Blo 1405522 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B1779995 : Blo 1405522 1779995 := bstep (se 1 (by rfl) ⟨1334996, by rfl⟩ : syracuseStep 1779995 = 2669993) B2669993
theorem B3164471 : Blo 1405522 3164471 := bstep (se 1 (by rfl) ⟨2373353, by rfl⟩ : syracuseStep 3164471 = 4746707) B4746707
theorem B3164651 : Blo 1405522 3164651 := bstep (se 1 (by rfl) ⟨2373488, by rfl⟩ : syracuseStep 3164651 = 4746977) B4746977
theorem B3557945 : Blo 1405522 3557945 := bstep (se 2 (by rfl) ⟨1334229, by rfl⟩ : syracuseStep 3557945 = 2668459) B2668459
theorem B4745843 : Blo 1405522 4745843 := bstep (se 1 (by rfl) ⟨3559382, by rfl⟩ : syracuseStep 4745843 = 7118765) B7118765
theorem B9628307 : Blo 1405522 9628307 := bstep (se 1 (by rfl) ⟨7221230, by rfl⟩ : syracuseStep 9628307 = 14442461) B14442461
theorem B8121019 : Blo 1405522 8121019 := bstep (se 1 (by rfl) ⟨6090764, by rfl⟩ : syracuseStep 8121019 = 12181529) B12181529
theorem B6417083 : Blo 1405522 6417083 := bstep (se 1 (by rfl) ⟨4812812, by rfl⟩ : syracuseStep 6417083 = 9625625) B9625625
theorem B3558107 : Blo 1405522 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B4745951 : Blo 1405522 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B8006471 : Blo 1405522 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B6417377 : Blo 1405522 6417377 := bstep (se 2 (by rfl) ⟨2406516, by rfl⟩ : syracuseStep 6417377 = 4813033) B4813033
theorem B1781119 : Blo 1405522 1781119 := bstep (se 1 (by rfl) ⟨1335839, by rfl⟩ : syracuseStep 1781119 = 2671679) B2671679
theorem B2108831 : Blo 1405522 2108831 := bstep (se 1 (by rfl) ⟨1581623, by rfl⟩ : syracuseStep 2108831 = 3163247) B3163247
theorem B3165839 : Blo 1405522 3165839 := bstep (se 1 (by rfl) ⟨2374379, by rfl⟩ : syracuseStep 3165839 = 4748759) B4748759
theorem B2109095 : Blo 1405522 2109095 := bstep (se 1 (by rfl) ⟨1581821, by rfl⟩ : syracuseStep 2109095 = 3163643) B3163643
theorem B4746923 : Blo 1405522 4746923 := bstep (se 1 (by rfl) ⟨3560192, by rfl⟩ : syracuseStep 4746923 = 7120385) B7120385
theorem B2109119 : Blo 1405522 2109119 := bstep (se 1 (by rfl) ⟨1581839, by rfl⟩ : syracuseStep 2109119 = 3163679) B3163679
theorem B3165929 : Blo 1405522 3165929 := bstep (se 2 (by rfl) ⟨1187223, by rfl⟩ : syracuseStep 3165929 = 2374447) B2374447
theorem B2109215 : Blo 1405522 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B8007497 : Blo 1405522 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B7122977 : Blo 1405522 7122977 := bstep (se 2 (by rfl) ⟨2671116, by rfl⟩ : syracuseStep 7122977 = 5342233) B5342233
theorem B2109503 : Blo 1405522 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B8015993 : Blo 1405522 8015993 := bstep (se 2 (by rfl) ⟨3005997, by rfl⟩ : syracuseStep 8015993 = 6011995) B6011995
theorem B6754499 : Blo 1405522 6754499 := bstep (se 1 (by rfl) ⟨5065874, by rfl⟩ : syracuseStep 6754499 = 10131749) B10131749
theorem B4747463 : Blo 1405522 4747463 := bstep (se 1 (by rfl) ⟨3560597, by rfl⟩ : syracuseStep 4747463 = 7121195) B7121195
theorem B2109695 : Blo 1405522 2109695 := bstep (se 1 (by rfl) ⟨1582271, by rfl⟩ : syracuseStep 2109695 = 3164543) B3164543
theorem B2109737 : Blo 1405522 2109737 := bstep (se 2 (by rfl) ⟨791151, by rfl⟩ : syracuseStep 2109737 = 1582303) B1582303
theorem B36033011 : Blo 1405522 36033011 := bstep (se 1 (by rfl) ⟨27024758, by rfl⟩ : syracuseStep 36033011 = 54049517) B54049517
theorem B3609095 : Blo 1405522 3609095 := bstep (se 1 (by rfl) ⟨2706821, by rfl⟩ : syracuseStep 3609095 = 5413643) B5413643
theorem B5706247 : Blo 1405522 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B2110007 : Blo 1405522 2110007 := bstep (se 1 (by rfl) ⟨1582505, by rfl⟩ : syracuseStep 2110007 = 3165011) B3165011
theorem B24048251 : Blo 1405522 24048251 := bstep (se 1 (by rfl) ⟨18036188, by rfl⟩ : syracuseStep 24048251 = 36072377) B36072377
theorem B1405723 : Blo 1405522 1405723 := bstep (se 1 (by rfl) ⟨1054292, by rfl⟩ : syracuseStep 1405723 = 2108585) B2108585
theorem B2110247 : Blo 1405522 2110247 := bstep (se 1 (by rfl) ⟨1582685, by rfl⟩ : syracuseStep 2110247 = 3165371) B3165371
theorem B30397319 : Blo 1405522 30397319 := bstep (se 1 (by rfl) ⟨22797989, by rfl⟩ : syracuseStep 30397319 = 45595979) B45595979
theorem B2110367 : Blo 1405522 2110367 := bstep (se 1 (by rfl) ⟨1582775, by rfl⟩ : syracuseStep 2110367 = 3165551) B3165551
theorem B1405999 : Blo 1405522 1405999 := bstep (se 1 (by rfl) ⟨1054499, by rfl⟩ : syracuseStep 1405999 = 2108999) B2108999
theorem B1406119 : Blo 1405522 1406119 := bstep (se 1 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 1406119 = 2109179) B2109179
theorem B2110841 : Blo 1405522 2110841 := bstep (se 2 (by rfl) ⟨791565, by rfl⟩ : syracuseStep 2110841 = 1583131) B1583131
theorem B2110847 : Blo 1405522 2110847 := bstep (se 1 (by rfl) ⟨1583135, by rfl⟩ : syracuseStep 2110847 = 3166271) B3166271
theorem B3905023 : Blo 1405522 3905023 := bstep (se 1 (by rfl) ⟨2928767, by rfl⟩ : syracuseStep 3905023 = 5857535) B5857535
theorem B2111003 : Blo 1405522 2111003 := bstep (se 1 (by rfl) ⟨1583252, by rfl⟩ : syracuseStep 2111003 = 3166505) B3166505
theorem B115455557 : Blo 1405522 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B1406567 : Blo 1405522 1406567 := bstep (se 1 (by rfl) ⟨1054925, by rfl⟩ : syracuseStep 1406567 = 2109851) B2109851
theorem B4748921 : Blo 1405522 4748921 := bstep (se 2 (by rfl) ⟨1780845, by rfl⟩ : syracuseStep 4748921 = 3561691) B3561691
theorem B2111183 : Blo 1405522 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B10131263 : Blo 1405522 10131263 := bstep (se 1 (by rfl) ⟨7598447, by rfl⟩ : syracuseStep 10131263 = 15196895) B15196895
theorem B8558399 : Blo 1405522 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B1406847 : Blo 1405522 1406847 := bstep (se 1 (by rfl) ⟨1055135, by rfl⟩ : syracuseStep 1406847 = 2110271) B2110271
theorem B1406943 : Blo 1405522 1406943 := bstep (se 1 (by rfl) ⟨1055207, by rfl⟩ : syracuseStep 1406943 = 2110415) B2110415
theorem B1406971 : Blo 1405522 1406971 := bstep (se 1 (by rfl) ⟨1055228, by rfl⟩ : syracuseStep 1406971 = 2110457) B2110457
theorem B1407003 : Blo 1405522 1407003 := bstep (se 1 (by rfl) ⟨1055252, by rfl⟩ : syracuseStep 1407003 = 2110505) B2110505
theorem B1407023 : Blo 1405522 1407023 := bstep (se 1 (by rfl) ⟨1055267, by rfl⟩ : syracuseStep 1407023 = 2110535) B2110535
theorem B5339303 : Blo 1405522 5339303 := bstep (se 1 (by rfl) ⟨4004477, by rfl⟩ : syracuseStep 5339303 = 8008955) B8008955
theorem B1407143 : Blo 1405522 1407143 := bstep (se 1 (by rfl) ⟨1055357, by rfl⟩ : syracuseStep 1407143 = 2110715) B2110715
theorem B4004329 : Blo 1405522 4004329 := bstep (se 2 (by rfl) ⟨1501623, by rfl⟩ : syracuseStep 4004329 = 3003247) B3003247
theorem B10131979 : Blo 1405522 10131979 := bstep (se 1 (by rfl) ⟨7598984, by rfl⟩ : syracuseStep 10131979 = 15197969) B15197969
theorem B2251423 : Blo 1405522 2251423 := bstep (se 1 (by rfl) ⟨1688567, by rfl⟩ : syracuseStep 2251423 = 3377135) B3377135
theorem B4004603 : Blo 1405522 4004603 := bstep (se 1 (by rfl) ⟨3003452, by rfl⟩ : syracuseStep 4004603 = 6006905) B6006905
theorem B15203159 : Blo 1405522 15203159 := bstep (se 1 (by rfl) ⟨11402369, by rfl⟩ : syracuseStep 15203159 = 22804739) B22804739
theorem B3562451 : Blo 1405522 3562451 := bstep (se 1 (by rfl) ⟨2671838, by rfl⟩ : syracuseStep 3562451 = 5343677) B5343677
theorem B2669689 : Blo 1405522 2669689 := bstep (se 2 (by rfl) ⟨1001133, by rfl⟩ : syracuseStep 2669689 = 2002267) B2002267
theorem B10673531 : Blo 1405522 10673531 := bstep (se 1 (by rfl) ⟨8005148, by rfl⟩ : syracuseStep 10673531 = 16010297) B16010297
theorem B1899931 : Blo 1405522 1899931 := bstep (se 1 (by rfl) ⟨1424948, by rfl⟩ : syracuseStep 1899931 = 2849897) B2849897
theorem B9133505 : Blo 1405522 9133505 := bstep (se 2 (by rfl) ⟨3425064, by rfl⟩ : syracuseStep 9133505 = 6850129) B6850129
theorem B6004205 : Blo 1405522 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B17350139 : Blo 1405522 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B3800639 : Blo 1405522 3800639 := bstep (se 1 (by rfl) ⟨2850479, by rfl⟩ : syracuseStep 3800639 = 5700959) B5700959
theorem B25673435 : Blo 1405522 25673435 := bstep (se 1 (by rfl) ⟨19255076, by rfl⟩ : syracuseStep 25673435 = 38510153) B38510153
theorem B92520305 : Blo 1405522 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B4005787 : Blo 1405522 4005787 := bstep (se 1 (by rfl) ⟨3004340, by rfl⟩ : syracuseStep 4005787 = 6008681) B6008681
theorem B105488351 : Blo 1405522 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B12353903 : Blo 1405522 12353903 := bstep (se 1 (by rfl) ⟨9265427, by rfl⟩ : syracuseStep 12353903 = 18530855) B18530855
theorem B16032167 : Blo 1405522 16032167 := bstep (se 1 (by rfl) ⟨12024125, by rfl⟩ : syracuseStep 16032167 = 24048251) B24048251
theorem B13509305 : Blo 1405522 13509305 := bstep (se 2 (by rfl) ⟨5065989, by rfl⟩ : syracuseStep 13509305 = 10131979) B10131979
theorem B3162887 : Blo 1405522 3162887 := bstep (se 1 (by rfl) ⟨2372165, by rfl⟩ : syracuseStep 3162887 = 4744331) B4744331
theorem B10135037 : Blo 1405522 10135037 := bstep (se 3 (by rfl) ⟨1900319, by rfl⟩ : syracuseStep 10135037 = 3800639) B3800639
theorem B307881485 : Blo 1405522 307881485 := bstep (se 3 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 307881485 = 115455557) B115455557
theorem B3163895 : Blo 1405522 3163895 := bstep (se 1 (by rfl) ⟨2372921, by rfl⟩ : syracuseStep 3163895 = 4745843) B4745843
theorem B4278055 : Blo 1405522 4278055 := bstep (se 1 (by rfl) ⟨3208541, by rfl⟩ : syracuseStep 4278055 = 6417083) B6417083
theorem B3163967 : Blo 1405522 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B2533241 : Blo 1405522 2533241 := bstep (se 2 (by rfl) ⟨949965, by rfl⟩ : syracuseStep 2533241 = 1899931) B1899931
theorem B10135439 : Blo 1405522 10135439 := bstep (se 1 (by rfl) ⟨7601579, by rfl⟩ : syracuseStep 10135439 = 15203159) B15203159
theorem B4278251 : Blo 1405522 4278251 := bstep (se 1 (by rfl) ⟨3208688, by rfl⟩ : syracuseStep 4278251 = 6417377) B6417377
theorem B6089003 : Blo 1405522 6089003 := bstep (se 1 (by rfl) ⟨4566752, by rfl⟩ : syracuseStep 6089003 = 9133505) B9133505
theorem B3164615 : Blo 1405522 3164615 := bstep (se 1 (by rfl) ⟨2373461, by rfl⟩ : syracuseStep 3164615 = 4746923) B4746923
theorem B17115623 : Blo 1405522 17115623 := bstep (se 1 (by rfl) ⟨12836717, by rfl⟩ : syracuseStep 17115623 = 25673435) B25673435
theorem B61680203 : Blo 1405522 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B5343995 : Blo 1405522 5343995 := bstep (se 1 (by rfl) ⟨4007996, by rfl⟩ : syracuseStep 5343995 = 8015993) B8015993
theorem B3164975 : Blo 1405522 3164975 := bstep (se 1 (by rfl) ⟨2373731, by rfl⟩ : syracuseStep 3164975 = 4747463) B4747463
theorem B2108393 : Blo 1405522 2108393 := bstep (se 2 (by rfl) ⟨790647, by rfl⟩ : syracuseStep 2108393 = 1581295) B1581295
theorem B13708271 : Blo 1405522 13708271 := bstep (se 1 (by rfl) ⟨10281203, by rfl⟩ : syracuseStep 13708271 = 20562407) B20562407
theorem B24022007 : Blo 1405522 24022007 := bstep (se 1 (by rfl) ⟨18016505, by rfl⟩ : syracuseStep 24022007 = 36033011) B36033011
theorem B316386593 : Blo 1405522 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B4746653 : Blo 1405522 4746653 := bstep (se 3 (by rfl) ⟨889997, by rfl⟩ : syracuseStep 4746653 = 1779995) B1779995
theorem B9006511 : Blo 1405522 9006511 := bstep (se 1 (by rfl) ⟨6754883, by rfl⟩ : syracuseStep 9006511 = 13509767) B13509767
theorem B2108879 : Blo 1405522 2108879 := bstep (se 1 (by rfl) ⟨1581659, by rfl⟩ : syracuseStep 2108879 = 3163319) B3163319
theorem B3001897 : Blo 1405522 3001897 := bstep (se 2 (by rfl) ⟨1125711, by rfl⟩ : syracuseStep 3001897 = 2251423) B2251423
theorem B2108975 : Blo 1405522 2108975 := bstep (se 1 (by rfl) ⟨1581731, by rfl⟩ : syracuseStep 2108975 = 3163463) B3163463
theorem B3165947 : Blo 1405522 3165947 := bstep (se 1 (by rfl) ⟨2374460, by rfl⟩ : syracuseStep 3165947 = 4748921) B4748921
theorem B6754175 : Blo 1405522 6754175 := bstep (se 1 (by rfl) ⟨5065631, by rfl⟩ : syracuseStep 6754175 = 10131263) B10131263
theorem B5705599 : Blo 1405522 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B3559535 : Blo 1405522 3559535 := bstep (se 1 (by rfl) ⟨2669651, by rfl⟩ : syracuseStep 3559535 = 5339303) B5339303
theorem B3559585 : Blo 1405522 3559585 := bstep (se 2 (by rfl) ⟨1334844, by rfl⟩ : syracuseStep 3559585 = 2669689) B2669689
theorem B10686653 : Blo 1405522 10686653 := bstep (se 3 (by rfl) ⟨2003747, by rfl⟩ : syracuseStep 10686653 = 4007495) B4007495
theorem B2109647 : Blo 1405522 2109647 := bstep (se 1 (by rfl) ⟨1582235, by rfl⟩ : syracuseStep 2109647 = 3164471) B3164471
theorem B2109767 : Blo 1405522 2109767 := bstep (se 1 (by rfl) ⟨1582325, by rfl⟩ : syracuseStep 2109767 = 3164651) B3164651
theorem B2371963 : Blo 1405522 2371963 := bstep (se 1 (by rfl) ⟨1778972, by rfl⟩ : syracuseStep 2371963 = 3557945) B3557945
theorem B12022181 : Blo 1405522 12022181 := bstep (se 4 (by rfl) ⟨1127079, by rfl⟩ : syracuseStep 12022181 = 2254159) B2254159
theorem B6418871 : Blo 1405522 6418871 := bstep (se 1 (by rfl) ⟨4814153, by rfl⟩ : syracuseStep 6418871 = 9628307) B9628307
theorem B2372071 : Blo 1405522 2372071 := bstep (se 1 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 2372071 = 3558107) B3558107
theorem B5337647 : Blo 1405522 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B5206697 : Blo 1405522 5206697 := bstep (se 2 (by rfl) ⟨1952511, by rfl⟩ : syracuseStep 5206697 = 3905023) B3905023
theorem B7115687 : Blo 1405522 7115687 := bstep (se 1 (by rfl) ⟨5336765, by rfl⟩ : syracuseStep 7115687 = 10673531) B10673531
theorem B1405887 : Blo 1405522 1405887 := bstep (se 1 (by rfl) ⟨1054415, by rfl⟩ : syracuseStep 1405887 = 2108831) B2108831
theorem B4002803 : Blo 1405522 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B2110559 : Blo 1405522 2110559 := bstep (se 1 (by rfl) ⟨1582919, by rfl⟩ : syracuseStep 2110559 = 3165839) B3165839
theorem B1406063 : Blo 1405522 1406063 := bstep (se 1 (by rfl) ⟨1054547, by rfl⟩ : syracuseStep 1406063 = 2109095) B2109095
theorem B1406079 : Blo 1405522 1406079 := bstep (se 1 (by rfl) ⟨1054559, by rfl⟩ : syracuseStep 1406079 = 2109119) B2109119
theorem B2110619 : Blo 1405522 2110619 := bstep (se 1 (by rfl) ⟨1582964, by rfl⟩ : syracuseStep 2110619 = 3165929) B3165929
theorem B1406143 : Blo 1405522 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B5338331 : Blo 1405522 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B70325567 : Blo 1405522 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B4748651 : Blo 1405522 4748651 := bstep (se 1 (by rfl) ⟨3561488, by rfl⟩ : syracuseStep 4748651 = 7122977) B7122977
theorem B1406335 : Blo 1405522 1406335 := bstep (se 1 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 1406335 = 2109503) B2109503
theorem B4502999 : Blo 1405522 4502999 := bstep (se 1 (by rfl) ⟨3377249, by rfl⟩ : syracuseStep 4502999 = 6754499) B6754499
theorem B1406463 : Blo 1405522 1406463 := bstep (se 1 (by rfl) ⟨1054847, by rfl⟩ : syracuseStep 1406463 = 2109695) B2109695
theorem B1406491 : Blo 1405522 1406491 := bstep (se 1 (by rfl) ⟨1054868, by rfl⟩ : syracuseStep 1406491 = 2109737) B2109737
theorem B1406671 : Blo 1405522 1406671 := bstep (se 1 (by rfl) ⟨1055003, by rfl⟩ : syracuseStep 1406671 = 2110007) B2110007
theorem B1406831 : Blo 1405522 1406831 := bstep (se 1 (by rfl) ⟨1055123, by rfl⟩ : syracuseStep 1406831 = 2110247) B2110247
theorem B20264879 : Blo 1405522 20264879 := bstep (se 1 (by rfl) ⟨15198659, by rfl⟩ : syracuseStep 20264879 = 30397319) B30397319
theorem B1406911 : Blo 1405522 1406911 := bstep (se 1 (by rfl) ⟨1055183, by rfl⟩ : syracuseStep 1406911 = 2110367) B2110367
theorem B5339105 : Blo 1405522 5339105 := bstep (se 2 (by rfl) ⟨2002164, by rfl⟩ : syracuseStep 5339105 = 4004329) B4004329
theorem B7608329 : Blo 1405522 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B13523111 : Blo 1405522 13523111 := bstep (se 1 (by rfl) ⟨10142333, by rfl⟩ : syracuseStep 13523111 = 20284667) B20284667
theorem B7116983 : Blo 1405522 7116983 := bstep (se 1 (by rfl) ⟨5337737, by rfl⟩ : syracuseStep 7116983 = 10675475) B10675475
theorem B10828025 : Blo 1405522 10828025 := bstep (se 2 (by rfl) ⟨4060509, by rfl⟩ : syracuseStep 10828025 = 8121019) B8121019
theorem B1407227 : Blo 1405522 1407227 := bstep (se 1 (by rfl) ⟨1055420, by rfl⟩ : syracuseStep 1407227 = 2110841) B2110841
theorem B1407231 : Blo 1405522 1407231 := bstep (se 1 (by rfl) ⟨1055423, by rfl⟩ : syracuseStep 1407231 = 2110847) B2110847
theorem B1407335 : Blo 1405522 1407335 := bstep (se 1 (by rfl) ⟨1055501, by rfl⟩ : syracuseStep 1407335 = 2111003) B2111003
theorem B1407455 : Blo 1405522 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B9624253 : Blo 1405522 9624253 := bstep (se 3 (by rfl) ⟨1804547, by rfl⟩ : syracuseStep 9624253 = 3609095) B3609095
theorem B12016471 : Blo 1405522 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B2669735 : Blo 1405522 2669735 := bstep (se 1 (by rfl) ⟨2002301, by rfl⟩ : syracuseStep 2669735 = 4004603) B4004603
theorem B2374825 : Blo 1405522 2374825 := bstep (se 2 (by rfl) ⟨890559, by rfl⟩ : syracuseStep 2374825 = 1781119) B1781119
theorem B2374967 : Blo 1405522 2374967 := bstep (se 1 (by rfl) ⟨1781225, by rfl⟩ : syracuseStep 2374967 = 3562451) B3562451
theorem B20274569 : Blo 1405522 20274569 := bstep (se 2 (by rfl) ⟨7602963, by rfl⟩ : syracuseStep 20274569 = 15205927) B15205927
theorem B11566759 : Blo 1405522 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B5341049 : Blo 1405522 5341049 := bstep (se 2 (by rfl) ⟨2002893, by rfl⟩ : syracuseStep 5341049 = 4005787) B4005787
theorem B3162617 : Blo 1405522 3162617 := bstep (se 2 (by rfl) ⟨1185981, by rfl⟩ : syracuseStep 3162617 = 2371963) B2371963
theorem B4743791 : Blo 1405522 4743791 := bstep (se 1 (by rfl) ⟨3557843, by rfl⟩ : syracuseStep 4743791 = 7115687) B7115687
theorem B3162761 : Blo 1405522 3162761 := bstep (se 2 (by rfl) ⟨1186035, by rfl⟩ : syracuseStep 3162761 = 2372071) B2372071
theorem B46883711 : Blo 1405522 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B13509919 : Blo 1405522 13509919 := bstep (se 1 (by rfl) ⟨10132439, by rfl⟩ : syracuseStep 13509919 = 20264879) B20264879
theorem B2852167 : Blo 1405522 2852167 := bstep (se 1 (by rfl) ⟨2139125, by rfl⟩ : syracuseStep 2852167 = 4278251) B4278251
theorem B5072219 : Blo 1405522 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B4744655 : Blo 1405522 4744655 := bstep (se 1 (by rfl) ⟨3558491, by rfl⟩ : syracuseStep 4744655 = 7116983) B7116983
theorem B7218683 : Blo 1405522 7218683 := bstep (se 1 (by rfl) ⟨5414012, by rfl⟩ : syracuseStep 7218683 = 10828025) B10828025
theorem B1779823 : Blo 1405522 1779823 := bstep (se 1 (by rfl) ⟨1334867, by rfl⟩ : syracuseStep 1779823 = 2669735) B2669735
theorem B1583311 : Blo 1405522 1583311 := bstep (se 1 (by rfl) ⟨1187483, by rfl⟩ : syracuseStep 1583311 = 2374967) B2374967
theorem B3164435 : Blo 1405522 3164435 := bstep (se 1 (by rfl) ⟨2373326, by rfl⟩ : syracuseStep 3164435 = 4746653) B4746653
theorem B5704073 : Blo 1405522 5704073 := bstep (se 2 (by rfl) ⟨2139027, by rfl⟩ : syracuseStep 5704073 = 4278055) B4278055
theorem B4746113 : Blo 1405522 4746113 := bstep (se 2 (by rfl) ⟨1779792, by rfl⟩ : syracuseStep 4746113 = 3559585) B3559585
theorem B8235935 : Blo 1405522 8235935 := bstep (se 1 (by rfl) ⟨6176951, by rfl⟩ : syracuseStep 8235935 = 12353903) B12353903
theorem B8014787 : Blo 1405522 8014787 := bstep (se 1 (by rfl) ⟨6011090, by rfl⟩ : syracuseStep 8014787 = 12022181) B12022181
theorem B4279247 : Blo 1405522 4279247 := bstep (se 1 (by rfl) ⟨3209435, by rfl⟩ : syracuseStep 4279247 = 6418871) B6418871
theorem B3558431 : Blo 1405522 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B9006203 : Blo 1405522 9006203 := bstep (se 1 (by rfl) ⟨6754652, by rfl⟩ : syracuseStep 9006203 = 13509305) B13509305
theorem B2108591 : Blo 1405522 2108591 := bstep (se 1 (by rfl) ⟨1581443, by rfl⟩ : syracuseStep 2108591 = 3162887) B3162887
theorem B3558887 : Blo 1405522 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B3165767 : Blo 1405522 3165767 := bstep (se 1 (by rfl) ⟨2374325, by rfl⟩ : syracuseStep 3165767 = 4748651) B4748651
theorem B12832337 : Blo 1405522 12832337 := bstep (se 2 (by rfl) ⟨4812126, by rfl⟩ : syracuseStep 12832337 = 9624253) B9624253
theorem B205254323 : Blo 1405522 205254323 := bstep (se 1 (by rfl) ⟨153940742, by rfl⟩ : syracuseStep 205254323 = 307881485) B307881485
theorem B2109263 : Blo 1405522 2109263 := bstep (se 1 (by rfl) ⟨1581947, by rfl⟩ : syracuseStep 2109263 = 3163895) B3163895
theorem B2109311 : Blo 1405522 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B3559403 : Blo 1405522 3559403 := bstep (se 1 (by rfl) ⟨2669552, by rfl⟩ : syracuseStep 3559403 = 5339105) B5339105
theorem B9015407 : Blo 1405522 9015407 := bstep (se 1 (by rfl) ⟨6761555, by rfl⟩ : syracuseStep 9015407 = 13523111) B13523111
theorem B4059335 : Blo 1405522 4059335 := bstep (se 1 (by rfl) ⟨3044501, by rfl⟩ : syracuseStep 4059335 = 6089003) B6089003
theorem B3166433 : Blo 1405522 3166433 := bstep (se 2 (by rfl) ⟨1187412, by rfl⟩ : syracuseStep 3166433 = 2374825) B2374825
theorem B2109743 : Blo 1405522 2109743 := bstep (se 1 (by rfl) ⟨1582307, by rfl⟩ : syracuseStep 2109743 = 3164615) B3164615
theorem B41120135 : Blo 1405522 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B2109983 : Blo 1405522 2109983 := bstep (se 1 (by rfl) ⟨1582487, by rfl⟩ : syracuseStep 2109983 = 3164975) B3164975
theorem B1405595 : Blo 1405522 1405595 := bstep (se 1 (by rfl) ⟨1054196, by rfl⟩ : syracuseStep 1405595 = 2108393) B2108393
theorem B9138847 : Blo 1405522 9138847 := bstep (se 1 (by rfl) ⟨6854135, by rfl⟩ : syracuseStep 9138847 = 13708271) B13708271
theorem B4002529 : Blo 1405522 4002529 := bstep (se 2 (by rfl) ⟨1500948, by rfl⟩ : syracuseStep 4002529 = 3001897) B3001897
theorem B210924395 : Blo 1405522 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B15422345 : Blo 1405522 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B1405919 : Blo 1405522 1405919 := bstep (se 1 (by rfl) ⟨1054439, by rfl⟩ : syracuseStep 1405919 = 2108879) B2108879
theorem B6755309 : Blo 1405522 6755309 := bstep (se 3 (by rfl) ⟨1266620, by rfl⟩ : syracuseStep 6755309 = 2533241) B2533241
theorem B1405983 : Blo 1405522 1405983 := bstep (se 1 (by rfl) ⟨1054487, by rfl⟩ : syracuseStep 1405983 = 2108975) B2108975
theorem B2110631 : Blo 1405522 2110631 := bstep (se 1 (by rfl) ⟨1582973, by rfl⟩ : syracuseStep 2110631 = 3165947) B3165947
theorem B7607465 : Blo 1405522 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B3560699 : Blo 1405522 3560699 := bstep (se 1 (by rfl) ⟨2670524, by rfl⟩ : syracuseStep 3560699 = 5341049) B5341049
theorem B4502783 : Blo 1405522 4502783 := bstep (se 1 (by rfl) ⟨3377087, by rfl⟩ : syracuseStep 4502783 = 6754175) B6754175
theorem B2373023 : Blo 1405522 2373023 := bstep (se 1 (by rfl) ⟨1779767, by rfl⟩ : syracuseStep 2373023 = 3559535) B3559535
theorem B7124435 : Blo 1405522 7124435 := bstep (se 1 (by rfl) ⟨5343326, by rfl⟩ : syracuseStep 7124435 = 10686653) B10686653
theorem B1406431 : Blo 1405522 1406431 := bstep (se 1 (by rfl) ⟨1054823, by rfl⟩ : syracuseStep 1406431 = 2109647) B2109647
theorem B1406511 : Blo 1405522 1406511 := bstep (se 1 (by rfl) ⟨1054883, by rfl⟩ : syracuseStep 1406511 = 2109767) B2109767
theorem B10688111 : Blo 1405522 10688111 := bstep (se 1 (by rfl) ⟨8016083, by rfl⟩ : syracuseStep 10688111 = 16032167) B16032167
theorem B3471131 : Blo 1405522 3471131 := bstep (se 1 (by rfl) ⟨2603348, by rfl⟩ : syracuseStep 3471131 = 5206697) B5206697
theorem B2668535 : Blo 1405522 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B1407039 : Blo 1405522 1407039 := bstep (se 1 (by rfl) ⟨1055279, by rfl⟩ : syracuseStep 1407039 = 2110559) B2110559
theorem B1407079 : Blo 1405522 1407079 := bstep (se 1 (by rfl) ⟨1055309, by rfl⟩ : syracuseStep 1407079 = 2110619) B2110619
theorem B6756691 : Blo 1405522 6756691 := bstep (se 1 (by rfl) ⟨5067518, by rfl⟩ : syracuseStep 6756691 = 10135037) B10135037
theorem B16021961 : Blo 1405522 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B12007997 : Blo 1405522 12007997 := bstep (se 3 (by rfl) ⟨2251499, by rfl⟩ : syracuseStep 12007997 = 4502999) B4502999
theorem B6756959 : Blo 1405522 6756959 := bstep (se 1 (by rfl) ⟨5067719, by rfl⟩ : syracuseStep 6756959 = 10135439) B10135439
theorem B11410415 : Blo 1405522 11410415 := bstep (se 1 (by rfl) ⟨8557811, by rfl⟩ : syracuseStep 11410415 = 17115623) B17115623
theorem B3562663 : Blo 1405522 3562663 := bstep (se 1 (by rfl) ⟨2671997, by rfl⟩ : syracuseStep 3562663 = 5343995) B5343995
theorem B12008681 : Blo 1405522 12008681 := bstep (se 2 (by rfl) ⟨4503255, by rfl⟩ : syracuseStep 12008681 = 9006511) B9006511
theorem B16014671 : Blo 1405522 16014671 := bstep (se 1 (by rfl) ⟨12011003, by rfl⟩ : syracuseStep 16014671 = 24022007) B24022007
theorem B13516379 : Blo 1405522 13516379 := bstep (se 1 (by rfl) ⟨10137284, by rfl⟩ : syracuseStep 13516379 = 20274569) B20274569
theorem B3162527 : Blo 1405522 3162527 := bstep (se 1 (by rfl) ⟨2371895, by rfl⟩ : syracuseStep 3162527 = 4743791) B4743791
theorem B140616263 : Blo 1405522 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B10281563 : Blo 1405522 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B5071643 : Blo 1405522 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B1582015 : Blo 1405522 1582015 := bstep (se 1 (by rfl) ⟨1186511, by rfl⟩ : syracuseStep 1582015 = 2373023) B2373023
theorem B3163103 : Blo 1405522 3163103 := bstep (se 1 (by rfl) ⟨2372327, by rfl⟩ : syracuseStep 3163103 = 4744655) B4744655
theorem B1779023 : Blo 1405522 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B3802715 : Blo 1405522 3802715 := bstep (se 1 (by rfl) ⟨2852036, by rfl⟩ : syracuseStep 3802715 = 5704073) B5704073
theorem B8005331 : Blo 1405522 8005331 := bstep (se 1 (by rfl) ⟨6003998, by rfl⟩ : syracuseStep 8005331 = 12007997) B12007997
theorem B3802889 : Blo 1405522 3802889 := bstep (se 2 (by rfl) ⟨1426083, by rfl⟩ : syracuseStep 3802889 = 2852167) B2852167
theorem B3164075 : Blo 1405522 3164075 := bstep (se 1 (by rfl) ⟨2373056, by rfl⟩ : syracuseStep 3164075 = 4746113) B4746113
theorem B5490623 : Blo 1405522 5490623 := bstep (se 1 (by rfl) ⟨4117967, by rfl⟩ : syracuseStep 5490623 = 8235935) B8235935
theorem B5343191 : Blo 1405522 5343191 := bstep (se 1 (by rfl) ⟨4007393, by rfl⟩ : syracuseStep 5343191 = 8014787) B8014787
theorem B2852831 : Blo 1405522 2852831 := bstep (se 1 (by rfl) ⟨2139623, by rfl⟩ : syracuseStep 2852831 = 4279247) B4279247
theorem B8005787 : Blo 1405522 8005787 := bstep (se 1 (by rfl) ⟨6004340, by rfl⟩ : syracuseStep 8005787 = 12008681) B12008681
theorem B10676447 : Blo 1405522 10676447 := bstep (se 1 (by rfl) ⟨8007335, by rfl⟩ : syracuseStep 10676447 = 16014671) B16014671
theorem B8554891 : Blo 1405522 8554891 := bstep (se 1 (by rfl) ⟨6416168, by rfl⟩ : syracuseStep 8554891 = 12832337) B12832337
theorem B2706223 : Blo 1405522 2706223 := bstep (se 1 (by rfl) ⟨2029667, by rfl⟩ : syracuseStep 2706223 = 4059335) B4059335
theorem B27413423 : Blo 1405522 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B2108411 : Blo 1405522 2108411 := bstep (se 1 (by rfl) ⟨1581308, by rfl⟩ : syracuseStep 2108411 = 3162617) B3162617
theorem B2108507 : Blo 1405522 2108507 := bstep (se 1 (by rfl) ⟨1581380, by rfl⟩ : syracuseStep 2108507 = 3162761) B3162761
theorem B31255807 : Blo 1405522 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B3001855 : Blo 1405522 3001855 := bstep (se 1 (by rfl) ⟨2251391, by rfl⟩ : syracuseStep 3001855 = 4502783) B4502783
theorem B12185129 : Blo 1405522 12185129 := bstep (se 2 (by rfl) ⟨4569423, by rfl⟩ : syracuseStep 12185129 = 9138847) B9138847
theorem B5336705 : Blo 1405522 5336705 := bstep (se 2 (by rfl) ⟨2001264, by rfl⟩ : syracuseStep 5336705 = 4002529) B4002529
theorem B4812455 : Blo 1405522 4812455 := bstep (se 1 (by rfl) ⟨3609341, by rfl⟩ : syracuseStep 4812455 = 7218683) B7218683
theorem B2109623 : Blo 1405522 2109623 := bstep (se 1 (by rfl) ⟨1582217, by rfl⟩ : syracuseStep 2109623 = 3164435) B3164435
theorem B18018557 : Blo 1405522 18018557 := bstep (se 3 (by rfl) ⟨3378479, by rfl⟩ : syracuseStep 18018557 = 6756959) B6756959
theorem B7606943 : Blo 1405522 7606943 := bstep (se 1 (by rfl) ⟨5705207, by rfl⟩ : syracuseStep 7606943 = 11410415) B11410415
theorem B2372287 : Blo 1405522 2372287 := bstep (se 1 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 2372287 = 3558431) B3558431
theorem B1405727 : Blo 1405522 1405727 := bstep (se 1 (by rfl) ⟨1054295, by rfl⟩ : syracuseStep 1405727 = 2108591) B2108591
theorem B2372591 : Blo 1405522 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B2110511 : Blo 1405522 2110511 := bstep (se 1 (by rfl) ⟨1582883, by rfl⟩ : syracuseStep 2110511 = 3165767) B3165767
theorem B136836215 : Blo 1405522 136836215 := bstep (se 1 (by rfl) ⟨102627161, by rfl⟩ : syracuseStep 136836215 = 205254323) B205254323
theorem B1406175 : Blo 1405522 1406175 := bstep (se 1 (by rfl) ⟨1054631, by rfl⟩ : syracuseStep 1406175 = 2109263) B2109263
theorem B1406207 : Blo 1405522 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B2372935 : Blo 1405522 2372935 := bstep (se 1 (by rfl) ⟨1779701, by rfl⟩ : syracuseStep 2372935 = 3559403) B3559403
theorem B6010271 : Blo 1405522 6010271 := bstep (se 1 (by rfl) ⟨4507703, by rfl⟩ : syracuseStep 6010271 = 9015407) B9015407
theorem B2373097 : Blo 1405522 2373097 := bstep (se 2 (by rfl) ⟨889911, by rfl⟩ : syracuseStep 2373097 = 1779823) B1779823
theorem B2110955 : Blo 1405522 2110955 := bstep (se 1 (by rfl) ⟨1583216, by rfl⟩ : syracuseStep 2110955 = 3166433) B3166433
theorem B1406495 : Blo 1405522 1406495 := bstep (se 1 (by rfl) ⟨1054871, by rfl⟩ : syracuseStep 1406495 = 2109743) B2109743
theorem B2111081 : Blo 1405522 2111081 := bstep (se 2 (by rfl) ⟨791655, by rfl⟩ : syracuseStep 2111081 = 1583311) B1583311
theorem B1406655 : Blo 1405522 1406655 := bstep (se 1 (by rfl) ⟨1054991, by rfl⟩ : syracuseStep 1406655 = 2109983) B2109983
theorem B9008921 : Blo 1405522 9008921 := bstep (se 2 (by rfl) ⟨3378345, by rfl⟩ : syracuseStep 9008921 = 6756691) B6756691
theorem B4503539 : Blo 1405522 4503539 := bstep (se 1 (by rfl) ⟨3377654, by rfl⟩ : syracuseStep 4503539 = 6755309) B6755309
theorem B1407087 : Blo 1405522 1407087 := bstep (se 1 (by rfl) ⟨1055315, by rfl⟩ : syracuseStep 1407087 = 2110631) B2110631
theorem B2373799 : Blo 1405522 2373799 := bstep (se 1 (by rfl) ⟨1780349, by rfl⟩ : syracuseStep 2373799 = 3560699) B3560699
theorem B3381479 : Blo 1405522 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B4749623 : Blo 1405522 4749623 := bstep (se 1 (by rfl) ⟨3562217, by rfl⟩ : syracuseStep 4749623 = 7124435) B7124435
theorem B7125407 : Blo 1405522 7125407 := bstep (se 1 (by rfl) ⟨5344055, by rfl⟩ : syracuseStep 7125407 = 10688111) B10688111
theorem B4750217 : Blo 1405522 4750217 := bstep (se 2 (by rfl) ⟨1781331, by rfl⟩ : syracuseStep 4750217 = 3562663) B3562663
theorem B10681307 : Blo 1405522 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B18013225 : Blo 1405522 18013225 := bstep (se 2 (by rfl) ⟨6754959, by rfl⟩ : syracuseStep 18013225 = 13509919) B13509919
theorem B9256349 : Blo 1405522 9256349 := bstep (se 3 (by rfl) ⟨1735565, by rfl⟩ : syracuseStep 9256349 = 3471131) B3471131
theorem B6004135 : Blo 1405522 6004135 := bstep (se 1 (by rfl) ⟨4503101, by rfl⟩ : syracuseStep 6004135 = 9006203) B9006203
theorem B9010919 : Blo 1405522 9010919 := bstep (se 1 (by rfl) ⟨6758189, by rfl⟩ : syracuseStep 9010919 = 13516379) B13516379
theorem B5071295 : Blo 1405522 5071295 := bstep (se 1 (by rfl) ⟨3803471, by rfl⟩ : syracuseStep 5071295 = 7606943) B7606943
theorem B1581727 : Blo 1405522 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B4744061 : Blo 1405522 4744061 := bstep (se 3 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 4744061 = 1779023) B1779023
theorem B3163049 : Blo 1405522 3163049 := bstep (se 2 (by rfl) ⟨1186143, by rfl⟩ : syracuseStep 3163049 = 2372287) B2372287
theorem B4006847 : Blo 1405522 4006847 := bstep (se 1 (by rfl) ⟨3005135, by rfl⟩ : syracuseStep 4006847 = 6010271) B6010271
theorem B6005947 : Blo 1405522 6005947 := bstep (se 1 (by rfl) ⟨4504460, by rfl⟩ : syracuseStep 6005947 = 9008921) B9008921
theorem B1901887 : Blo 1405522 1901887 := bstep (se 1 (by rfl) ⟨1426415, by rfl⟩ : syracuseStep 1901887 = 2852831) B2852831
theorem B2254319 : Blo 1405522 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B41674409 : Blo 1405522 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B3163913 : Blo 1405522 3163913 := bstep (se 2 (by rfl) ⟨1186467, by rfl⟩ : syracuseStep 3163913 = 2372935) B2372935
theorem B8005513 : Blo 1405522 8005513 := bstep (se 2 (by rfl) ⟨3002067, by rfl⟩ : syracuseStep 8005513 = 6004135) B6004135
theorem B3164129 : Blo 1405522 3164129 := bstep (se 2 (by rfl) ⟨1186548, by rfl⟩ : syracuseStep 3164129 = 2373097) B2373097
theorem B7120871 : Blo 1405522 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B6170899 : Blo 1405522 6170899 := bstep (se 1 (by rfl) ⟨4628174, by rfl⟩ : syracuseStep 6170899 = 9256349) B9256349
theorem B3557803 : Blo 1405522 3557803 := bstep (se 1 (by rfl) ⟨2668352, by rfl⟩ : syracuseStep 3557803 = 5336705) B5336705
theorem B6007279 : Blo 1405522 6007279 := bstep (se 1 (by rfl) ⟨4505459, by rfl⟩ : syracuseStep 6007279 = 9010919) B9010919
theorem B14641661 : Blo 1405522 14641661 := bstep (se 3 (by rfl) ⟨2745311, by rfl⟩ : syracuseStep 14641661 = 5490623) B5490623
theorem B12012371 : Blo 1405522 12012371 := bstep (se 1 (by rfl) ⟨9009278, by rfl⟩ : syracuseStep 12012371 = 18018557) B18018557
theorem B3165065 : Blo 1405522 3165065 := bstep (se 2 (by rfl) ⟨1186899, by rfl⟩ : syracuseStep 3165065 = 2373799) B2373799
theorem B2108351 : Blo 1405522 2108351 := bstep (se 1 (by rfl) ⟨1581263, by rfl⟩ : syracuseStep 2108351 = 3162527) B3162527
theorem B11406521 : Blo 1405522 11406521 := bstep (se 2 (by rfl) ⟨4277445, by rfl⟩ : syracuseStep 11406521 = 8554891) B8554891
theorem B2108735 : Blo 1405522 2108735 := bstep (se 1 (by rfl) ⟨1581551, by rfl⟩ : syracuseStep 2108735 = 3163103) B3163103
theorem B2535143 : Blo 1405522 2535143 := bstep (se 1 (by rfl) ⟨1901357, by rfl⟩ : syracuseStep 2535143 = 3802715) B3802715
theorem B3608297 : Blo 1405522 3608297 := bstep (se 2 (by rfl) ⟨1353111, by rfl⟩ : syracuseStep 3608297 = 2706223) B2706223
theorem B5336887 : Blo 1405522 5336887 := bstep (se 1 (by rfl) ⟨4002665, by rfl⟩ : syracuseStep 5336887 = 8005331) B8005331
theorem B2109353 : Blo 1405522 2109353 := bstep (se 2 (by rfl) ⟨791007, by rfl⟩ : syracuseStep 2109353 = 1582015) B1582015
theorem B2109383 : Blo 1405522 2109383 := bstep (se 1 (by rfl) ⟨1582037, by rfl⟩ : syracuseStep 2109383 = 3164075) B3164075
theorem B3002359 : Blo 1405522 3002359 := bstep (se 1 (by rfl) ⟨2251769, by rfl⟩ : syracuseStep 3002359 = 4503539) B4503539
theorem B5337191 : Blo 1405522 5337191 := bstep (se 1 (by rfl) ⟨4002893, by rfl⟩ : syracuseStep 5337191 = 8005787) B8005787
theorem B374976701 : Blo 1405522 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B3166415 : Blo 1405522 3166415 := bstep (se 1 (by rfl) ⟨2374811, by rfl⟩ : syracuseStep 3166415 = 4749623) B4749623
theorem B3166811 : Blo 1405522 3166811 := bstep (se 1 (by rfl) ⟨2375108, by rfl⟩ : syracuseStep 3166811 = 4750217) B4750217
theorem B1405607 : Blo 1405522 1405607 := bstep (se 1 (by rfl) ⟨1054205, by rfl⟩ : syracuseStep 1405607 = 2108411) B2108411
theorem B4002473 : Blo 1405522 4002473 := bstep (se 2 (by rfl) ⟨1500927, by rfl⟩ : syracuseStep 4002473 = 3001855) B3001855
theorem B1405671 : Blo 1405522 1405671 := bstep (se 1 (by rfl) ⟨1054253, by rfl⟩ : syracuseStep 1405671 = 2108507) B2108507
theorem B8123419 : Blo 1405522 8123419 := bstep (se 1 (by rfl) ⟨6092564, by rfl⟩ : syracuseStep 8123419 = 12185129) B12185129
theorem B3208303 : Blo 1405522 3208303 := bstep (se 1 (by rfl) ⟨2406227, by rfl⟩ : syracuseStep 3208303 = 4812455) B4812455
theorem B1406415 : Blo 1405522 1406415 := bstep (se 1 (by rfl) ⟨1054811, by rfl⟩ : syracuseStep 1406415 = 2109623) B2109623
theorem B6854375 : Blo 1405522 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B3381095 : Blo 1405522 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B1407007 : Blo 1405522 1407007 := bstep (se 1 (by rfl) ⟨1055255, by rfl⟩ : syracuseStep 1407007 = 2110511) B2110511
theorem B91224143 : Blo 1405522 91224143 := bstep (se 1 (by rfl) ⟨68418107, by rfl⟩ : syracuseStep 91224143 = 136836215) B136836215
theorem B1407303 : Blo 1405522 1407303 := bstep (se 1 (by rfl) ⟨1055477, by rfl⟩ : syracuseStep 1407303 = 2110955) B2110955
theorem B1407387 : Blo 1405522 1407387 := bstep (se 1 (by rfl) ⟨1055540, by rfl⟩ : syracuseStep 1407387 = 2111081) B2111081
theorem B3562127 : Blo 1405522 3562127 := bstep (se 1 (by rfl) ⟨2671595, by rfl⟩ : syracuseStep 3562127 = 5343191) B5343191
theorem B24017633 : Blo 1405522 24017633 := bstep (se 2 (by rfl) ⟨9006612, by rfl⟩ : syracuseStep 24017633 = 18013225) B18013225
theorem B7117631 : Blo 1405522 7117631 := bstep (se 1 (by rfl) ⟨5338223, by rfl⟩ : syracuseStep 7117631 = 10676447) B10676447
theorem B4750271 : Blo 1405522 4750271 := bstep (se 1 (by rfl) ⟨3562703, by rfl⟩ : syracuseStep 4750271 = 7125407) B7125407
theorem B18275615 : Blo 1405522 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B10141037 : Blo 1405522 10141037 := bstep (se 3 (by rfl) ⟨1901444, by rfl⟩ : syracuseStep 10141037 = 3802889) B3802889
theorem B30417389 : Blo 1405522 30417389 := bstep (se 3 (by rfl) ⟨5703260, by rfl⟩ : syracuseStep 30417389 = 11406521) B11406521
theorem B4743737 : Blo 1405522 4743737 := bstep (se 2 (by rfl) ⟨1778901, by rfl⟩ : syracuseStep 4743737 = 3557803) B3557803
theorem B3162707 : Blo 1405522 3162707 := bstep (se 1 (by rfl) ⟨2372030, by rfl⟩ : syracuseStep 3162707 = 4744061) B4744061
theorem B2671231 : Blo 1405522 2671231 := bstep (se 1 (by rfl) ⟨2003423, by rfl⟩ : syracuseStep 2671231 = 4006847) B4006847
theorem B2254063 : Blo 1405522 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B39044429 : Blo 1405522 39044429 := bstep (se 3 (by rfl) ⟨7320830, by rfl⟩ : syracuseStep 39044429 = 14641661) B14641661
theorem B10831225 : Blo 1405522 10831225 := bstep (se 2 (by rfl) ⟨4061709, by rfl⟩ : syracuseStep 10831225 = 8123419) B8123419
theorem B4277737 : Blo 1405522 4277737 := bstep (se 2 (by rfl) ⟨1604151, by rfl⟩ : syracuseStep 4277737 = 3208303) B3208303
theorem B10143397 : Blo 1405522 10143397 := bstep (se 4 (by rfl) ⟨950943, by rfl⟩ : syracuseStep 10143397 = 1901887) B1901887
theorem B4745087 : Blo 1405522 4745087 := bstep (se 1 (by rfl) ⟨3558815, by rfl⟩ : syracuseStep 4745087 = 7117631) B7117631
theorem B12183743 : Blo 1405522 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B6760691 : Blo 1405522 6760691 := bstep (se 1 (by rfl) ⟨5070518, by rfl⟩ : syracuseStep 6760691 = 10141037) B10141037
theorem B3558127 : Blo 1405522 3558127 := bstep (se 1 (by rfl) ⟨2668595, by rfl⟩ : syracuseStep 3558127 = 5337191) B5337191
theorem B8227865 : Blo 1405522 8227865 := bstep (se 2 (by rfl) ⟨3085449, by rfl⟩ : syracuseStep 8227865 = 6170899) B6170899
theorem B2108699 : Blo 1405522 2108699 := bstep (se 1 (by rfl) ⟨1581524, by rfl⟩ : syracuseStep 2108699 = 3163049) B3163049
theorem B2108969 : Blo 1405522 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B1502879 : Blo 1405522 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B27782939 : Blo 1405522 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B2109275 : Blo 1405522 2109275 := bstep (se 1 (by rfl) ⟨1581956, by rfl⟩ : syracuseStep 2109275 = 3163913) B3163913
theorem B2109419 : Blo 1405522 2109419 := bstep (se 1 (by rfl) ⟨1582064, by rfl⟩ : syracuseStep 2109419 = 3164129) B3164129
theorem B4747247 : Blo 1405522 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B8007929 : Blo 1405522 8007929 := bstep (se 2 (by rfl) ⟨3002973, by rfl⟩ : syracuseStep 8007929 = 6005947) B6005947
theorem B16011755 : Blo 1405522 16011755 := bstep (se 1 (by rfl) ⟨12008816, by rfl⟩ : syracuseStep 16011755 = 24017633) B24017633
theorem B8008247 : Blo 1405522 8008247 := bstep (se 1 (by rfl) ⟨6006185, by rfl⟩ : syracuseStep 8008247 = 12012371) B12012371
theorem B2110043 : Blo 1405522 2110043 := bstep (se 1 (by rfl) ⟨1582532, by rfl⟩ : syracuseStep 2110043 = 3165065) B3165065
theorem B1405567 : Blo 1405522 1405567 := bstep (se 1 (by rfl) ⟨1054175, by rfl⟩ : syracuseStep 1405567 = 2108351) B2108351
theorem B3166847 : Blo 1405522 3166847 := bstep (se 1 (by rfl) ⟨2375135, by rfl⟩ : syracuseStep 3166847 = 4750271) B4750271
theorem B1405823 : Blo 1405522 1405823 := bstep (se 1 (by rfl) ⟨1054367, by rfl⟩ : syracuseStep 1405823 = 2108735) B2108735
theorem B7115849 : Blo 1405522 7115849 := bstep (se 2 (by rfl) ⟨2668443, by rfl⟩ : syracuseStep 7115849 = 5336887) B5336887
theorem B2405531 : Blo 1405522 2405531 := bstep (se 1 (by rfl) ⟨1804148, by rfl⟩ : syracuseStep 2405531 = 3608297) B3608297
theorem B1406235 : Blo 1405522 1406235 := bstep (se 1 (by rfl) ⟨1054676, by rfl⟩ : syracuseStep 1406235 = 2109353) B2109353
theorem B1406255 : Blo 1405522 1406255 := bstep (se 1 (by rfl) ⟨1054691, by rfl⟩ : syracuseStep 1406255 = 2109383) B2109383
theorem B4003145 : Blo 1405522 4003145 := bstep (se 2 (by rfl) ⟨1501179, by rfl⟩ : syracuseStep 4003145 = 3002359) B3002359
theorem B249984467 : Blo 1405522 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B2110943 : Blo 1405522 2110943 := bstep (se 1 (by rfl) ⟨1583207, by rfl⟩ : syracuseStep 2110943 = 3166415) B3166415
theorem B3380863 : Blo 1405522 3380863 := bstep (se 1 (by rfl) ⟨2535647, by rfl⟩ : syracuseStep 3380863 = 5071295) B5071295
theorem B2111207 : Blo 1405522 2111207 := bstep (se 1 (by rfl) ⟨1583405, by rfl⟩ : syracuseStep 2111207 = 3166811) B3166811
theorem B2668315 : Blo 1405522 2668315 := bstep (se 1 (by rfl) ⟨2001236, by rfl⟩ : syracuseStep 2668315 = 4002473) B4002473
theorem B8009705 : Blo 1405522 8009705 := bstep (se 2 (by rfl) ⟨3003639, by rfl⟩ : syracuseStep 8009705 = 6007279) B6007279
theorem B4569583 : Blo 1405522 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B60816095 : Blo 1405522 60816095 := bstep (se 1 (by rfl) ⟨45612071, by rfl⟩ : syracuseStep 60816095 = 91224143) B91224143
theorem B2374751 : Blo 1405522 2374751 := bstep (se 1 (by rfl) ⟨1781063, by rfl⟩ : syracuseStep 2374751 = 3562127) B3562127
theorem B27041525 : Blo 1405522 27041525 := bstep (se 5 (by rfl) ⟨1267571, by rfl⟩ : syracuseStep 27041525 = 2535143) B2535143
theorem B10674017 : Blo 1405522 10674017 := bstep (se 2 (by rfl) ⟨4002756, by rfl⟩ : syracuseStep 10674017 = 8005513) B8005513
theorem B10674503 : Blo 1405522 10674503 := bstep (se 1 (by rfl) ⟨8005877, by rfl⟩ : syracuseStep 10674503 = 16011755) B16011755
theorem B3162491 : Blo 1405522 3162491 := bstep (se 1 (by rfl) ⟨2371868, by rfl⟩ : syracuseStep 3162491 = 4743737) B4743737
theorem B32489981 : Blo 1405522 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B4743899 : Blo 1405522 4743899 := bstep (se 1 (by rfl) ⟨3557924, by rfl⟩ : syracuseStep 4743899 = 7115849) B7115849
theorem B4744169 : Blo 1405522 4744169 := bstep (se 2 (by rfl) ⟨1779063, by rfl⟩ : syracuseStep 4744169 = 3558127) B3558127
theorem B3163391 : Blo 1405522 3163391 := bstep (se 1 (by rfl) ⟨2372543, by rfl⟩ : syracuseStep 3163391 = 4745087) B4745087
theorem B4507127 : Blo 1405522 4507127 := bstep (se 1 (by rfl) ⟨3380345, by rfl⟩ : syracuseStep 4507127 = 6760691) B6760691
theorem B40544063 : Blo 1405522 40544063 := bstep (se 1 (by rfl) ⟨30408047, by rfl⟩ : syracuseStep 40544063 = 60816095) B60816095
theorem B1583167 : Blo 1405522 1583167 := bstep (se 1 (by rfl) ⟨1187375, by rfl⟩ : syracuseStep 1583167 = 2374751) B2374751
theorem B4507817 : Blo 1405522 4507817 := bstep (se 2 (by rfl) ⟨1690431, by rfl⟩ : syracuseStep 4507817 = 3380863) B3380863
theorem B3557753 : Blo 1405522 3557753 := bstep (se 2 (by rfl) ⟨1334157, by rfl⟩ : syracuseStep 3557753 = 2668315) B2668315
theorem B3164831 : Blo 1405522 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B20278259 : Blo 1405522 20278259 := bstep (se 1 (by rfl) ⟨15208694, by rfl⟩ : syracuseStep 20278259 = 30417389) B30417389
theorem B2108471 : Blo 1405522 2108471 := bstep (se 1 (by rfl) ⟨1581353, by rfl⟩ : syracuseStep 2108471 = 3162707) B3162707
theorem B26029619 : Blo 1405522 26029619 := bstep (se 1 (by rfl) ⟨19522214, by rfl⟩ : syracuseStep 26029619 = 39044429) B39044429
theorem B5485243 : Blo 1405522 5485243 := bstep (se 1 (by rfl) ⟨4113932, by rfl⟩ : syracuseStep 5485243 = 8227865) B8227865
theorem B1405799 : Blo 1405522 1405799 := bstep (se 1 (by rfl) ⟨1054349, by rfl⟩ : syracuseStep 1405799 = 2108699) B2108699
theorem B1405979 : Blo 1405522 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B18027683 : Blo 1405522 18027683 := bstep (se 1 (by rfl) ⟨13520762, by rfl⟩ : syracuseStep 18027683 = 27041525) B27041525
theorem B1406183 : Blo 1405522 1406183 := bstep (se 1 (by rfl) ⟨1054637, by rfl⟩ : syracuseStep 1406183 = 2109275) B2109275
theorem B7116011 : Blo 1405522 7116011 := bstep (se 1 (by rfl) ⟨5337008, by rfl⟩ : syracuseStep 7116011 = 10674017) B10674017
theorem B1406279 : Blo 1405522 1406279 := bstep (se 1 (by rfl) ⟨1054709, by rfl⟩ : syracuseStep 1406279 = 2109419) B2109419
theorem B5338619 : Blo 1405522 5338619 := bstep (se 1 (by rfl) ⟨4003964, by rfl⟩ : syracuseStep 5338619 = 8007929) B8007929
theorem B5338831 : Blo 1405522 5338831 := bstep (se 1 (by rfl) ⟨4004123, by rfl⟩ : syracuseStep 5338831 = 8008247) B8008247
theorem B1406695 : Blo 1405522 1406695 := bstep (se 1 (by rfl) ⟨1055021, by rfl⟩ : syracuseStep 1406695 = 2110043) B2110043
theorem B2111231 : Blo 1405522 2111231 := bstep (se 1 (by rfl) ⟨1583423, by rfl⟩ : syracuseStep 2111231 = 3166847) B3166847
theorem B6092777 : Blo 1405522 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B1603687 : Blo 1405522 1603687 := bstep (se 1 (by rfl) ⟨1202765, by rfl⟩ : syracuseStep 1603687 = 2405531) B2405531
theorem B3561641 : Blo 1405522 3561641 := bstep (se 2 (by rfl) ⟨1335615, by rfl⟩ : syracuseStep 3561641 = 2671231) B2671231
theorem B2668763 : Blo 1405522 2668763 := bstep (se 1 (by rfl) ⟨2001572, by rfl⟩ : syracuseStep 2668763 = 4003145) B4003145
theorem B166656311 : Blo 1405522 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B1407295 : Blo 1405522 1407295 := bstep (se 1 (by rfl) ⟨1055471, by rfl⟩ : syracuseStep 1407295 = 2110943) B2110943
theorem B1407471 : Blo 1405522 1407471 := bstep (se 1 (by rfl) ⟨1055603, by rfl⟩ : syracuseStep 1407471 = 2111207) B2111207
theorem B5339803 : Blo 1405522 5339803 := bstep (se 1 (by rfl) ⟨4004852, by rfl⟩ : syracuseStep 5339803 = 8009705) B8009705
theorem B3005417 : Blo 1405522 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B16030709 : Blo 1405522 16030709 := bstep (se 5 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 16030709 = 1502879) B1502879
theorem B14441633 : Blo 1405522 14441633 := bstep (se 2 (by rfl) ⟨5415612, by rfl⟩ : syracuseStep 14441633 = 10831225) B10831225
theorem B13524529 : Blo 1405522 13524529 := bstep (se 2 (by rfl) ⟨5071698, by rfl⟩ : syracuseStep 13524529 = 10143397) B10143397
theorem B18521959 : Blo 1405522 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B22814597 : Blo 1405522 22814597 := bstep (se 4 (by rfl) ⟨2138868, by rfl⟩ : syracuseStep 22814597 = 4277737) B4277737
theorem B2138249 : Blo 1405522 2138249 := bstep (se 2 (by rfl) ⟨801843, by rfl⟩ : syracuseStep 2138249 = 1603687) B1603687
theorem B21659987 : Blo 1405522 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B3162599 : Blo 1405522 3162599 := bstep (se 1 (by rfl) ⟨2371949, by rfl⟩ : syracuseStep 3162599 = 4743899) B4743899
theorem B3162779 : Blo 1405522 3162779 := bstep (se 1 (by rfl) ⟨2372084, by rfl⟩ : syracuseStep 3162779 = 4744169) B4744169
theorem B12018455 : Blo 1405522 12018455 := bstep (se 1 (by rfl) ⟨9013841, by rfl⟩ : syracuseStep 12018455 = 18027683) B18027683
theorem B4744007 : Blo 1405522 4744007 := bstep (se 1 (by rfl) ⟨3558005, by rfl⟩ : syracuseStep 4744007 = 7116011) B7116011
theorem B7119737 : Blo 1405522 7119737 := bstep (se 2 (by rfl) ⟨2669901, by rfl⟩ : syracuseStep 7119737 = 5339803) B5339803
theorem B1779175 : Blo 1405522 1779175 := bstep (se 1 (by rfl) ⟨1334381, by rfl⟩ : syracuseStep 1779175 = 2668763) B2668763
theorem B13518839 : Blo 1405522 13518839 := bstep (se 1 (by rfl) ⟨10139129, by rfl⟩ : syracuseStep 13518839 = 20278259) B20278259
theorem B18032705 : Blo 1405522 18032705 := bstep (se 2 (by rfl) ⟨6762264, by rfl⟩ : syracuseStep 18032705 = 13524529) B13524529
theorem B9627755 : Blo 1405522 9627755 := bstep (se 1 (by rfl) ⟨7220816, by rfl⟩ : syracuseStep 9627755 = 14441633) B14441633
theorem B17353079 : Blo 1405522 17353079 := bstep (se 1 (by rfl) ⟨13014809, by rfl⟩ : syracuseStep 17353079 = 26029619) B26029619
theorem B16247405 : Blo 1405522 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B2108327 : Blo 1405522 2108327 := bstep (se 1 (by rfl) ⟨1581245, by rfl⟩ : syracuseStep 2108327 = 3162491) B3162491
theorem B12020845 : Blo 1405522 12020845 := bstep (se 3 (by rfl) ⟨2253908, by rfl⟩ : syracuseStep 12020845 = 4507817) B4507817
theorem B2108927 : Blo 1405522 2108927 := bstep (se 1 (by rfl) ⟨1581695, by rfl⟩ : syracuseStep 2108927 = 3163391) B3163391
theorem B3559079 : Blo 1405522 3559079 := bstep (se 1 (by rfl) ⟨2669309, by rfl⟩ : syracuseStep 3559079 = 5338619) B5338619
theorem B27029375 : Blo 1405522 27029375 := bstep (se 1 (by rfl) ⟨20272031, by rfl⟩ : syracuseStep 27029375 = 40544063) B40544063
theorem B111104207 : Blo 1405522 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B2371835 : Blo 1405522 2371835 := bstep (se 1 (by rfl) ⟨1778876, by rfl⟩ : syracuseStep 2371835 = 3557753) B3557753
theorem B2109887 : Blo 1405522 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B2003611 : Blo 1405522 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B10687139 : Blo 1405522 10687139 := bstep (se 1 (by rfl) ⟨8015354, by rfl⟩ : syracuseStep 10687139 = 16030709) B16030709
theorem B1405647 : Blo 1405522 1405647 := bstep (se 1 (by rfl) ⟨1054235, by rfl⟩ : syracuseStep 1405647 = 2108471) B2108471
theorem B24695945 : Blo 1405522 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B15209731 : Blo 1405522 15209731 := bstep (se 1 (by rfl) ⟨11407298, by rfl⟩ : syracuseStep 15209731 = 22814597) B22814597
theorem B2110889 : Blo 1405522 2110889 := bstep (se 2 (by rfl) ⟨791583, by rfl⟩ : syracuseStep 2110889 = 1583167) B1583167
theorem B7116335 : Blo 1405522 7116335 := bstep (se 1 (by rfl) ⟨5337251, by rfl⟩ : syracuseStep 7116335 = 10674503) B10674503
theorem B7313657 : Blo 1405522 7313657 := bstep (se 2 (by rfl) ⟨2742621, by rfl⟩ : syracuseStep 7313657 = 5485243) B5485243
theorem B3004751 : Blo 1405522 3004751 := bstep (se 1 (by rfl) ⟨2253563, by rfl⟩ : syracuseStep 3004751 = 4507127) B4507127
theorem B1407487 : Blo 1405522 1407487 := bstep (se 1 (by rfl) ⟨1055615, by rfl⟩ : syracuseStep 1407487 = 2111231) B2111231
theorem B2374427 : Blo 1405522 2374427 := bstep (se 1 (by rfl) ⟨1780820, by rfl⟩ : syracuseStep 2374427 = 3561641) B3561641
theorem B7118441 : Blo 1405522 7118441 := bstep (se 2 (by rfl) ⟨2669415, by rfl⟩ : syracuseStep 7118441 = 5338831) B5338831
theorem B1581223 : Blo 1405522 1581223 := bstep (se 1 (by rfl) ⟨1185917, by rfl⟩ : syracuseStep 1581223 = 2371835) B2371835
theorem B25674013 : Blo 1405522 25674013 := bstep (se 3 (by rfl) ⟨4813877, by rfl⟩ : syracuseStep 25674013 = 9627755) B9627755
theorem B5701997 : Blo 1405522 5701997 := bstep (se 3 (by rfl) ⟨1069124, by rfl⟩ : syracuseStep 5701997 = 2138249) B2138249
theorem B8012303 : Blo 1405522 8012303 := bstep (se 1 (by rfl) ⟨6009227, by rfl⟩ : syracuseStep 8012303 = 12018455) B12018455
theorem B3162671 : Blo 1405522 3162671 := bstep (se 1 (by rfl) ⟨2372003, by rfl⟩ : syracuseStep 3162671 = 4744007) B4744007
theorem B2671481 : Blo 1405522 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B4744223 : Blo 1405522 4744223 := bstep (se 1 (by rfl) ⟨3558167, by rfl⟩ : syracuseStep 4744223 = 7116335) B7116335
theorem B9012559 : Blo 1405522 9012559 := bstep (se 1 (by rfl) ⟨6759419, by rfl⟩ : syracuseStep 9012559 = 13518839) B13518839
theorem B11568719 : Blo 1405522 11568719 := bstep (se 1 (by rfl) ⟨8676539, by rfl⟩ : syracuseStep 11568719 = 17353079) B17353079
theorem B10831603 : Blo 1405522 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B1582951 : Blo 1405522 1582951 := bstep (se 1 (by rfl) ⟨1187213, by rfl⟩ : syracuseStep 1582951 = 2374427) B2374427
theorem B4745627 : Blo 1405522 4745627 := bstep (se 1 (by rfl) ⟨3559220, by rfl⟩ : syracuseStep 4745627 = 7118441) B7118441
theorem B2108399 : Blo 1405522 2108399 := bstep (se 1 (by rfl) ⟨1581299, by rfl⟩ : syracuseStep 2108399 = 3162599) B3162599
theorem B2108519 : Blo 1405522 2108519 := bstep (se 1 (by rfl) ⟨1581389, by rfl⟩ : syracuseStep 2108519 = 3162779) B3162779
theorem B4746491 : Blo 1405522 4746491 := bstep (se 1 (by rfl) ⟨3559868, by rfl⟩ : syracuseStep 4746491 = 7119737) B7119737
theorem B12021803 : Blo 1405522 12021803 := bstep (se 1 (by rfl) ⟨9016352, by rfl⟩ : syracuseStep 12021803 = 18032705) B18032705
theorem B16027793 : Blo 1405522 16027793 := bstep (se 2 (by rfl) ⟨6010422, by rfl⟩ : syracuseStep 16027793 = 12020845) B12020845
theorem B2003167 : Blo 1405522 2003167 := bstep (se 1 (by rfl) ⟨1502375, by rfl⟩ : syracuseStep 2003167 = 3004751) B3004751
theorem B20279641 : Blo 1405522 20279641 := bstep (se 2 (by rfl) ⟨7604865, by rfl⟩ : syracuseStep 20279641 = 15209731) B15209731
theorem B1405551 : Blo 1405522 1405551 := bstep (se 1 (by rfl) ⟨1054163, by rfl⟩ : syracuseStep 1405551 = 2108327) B2108327
theorem B2372233 : Blo 1405522 2372233 := bstep (se 2 (by rfl) ⟨889587, by rfl⟩ : syracuseStep 2372233 = 1779175) B1779175
theorem B1405951 : Blo 1405522 1405951 := bstep (se 1 (by rfl) ⟨1054463, by rfl⟩ : syracuseStep 1405951 = 2108927) B2108927
theorem B2372719 : Blo 1405522 2372719 := bstep (se 1 (by rfl) ⟨1779539, by rfl⟩ : syracuseStep 2372719 = 3559079) B3559079
theorem B18019583 : Blo 1405522 18019583 := bstep (se 1 (by rfl) ⟨13514687, by rfl⟩ : syracuseStep 18019583 = 27029375) B27029375
theorem B74069471 : Blo 1405522 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B14439991 : Blo 1405522 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B1406591 : Blo 1405522 1406591 := bstep (se 1 (by rfl) ⟨1054943, by rfl⟩ : syracuseStep 1406591 = 2109887) B2109887
theorem B7124759 : Blo 1405522 7124759 := bstep (se 1 (by rfl) ⟨5343569, by rfl⟩ : syracuseStep 7124759 = 10687139) B10687139
theorem B16463963 : Blo 1405522 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B1407259 : Blo 1405522 1407259 := bstep (se 1 (by rfl) ⟨1055444, by rfl⟩ : syracuseStep 1407259 = 2110889) B2110889
theorem B78012341 : Blo 1405522 78012341 := bstep (se 5 (by rfl) ⟨3656828, by rfl⟩ : syracuseStep 78012341 = 7313657) B7313657
theorem B3801331 : Blo 1405522 3801331 := bstep (se 1 (by rfl) ⟨2850998, by rfl⟩ : syracuseStep 3801331 = 5701997) B5701997
theorem B2670889 : Blo 1405522 2670889 := bstep (se 2 (by rfl) ⟨1001583, by rfl⟩ : syracuseStep 2670889 = 2003167) B2003167
theorem B5341535 : Blo 1405522 5341535 := bstep (se 1 (by rfl) ⟨4006151, by rfl⟩ : syracuseStep 5341535 = 8012303) B8012303
theorem B3162815 : Blo 1405522 3162815 := bstep (se 1 (by rfl) ⟨2372111, by rfl⟩ : syracuseStep 3162815 = 4744223) B4744223
theorem B3162977 : Blo 1405522 3162977 := bstep (se 2 (by rfl) ⟨1186116, by rfl⟩ : syracuseStep 3162977 = 2372233) B2372233
theorem B3163625 : Blo 1405522 3163625 := bstep (se 2 (by rfl) ⟨1186359, by rfl⟩ : syracuseStep 3163625 = 2372719) B2372719
theorem B3163751 : Blo 1405522 3163751 := bstep (se 1 (by rfl) ⟨2372813, by rfl⟩ : syracuseStep 3163751 = 4745627) B4745627
theorem B19253321 : Blo 1405522 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B3164327 : Blo 1405522 3164327 := bstep (se 1 (by rfl) ⟨2373245, by rfl⟩ : syracuseStep 3164327 = 4746491) B4746491
theorem B8014535 : Blo 1405522 8014535 := bstep (se 1 (by rfl) ⟨6010901, by rfl⟩ : syracuseStep 8014535 = 12021803) B12021803
theorem B10685195 : Blo 1405522 10685195 := bstep (se 1 (by rfl) ⟨8013896, by rfl⟩ : syracuseStep 10685195 = 16027793) B16027793
theorem B2108297 : Blo 1405522 2108297 := bstep (se 2 (by rfl) ⟨790611, by rfl⟩ : syracuseStep 2108297 = 1581223) B1581223
theorem B2108447 : Blo 1405522 2108447 := bstep (se 1 (by rfl) ⟨1581335, by rfl⟩ : syracuseStep 2108447 = 3162671) B3162671
theorem B12013055 : Blo 1405522 12013055 := bstep (se 1 (by rfl) ⟨9009791, by rfl⟩ : syracuseStep 12013055 = 18019583) B18019583
theorem B1405599 : Blo 1405522 1405599 := bstep (se 1 (by rfl) ⟨1054199, by rfl⟩ : syracuseStep 1405599 = 2108399) B2108399
theorem B1405679 : Blo 1405522 1405679 := bstep (se 1 (by rfl) ⟨1054259, by rfl⟩ : syracuseStep 1405679 = 2108519) B2108519
theorem B7123949 : Blo 1405522 7123949 := bstep (se 3 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 7123949 = 2671481) B2671481
theorem B2110601 : Blo 1405522 2110601 := bstep (se 2 (by rfl) ⟨791475, by rfl⟩ : syracuseStep 2110601 = 1582951) B1582951
theorem B52008227 : Blo 1405522 52008227 := bstep (se 1 (by rfl) ⟨39006170, by rfl⟩ : syracuseStep 52008227 = 78012341) B78012341
theorem B27039521 : Blo 1405522 27039521 := bstep (se 2 (by rfl) ⟨10139820, by rfl⟩ : syracuseStep 27039521 = 20279641) B20279641
theorem B49379647 : Blo 1405522 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B4749839 : Blo 1405522 4749839 := bstep (se 1 (by rfl) ⟨3562379, by rfl⟩ : syracuseStep 4749839 = 7124759) B7124759
theorem B10975975 : Blo 1405522 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B136928069 : Blo 1405522 136928069 := bstep (se 4 (by rfl) ⟨12837006, by rfl⟩ : syracuseStep 136928069 = 25674013) B25674013
theorem B30849917 : Blo 1405522 30849917 := bstep (se 3 (by rfl) ⟨5784359, by rfl⟩ : syracuseStep 30849917 = 11568719) B11568719
theorem B12016745 : Blo 1405522 12016745 := bstep (se 2 (by rfl) ⟨4506279, by rfl⟩ : syracuseStep 12016745 = 9012559) B9012559
theorem B14442137 : Blo 1405522 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B5343023 : Blo 1405522 5343023 := bstep (se 1 (by rfl) ⟨4007267, by rfl⟩ : syracuseStep 5343023 = 8014535) B8014535
theorem B91285379 : Blo 1405522 91285379 := bstep (se 1 (by rfl) ⟨68464034, by rfl⟩ : syracuseStep 91285379 = 136928069) B136928069
theorem B82266445 : Blo 1405522 82266445 := bstep (se 3 (by rfl) ⟨15424958, by rfl⟩ : syracuseStep 82266445 = 30849917) B30849917
theorem B9628091 : Blo 1405522 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B2108543 : Blo 1405522 2108543 := bstep (se 1 (by rfl) ⟨1581407, by rfl⟩ : syracuseStep 2108543 = 3162815) B3162815
theorem B2108651 : Blo 1405522 2108651 := bstep (se 1 (by rfl) ⟨1581488, by rfl⟩ : syracuseStep 2108651 = 3162977) B3162977
theorem B34672151 : Blo 1405522 34672151 := bstep (se 1 (by rfl) ⟨26004113, by rfl⟩ : syracuseStep 34672151 = 52008227) B52008227
theorem B2109083 : Blo 1405522 2109083 := bstep (se 1 (by rfl) ⟨1581812, by rfl⟩ : syracuseStep 2109083 = 3163625) B3163625
theorem B2109167 : Blo 1405522 2109167 := bstep (se 1 (by rfl) ⟨1581875, by rfl⟩ : syracuseStep 2109167 = 3163751) B3163751
theorem B18026347 : Blo 1405522 18026347 := bstep (se 1 (by rfl) ⟨13519760, by rfl⟩ : syracuseStep 18026347 = 27039521) B27039521
theorem B2109551 : Blo 1405522 2109551 := bstep (se 1 (by rfl) ⟨1582163, by rfl⟩ : syracuseStep 2109551 = 3164327) B3164327
theorem B3166559 : Blo 1405522 3166559 := bstep (se 1 (by rfl) ⟨2374919, by rfl⟩ : syracuseStep 3166559 = 4749839) B4749839
theorem B7123463 : Blo 1405522 7123463 := bstep (se 1 (by rfl) ⟨5342597, by rfl⟩ : syracuseStep 7123463 = 10685195) B10685195
theorem B1405531 : Blo 1405522 1405531 := bstep (se 1 (by rfl) ⟨1054148, by rfl⟩ : syracuseStep 1405531 = 2108297) B2108297
theorem B1405631 : Blo 1405522 1405631 := bstep (se 1 (by rfl) ⟨1054223, by rfl⟩ : syracuseStep 1405631 = 2108447) B2108447
theorem B8008703 : Blo 1405522 8008703 := bstep (se 1 (by rfl) ⟨6006527, by rfl⟩ : syracuseStep 8008703 = 12013055) B12013055
theorem B3561023 : Blo 1405522 3561023 := bstep (se 1 (by rfl) ⟨2670767, by rfl⟩ : syracuseStep 3561023 = 5341535) B5341535
theorem B5068441 : Blo 1405522 5068441 := bstep (se 2 (by rfl) ⟨1900665, by rfl⟩ : syracuseStep 5068441 = 3801331) B3801331
theorem B3561185 : Blo 1405522 3561185 := bstep (se 2 (by rfl) ⟨1335444, by rfl⟩ : syracuseStep 3561185 = 2670889) B2670889
theorem B4749299 : Blo 1405522 4749299 := bstep (se 1 (by rfl) ⟨3561974, by rfl⟩ : syracuseStep 4749299 = 7123949) B7123949
theorem B1407067 : Blo 1405522 1407067 := bstep (se 1 (by rfl) ⟨1055300, by rfl⟩ : syracuseStep 1407067 = 2110601) B2110601
theorem B58538533 : Blo 1405522 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B1053432469 : Blo 1405522 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B12835547 : Blo 1405522 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B8011163 : Blo 1405522 8011163 := bstep (se 1 (by rfl) ⟨6008372, by rfl⟩ : syracuseStep 8011163 = 12016745) B12016745
theorem B1404576625 : Blo 1405522 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B3166199 : Blo 1405522 3166199 := bstep (se 1 (by rfl) ⟨2374649, by rfl⟩ : syracuseStep 3166199 = 4749299) B4749299
theorem B92459069 : Blo 1405522 92459069 := bstep (se 3 (by rfl) ⟨17336075, by rfl⟩ : syracuseStep 92459069 = 34672151) B34672151
theorem B6418727 : Blo 1405522 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B8557031 : Blo 1405522 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B1405695 : Blo 1405522 1405695 := bstep (se 1 (by rfl) ⟨1054271, by rfl⟩ : syracuseStep 1405695 = 2108543) B2108543
theorem B1405767 : Blo 1405522 1405767 := bstep (se 1 (by rfl) ⟨1054325, by rfl⟩ : syracuseStep 1405767 = 2108651) B2108651
theorem B1406055 : Blo 1405522 1406055 := bstep (se 1 (by rfl) ⟨1054541, by rfl⟩ : syracuseStep 1406055 = 2109083) B2109083
theorem B1406111 : Blo 1405522 1406111 := bstep (se 1 (by rfl) ⟨1054583, by rfl⟩ : syracuseStep 1406111 = 2109167) B2109167
theorem B1406367 : Blo 1405522 1406367 := bstep (se 1 (by rfl) ⟨1054775, by rfl⟩ : syracuseStep 1406367 = 2109551) B2109551
theorem B2111039 : Blo 1405522 2111039 := bstep (se 1 (by rfl) ⟨1583279, by rfl⟩ : syracuseStep 2111039 = 3166559) B3166559
theorem B4748975 : Blo 1405522 4748975 := bstep (se 1 (by rfl) ⟨3561731, by rfl⟩ : syracuseStep 4748975 = 7123463) B7123463
theorem B109688593 : Blo 1405522 109688593 := bstep (se 2 (by rfl) ⟨41133222, by rfl⟩ : syracuseStep 109688593 = 82266445) B82266445
theorem B5339135 : Blo 1405522 5339135 := bstep (se 1 (by rfl) ⟨4004351, by rfl⟩ : syracuseStep 5339135 = 8008703) B8008703
theorem B78051377 : Blo 1405522 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B2374015 : Blo 1405522 2374015 := bstep (se 1 (by rfl) ⟨1780511, by rfl⟩ : syracuseStep 2374015 = 3561023) B3561023
theorem B2374123 : Blo 1405522 2374123 := bstep (se 1 (by rfl) ⟨1780592, by rfl⟩ : syracuseStep 2374123 = 3561185) B3561185
theorem B3562015 : Blo 1405522 3562015 := bstep (se 1 (by rfl) ⟨2671511, by rfl⟩ : syracuseStep 3562015 = 5343023) B5343023
theorem B60856919 : Blo 1405522 60856919 := bstep (se 1 (by rfl) ⟨45642689, by rfl⟩ : syracuseStep 60856919 = 91285379) B91285379
theorem B6757921 : Blo 1405522 6757921 := bstep (se 2 (by rfl) ⟨2534220, by rfl⟩ : syracuseStep 6757921 = 5068441) B5068441
theorem B5340775 : Blo 1405522 5340775 := bstep (se 1 (by rfl) ⟨4005581, by rfl⟩ : syracuseStep 5340775 = 8011163) B8011163
theorem B24035129 : Blo 1405522 24035129 := bstep (se 2 (by rfl) ⟨9013173, by rfl⟩ : syracuseStep 24035129 = 18026347) B18026347
theorem B7121033 : Blo 1405522 7121033 := bstep (se 2 (by rfl) ⟨2670387, by rfl⟩ : syracuseStep 7121033 = 5340775) B5340775
theorem B61639379 : Blo 1405522 61639379 := bstep (se 1 (by rfl) ⟨46229534, by rfl⟩ : syracuseStep 61639379 = 92459069) B92459069
theorem B4279151 : Blo 1405522 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B5704687 : Blo 1405522 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B3165353 : Blo 1405522 3165353 := bstep (se 2 (by rfl) ⟨1187007, by rfl⟩ : syracuseStep 3165353 = 2374015) B2374015
theorem B3165497 : Blo 1405522 3165497 := bstep (se 2 (by rfl) ⟨1187061, by rfl⟩ : syracuseStep 3165497 = 2374123) B2374123
theorem B3165983 : Blo 1405522 3165983 := bstep (se 1 (by rfl) ⟨2374487, by rfl⟩ : syracuseStep 3165983 = 4748975) B4748975
theorem B1872768833 : Blo 1405522 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B3559423 : Blo 1405522 3559423 := bstep (se 1 (by rfl) ⟨2669567, by rfl⟩ : syracuseStep 3559423 = 5339135) B5339135
theorem B40571279 : Blo 1405522 40571279 := bstep (se 1 (by rfl) ⟨30428459, by rfl⟩ : syracuseStep 40571279 = 60856919) B60856919
theorem B2110799 : Blo 1405522 2110799 := bstep (se 1 (by rfl) ⟨1583099, by rfl⟩ : syracuseStep 2110799 = 3166199) B3166199
theorem B4749353 : Blo 1405522 4749353 := bstep (se 2 (by rfl) ⟨1781007, by rfl⟩ : syracuseStep 4749353 = 3562015) B3562015
theorem B1407359 : Blo 1405522 1407359 := bstep (se 1 (by rfl) ⟨1055519, by rfl⟩ : syracuseStep 1407359 = 2111039) B2111039
theorem B52034251 : Blo 1405522 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B9010561 : Blo 1405522 9010561 := bstep (se 2 (by rfl) ⟨3378960, by rfl⟩ : syracuseStep 9010561 = 6757921) B6757921
theorem B146251457 : Blo 1405522 146251457 := bstep (se 2 (by rfl) ⟨54844296, by rfl⟩ : syracuseStep 146251457 = 109688593) B109688593
theorem B16023419 : Blo 1405522 16023419 := bstep (se 1 (by rfl) ⟨12017564, by rfl⟩ : syracuseStep 16023419 = 24035129) B24035129
theorem B69379001 : Blo 1405522 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B41092919 : Blo 1405522 41092919 := bstep (se 1 (by rfl) ⟨30819689, by rfl⟩ : syracuseStep 41092919 = 61639379) B61639379
theorem B2852767 : Blo 1405522 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B1248512555 : Blo 1405522 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B4745897 : Blo 1405522 4745897 := bstep (se 2 (by rfl) ⟨1779711, by rfl⟩ : syracuseStep 4745897 = 3559423) B3559423
theorem B3166235 : Blo 1405522 3166235 := bstep (se 1 (by rfl) ⟨2374676, by rfl⟩ : syracuseStep 3166235 = 4749353) B4749353
theorem B4747355 : Blo 1405522 4747355 := bstep (se 1 (by rfl) ⟨3560516, by rfl⟩ : syracuseStep 4747355 = 7121033) B7121033
theorem B12014081 : Blo 1405522 12014081 := bstep (se 2 (by rfl) ⟨4505280, by rfl⟩ : syracuseStep 12014081 = 9010561) B9010561
theorem B2110235 : Blo 1405522 2110235 := bstep (se 1 (by rfl) ⟨1582676, by rfl⟩ : syracuseStep 2110235 = 3165353) B3165353
theorem B2110331 : Blo 1405522 2110331 := bstep (se 1 (by rfl) ⟨1582748, by rfl⟩ : syracuseStep 2110331 = 3165497) B3165497
theorem B2110655 : Blo 1405522 2110655 := bstep (se 1 (by rfl) ⟨1582991, by rfl⟩ : syracuseStep 2110655 = 3165983) B3165983
theorem B27047519 : Blo 1405522 27047519 := bstep (se 1 (by rfl) ⟨20285639, by rfl⟩ : syracuseStep 27047519 = 40571279) B40571279
theorem B1407199 : Blo 1405522 1407199 := bstep (se 1 (by rfl) ⟨1055399, by rfl⟩ : syracuseStep 1407199 = 2110799) B2110799
theorem B97500971 : Blo 1405522 97500971 := bstep (se 1 (by rfl) ⟨73125728, by rfl⟩ : syracuseStep 97500971 = 146251457) B146251457
theorem B30424997 : Blo 1405522 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B10682279 : Blo 1405522 10682279 := bstep (se 1 (by rfl) ⟨8011709, by rfl⟩ : syracuseStep 10682279 = 16023419) B16023419
theorem B46252667 : Blo 1405522 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B18031679 : Blo 1405522 18031679 := bstep (se 1 (by rfl) ⟨13523759, by rfl⟩ : syracuseStep 18031679 = 27047519) B27047519
theorem B27395279 : Blo 1405522 27395279 := bstep (se 1 (by rfl) ⟨20546459, by rfl⟩ : syracuseStep 27395279 = 41092919) B41092919
theorem B832341703 : Blo 1405522 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B3163931 : Blo 1405522 3163931 := bstep (se 1 (by rfl) ⟨2372948, by rfl⟩ : syracuseStep 3163931 = 4745897) B4745897
theorem B3803689 : Blo 1405522 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B7121519 : Blo 1405522 7121519 := bstep (se 1 (by rfl) ⟨5341139, by rfl⟩ : syracuseStep 7121519 = 10682279) B10682279
theorem B3164903 : Blo 1405522 3164903 := bstep (se 1 (by rfl) ⟨2373677, by rfl⟩ : syracuseStep 3164903 = 4747355) B4747355
theorem B65000647 : Blo 1405522 65000647 := bstep (se 1 (by rfl) ⟨48750485, by rfl⟩ : syracuseStep 65000647 = 97500971) B97500971
theorem B2110823 : Blo 1405522 2110823 := bstep (se 1 (by rfl) ⟨1583117, by rfl⟩ : syracuseStep 2110823 = 3166235) B3166235
theorem B8009387 : Blo 1405522 8009387 := bstep (se 1 (by rfl) ⟨6007040, by rfl⟩ : syracuseStep 8009387 = 12014081) B12014081
theorem B1406823 : Blo 1405522 1406823 := bstep (se 1 (by rfl) ⟨1055117, by rfl⟩ : syracuseStep 1406823 = 2110235) B2110235
theorem B1406887 : Blo 1405522 1406887 := bstep (se 1 (by rfl) ⟨1055165, by rfl⟩ : syracuseStep 1406887 = 2110331) B2110331
theorem B1407103 : Blo 1405522 1407103 := bstep (se 1 (by rfl) ⟨1055327, by rfl⟩ : syracuseStep 1407103 = 2110655) B2110655
theorem B81133325 : Blo 1405522 81133325 := bstep (se 3 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 81133325 = 30424997) B30424997
theorem B5071585 : Blo 1405522 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B346670117 : Blo 1405522 346670117 := bstep (se 4 (by rfl) ⟨32500323, by rfl⟩ : syracuseStep 346670117 = 65000647) B65000647
theorem B123340445 : Blo 1405522 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B1109788937 : Blo 1405522 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B12021119 : Blo 1405522 12021119 := bstep (se 1 (by rfl) ⟨9015839, by rfl⟩ : syracuseStep 12021119 = 18031679) B18031679
theorem B18263519 : Blo 1405522 18263519 := bstep (se 1 (by rfl) ⟨13697639, by rfl⟩ : syracuseStep 18263519 = 27395279) B27395279
theorem B2109287 : Blo 1405522 2109287 := bstep (se 1 (by rfl) ⟨1581965, by rfl⟩ : syracuseStep 2109287 = 3163931) B3163931
theorem B4747679 : Blo 1405522 4747679 := bstep (se 1 (by rfl) ⟨3560759, by rfl⟩ : syracuseStep 4747679 = 7121519) B7121519
theorem B2109935 : Blo 1405522 2109935 := bstep (se 1 (by rfl) ⟨1582451, by rfl⟩ : syracuseStep 2109935 = 3164903) B3164903
theorem B54088883 : Blo 1405522 54088883 := bstep (se 1 (by rfl) ⟨40566662, by rfl⟩ : syracuseStep 54088883 = 81133325) B81133325
theorem B1407215 : Blo 1405522 1407215 := bstep (se 1 (by rfl) ⟨1055411, by rfl⟩ : syracuseStep 1407215 = 2110823) B2110823
theorem B5339591 : Blo 1405522 5339591 := bstep (se 1 (by rfl) ⟨4004693, by rfl⟩ : syracuseStep 5339591 = 8009387) B8009387
theorem B231113411 : Blo 1405522 231113411 := bstep (se 1 (by rfl) ⟨173335058, by rfl⟩ : syracuseStep 231113411 = 346670117) B346670117
theorem B8014079 : Blo 1405522 8014079 := bstep (se 1 (by rfl) ⟨6010559, by rfl⟩ : syracuseStep 8014079 = 12021119) B12021119
theorem B12175679 : Blo 1405522 12175679 := bstep (se 1 (by rfl) ⟨9131759, by rfl⟩ : syracuseStep 12175679 = 18263519) B18263519
theorem B3165119 : Blo 1405522 3165119 := bstep (se 1 (by rfl) ⟨2373839, by rfl⟩ : syracuseStep 3165119 = 4747679) B4747679
theorem B6762113 : Blo 1405522 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B82226963 : Blo 1405522 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B3559727 : Blo 1405522 3559727 := bstep (se 1 (by rfl) ⟨2669795, by rfl⟩ : syracuseStep 3559727 = 5339591) B5339591
theorem B1406191 : Blo 1405522 1406191 := bstep (se 1 (by rfl) ⟨1054643, by rfl⟩ : syracuseStep 1406191 = 2109287) B2109287
theorem B1406623 : Blo 1405522 1406623 := bstep (se 1 (by rfl) ⟨1054967, by rfl⟩ : syracuseStep 1406623 = 2109935) B2109935
theorem B36059255 : Blo 1405522 36059255 := bstep (se 1 (by rfl) ⟨27044441, by rfl⟩ : syracuseStep 36059255 = 54088883) B54088883
theorem B739859291 : Blo 1405522 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B154075607 : Blo 1405522 154075607 := bstep (se 1 (by rfl) ⟨115556705, by rfl⟩ : syracuseStep 154075607 = 231113411) B231113411
theorem B5342719 : Blo 1405522 5342719 := bstep (se 1 (by rfl) ⟨4007039, by rfl⟩ : syracuseStep 5342719 = 8014079) B8014079
theorem B4508075 : Blo 1405522 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B24039503 : Blo 1405522 24039503 := bstep (se 1 (by rfl) ⟨18029627, by rfl⟩ : syracuseStep 24039503 = 36059255) B36059255
theorem B2110079 : Blo 1405522 2110079 := bstep (se 1 (by rfl) ⟨1582559, by rfl⟩ : syracuseStep 2110079 = 3165119) B3165119
theorem B54817975 : Blo 1405522 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B2373151 : Blo 1405522 2373151 := bstep (se 1 (by rfl) ⟨1779863, by rfl⟩ : syracuseStep 2373151 = 3559727) B3559727
theorem B8117119 : Blo 1405522 8117119 := bstep (se 1 (by rfl) ⟨6087839, by rfl⟩ : syracuseStep 8117119 = 12175679) B12175679
theorem B493239527 : Blo 1405522 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B10822825 : Blo 1405522 10822825 := bstep (se 2 (by rfl) ⟨4058559, by rfl⟩ : syracuseStep 10822825 = 8117119) B8117119
theorem B73090633 : Blo 1405522 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B3164201 : Blo 1405522 3164201 := bstep (se 2 (by rfl) ⟨1186575, by rfl⟩ : syracuseStep 3164201 = 2373151) B2373151
theorem B16026335 : Blo 1405522 16026335 := bstep (se 1 (by rfl) ⟨12019751, by rfl⟩ : syracuseStep 16026335 = 24039503) B24039503
theorem B7123625 : Blo 1405522 7123625 := bstep (se 2 (by rfl) ⟨2671359, by rfl⟩ : syracuseStep 7123625 = 5342719) B5342719
theorem B102717071 : Blo 1405522 102717071 := bstep (se 1 (by rfl) ⟨77037803, by rfl⟩ : syracuseStep 102717071 = 154075607) B154075607
theorem B1406719 : Blo 1405522 1406719 := bstep (se 1 (by rfl) ⟨1055039, by rfl⟩ : syracuseStep 1406719 = 2110079) B2110079
theorem B3005383 : Blo 1405522 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B328826351 : Blo 1405522 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B57721733 : Blo 1405522 57721733 := bstep (se 4 (by rfl) ⟨5411412, by rfl⟩ : syracuseStep 57721733 = 10822825) B10822825
theorem B68478047 : Blo 1405522 68478047 := bstep (se 1 (by rfl) ⟨51358535, by rfl⟩ : syracuseStep 68478047 = 102717071) B102717071
theorem B4007177 : Blo 1405522 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B10684223 : Blo 1405522 10684223 := bstep (se 1 (by rfl) ⟨8013167, by rfl⟩ : syracuseStep 10684223 = 16026335) B16026335
theorem B97454177 : Blo 1405522 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B2109467 : Blo 1405522 2109467 := bstep (se 1 (by rfl) ⟨1582100, by rfl⟩ : syracuseStep 2109467 = 3164201) B3164201
theorem B4749083 : Blo 1405522 4749083 := bstep (se 1 (by rfl) ⟨3561812, by rfl⟩ : syracuseStep 4749083 = 7123625) B7123625
theorem B876870269 : Blo 1405522 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B2671451 : Blo 1405522 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B38481155 : Blo 1405522 38481155 := bstep (se 1 (by rfl) ⟨28860866, by rfl⟩ : syracuseStep 38481155 = 57721733) B57721733
theorem B3166055 : Blo 1405522 3166055 := bstep (se 1 (by rfl) ⟨2374541, by rfl⟩ : syracuseStep 3166055 = 4749083) B4749083
theorem B7122815 : Blo 1405522 7122815 := bstep (se 1 (by rfl) ⟨5342111, by rfl⟩ : syracuseStep 7122815 = 10684223) B10684223
theorem B1406311 : Blo 1405522 1406311 := bstep (se 1 (by rfl) ⟨1054733, by rfl⟩ : syracuseStep 1406311 = 2109467) B2109467
theorem B45652031 : Blo 1405522 45652031 := bstep (se 1 (by rfl) ⟨34239023, by rfl⟩ : syracuseStep 45652031 = 68478047) B68478047
theorem B64969451 : Blo 1405522 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B584580179 : Blo 1405522 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B30434687 : Blo 1405522 30434687 := bstep (se 1 (by rfl) ⟨22826015, by rfl⟩ : syracuseStep 30434687 = 45652031) B45652031
theorem B43312967 : Blo 1405522 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B389720119 : Blo 1405522 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B1780967 : Blo 1405522 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B25654103 : Blo 1405522 25654103 := bstep (se 1 (by rfl) ⟨19240577, by rfl⟩ : syracuseStep 25654103 = 38481155) B38481155
theorem B2110703 : Blo 1405522 2110703 := bstep (se 1 (by rfl) ⟨1583027, by rfl⟩ : syracuseStep 2110703 = 3166055) B3166055
theorem B4748543 : Blo 1405522 4748543 := bstep (se 1 (by rfl) ⟨3561407, by rfl⟩ : syracuseStep 4748543 = 7122815) B7122815
theorem B519626825 : Blo 1405522 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B3165695 : Blo 1405522 3165695 := bstep (se 1 (by rfl) ⟨2374271, by rfl⟩ : syracuseStep 3165695 = 4748543) B4748543
theorem B17102735 : Blo 1405522 17102735 := bstep (se 1 (by rfl) ⟨12827051, by rfl⟩ : syracuseStep 17102735 = 25654103) B25654103
theorem B4749245 : Blo 1405522 4749245 := bstep (se 3 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 4749245 = 1780967) B1780967
theorem B1407135 : Blo 1405522 1407135 := bstep (se 1 (by rfl) ⟨1055351, by rfl⟩ : syracuseStep 1407135 = 2110703) B2110703
theorem B20289791 : Blo 1405522 20289791 := bstep (se 1 (by rfl) ⟨15217343, by rfl⟩ : syracuseStep 20289791 = 30434687) B30434687
theorem B28875311 : Blo 1405522 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B13526527 : Blo 1405522 13526527 := bstep (se 1 (by rfl) ⟨10144895, by rfl⟩ : syracuseStep 13526527 = 20289791) B20289791
theorem B346417883 : Blo 1405522 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B3166163 : Blo 1405522 3166163 := bstep (se 1 (by rfl) ⟨2374622, by rfl⟩ : syracuseStep 3166163 = 4749245) B4749245
theorem B2110463 : Blo 1405522 2110463 := bstep (se 1 (by rfl) ⟨1582847, by rfl⟩ : syracuseStep 2110463 = 3165695) B3165695
theorem B11401823 : Blo 1405522 11401823 := bstep (se 1 (by rfl) ⟨8551367, by rfl⟩ : syracuseStep 11401823 = 17102735) B17102735
theorem B19250207 : Blo 1405522 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B230945255 : Blo 1405522 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B18035369 : Blo 1405522 18035369 := bstep (se 2 (by rfl) ⟨6763263, by rfl⟩ : syracuseStep 18035369 = 13526527) B13526527
theorem B12833471 : Blo 1405522 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B2110775 : Blo 1405522 2110775 := bstep (se 1 (by rfl) ⟨1583081, by rfl⟩ : syracuseStep 2110775 = 3166163) B3166163
theorem B1406975 : Blo 1405522 1406975 := bstep (se 1 (by rfl) ⟨1055231, by rfl⟩ : syracuseStep 1406975 = 2110463) B2110463
theorem B7601215 : Blo 1405522 7601215 := bstep (se 1 (by rfl) ⟨5700911, by rfl⟩ : syracuseStep 7601215 = 11401823) B11401823
theorem B10134953 : Blo 1405522 10134953 := bstep (se 2 (by rfl) ⟨3800607, by rfl⟩ : syracuseStep 10134953 = 7601215) B7601215
theorem B153963503 : Blo 1405522 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B8555647 : Blo 1405522 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B12023579 : Blo 1405522 12023579 := bstep (se 1 (by rfl) ⟨9017684, by rfl⟩ : syracuseStep 12023579 = 18035369) B18035369
theorem B1407183 : Blo 1405522 1407183 := bstep (se 1 (by rfl) ⟨1055387, by rfl⟩ : syracuseStep 1407183 = 2110775) B2110775
theorem B8015719 : Blo 1405522 8015719 := bstep (se 1 (by rfl) ⟨6011789, by rfl⟩ : syracuseStep 8015719 = 12023579) B12023579
theorem B11407529 : Blo 1405522 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B102642335 : Blo 1405522 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B6756635 : Blo 1405522 6756635 := bstep (se 1 (by rfl) ⟨5067476, by rfl⟩ : syracuseStep 6756635 = 10134953) B10134953
theorem B68428223 : Blo 1405522 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B7605019 : Blo 1405522 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B10687625 : Blo 1405522 10687625 := bstep (se 2 (by rfl) ⟨4007859, by rfl⟩ : syracuseStep 10687625 = 8015719) B8015719
theorem B4504423 : Blo 1405522 4504423 := bstep (se 1 (by rfl) ⟨3378317, by rfl⟩ : syracuseStep 4504423 = 6756635) B6756635
theorem B6005897 : Blo 1405522 6005897 := bstep (se 2 (by rfl) ⟨2252211, by rfl⟩ : syracuseStep 6005897 = 4504423) B4504423
theorem B40560101 : Blo 1405522 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B45618815 : Blo 1405522 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B7125083 : Blo 1405522 7125083 := bstep (se 1 (by rfl) ⟨5343812, by rfl⟩ : syracuseStep 7125083 = 10687625) B10687625
theorem B30412543 : Blo 1405522 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B4003931 : Blo 1405522 4003931 := bstep (se 1 (by rfl) ⟨3002948, by rfl⟩ : syracuseStep 4003931 = 6005897) B6005897
theorem B27040067 : Blo 1405522 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B4750055 : Blo 1405522 4750055 := bstep (se 1 (by rfl) ⟨3562541, by rfl⟩ : syracuseStep 4750055 = 7125083) B7125083
theorem B18026711 : Blo 1405522 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B3166703 : Blo 1405522 3166703 := bstep (se 1 (by rfl) ⟨2375027, by rfl⟩ : syracuseStep 3166703 = 4750055) B4750055
theorem B2669287 : Blo 1405522 2669287 := bstep (se 1 (by rfl) ⟨2001965, by rfl⟩ : syracuseStep 2669287 = 4003931) B4003931
theorem B40550057 : Blo 1405522 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B12017807 : Blo 1405522 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B3559049 : Blo 1405522 3559049 := bstep (se 2 (by rfl) ⟨1334643, by rfl⟩ : syracuseStep 3559049 = 2669287) B2669287
theorem B2111135 : Blo 1405522 2111135 := bstep (se 1 (by rfl) ⟨1583351, by rfl⟩ : syracuseStep 2111135 = 3166703) B3166703
theorem B27033371 : Blo 1405522 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B8011871 : Blo 1405522 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B2372699 : Blo 1405522 2372699 := bstep (se 1 (by rfl) ⟨1779524, by rfl⟩ : syracuseStep 2372699 = 3559049) B3559049
theorem B1407423 : Blo 1405522 1407423 := bstep (se 1 (by rfl) ⟨1055567, by rfl⟩ : syracuseStep 1407423 = 2111135) B2111135
theorem B18022247 : Blo 1405522 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B5341247 : Blo 1405522 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B1581799 : Blo 1405522 1581799 := bstep (se 1 (by rfl) ⟨1186349, by rfl⟩ : syracuseStep 1581799 = 2372699) B2372699
theorem B12014831 : Blo 1405522 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B2109065 : Blo 1405522 2109065 := bstep (se 2 (by rfl) ⟨790899, by rfl⟩ : syracuseStep 2109065 = 1581799) B1581799
theorem B3560831 : Blo 1405522 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B8009887 : Blo 1405522 8009887 := bstep (se 1 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 8009887 = 12014831) B12014831
theorem B1406043 : Blo 1405522 1406043 := bstep (se 1 (by rfl) ⟨1054532, by rfl⟩ : syracuseStep 1406043 = 2109065) B2109065
theorem B10679849 : Blo 1405522 10679849 := bstep (se 2 (by rfl) ⟨4004943, by rfl⟩ : syracuseStep 10679849 = 8009887) B8009887
theorem B2373887 : Blo 1405522 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B7119899 : Blo 1405522 7119899 := bstep (se 1 (by rfl) ⟨5339924, by rfl⟩ : syracuseStep 7119899 = 10679849) B10679849
theorem B1582591 : Blo 1405522 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B4746599 : Blo 1405522 4746599 := bstep (se 1 (by rfl) ⟨3559949, by rfl⟩ : syracuseStep 4746599 = 7119899) B7119899
theorem B2110121 : Blo 1405522 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B3164399 : Blo 1405522 3164399 := bstep (se 1 (by rfl) ⟨2373299, by rfl⟩ : syracuseStep 3164399 = 4746599) B4746599
theorem B1406747 : Blo 1405522 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B2109599 : Blo 1405522 2109599 := bstep (se 1 (by rfl) ⟨1582199, by rfl⟩ : syracuseStep 2109599 = 3164399) B3164399
theorem B1406399 : Blo 1405522 1406399 := bstep (se 1 (by rfl) ⟨1054799, by rfl⟩ : syracuseStep 1406399 = 2109599) B2109599

theorem C0 (j : ℕ) (h1 : 351380 ≤ j) (h2 : j ≤ 351879) : Blo 1405522 (4 * j + 3) := by
  interval_cases j
  · exact B1405523
  · exact B1405527
  · exact B1405531
  · exact B1405535
  · exact B1405539
  · exact B1405543
  · exact B1405547
  · exact B1405551
  · exact B1405555
  · exact B1405559
  · exact B1405563
  · exact B1405567
  · exact B1405571
  · exact B1405575
  · exact B1405579
  · exact B1405583
  · exact B1405587
  · exact B1405591
  · exact B1405595
  · exact B1405599
  · exact B1405603
  · exact B1405607
  · exact B1405611
  · exact B1405615
  · exact B1405619
  · exact B1405623
  · exact B1405627
  · exact B1405631
  · exact B1405635
  · exact B1405639
  · exact B1405643
  · exact B1405647
  · exact B1405651
  · exact B1405655
  · exact B1405659
  · exact B1405663
  · exact B1405667
  · exact B1405671
  · exact B1405675
  · exact B1405679
  · exact B1405683
  · exact B1405687
  · exact B1405691
  · exact B1405695
  · exact B1405699
  · exact B1405703
  · exact B1405707
  · exact B1405711
  · exact B1405715
  · exact B1405719
  · exact B1405723
  · exact B1405727
  · exact B1405731
  · exact B1405735
  · exact B1405739
  · exact B1405743
  · exact B1405747
  · exact B1405751
  · exact B1405755
  · exact B1405759
  · exact B1405763
  · exact B1405767
  · exact B1405771
  · exact B1405775
  · exact B1405779
  · exact B1405783
  · exact B1405787
  · exact B1405791
  · exact B1405795
  · exact B1405799
  · exact B1405803
  · exact B1405807
  · exact B1405811
  · exact B1405815
  · exact B1405819
  · exact B1405823
  · exact B1405827
  · exact B1405831
  · exact B1405835
  · exact B1405839
  · exact B1405843
  · exact B1405847
  · exact B1405851
  · exact B1405855
  · exact B1405859
  · exact B1405863
  · exact B1405867
  · exact B1405871
  · exact B1405875
  · exact B1405879
  · exact B1405883
  · exact B1405887
  · exact B1405891
  · exact B1405895
  · exact B1405899
  · exact B1405903
  · exact B1405907
  · exact B1405911
  · exact B1405915
  · exact B1405919
  · exact B1405923
  · exact B1405927
  · exact B1405931
  · exact B1405935
  · exact B1405939
  · exact B1405943
  · exact B1405947
  · exact B1405951
  · exact B1405955
  · exact B1405959
  · exact B1405963
  · exact B1405967
  · exact B1405971
  · exact B1405975
  · exact B1405979
  · exact B1405983
  · exact B1405987
  · exact B1405991
  · exact B1405995
  · exact B1405999
  · exact B1406003
  · exact B1406007
  · exact B1406011
  · exact B1406015
  · exact B1406019
  · exact B1406023
  · exact B1406027
  · exact B1406031
  · exact B1406035
  · exact B1406039
  · exact B1406043
  · exact B1406047
  · exact B1406051
  · exact B1406055
  · exact B1406059
  · exact B1406063
  · exact B1406067
  · exact B1406071
  · exact B1406075
  · exact B1406079
  · exact B1406083
  · exact B1406087
  · exact B1406091
  · exact B1406095
  · exact B1406099
  · exact B1406103
  · exact B1406107
  · exact B1406111
  · exact B1406115
  · exact B1406119
  · exact B1406123
  · exact B1406127
  · exact B1406131
  · exact B1406135
  · exact B1406139
  · exact B1406143
  · exact B1406147
  · exact B1406151
  · exact B1406155
  · exact B1406159
  · exact B1406163
  · exact B1406167
  · exact B1406171
  · exact B1406175
  · exact B1406179
  · exact B1406183
  · exact B1406187
  · exact B1406191
  · exact B1406195
  · exact B1406199
  · exact B1406203
  · exact B1406207
  · exact B1406211
  · exact B1406215
  · exact B1406219
  · exact B1406223
  · exact B1406227
  · exact B1406231
  · exact B1406235
  · exact B1406239
  · exact B1406243
  · exact B1406247
  · exact B1406251
  · exact B1406255
  · exact B1406259
  · exact B1406263
  · exact B1406267
  · exact B1406271
  · exact B1406275
  · exact B1406279
  · exact B1406283
  · exact B1406287
  · exact B1406291
  · exact B1406295
  · exact B1406299
  · exact B1406303
  · exact B1406307
  · exact B1406311
  · exact B1406315
  · exact B1406319
  · exact B1406323
  · exact B1406327
  · exact B1406331
  · exact B1406335
  · exact B1406339
  · exact B1406343
  · exact B1406347
  · exact B1406351
  · exact B1406355
  · exact B1406359
  · exact B1406363
  · exact B1406367
  · exact B1406371
  · exact B1406375
  · exact B1406379
  · exact B1406383
  · exact B1406387
  · exact B1406391
  · exact B1406395
  · exact B1406399
  · exact B1406403
  · exact B1406407
  · exact B1406411
  · exact B1406415
  · exact B1406419
  · exact B1406423
  · exact B1406427
  · exact B1406431
  · exact B1406435
  · exact B1406439
  · exact B1406443
  · exact B1406447
  · exact B1406451
  · exact B1406455
  · exact B1406459
  · exact B1406463
  · exact B1406467
  · exact B1406471
  · exact B1406475
  · exact B1406479
  · exact B1406483
  · exact B1406487
  · exact B1406491
  · exact B1406495
  · exact B1406499
  · exact B1406503
  · exact B1406507
  · exact B1406511
  · exact B1406515
  · exact B1406519
  · exact B1406523
  · exact B1406527
  · exact B1406531
  · exact B1406535
  · exact B1406539
  · exact B1406543
  · exact B1406547
  · exact B1406551
  · exact B1406555
  · exact B1406559
  · exact B1406563
  · exact B1406567
  · exact B1406571
  · exact B1406575
  · exact B1406579
  · exact B1406583
  · exact B1406587
  · exact B1406591
  · exact B1406595
  · exact B1406599
  · exact B1406603
  · exact B1406607
  · exact B1406611
  · exact B1406615
  · exact B1406619
  · exact B1406623
  · exact B1406627
  · exact B1406631
  · exact B1406635
  · exact B1406639
  · exact B1406643
  · exact B1406647
  · exact B1406651
  · exact B1406655
  · exact B1406659
  · exact B1406663
  · exact B1406667
  · exact B1406671
  · exact B1406675
  · exact B1406679
  · exact B1406683
  · exact B1406687
  · exact B1406691
  · exact B1406695
  · exact B1406699
  · exact B1406703
  · exact B1406707
  · exact B1406711
  · exact B1406715
  · exact B1406719
  · exact B1406723
  · exact B1406727
  · exact B1406731
  · exact B1406735
  · exact B1406739
  · exact B1406743
  · exact B1406747
  · exact B1406751
  · exact B1406755
  · exact B1406759
  · exact B1406763
  · exact B1406767
  · exact B1406771
  · exact B1406775
  · exact B1406779
  · exact B1406783
  · exact B1406787
  · exact B1406791
  · exact B1406795
  · exact B1406799
  · exact B1406803
  · exact B1406807
  · exact B1406811
  · exact B1406815
  · exact B1406819
  · exact B1406823
  · exact B1406827
  · exact B1406831
  · exact B1406835
  · exact B1406839
  · exact B1406843
  · exact B1406847
  · exact B1406851
  · exact B1406855
  · exact B1406859
  · exact B1406863
  · exact B1406867
  · exact B1406871
  · exact B1406875
  · exact B1406879
  · exact B1406883
  · exact B1406887
  · exact B1406891
  · exact B1406895
  · exact B1406899
  · exact B1406903
  · exact B1406907
  · exact B1406911
  · exact B1406915
  · exact B1406919
  · exact B1406923
  · exact B1406927
  · exact B1406931
  · exact B1406935
  · exact B1406939
  · exact B1406943
  · exact B1406947
  · exact B1406951
  · exact B1406955
  · exact B1406959
  · exact B1406963
  · exact B1406967
  · exact B1406971
  · exact B1406975
  · exact B1406979
  · exact B1406983
  · exact B1406987
  · exact B1406991
  · exact B1406995
  · exact B1406999
  · exact B1407003
  · exact B1407007
  · exact B1407011
  · exact B1407015
  · exact B1407019
  · exact B1407023
  · exact B1407027
  · exact B1407031
  · exact B1407035
  · exact B1407039
  · exact B1407043
  · exact B1407047
  · exact B1407051
  · exact B1407055
  · exact B1407059
  · exact B1407063
  · exact B1407067
  · exact B1407071
  · exact B1407075
  · exact B1407079
  · exact B1407083
  · exact B1407087
  · exact B1407091
  · exact B1407095
  · exact B1407099
  · exact B1407103
  · exact B1407107
  · exact B1407111
  · exact B1407115
  · exact B1407119
  · exact B1407123
  · exact B1407127
  · exact B1407131
  · exact B1407135
  · exact B1407139
  · exact B1407143
  · exact B1407147
  · exact B1407151
  · exact B1407155
  · exact B1407159
  · exact B1407163
  · exact B1407167
  · exact B1407171
  · exact B1407175
  · exact B1407179
  · exact B1407183
  · exact B1407187
  · exact B1407191
  · exact B1407195
  · exact B1407199
  · exact B1407203
  · exact B1407207
  · exact B1407211
  · exact B1407215
  · exact B1407219
  · exact B1407223
  · exact B1407227
  · exact B1407231
  · exact B1407235
  · exact B1407239
  · exact B1407243
  · exact B1407247
  · exact B1407251
  · exact B1407255
  · exact B1407259
  · exact B1407263
  · exact B1407267
  · exact B1407271
  · exact B1407275
  · exact B1407279
  · exact B1407283
  · exact B1407287
  · exact B1407291
  · exact B1407295
  · exact B1407299
  · exact B1407303
  · exact B1407307
  · exact B1407311
  · exact B1407315
  · exact B1407319
  · exact B1407323
  · exact B1407327
  · exact B1407331
  · exact B1407335
  · exact B1407339
  · exact B1407343
  · exact B1407347
  · exact B1407351
  · exact B1407355
  · exact B1407359
  · exact B1407363
  · exact B1407367
  · exact B1407371
  · exact B1407375
  · exact B1407379
  · exact B1407383
  · exact B1407387
  · exact B1407391
  · exact B1407395
  · exact B1407399
  · exact B1407403
  · exact B1407407
  · exact B1407411
  · exact B1407415
  · exact B1407419
  · exact B1407423
  · exact B1407427
  · exact B1407431
  · exact B1407435
  · exact B1407439
  · exact B1407443
  · exact B1407447
  · exact B1407451
  · exact B1407455
  · exact B1407459
  · exact B1407463
  · exact B1407467
  · exact B1407471
  · exact B1407475
  · exact B1407479
  · exact B1407483
  · exact B1407487
  · exact B1407491
  · exact B1407495
  · exact B1407499
  · exact B1407503
  · exact B1407507
  · exact B1407511
  · exact B1407515
  · exact B1407519

theorem solution (m : ℕ) (hlo : 1405522 ≤ m) (hhi : m ≤ 1407522) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 351380 ≤ j := by omega
    have hj2 : j ≤ 351879 := by omega
    have hb : Blo 1405522 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
